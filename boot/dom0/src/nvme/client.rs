//! Port of Atmosphere's `dom0/src/nvme_client.rs`: the NVMe benchmark in the thesis's three
//! configurations, sequential 4 KiB reads and writes with submission batches of 1 and 32, each run for
//! `NVME_BENCH_SECS` seconds.
//!
//! 1. `linked`: the driver statically linked into dom0's own thread (`run_blocktest_raw_with_delay`).
//! 2. `ipc`: the driver in a child process on CPU 0, like dom0. The client fills a batch into the shared
//!    ring and calls the driver once per batch (`call`); the driver runs one
//!    `submit_and_poll_breq_with_ringbuffer` and answers with `reply_and_receive`.
//! 3. `twocore`: the same driver process polling the ring on CPU 1 while the client spins on CPU 0, as
//!    in Atmosphere's ring-buffer client (`test_nvme_with_ring_buffer_ap`).
//!
//! The driver process shares dom0's image (and so the statics below) and gets the function with
//! `send_pci`, BAR0 and the ring pages with `send_pages`; it maps its DMA memory into its own IOMMU table.
//! CPU 1 is Off during the first two configurations, so the driver process cannot move off CPU 0, and
//! online again from the third on. Each configuration ends with the controller disabled, and the child
//! killed, which returns the function to dom0 detached.

use super::device::{num_lbas, NvmeDevice};
use super::nvme_test::{report, run_blocktest_raw_with_delay, Samples};
use super::pci::{find_nvme, NvmeFunction, PciBarAddr};
use super::ring_buffer::GenericRingBuffer;
use super::time::{rdtsc, tsc_hz};
use super::{BlockOp, BlockReq};
use crate::{check, current_cpu, entry, expect_error, fund, quiet, stack_top, wait_for, wait_yield};
use core::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use vsys::*;

/// Seconds per run; `VERIFLAT_NVME_SECS` of the dom0 build overrides the default 2 (30 for the thesis's
/// runs).
pub const NVME_BENCH_SECS: u64 = match option_env!("VERIFLAT_NVME_SECS") {
    Some(s) => parse_u64(s),
    None => 2,
};

const fn parse_u64(s: &str) -> u64 {
    let b = s.as_bytes();
    let mut i = 0;
    let mut v = 0;
    while i < b.len() {
        assert!(b[i].is_ascii_digit(), "VERIFLAT_NVME_SECS must be a decimal number");
        v = v * 10 + (b[i] - b'0') as u64;
        i += 1;
    }
    v
}

/// The runs of each configuration: (write, batch).
const RUNS: [(bool, u64); 4] = [(false, 1), (false, 32), (true, 1), (true, 32)];

/// dom0's descriptor of the endpoint the driver process holds in its descriptor 0.
const NVME_ENDPOINT: usize = 7;
/// The shared ring, at the same address in both processes.
const RING_VA: usize = 0xda_0000_0000;
const RING_PAGES: usize = core::mem::size_of::<Ring>().div_ceil(4096);
type Ring = GenericRingBuffer<BlockReq, BlockReq>;
/// The CPU the `twocore` driver polls on.
const DRIVER_CPU: usize = 1;

const MODE_IPC: usize = 1;
const MODE_TWOCORE: usize = 2;

static mut DRIVER_STACK: [u8; 128 * 1024] = [0; 128 * 1024];
/// The function, its BAR0, and the configuration, for the driver process.
static FN_BDF: AtomicUsize = AtomicUsize::new(0);
static FN_BAR_PHYS: AtomicUsize = AtomicUsize::new(0);
static FN_BAR_PAGES: AtomicUsize = AtomicUsize::new(0);
static MODE: AtomicUsize = AtomicUsize::new(0);
/// Set once the driver process initialized the controller.
static DRIVER_READY: AtomicBool = AtomicBool::new(false);
/// One plus the CPU the driver first served on; 0 until then.
static DRIVER_RAN_ON: AtomicUsize = AtomicUsize::new(0);
static STOP: AtomicBool = AtomicBool::new(false);
static STOPPED: AtomicBool = AtomicBool::new(false);

fn shared_function() -> NvmeFunction {
    let bdf = FN_BDF.load(Ordering::SeqCst);
    NvmeFunction {
        bus: bdf >> 8, dev: (bdf >> 3) & 0x1f, fun: bdf & 7, vendor: 0, device: 0,
        bar_phys: FN_BAR_PHYS.load(Ordering::SeqCst), bar_pages: FN_BAR_PAGES.load(Ordering::SeqCst),
    }
}

fn ring() -> &'static mut Ring {
    unsafe { &mut *(RING_VA as *mut Ring) }
}

/// Runs the three configurations, or logs that it skips them when bus 0 has no NVMe function.
pub fn run(image: usize, pages: usize) {
    let Some(f) = find_nvme() else {
        log::info!("nvme bench skipped: no NVMe function on bus 0");
        return;
    };
    log::info!(
        "nvme: {:02x}:{:02x}.{} vendor {:04x} device {:04x}, BAR0 {:#x} ({} pages) at {:#x}, {} s per run, TSC {} MHz",
        f.bus, f.dev, f.fun, f.vendor, f.device, f.bar_phys, f.bar_pages, f.bar_va(), NVME_BENCH_SECS, tsc_hz() / 1_000_000
    );
    FN_BDF.store(f.bus << 8 | f.dev << 3 | f.fun, Ordering::SeqCst);
    FN_BAR_PHYS.store(f.bar_phys, Ordering::SeqCst);
    FN_BAR_PAGES.store(f.bar_pages, Ordering::SeqCst);
    crate::slab_alloc::init();
    take_driver_cpu_off();

    // 1. linked
    check("nvme pci_attach_dma (dom0)", unsafe { sys_pci_attach_dma(f.bus, f.dev, f.fun) });
    {
        let mut dev = NvmeDevice::new(f.bar());
        dev.init();
        for (is_write, batch) in RUNS {
            run_blocktest_raw_with_delay(&mut dev, NVME_BENCH_SECS, batch, is_write, false, 0);
        }
        dev.shutdown();
    }

    // 2. ipc and 3. twocore, over one ring that dom0 maps and shares with each driver process.
    fund("nvme ring funding", 3 * RING_PAGES);
    check("nvme mmap_4k (ring)", unsafe { sys_mmap_4k(RING_VA, RING_PAGES) });
    check("nvme new_endpoint", unsafe { sys_new_endpoint(NVME_ENDPOINT) });
    for mode in [MODE_IPC, MODE_TWOCORE] {
        ring_configuration(&f, mode, image, pages);
    }
    check("nvme unmap_4k (ring)", unsafe { sys_unmap_4k(RING_VA, RING_PAGES) });
    log::info!("nvme bench passed");
}

/// Takes CPU 1 Off: an offline request succeeds once and then fails with ErrorCpuAlreadyOff once it is Off.
fn take_driver_cpu_off() {
    check("nvme cpu_offline_request(1)", unsafe { sys_cpu_offline_request(DRIVER_CPU) });
    let start = rdtsc();
    loop {
        let ret = unsafe { sys_cpu_offline_request(DRIVER_CPU) };
        if error_name(ret) == "ErrorCpuAlreadyOff" {
            return;
        }
        if ret < 0 || rdtsc() - start > crate::WAIT_LIMIT {
            expect_error("nvme cpu_offline_request until CPU 1 is Off", ret, "ErrorCpuAlreadyOff");
        }
        core::hint::spin_loop();
    }
}

fn ring_configuration(f: &NvmeFunction, mode: usize, image: usize, pages: usize) {
    let (config, expected_cpu) = if mode == MODE_IPC { ("ipc", 0) } else { ("twocore", DRIVER_CPU) };
    ring().init();
    MODE.store(mode, Ordering::SeqCst);
    for flag in [&DRIVER_READY, &STOP, &STOPPED] {
        flag.store(false, Ordering::SeqCst);
    }
    DRIVER_RAN_ON.store(0, Ordering::SeqCst);

    fund("nvme driver process funding", 6 + 3 * pages);
    let sp = stack_top(&raw const DRIVER_STACK);
    check("nvme new_process_with_iommu_and_endpoint (driver)", unsafe {
        sys_new_process_with_iommu_and_endpoint(image, pages, NVME_ENDPOINT, entry(nvme_driver_process), sp)
    });
    check("nvme send_pci", unsafe { sys_send_pci(NVME_ENDPOINT, f.bus, f.dev, f.fun) });
    check("nvme send_pages (BAR0)", unsafe { sys_send_pages(NVME_ENDPOINT, f.bar_va(), f.bar_pages) });
    check("nvme send_pages (ring)", unsafe { sys_send_pages(NVME_ENDPOINT, RING_VA, RING_PAGES) });
    wait_yield("the NVMe driver process to initialize the controller", || DRIVER_READY.load(Ordering::SeqCst));
    if mode == MODE_TWOCORE {
        // CPU 1 comes online and pulls the only queued thread, the driver, which yields until it runs there.
        check("nvme cpu_online(1)", unsafe { sys_cpu_online(DRIVER_CPU) });
        wait_for("the NVMe driver on CPU 1", || DRIVER_RAN_ON.load(Ordering::SeqCst) != 0);
    }

    for (is_write, batch) in RUNS {
        run_ring_client(config, mode == MODE_IPC, is_write, batch);
    }

    STOP.store(true, Ordering::SeqCst);
    if mode == MODE_IPC {
        quiet("nvme call (stop)", unsafe { sys_call(NVME_ENDPOINT) });
    }
    wait_for("the NVMe driver to stop", || STOPPED.load(Ordering::SeqCst));
    let ran_on = DRIVER_RAN_ON.load(Ordering::SeqCst);
    if ran_on != expected_cpu + 1 {
        log::error!("nvme {}: the driver served on CPU {}, expected {}", config, ran_on as isize - 1, expected_cpu);
        unsafe { sys_debug_exit(1) };
    }
    check("nvme kill_process(0) (driver)", unsafe { sys_kill_process(0) });
}

/// The client of the ring configurations, after Atmosphere's ring-buffer client: each round takes up to
/// `batch_sz` replies, recycling their buffers, and pushes up to `batch_sz` new sequential requests, then
/// in the `ipc` configuration calls the driver. A sample is one round including the call (`ipc`), or
/// the cycles since the previous round that moved a request (`twocore`). At the end the client waits
/// for every request it pushed.
fn run_ring_client(config: &str, ipc: bool, is_write: bool, batch_sz: u64) {
    let ring = ring();
    let op = if is_write { BlockOp::Write } else { BlockOp::Read };
    let max_block_num = num_lbas().saturating_sub(8).max(8);
    let (mut block_num, mut in_flight, mut completed) = (0u64, 0u64, 0u64);
    let mut samples = Samples::new();
    let call = || quiet("nvme call", unsafe { sys_call(NVME_ENDPOINT) });
    let pop = |ring: &mut Ring, in_flight: &mut u64| {
        let mut pop_count = 0;
        while pop_count < batch_sz {
            let Some(breq) = ring.reply_queue.try_pop() else { break };
            ring.try_push_allocator(breq.data);
            pop_count += 1;
        }
        *in_flight -= pop_count;
        pop_count
    };

    let tsc_start = rdtsc();
    let tsc_end = tsc_start + NVME_BENCH_SECS * tsc_hz();
    let mut last = tsc_start;
    loop {
        let round_start = rdtsc();
        let pop_count = pop(ring, &mut in_flight);
        completed += pop_count;
        let mut push_count = 0;
        while push_count < batch_sz && !ring.request_queue.is_full() {
            let Some(data) = ring.try_pop_allocator() else { break };
            ring.request_queue.try_push(&BlockReq::new(block_num, 8, data, op));
            block_num = (block_num + 8) % max_block_num;
            push_count += 1;
        }
        in_flight += push_count;
        if ipc {
            call();
        }
        let now = rdtsc();
        if ipc {
            samples.record(now - round_start);
        } else if pop_count + push_count > 0 {
            samples.record(now - last);
            last = now;
        }
        if now > tsc_end {
            break;
        }
    }
    let elapsed = rdtsc() - tsc_start;

    let drain_start = rdtsc();
    while in_flight > 0 {
        pop(ring, &mut in_flight);
        if ipc {
            call();
        }
        if rdtsc() - drain_start > 10 * tsc_hz() {
            log::error!("nvme {}: {} requests still pending after the run", config, in_flight);
            unsafe { sys_debug_exit(1) };
        }
    }
    report(config, is_write, batch_sz, completed, elapsed, if ipc { "batch+call" } else { "batch period" }, &mut samples);
}

/// First thread of the driver process: takes the function, BAR0, and the ring from dom0, maps the ring
/// into its IOMMU table, attaches the function, initializes the controller, and serves the ring, once
/// per call (`ipc`) or polling on CPU 1 (`twocore`) until dom0 sets `STOP`. Then it disables the
/// controller and blocks until dom0 kills it.
extern "C" fn nvme_driver_process() -> ! {
    let f = shared_function();
    // A receiver holds 3 4K quota per page for the worst case of page tables (as do mmap and IOMMU maps).
    fund("nvme driver receive funding", 3 * (f.bar_pages + RING_PAGES));
    quiet("nvme driver receive_pci", unsafe { sys_receive_pci(0, f.bus, f.dev, f.fun) });
    quiet("nvme driver receive_pages (BAR0)", unsafe { sys_receive_pages(0, f.bar_va(), f.bar_pages) });
    quiet("nvme driver receive_pages (ring)", unsafe { sys_receive_pages(0, RING_VA, RING_PAGES) });
    crate::slab_alloc::init();
    fund("nvme driver ring IOMMU funding", 3 * RING_PAGES);
    quiet("nvme driver iommu_map_4k (ring)", unsafe { sys_iommu_map_4k(RING_VA, RING_VA, RING_PAGES) });
    quiet("nvme driver pci_attach_dma", unsafe { sys_pci_attach_dma(f.bus, f.dev, f.fun) });
    let mut dev = NvmeDevice::new(PciBarAddr::new(f.bar_va() as u64, f.bar_pages * 4096));
    dev.init();
    let ring = ring();
    DRIVER_READY.store(true, Ordering::SeqCst);
    if MODE.load(Ordering::SeqCst) == MODE_IPC {
        quiet("nvme driver receive_call", unsafe { sys_receive_call(0) });
        DRIVER_RAN_ON.store(current_cpu() + 1, Ordering::SeqCst);
        loop {
            dev.submit_and_poll_breq_with_ringbuffer(&mut ring.request_queue, &mut ring.reply_queue);
            if STOP.load(Ordering::SeqCst) {
                dev.shutdown();
                STOPPED.store(true, Ordering::SeqCst);
            }
            quiet("nvme driver reply_and_receive", unsafe { sys_reply_and_receive(0) });
        }
    }
    while current_cpu() != DRIVER_CPU {
        unsafe { sys_schedule() };
    }
    DRIVER_RAN_ON.store(current_cpu() + 1, Ordering::SeqCst);
    while !STOP.load(Ordering::SeqCst) {
        dev.submit_and_poll_breq_with_ringbuffer(&mut ring.request_queue, &mut ring.reply_queue);
    }
    dev.shutdown();
    STOPPED.store(true, Ordering::SeqCst);
    loop {
        unsafe { sys_receive_call(0) };
    }
}
