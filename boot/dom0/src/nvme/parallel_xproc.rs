//! Not in Atmosphere: the cross-process multi-queue NVMe benchmark `parallel_nvme_xproc`, `parallel_nvme` with the
//! driver and the application in two processes that pass work by IPC, one pair per CPU (`VERIFLAT_PARALLEL=nvme_xproc`
//! of a no-timer dom0).
//!
//! The driver is a child process of dom0 that shares dom0's image and has its own IOMMU table. Its first thread
//! takes the NVMe function (`send_pci`) and BAR0 (`send_pages`) from dom0, attaches the function, resets the
//! controller, sends Set Features Number of Queues and creates I/O queue pair k + 1 with its rings in its own heap
//! for each worker k, then creates driver thread k, which owns that queue pair alone. The application is dom0: worker
//! k is dom0's first thread on CPU 0 for k = 0, else the client of parallel call pair k on CPU k, as in
//! `parallel_nvme`.
//!
//! Endpoints. dom0 creates endpoint `HANDOFF_ENDPOINT` before the call pairs start and hands it to each pair client
//! over the pair's endpoint before the pair's server exists (`pair_client`); the driver process holds it in its
//! descriptor 0. Worker k creates its own endpoint and sends it over the handoff endpoint to driver thread k, which
//! holds the handoff endpoint in its descriptor 0 and receives worker k's endpoint into descriptor 1; from then on
//! the pair talks only over that endpoint. dom0 lets one driver thread wait on the handoff endpoint at a time.
//!
//! Buffers, as the `ipc` configuration of the single-queue benchmark (`client`) shares its ring: worker k maps its
//! region of `REGION_PAGES` pages (a control page, then `MAX_BATCH` 4 KiB data buffers) in dom0 and shares it with
//! `send_pages`; driver thread k receives it at the same address and maps it into the driver process's IOMMU table
//! at IOVA = VA, so the controller reads and writes the application's buffers directly.
//!
//! One round trip per round: worker k writes up to `batch - in flight` new requests (LBA, buffer, op) into its
//! control page and `call`s driver thread k with their count (`sys_call_usize`); the driver thread submits them with
//! one doorbell write, reaps every posted completion of its queue pair, waiting for at least one while any request
//! is in flight, writes their buffer numbers into the control page and answers with their count
//! (`sys_reply_and_receive_usize`). A call runs the waiting driver thread on the caller's CPU, so each pair stays on
//! its CPU without any placement. Batch, LBA ranges, phases and output follow `parallel_nvme`; the `calls` line of
//! each run gives the round trips of the concurrent phase and its completions per round trip.
//!
//! Worker count = min(CPUs, `MAX_QUEUES` = 24, the I/O queue pairs the controller allocates). Afterwards dom0 has
//! the driver disable the controller, kills the driver process, which returns the function to dom0 detached, and
//! unmaps the regions.

use super::cmd as nvme_cmd;
use super::device::{blocks_per_4k, lba_shift, num_lbas, NvmeDevice};
use super::dma::{allocate_dma, Dma, NvmeCommand, NvmeCompletion};
use super::parallel::{time_run, Measured, MAX_BATCH, MAX_QUEUES, RUNS, WINDOW_MS};
use super::pci::{choose_nvme, selected_nvme, NvmeFunction};
use super::queue::QUEUE_DEPTH;
use super::time::{rdtsc, tsc_hz, tsc_rate};
use crate::{current_cpu, entry, fund, image_range, quiet, quiet_value, stack_top, wait_for, wait_yield, PAIRS};
use crate::{PHASE_NVME_XPROC_FIRST, PHASE_NVME_XPROC_SETUP};
use core::sync::atomic::{AtomicBool, AtomicU64, AtomicU8, AtomicUsize, Ordering};
use vsys::*;

/// The phases worker k >= 1 is released into after its setup: run c alone is `PHASE_NVME_XPROC_FIRST + 2 * c`, all
/// at once the next.
pub const PHASES: usize = 2 * RUNS.len();
/// dom0's descriptor (of its first thread and of each pair client) of the endpoint the driver process's threads hold
/// in descriptor 0.
pub const HANDOFF_ENDPOINT: usize = 2;
/// The descriptor where worker k creates its endpoint to driver thread k, which holds it in descriptor 1.
const WORKER_ENDPOINT: usize = 3;
const DRIVER_ENDPOINT: usize = 1;
/// Worker k's region at `REGION_VA + k * REGION_STRIDE`, in dom0 and in the driver process, each in a 2 MiB window
/// of its own: a control page and `MAX_BATCH` data buffers. Above the heap (`0xd8_..`) and the single-queue
/// benchmark's ring (`0xda_..`).
const REGION_VA: usize = 0xdc_0000_0000;
const REGION_STRIDE: usize = 1 << 21;
const REGION_PAGES: usize = 1 + MAX_BATCH;
const DRIVER_STACK_SIZE: usize = 32 * 1024;

/// One request in worker k's control page: its first LBA, its data buffer (= command ID), and whether it writes.
#[derive(Clone, Copy)]
#[repr(C)]
struct Request {
    lba: u64,
    slot: u16,
    write: u16,
    _pad: u32,
}

/// Worker k's control page: the new requests of a call, then the buffers of the completions of its answer.
#[repr(C)]
struct Control {
    submit: [Request; MAX_BATCH],
    done: [u16; MAX_BATCH],
}

const _: () = assert!(core::mem::size_of::<Control>() <= 4096);

fn region(k: usize) -> usize {
    REGION_VA + k * REGION_STRIDE
}

fn control(k: usize) -> *mut Control {
    region(k) as *mut Control
}

fn buffer(k: usize, slot: u16) -> usize {
    region(k) + (1 + slot as usize) * 4096
}

/// I/O queue pair k + 1 of driver thread k, in the driver process's heap.
struct DriverQueue {
    sq: Dma<[NvmeCommand; QUEUE_DEPTH]>,
    cq: Dma<[NvmeCompletion; QUEUE_DEPTH]>,
    len: usize,
    tail: usize,
    head: usize,
    phase: bool,
    sq_doorbell: *mut u32,
    cq_doorbell: *mut u32,
}

// The statics below live in dom0's image, which the driver process shares: dom0 and the driver process exchange
// setup state through them, never requests.

/// Driver queue k; only the driver process touches these, its first thread before it creates driver thread k.
static mut DRIVER_QUEUES: [Option<DriverQueue>; MAX_QUEUES] = [const { None }; MAX_QUEUES];
/// The function, written by dom0 before it creates the driver process.
static mut FUNCTION: Option<NvmeFunction> = None;
/// The queue pairs dom0 asks for (one per CPU, at most `MAX_QUEUES`).
static WANTED: AtomicUsize = AtomicUsize::new(0);
/// Set by the driver's first thread once the controller is up: `READY` with `WORKERS` and `LBAS_PER_WORKER`, or
/// `SKIPPED` when the LBA size exceeds 4 KiB.
static STATUS: AtomicUsize = AtomicUsize::new(0);
const READY: usize = 1;
const SKIPPED: usize = 2;
static WORKERS: AtomicUsize = AtomicUsize::new(0);
static LBAS_PER_WORKER: AtomicU64 = AtomicU64::new(0);
/// How many driver threads dom0 lets the driver's first thread create, and the driver thread being created.
static CREATE: AtomicUsize = AtomicUsize::new(0);
static CREATING: AtomicUsize = AtomicUsize::new(0);
/// Driver thread k's setup stage: `WAITS_ENDPOINT` blocked on the handoff endpoint, `WAITS_REGION` blocked for
/// worker k's region, `SERVES` blocked for worker k's calls.
static STAGE: [AtomicU8; MAX_QUEUES] = [const { AtomicU8::new(0) }; MAX_QUEUES];
const WAITS_ENDPOINT: u8 = 1;
const WAITS_REGION: u8 = 2;
const SERVES: u8 = 3;
/// Set by the driver's first thread right before it blocks for dom0's stop call.
static PARKED: AtomicBool = AtomicBool::new(false);
static mut DRIVER_MAIN_STACK: [u8; 128 * 1024] = [0; 128 * 1024];
static mut DRIVER_STACKS: [[u8; DRIVER_STACK_SIZE]; MAX_QUEUES] = [[0; DRIVER_STACK_SIZE]; MAX_QUEUES];
/// Written by dom0 when the build runs this benchmark and the function exists, before the pair clients start.
static HANDOFF: AtomicBool = AtomicBool::new(false);

static MEASURED: [Measured; MAX_QUEUES] = [const { Measured::new() }; MAX_QUEUES];

fn fail(what: core::fmt::Arguments) -> ! {
    log::error!("parallel_nvme_xproc: {}", what);
    unsafe { sys_debug_exit(1) };
}

/// Whether the parallel call timing must hand `HANDOFF_ENDPOINT` to its clients: when the build runs this benchmark
/// (the caller checks) and `pci::choose_nvme` picks an NVMe function. Creates the endpoint in dom0's first thread,
/// funded by it.
pub fn prepare_handoff() -> bool {
    if choose_nvme().is_err() {
        return false;
    }
    fund("parallel_nvme_xproc handoff endpoint funding", 1);
    quiet("parallel_nvme_xproc new_endpoint (handoff)", unsafe { sys_new_endpoint(HANDOFF_ENDPOINT) });
    HANDOFF.store(true, Ordering::SeqCst);
    true
}

/// Whether a new pair client takes `HANDOFF_ENDPOINT` from dom0 first (`pair_client`).
pub fn handoff() -> bool {
    HANDOFF.load(Ordering::SeqCst)
}

/// Runs the benchmark over the first `n` parallel call pairs on the NVMe function `pci::selected_nvme` picks, or logs
/// that it skips it (also when its LBA size exceeds 4 KiB).
pub fn run(n: usize) {
    let Some(f) = selected_nvme("parallel_nvme_xproc") else {
        return;
    };
    if !handoff() {
        fail(format_args!("the pair clients do not hold the handoff endpoint"));
    }
    let Some((hz, source)) = tsc_rate() else {
        fail(format_args!("no CPUID source gives the TSC rate; build dom0 with VERIFLAT_TSC_MHZ set to it"));
    };
    log::info!(
        "parallel_nvme_xproc: NVMe function {:02x}:{:02x}.{} (vendor {:04x} device {:04x}, BAR0 {:#x}), TSC {} MHz from {}",
        f.bus, f.dev, f.fun, f.vendor, f.device, f.bar_phys, hz / 1_000_000, source
    );

    // The driver process: dom0's image, its own IOMMU table, the handoff endpoint; then the function and BAR0.
    unsafe { FUNCTION = Some(f) };
    WANTED.store(n.min(MAX_QUEUES), Ordering::SeqCst);
    for flag in [&STATUS, &WORKERS, &CREATE, &CREATING] {
        flag.store(0, Ordering::SeqCst);
    }
    for stage in &STAGE {
        stage.store(0, Ordering::SeqCst);
    }
    PARKED.store(false, Ordering::SeqCst);
    let (image, pages) = image_range();
    fund("parallel_nvme_xproc driver process funding", 6 + 3 * pages);
    let sp = stack_top(&raw const DRIVER_MAIN_STACK);
    quiet("parallel_nvme_xproc new_process_with_iommu_and_endpoint (driver)", unsafe {
        sys_new_process_with_iommu_and_endpoint(image, pages, HANDOFF_ENDPOINT, entry(driver_main), sp)
    });
    quiet("parallel_nvme_xproc send_pci", unsafe { sys_send_pci(HANDOFF_ENDPOINT, f.bus, f.dev, f.fun) });
    quiet("parallel_nvme_xproc send_pages (BAR0)", unsafe { sys_send_pages(HANDOFF_ENDPOINT, f.bar_va(), f.bar_pages) });
    wait_yield("the parallel_nvme_xproc driver to initialize the controller", || STATUS.load(Ordering::SeqCst) != 0);
    if STATUS.load(Ordering::SeqCst) == SKIPPED {
        wait_yield("the parallel_nvme_xproc driver to park", || PARKED.load(Ordering::SeqCst));
        quiet("parallel_nvme_xproc kill_process(0) (driver)", unsafe { sys_kill_process(0) });
        log::info!("parallel_nvme_xproc skipped: namespace 1's LBA size {} bytes does not divide the 4 KiB request", 1u64 << lba_shift());
        return;
    }

    // One pair at a time: the driver's first thread creates driver thread k, which blocks on the handoff endpoint
    // (on CPU 0, so dom0's first thread sees the stage only once it blocked); then worker k sets the pair up.
    let workers = WORKERS.load(Ordering::SeqCst);
    for k in 0..workers {
        CREATE.store(k + 1, Ordering::SeqCst);
        wait_yield("a parallel_nvme_xproc driver thread", || STAGE[k].load(Ordering::SeqCst) == WAITS_ENDPOINT);
        if k == 0 {
            worker_setup(0);
        } else {
            let pair = &PAIRS[k];
            pair.ready.store(false, Ordering::SeqCst);
            pair.go.store(PHASE_NVME_XPROC_SETUP, Ordering::SeqCst);
            wait_for("a parallel_nvme_xproc worker setup", || pair.ready.load(Ordering::SeqCst));
        }
    }
    wait_yield("the parallel_nvme_xproc driver to park", || PARKED.load(Ordering::SeqCst));
    log::info!(
        "parallel_nvme_xproc: {} workers (CPUs {}, cap {}), {} LBAs of {} bytes per worker, {} ms per phase",
        workers, n, MAX_QUEUES, LBAS_PER_WORKER.load(Ordering::SeqCst), 1u64 << lba_shift(), WINDOW_MS
    );

    for (c, &(is_write, batch)) in RUNS.iter().enumerate() {
        time_run("parallel_nvme_xproc", PHASE_NVME_XPROC_FIRST, &MEASURED, |phase| worker(0, phase), workers, c, is_write, batch);
    }

    // The driver disables the controller, which deletes every queue, so no DMA reaches the regions after it; killing
    // the driver process returns the function to dom0.
    quiet("parallel_nvme_xproc call (stop)", unsafe { sys_call(HANDOFF_ENDPOINT) });
    quiet("parallel_nvme_xproc kill_process(0) (driver)", unsafe { sys_kill_process(0) });
    for k in 0..workers {
        quiet("parallel_nvme_xproc unmap_4k (region)", unsafe { sys_unmap_4k(region(k), REGION_PAGES) });
    }
    log::info!("parallel_nvme_xproc passed");
}

/// Worker k's setup on CPU k (dom0's first thread for k = 0): creates its endpoint and sends it to driver thread k,
/// which then runs on this CPU; maps its region and shares it with the driver thread, yielding to it until it waits
/// for the first call.
pub fn worker_setup(k: usize) {
    // One for the endpoint, 4 per page for `mmap_4k`.
    fund("parallel_nvme_xproc worker funding", 1 + 4 * REGION_PAGES);
    quiet("parallel_nvme_xproc new_endpoint (worker)", unsafe { sys_new_endpoint(WORKER_ENDPOINT) });
    quiet("parallel_nvme_xproc send_endpoint (worker)", unsafe { sys_send_endpoint(HANDOFF_ENDPOINT, WORKER_ENDPOINT) });
    quiet("parallel_nvme_xproc mmap_4k (region)", unsafe { sys_mmap_4k(region(k), REGION_PAGES) });
    wait_yield("a parallel_nvme_xproc driver thread to wait for its region", || STAGE[k].load(Ordering::SeqCst) == WAITS_REGION);
    quiet("parallel_nvme_xproc send_pages (region)", unsafe { sys_send_pages(WORKER_ENDPOINT, region(k), REGION_PAGES) });
    wait_yield("a parallel_nvme_xproc driver thread to serve", || STAGE[k].load(Ordering::SeqCst) == SERVES);
}

/// Worker `k` in `phase`, on CPU k: sequential 4 KiB requests with at most `batch` in flight, one call to driver
/// thread k per round, until the deadline of pair k, counting the completions answered by then; then calls until
/// every request completed, so the next phase starts with an empty queue, records the result, and marks the phase
/// done.
pub fn worker(k: usize, phase: usize) {
    let pair = &PAIRS[k];
    let (is_write, batch) = RUNS[(phase - PHASE_NVME_XPROC_FIRST) / 2];
    let deadline = pair.deadline.load(Ordering::SeqCst);
    if current_cpu() != k {
        fail(format_args!("worker {} runs on CPU {}", k, current_cpu()));
    }
    let ctl = control(k);
    let blocks = blocks_per_4k().unwrap() as u64;
    let (lbas, first_lba) = (LBAS_PER_WORKER.load(Ordering::SeqCst), k as u64 * LBAS_PER_WORKER.load(Ordering::SeqCst));
    let mut next_lba = first_lba;
    let mut free = [0u16; MAX_BATCH];
    for (i, slot) in free.iter_mut().enumerate() {
        *slot = i as u16;
    }
    let (mut nfree, mut in_flight, mut completed, mut calls) = (MAX_BATCH, 0, 0u64, 0u64);
    let mut round = |submit: bool, in_flight: &mut usize, nfree: &mut usize| -> u64 {
        let mut count = 0;
        while submit && *in_flight + count < batch {
            *nfree -= 1;
            let request = Request { lba: next_lba, slot: free[*nfree], write: is_write as u16, _pad: 0 };
            unsafe { core::ptr::write_volatile(&raw mut (*ctl).submit[count], request) };
            next_lba += blocks;
            if next_lba >= first_lba + lbas {
                next_lba = first_lba;
            }
            count += 1;
        }
        let reaped = quiet_value("parallel_nvme_xproc call_usize", unsafe { sys_call_usize(WORKER_ENDPOINT, count) });
        *in_flight += count;
        for i in 0..reaped {
            free[*nfree] = unsafe { core::ptr::read_volatile(&raw const (*ctl).done[i]) };
            *nfree += 1;
        }
        *in_flight -= reaped;
        reaped as u64
    };

    let begin = rdtsc();
    let end = loop {
        completed += round(true, &mut in_flight, &mut nfree);
        calls += 1;
        let now = rdtsc();
        if now >= deadline {
            break now;
        }
    };
    let drain_limit = rdtsc() + 10 * tsc_hz();
    while in_flight > 0 {
        round(false, &mut in_flight, &mut nfree);
        if rdtsc() > drain_limit {
            fail(format_args!("worker {}: {} requests still pending after the phase", k, in_flight));
        }
    }
    MEASURED[k].record(completed, begin, end, calls);
    pair.done.store(phase, Ordering::SeqCst);
}

/// First thread of the driver process, holding the handoff endpoint in descriptor 0: takes the function and BAR0,
/// attaches the function to the process's IOMMU table, brings the controller up with one I/O queue pair per worker,
/// creates the driver threads one at a time as dom0 asks, and blocks until dom0's stop call, when it disables the
/// controller and answers.
extern "C" fn driver_main() -> ! {
    let f = unsafe { FUNCTION }.unwrap();
    // A receiver holds 3 4K quota per page for the worst case of page tables.
    fund("parallel_nvme_xproc driver receive funding", 3 * f.bar_pages);
    quiet("parallel_nvme_xproc driver receive_pci", unsafe { sys_receive_pci(0, f.bus, f.dev, f.fun) });
    quiet("parallel_nvme_xproc driver receive_pages (BAR0)", unsafe { sys_receive_pages(0, f.bar_va(), f.bar_pages) });
    crate::slab_alloc::init();
    quiet("parallel_nvme_xproc driver pci_attach_dma", unsafe { sys_pci_attach_dma(f.bus, f.dev, f.fun) });
    let mut dev = NvmeDevice::new(f.bar());
    dev.init_admin_only();
    let Some(blocks) = blocks_per_4k() else {
        dev.shutdown();
        STATUS.store(SKIPPED, Ordering::SeqCst);
        park();
    };
    let blocks = blocks as u64;
    let want = WANTED.load(Ordering::SeqCst);
    let (nsqa, ncqa) =
        dev.set_number_of_queues(want as u16).unwrap_or_else(|s| fail(format_args!("Set Features Number of Queues: status {:#x}", s)));
    let workers = want.min(nsqa as usize).min(ncqa as usize);
    let len = QUEUE_DEPTH.min(dev.max_queue_entries());
    let per = num_lbas() / workers as u64 / blocks * blocks;
    if per < blocks {
        fail(format_args!("{} LBAs do not give each of {} workers a 4 KiB request", num_lbas(), workers));
    }
    for k in 0..workers {
        let qid = k as u16 + 1;
        let queue = DriverQueue {
            sq: allocate_dma().unwrap(), cq: allocate_dma().unwrap(), len, tail: 0, head: 0, phase: true,
            sq_doorbell: dev.doorbell(qid, false), cq_doorbell: dev.doorbell(qid, true),
        };
        if let Err(s) = dev.create_io_queue_pair(qid, queue.cq.physical(), queue.sq.physical(), len as u16) {
            fail(format_args!("creating I/O queue pair {}: status {:#x}", qid, s));
        }
        unsafe { (*(&raw mut DRIVER_QUEUES))[k] = Some(queue) };
    }
    log::info!("parallel_nvme_xproc driver: controller allocated {} SQ / {} CQ, {} entries per queue", nsqa, ncqa, len);
    LBAS_PER_WORKER.store(per, Ordering::SeqCst);
    WORKERS.store(workers, Ordering::SeqCst);
    STATUS.store(READY, Ordering::SeqCst);

    for k in 0..workers {
        wait_yield("dom0 to ask for a parallel_nvme_xproc driver thread", || CREATE.load(Ordering::SeqCst) > k);
        CREATING.store(k, Ordering::SeqCst);
        fund("parallel_nvme_xproc driver thread funding", 1);
        let sp = stack_top(unsafe { &raw const DRIVER_STACKS[k] });
        quiet("parallel_nvme_xproc new_thread_with_endpoint (driver thread)", unsafe {
            sys_new_thread_with_endpoint(0, entry(driver_thread), sp)
        });
    }

    // Only once the last driver thread took its worker's endpoint may this thread wait on the handoff endpoint, for
    // dom0's stop call after every run.
    wait_yield("the last parallel_nvme_xproc driver thread to serve", || STAGE[workers - 1].load(Ordering::SeqCst) == SERVES);
    PARKED.store(true, Ordering::SeqCst);
    quiet("parallel_nvme_xproc driver receive_call (stop)", unsafe { sys_receive_call(0) });
    dev.shutdown();
    loop {
        quiet("parallel_nvme_xproc driver reply_and_receive (stop)", unsafe { sys_reply_and_receive(0) });
    }
}

/// Blocks the driver's first thread until dom0 kills the process.
fn park() -> ! {
    PARKED.store(true, Ordering::SeqCst);
    loop {
        unsafe { sys_receive_call(0) };
    }
}

/// Driver thread k, holding the handoff endpoint in descriptor 0: takes worker k's endpoint into descriptor 1 (which
/// wakes it on worker k's CPU), then worker k's region, maps the region into the process's IOMMU table at IOVA = VA,
/// and serves worker k's calls on its queue pair forever.
extern "C" fn driver_thread() -> ! {
    let k = CREATING.load(Ordering::SeqCst);
    // 3 per page for `receive_pages` and 3 more for `iommu_map_4k`.
    fund("parallel_nvme_xproc driver thread region funding", 6 * REGION_PAGES);
    STAGE[k].store(WAITS_ENDPOINT, Ordering::SeqCst);
    quiet("parallel_nvme_xproc driver thread receive_endpoint", unsafe { sys_receive_endpoint(0, DRIVER_ENDPOINT) });
    STAGE[k].store(WAITS_REGION, Ordering::SeqCst);
    quiet("parallel_nvme_xproc driver thread receive_pages (region)", unsafe {
        sys_receive_pages(DRIVER_ENDPOINT, region(k), REGION_PAGES)
    });
    quiet("parallel_nvme_xproc driver thread iommu_map_4k (region)", unsafe {
        sys_iommu_map_4k(region(k), region(k), REGION_PAGES)
    });
    let Some(q) = (unsafe { (*(&raw mut DRIVER_QUEUES))[k].as_mut() }) else {
        fail(format_args!("driver thread {} has no queue pair", k));
    };
    let ctl = control(k);
    let blocks = blocks_per_4k().unwrap();
    let mut in_flight = 0usize;
    STAGE[k].store(SERVES, Ordering::SeqCst);
    let mut count = quiet_value("parallel_nvme_xproc driver thread receive_call", unsafe { sys_receive_call(DRIVER_ENDPOINT) });
    loop {
        if count > MAX_BATCH - in_flight {
            fail(format_args!("driver thread {}: {} new requests with {} in flight", k, count, in_flight));
        }
        for i in 0..count {
            let r = unsafe { core::ptr::read_volatile(&raw const (*ctl).submit[i]) };
            let buf = buffer(k, r.slot) as u64;
            let mut cmd = if r.write != 0 {
                nvme_cmd::io_write(r.slot, 1, r.lba, blocks - 1, buf, 0)
            } else {
                nvme_cmd::io_read(r.slot, 1, r.lba, blocks - 1, buf, 0)
            };
            cmd.cid = r.slot;
            unsafe { core::ptr::write_volatile(q.sq.as_mut_ptr().add(q.tail), cmd) };
            q.tail = (q.tail + 1) % q.len;
        }
        if count > 0 {
            unsafe { core::ptr::write_volatile(q.sq_doorbell, q.tail as u32) };
        }
        in_flight += count;
        let mut reaped = 0;
        if in_flight > 0 {
            let limit = rdtsc() + 10 * tsc_hz();
            while reaped == 0 {
                reaped = reap(k, q, ctl);
                if reaped == 0 && rdtsc() > limit {
                    fail(format_args!("driver thread {}: no completion of {} requests in 10 s", k, in_flight));
                }
            }
        }
        in_flight -= reaped;
        count = quiet_value("parallel_nvme_xproc driver thread reply_and_receive_usize", unsafe {
            sys_reply_and_receive_usize(DRIVER_ENDPOINT, reaped)
        });
    }
}

/// Takes every posted completion of driver thread `k`'s queue pair `q`, writes its command ID (= data buffer) into
/// the control page's answer, writes the completion head doorbell once if it took any, and returns how many it took.
#[inline(always)]
fn reap(k: usize, q: &mut DriverQueue, ctl: *mut Control) -> usize {
    let mut reaped = 0;
    loop {
        let entry = unsafe { core::ptr::read_volatile(q.cq.as_ptr().add(q.head)) };
        if ((entry.status & 1) == 1) != q.phase {
            break;
        }
        if entry.status >> 1 != 0 {
            fail(format_args!("driver thread {}: command {} failed with status {:#x}", k, { entry.cid }, { entry.status } >> 1));
        }
        unsafe { core::ptr::write_volatile(&raw mut (*ctl).done[reaped], entry.cid) };
        reaped += 1;
        q.head += 1;
        if q.head == q.len {
            q.head = 0;
            q.phase = !q.phase;
        }
    }
    if reaped > 0 {
        unsafe { core::ptr::write_volatile(q.cq_doorbell, q.head as u32) };
    }
    reaped
}
