//! E810 (ice) packet benchmark in dom0: the `boot/ice` driver core over BAR0 in the loader's window and DMA memory
//! from dom0's heap (mapped at IOVA = VA), one queue pair per CPU. Worker k runs on CPU k (worker 0 is dom0's first
//! thread) and owns queue pair k: it sends one fixed UDP frame in batches and counts what its Rx queue receives, for
//! `VERIFLAT_ICE_SECS` seconds; dom0 then reports per-queue and total packets per second from the TSC and the port
//! counters.
//!
//! The benchmark runs only in a dom0 built with feature `ice-bench` (`ICE_BENCH=1 boot/run.sh`), first thing after
//! boot while every other CPU is still Off, and exits afterwards; the default dom0 test only reports whether the
//! loader recorded an E810 function. Build-time settings (environment of the dom0 build):
//!
//! - `VERIFLAT_ICE_SECS` seconds of traffic (default 5); `VERIFLAT_ICE_QUEUES` queue pairs (default: one per CPU);
//! - `VERIFLAT_ICE_FRAME` frame size with CRC, 64..1518 (default 64); `VERIFLAT_ICE_MODE` `tx`, `rx` or `both`;
//! - `VERIFLAT_ICE_DST` destination MAC of every frame, or `VERIFLAT_ICE_PEER` the MAC of a peer running this
//!   benchmark (queue q sends to the peer's queue q; `VERIFLAT_ICE_PEER_QUEUES` if the peer has fewer queues);
//!   broadcast without either;
//! - `VERIFLAT_ICE_STEER` `mac` (per-queue steering MACs, default) or `promisc` (every frame to the VSI);
//! - `VERIFLAT_ICE_BDF` `bb:dd.f` of the function (default: the first E810-C, else the first E810);
//! - `VERIFLAT_ICE_LINK_SECS` how long to wait for the link (default 15).

use crate::nvme::time::{rdtsc, tsc_rate};
use crate::{check, current_cpu, entry, fund, quiet, wait_for};
use alloc::boxed::Box;
use alloc::vec::Vec;
use core::alloc::Layout;
use core::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use ice::bench::{line_rate_pps, rate, run_queue_pair, TxFrame, WorkerResult};
use ice::packet::{steering_mac, UdpFrame};
use ice::{Config, Device, DmaRegion, Mac, Platform, RxQueue, RxSteering, TxQueue};
use vsys::*;

/// An E810 function the loader recorded.
#[derive(Clone, Copy, Debug)]
pub struct IceFunction {
    pub bus: usize,
    pub dev: usize,
    pub fun: usize,
    pub device: u16,
    pub bar_phys: usize,
    pub bar_pages: usize,
}

/// Every recorded E810 function, in B/D/F order.
pub fn find_e810() -> Vec<IceFunction> {
    let mut found = Vec::new();
    for bus in 0..256 {
        for dev in 0..32 {
            for fun in 0..8 {
                let (rax, base, pages) = unsafe { sys_pci_info(bus, dev, fun) };
                if rax < 0 {
                    continue;
                }
                let id = rax as usize;
                let (vendor, device) = (((id >> 16) & 0xffff) as u16, (id & 0xffff) as u16);
                if ice::is_e810(vendor, device) {
                    found.push(IceFunction { bus, dev, fun, device, bar_phys: base, bar_pages: pages });
                }
            }
        }
    }
    found
}

/// The function the benchmark drives: `VERIFLAT_ICE_BDF`, else the first E810-C (100G), else the first E810.
fn pick(found: &[IceFunction]) -> Option<IceFunction> {
    if let Some(bdf) = option_env!("VERIFLAT_ICE_BDF") {
        let parse = || -> Option<(usize, usize, usize)> {
            let (bus, rest) = bdf.split_once(':')?;
            let (dev, fun) = rest.split_once('.')?;
            Some((usize::from_str_radix(bus, 16).ok()?, usize::from_str_radix(dev, 16).ok()?, fun.parse().ok()?))
        };
        let Some((b, d, f)) = parse() else {
            log::error!("ice: VERIFLAT_ICE_BDF={} is not bb:dd.f", bdf);
            unsafe { sys_debug_exit(1) };
        };
        return found.iter().copied().find(|x| (x.bus, x.dev, x.fun) == (b, d, f));
    }
    found.iter().copied().find(|f| ice::is_e810_c(f.device)).or_else(|| found.first().copied())
}

/// The default dom0 test's check: logs which E810 functions the loader recorded.
pub fn probe() {
    let found = find_e810();
    if found.is_empty() {
        log::info!("ice bench skipped: no E810 function recorded");
        return;
    }
    for f in &found {
        log::info!(
            "ice: E810 {:02x}:{:02x}.{} device {:04x}, BAR0 {:#x} ({} pages); build dom0 with feature ice-bench (ICE_BENCH=1) to run the benchmark",
            f.bus, f.dev, f.fun, f.device, f.bar_phys, f.bar_pages
        );
    }
}

/// BAR0 in dom0's loader window, DMA memory from the heap at IOVA = VA, delays from the TSC.
pub struct Dom0Platform {
    bar: usize,
    bar_len: usize,
    tsc_hz: u64,
}

impl Platform for Dom0Platform {
    fn read32(&self, offset: usize) -> u32 {
        debug_assert!(offset + 4 <= self.bar_len);
        unsafe { core::ptr::read_volatile((self.bar + offset) as *const u32) }
    }

    fn write32(&self, offset: usize, value: u32) {
        debug_assert!(offset + 4 <= self.bar_len);
        unsafe { core::ptr::write_volatile((self.bar + offset) as *mut u32, value) }
    }

    fn dma_alloc(&self, len: usize, align: usize) -> Option<DmaRegion> {
        // The heap maps every page into dom0's IOMMU table at IOVA = VA; runs above 2 KiB are page aligned and
        // contiguous, slabs are aligned to their power-of-two size.
        let layout = Layout::from_size_align(len, align.min(4096)).ok()?;
        let va = unsafe { alloc::alloc::alloc_zeroed(layout) };
        (!va.is_null()).then(|| DmaRegion { va, iova: va as u64, len })
    }

    fn delay_us(&self, us: u64) {
        let end = rdtsc() + us * self.tsc_hz / 1_000_000;
        while rdtsc() < end {
            core::hint::spin_loop();
        }
    }

    fn tsc(&self) -> u64 {
        rdtsc()
    }
}

/// The most worker CPUs.
const MAX_WORKERS: usize = 64;
const WORKER_STACK: usize = 64 * 1024;

/// What worker k owns and reports, reached through `WORKERS[k]`.
struct Worker {
    tx: TxQueue<'static, Dom0Platform>,
    rx: RxQueue<'static, Dom0Platform>,
    frame: Option<TxFrame>,
    do_rx: bool,
    result: WorkerResult,
}

#[allow(clippy::declare_interior_mutable_const)]
const ZERO: AtomicUsize = AtomicUsize::new(0);
#[allow(clippy::declare_interior_mutable_const)]
const NO: AtomicBool = AtomicBool::new(false);
static PLATFORM: AtomicUsize = AtomicUsize::new(0);
static WORKERS: [AtomicUsize; MAX_WORKERS] = [ZERO; MAX_WORKERS];
/// One plus the CPU worker k runs on; 0 until it runs.
static WORKER_CPU: [AtomicUsize; MAX_WORKERS] = [ZERO; MAX_WORKERS];
static WORKER_DONE: [AtomicBool; MAX_WORKERS] = [NO; MAX_WORKERS];
static NEXT_WORKER: AtomicUsize = AtomicUsize::new(0);
static GO: AtomicBool = AtomicBool::new(false);
static CYCLES: AtomicUsize = AtomicUsize::new(0);

fn platform() -> &'static Dom0Platform {
    unsafe { &*(PLATFORM.load(Ordering::SeqCst) as *const Dom0Platform) }
}

fn run_worker(k: usize) {
    let w = unsafe { &mut *(WORKERS[k].load(Ordering::SeqCst) as *mut Worker) };
    let frame = w.frame;
    w.result = run_queue_pair(platform(), &mut w.tx, &mut w.rx, frame.as_ref(), w.do_rx, CYCLES.load(Ordering::SeqCst) as u64);
    WORKER_DONE[k].store(true, Ordering::SeqCst);
}

/// Worker k > 0: records its CPU, waits for the start, runs its queue pair, then spins; dom0 resets the PF and
/// exits.
extern "C" fn ice_worker() -> ! {
    let k = NEXT_WORKER.load(Ordering::SeqCst);
    WORKER_CPU[k].store(current_cpu() + 1, Ordering::SeqCst);
    while !GO.load(Ordering::SeqCst) {
        core::hint::spin_loop();
    }
    run_worker(k);
    loop {
        core::hint::spin_loop();
    }
}

fn env_num(name: &str, value: Option<&str>, default: u64) -> u64 {
    match value {
        None => default,
        Some(s) => s.parse().unwrap_or_else(|_| {
            log::error!("ice: {}={} is not a decimal number", name, s);
            unsafe { sys_debug_exit(1) }
        }),
    }
}

fn env_mac(name: &str, value: Option<&str>) -> Option<[u8; 6]> {
    value.map(|s| {
        ice::parse_mac(s).unwrap_or_else(|| {
            log::error!("ice: {}={} is not a MAC address", name, s);
            unsafe { sys_debug_exit(1) }
        })
    })
}

/// CPUs the kernel runs: every CPU but 0 is Off, so an offline request fails without effect until the first missing
/// CPU, where it fails with InvalidArgument.
fn count_cpus() -> usize {
    let mut n = 1;
    while n < MAX_WORKERS {
        let ret = unsafe { sys_cpu_offline_request(n) };
        if error_name(ret) == "InvalidArgument" {
            break;
        }
        if error_name(ret) != "ErrorCpuAlreadyOff" {
            log::error!("ice: CPU {} is not Off at the start ({})", n, error_name(ret));
            unsafe { sys_debug_exit(1) };
        }
        n += 1;
    }
    n
}

fn fail(what: &str, e: ice::Error) -> ! {
    log::error!("ice: {}: {}", what, e);
    unsafe { sys_debug_exit(1) }
}

/// The benchmark (feature `ice-bench`). Logs that it is skipped when the loader recorded no E810 function.
pub fn run() {
    let found = find_e810();
    let Some(f) = pick(&found) else {
        log::info!("ice bench skipped: no E810 function recorded");
        return;
    };
    let Some((hz, source)) = tsc_rate() else {
        log::error!("ice bench: no CPUID source gives the TSC rate; build dom0 with VERIFLAT_TSC_MHZ set to it");
        unsafe { sys_debug_exit(1) };
    };
    let secs = env_num("VERIFLAT_ICE_SECS", option_env!("VERIFLAT_ICE_SECS"), 5);
    let frame_len = env_num("VERIFLAT_ICE_FRAME", option_env!("VERIFLAT_ICE_FRAME"), 64) as usize;
    if !(64..=1518).contains(&frame_len) {
        log::error!("ice: VERIFLAT_ICE_FRAME must be 64..1518");
        unsafe { sys_debug_exit(1) };
    }
    let (do_tx, do_rx) = match option_env!("VERIFLAT_ICE_MODE").unwrap_or("both") {
        "tx" => (true, false),
        "rx" => (false, true),
        "both" => (true, true),
        m => {
            log::error!("ice: VERIFLAT_ICE_MODE={} is not tx, rx or both", m);
            unsafe { sys_debug_exit(1) }
        }
    };
    let steering = match option_env!("VERIFLAT_ICE_STEER").unwrap_or("mac") {
        "mac" => RxSteering::PerQueueMac,
        "promisc" => RxSteering::Promiscuous,
        s => {
            log::error!("ice: VERIFLAT_ICE_STEER={} is not mac or promisc", s);
            unsafe { sys_debug_exit(1) }
        }
    };
    let dst = env_mac("VERIFLAT_ICE_DST", option_env!("VERIFLAT_ICE_DST"));
    let peer = env_mac("VERIFLAT_ICE_PEER", option_env!("VERIFLAT_ICE_PEER"));
    let cpus = count_cpus();
    let queues = (env_num("VERIFLAT_ICE_QUEUES", option_env!("VERIFLAT_ICE_QUEUES"), cpus as u64) as usize).clamp(1, cpus);
    let peer_queues = env_num("VERIFLAT_ICE_PEER_QUEUES", option_env!("VERIFLAT_ICE_PEER_QUEUES"), queues as u64) as usize;
    let link_secs = env_num("VERIFLAT_ICE_LINK_SECS", option_env!("VERIFLAT_ICE_LINK_SECS"), 15);
    log::info!(
        "ice: {:02x}:{:02x}.{} device {:04x}, BAR0 {:#x} ({} pages), {} CPUs, {} queue pairs, {} s, {}-byte frames, TSC {} MHz from {}",
        f.bus, f.dev, f.fun, f.device, f.bar_phys, f.bar_pages, cpus, queues, secs, frame_len, hz / 1_000_000, source
    );

    crate::slab_alloc::init();
    check("ice pci_attach_dma", unsafe { sys_pci_attach_dma(f.bus, f.dev, f.fun) });
    let p: &'static Dom0Platform =
        Box::leak(Box::new(Dom0Platform { bar: PCI_BAR_WINDOW_BASE + f.bar_phys, bar_len: f.bar_pages * 4096, tsc_hz: hz }));
    PLATFORM.store(p as *const Dom0Platform as usize, Ordering::SeqCst);
    let config = Config { queues, steering, ..Default::default() };
    let mut dev = Device::new(p, config).unwrap_or_else(|e| fail("bring-up", e));
    let link = dev.bring_link_up(link_secs * 1000).unwrap_or_else(|e| fail("link", e));
    if link.up {
        log::info!("ice: link up at {} Mb/s, max frame {}", link.speed_mbps, link.max_frame);
    } else {
        log::warn!("ice: link still down after {} s: frames will not reach the wire", link_secs);
    }

    let mac = dev.info.mac;
    for (q, (tx, rx)) in dev.take_queues().into_iter().enumerate() {
        let dst = match (dst, peer) {
            (Some(d), _) => d,
            (None, Some(peer)) => steering_mac(peer, q % peer_queues.max(1)),
            (None, None) => [0xff; 6],
        };
        let frame = UdpFrame {
            dst_mac: dst,
            src_mac: mac,
            src_ip: [10, 10, 0, 1 + q as u8],
            dst_ip: [10, 10, 1, 1 + q as u8],
            src_port: 1024 + q as u16,
            dst_port: 5000 + q as u16,
            len: frame_len - 4,
        };
        let frame = do_tx.then(|| TxFrame::new(p, &frame).unwrap_or_else(|e| fail("frame buffer", e)));
        if q == 0 {
            log::info!("ice: queue 0 sends to {}", Mac(dst));
        }
        // Each worker reaches its own state only through this pointer.
        let w = Box::into_raw(Box::new(Worker { tx, rx, frame, do_rx, result: WorkerResult::default() }));
        WORKERS[q].store(w as usize, Ordering::SeqCst);
    }
    CYCLES.store((secs * hz) as usize, Ordering::SeqCst);

    // Worker k > 0: a new thread on CPU 0's shard, which CPU k pulls when it comes online (CPU 0's shard holds no
    // other queued thread, and the workers before spin on their own CPUs).
    fund("ice worker funding", 2 * queues);
    for k in 1..queues {
        NEXT_WORKER.store(k, Ordering::SeqCst);
        let stack = unsafe { alloc::alloc::alloc(Layout::from_size_align(WORKER_STACK, 4096).unwrap()) } as usize;
        if stack == 0 {
            log::error!("ice: no memory for worker stacks");
            unsafe { sys_debug_exit(1) };
        }
        quiet("ice new_thread (worker)", unsafe { sys_new_thread(entry(ice_worker), stack + WORKER_STACK - 8) });
        quiet("ice cpu_online (worker)", unsafe { sys_cpu_online(k) });
        wait_for("an ice worker to start", || WORKER_CPU[k].load(Ordering::SeqCst) != 0);
        let cpu = WORKER_CPU[k].load(Ordering::SeqCst) - 1;
        if cpu != k {
            log::error!("ice: worker {} runs on CPU {}", k, cpu);
            unsafe { sys_debug_exit(1) };
        }
    }

    let before = dev.port_stats();
    GO.store(true, Ordering::SeqCst);
    run_worker(0);
    let start = rdtsc();
    for k in 0..queues {
        while !WORKER_DONE[k].load(Ordering::SeqCst) {
            if rdtsc() - start > 10 * hz {
                log::error!("ice: worker {} did not finish", k);
                unsafe { sys_debug_exit(1) };
            }
            core::hint::spin_loop();
        }
    }
    let stats = dev.port_stats().since(&before);

    let (mut tx_total, mut rx_total) = (0, 0);
    for q in 0..queues {
        let r = unsafe { (*(WORKERS[q].load(Ordering::SeqCst) as *const Worker)).result };
        let (tpps, rpps) = (rate(r.tx_packets, r.cycles, hz), rate(r.rx.packets, r.cycles, hz));
        tx_total += tpps;
        rx_total += rpps;
        log::info!("ice queue {} cpu {}: tx {} pps, rx {} pps, rx errors {}", q, q, tpps, rpps, r.rx.errors);
    }
    let line = if link.speed_mbps != 0 { line_rate_pps(frame_len as u64, link.speed_mbps as u64) } else { 0 };
    log::info!(
        "ice total: tx {} pps, rx {} pps over {} queues; line rate of {}-byte frames at {} Mb/s is {} pps",
        tx_total, rx_total, queues, frame_len, link.speed_mbps, line
    );
    log::info!(
        "ice port: rx {} unicast {} multicast {} broadcast {} bytes, tx {} unicast {} multicast {} broadcast {} bytes, {} CRC errors",
        stats.rx_unicast, stats.rx_multicast, stats.rx_broadcast, stats.rx_bytes, stats.tx_unicast, stats.tx_multicast,
        stats.tx_broadcast, stats.tx_bytes, stats.crc_errors
    );
    if let Err(e) = dev.shutdown() {
        log::warn!("ice: PF reset after the run: {}", e);
    }
    log::info!("ice bench passed");
}
