//! E810 (ice) packet benchmark in dom0: the `boot/ice` driver core over BAR0 in the loader's window and DMA memory
//! from dom0's heap (mapped at IOVA = VA), one queue pair per CPU. Worker k runs on CPU k (worker 0 is dom0's first
//! thread) and owns queue pair k: it sends one fixed UDP frame in batches and counts what its Rx queue receives, for
//! `VERIFLAT_ICE_SECS` seconds; dom0 then reports per-queue and total packets per second from the TSC and the port
//! counters.
//!
//! The benchmark runs only in a dom0 built with feature `ice-bench` (`ICE_BENCH=1 boot/bench/run.sh`), on a kernel without
//! the timer (feature `no-timer`, so that no tick on CPU 0 lets CPU k pull dom0's thread instead of worker k), first
//! thing after boot while every other CPU is still Off, and exits afterwards; the default dom0 test only reports whether the
//! loader recorded an E810 function. Build-time settings (environment of the dom0 build):
//!
//! - `VERIFLAT_ICE_SECS` seconds of traffic per round (default 5);
//! - `VERIFLAT_ICE_QUEUES`, `VERIFLAT_ICE_FRAME` (with CRC, 64..1518) and `VERIFLAT_ICE_MODE` (`tx`, `rx`, `both`):
//!   comma-separated lists (defaults: one queue per CPU, 64, `both`); one round per frame size, mode and queue
//!   count, in that nesting, all over one bring-up with a queue pair per worker CPU. Mode `rx` adds a sender on the
//!   last CPU that sends the measured queues' frames round robin (each from its queue's steering MAC), so against a
//!   reflector that swaps the MACs every measured queue receives; it measures at most CPUs - 1 queues;
//! - `VERIFLAT_ICE_DST` destination MAC of every frame, or `VERIFLAT_ICE_PEER` the MAC of a peer running this
//!   benchmark (queue q sends to the peer's queue q; `VERIFLAT_ICE_PEER_QUEUES` if the peer has fewer queues);
//!   broadcast without either;
//! - `VERIFLAT_ICE_POOL` copies of each queue's frame that the queue sends in turn (default 64; see `TxFrame`);
//! - `VERIFLAT_ICE_STEER` `mac` (per-queue steering MACs, default) or `promisc` (every frame to the VSI);
//! - `VERIFLAT_ICE_BDF` `bb:dd.f` of the function (default: the first E810-C, else the first E810);
//! - `VERIFLAT_ICE_LINK_SECS` how long to wait for the link (default 15).

use crate::nvme::time::{rdtsc, tsc_rate};
use crate::{check, current_cpu, entry, fund, quiet, wait_for};
use alloc::boxed::Box;
use alloc::vec::Vec;
use core::alloc::Layout;
use core::sync::atomic::{AtomicUsize, Ordering};
use ice::bench::{line_rate_pps, rate, run_forwarder, run_queue_pair, run_sender, TxFrame, WorkerResult};
use ice::maglev::{populate_lut, Maglev, CACHE_ENTRIES, ENTRY_BYTES, TABLE_SIZE};
use ice::packet::{steering_mac, UdpFrame};
use ice::{Config, Device, DmaRegion, Platform, RxQueue, RxSteering, TxQueue};
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
pub(crate) fn pick(found: &[IceFunction]) -> Option<IceFunction> {
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
    crate::slab_alloc::init();
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
pub(crate) const MAX_WORKERS: usize = 64;
const WORKER_STACK: usize = 64 * 1024;

/// What worker k owns and reports, reached through `WORKERS[k]`. dom0 writes `frame`'s contents, `send` and `do_rx`
/// only while every worker waits for the next round.
struct Worker {
    tx: TxQueue<'static, Dom0Platform>,
    rx: RxQueue<'static, Dom0Platform>,
    frame: TxFrame,
    send: bool,
    /// Sends `SENDER_FRAMES` round robin instead (mode rx).
    sender: bool,
    do_rx: bool,
    /// Mode fwd: the worker count n of the round (0: not forwarding); worker k forwards what queues k, k + n, ..
    /// receive on its Tx queue, with its flow cache `cache` (`CACHE_ENTRIES` entries).
    fwd: usize,
    cache: *mut [u64; 2],
    result: WorkerResult,
}

#[allow(clippy::declare_interior_mutable_const)]
const ZERO: AtomicUsize = AtomicUsize::new(0);
static PLATFORM: AtomicUsize = AtomicUsize::new(0);
static WORKERS: [AtomicUsize; MAX_WORKERS] = [ZERO; MAX_WORKERS];
/// One plus the CPU worker k runs on; 0 until it runs.
static WORKER_CPU: [AtomicUsize; MAX_WORKERS] = [ZERO; MAX_WORKERS];
/// The last round worker k finished.
static WORKER_DONE: [AtomicUsize; MAX_WORKERS] = [ZERO; MAX_WORKERS];
static NEXT_WORKER: AtomicUsize = AtomicUsize::new(0);
/// The round the workers run now (rounds count from 1); `usize::MAX` ends the benchmark.
static ROUND: AtomicUsize = AtomicUsize::new(0);
static CYCLES: AtomicUsize = AtomicUsize::new(0);
/// The sender's frames of the current round: a leaked `Vec<(u64, u16)>`, one per measured queue.
static SENDER_FRAMES: AtomicUsize = AtomicUsize::new(0);
/// Mode fwd: the shared maglev lookup table (`TABLE_SIZE` bytes), the queue pair count, the port's MAC and the
/// destination MAC of forwarded frames (each a u64 of 6 bytes).
static FWD_LUT: AtomicUsize = AtomicUsize::new(0);
static FWD_QUEUES: AtomicUsize = AtomicUsize::new(0);
static FWD_SRC: AtomicUsize = AtomicUsize::new(0);
static FWD_DST: AtomicUsize = AtomicUsize::new(0);

fn mac_of(word: usize) -> [u8; 6] {
    let b = (word as u64).to_le_bytes();
    [b[0], b[1], b[2], b[3], b[4], b[5]]
}

fn word_of(mac: [u8; 6]) -> usize {
    let mut b = [0u8; 8];
    b[..6].copy_from_slice(&mac);
    u64::from_le_bytes(b) as usize
}

fn platform() -> &'static Dom0Platform {
    unsafe { &*(PLATFORM.load(Ordering::SeqCst) as *const Dom0Platform) }
}

fn worker(k: usize) -> &'static mut Worker {
    unsafe { &mut *(WORKERS[k].load(Ordering::SeqCst) as *mut Worker) }
}

/// Runs worker k's part of the current round (nothing if it neither sends nor receives).
fn run_worker(k: usize, round: usize) {
    let w = worker(k);
    let cycles = CYCLES.load(Ordering::SeqCst) as u64;
    if w.fwd != 0 {
        // Worker k is the only one touching queues k, k + n, .. this round (the others with k < n hold their own).
        let n = w.fwd;
        let mut rxs: Vec<&mut RxQueue<'static, Dom0Platform>> =
            (k..FWD_QUEUES.load(Ordering::SeqCst)).step_by(n).map(|j| unsafe { &mut (*(WORKERS[j].load(Ordering::SeqCst) as *mut Worker)).rx }).collect();
        let lut = unsafe { core::slice::from_raw_parts(FWD_LUT.load(Ordering::SeqCst) as *const i8, TABLE_SIZE) };
        let mut m = Maglev::new(lut, unsafe { core::slice::from_raw_parts_mut(w.cache, CACHE_ENTRIES) });
        let tx = unsafe { &mut *core::ptr::addr_of_mut!(w.tx) };
        let (src, dst) = (mac_of(FWD_SRC.load(Ordering::SeqCst)), mac_of(FWD_DST.load(Ordering::SeqCst)));
        w.result = run_forwarder(platform(), tx, &mut rxs, &mut m, src, dst, cycles);
    } else if w.sender {
        let frames = unsafe { &*(SENDER_FRAMES.load(Ordering::SeqCst) as *const Vec<(u64, u16)>) };
        w.result = run_sender(platform(), &mut w.tx, frames, cycles);
    } else if w.send || w.do_rx {
        let frame = w.frame;
        w.result = run_queue_pair(platform(), &mut w.tx, &mut w.rx, w.send.then_some(&frame), w.do_rx, cycles);
    } else {
        w.result = WorkerResult::default();
    }
    WORKER_DONE[k].store(round, Ordering::SeqCst);
}

/// Worker k > 0: records its CPU, then runs every round dom0 starts, spinning in between.
extern "C" fn ice_worker() -> ! {
    let k = NEXT_WORKER.load(Ordering::SeqCst);
    WORKER_CPU[k].store(current_cpu() + 1, Ordering::SeqCst);
    let mut done = 0;
    loop {
        let r = ROUND.load(Ordering::SeqCst);
        if r != done && r != usize::MAX {
            run_worker(k, r);
            done = r;
        }
        core::hint::spin_loop();
    }
}

pub(crate) fn env_num(name: &str, value: Option<&str>, default: u64) -> u64 {
    match value {
        None => default,
        Some(s) => s.parse().unwrap_or_else(|_| {
            log::error!("ice: {}={} is not a decimal number", name, s);
            unsafe { sys_debug_exit(1) }
        }),
    }
}

/// A comma-separated list of decimal numbers, or `default`.
pub(crate) fn env_list(name: &str, value: Option<&str>, default: u64) -> Vec<u64> {
    match value {
        None => alloc::vec![default],
        Some(s) => s.split(',').map(|x| env_num(name, Some(x.trim()), 0)).collect(),
    }
}

pub(crate) fn env_mac(name: &str, value: Option<&str>) -> Option<[u8; 6]> {
    value.map(|s| {
        ice::parse_mac(s).unwrap_or_else(|| {
            log::error!("ice: {}={} is not a MAC address", name, s);
            unsafe { sys_debug_exit(1) }
        })
    })
}

/// CPUs the kernel runs: every CPU but 0 is Off, so an offline request fails without effect until the first missing
/// CPU, where it fails with InvalidArgument.
pub(crate) fn count_cpus() -> usize {
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

pub(crate) fn fail(what: &str, e: ice::Error) -> ! {
    log::error!("ice: {}: {}", what, e);
    unsafe { sys_debug_exit(1) }
}

/// What a mode does on the measured queues: (send, receive, one extra sender on the last CPU).
fn mode_roles(m: &str) -> (bool, bool, bool) {
    match m {
        "tx" => (true, false, false),
        "rx" => (false, true, true),
        "both" => (true, true, false),
        // Forwarding (`run_forwarder`): set up separately.
        "fwd" => (false, false, false),
        _ => {
            log::error!("ice: mode {} is not tx, rx, both or fwd", m);
            unsafe { sys_debug_exit(1) }
        }
    }
}

/// The benchmark (feature `ice-bench`). Logs that it is skipped when the loader recorded no E810 function.
pub fn run() {
    // find_e810 allocates once an E810 is recorded: the heap comes first (init is idempotent).
    crate::slab_alloc::init();
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
    let frames = env_list("VERIFLAT_ICE_FRAME", option_env!("VERIFLAT_ICE_FRAME"), 64);
    if frames.iter().any(|f| !(64..=1518).contains(f)) {
        log::error!("ice: VERIFLAT_ICE_FRAME must be 64..1518");
        unsafe { sys_debug_exit(1) };
    }
    let modes: Vec<&str> = option_env!("VERIFLAT_ICE_MODE").unwrap_or("both").split(',').collect();
    modes.iter().for_each(|m| _ = mode_roles(m));
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
    // Queue counts to measure, each a round per mode and frame size, all over one bring-up with a queue pair per
    // worker CPU; mode `rx` adds a sender on the last CPU, so it measures at most cpus - 1 queues.
    let sweep: Vec<usize> = env_list("VERIFLAT_ICE_QUEUES", option_env!("VERIFLAT_ICE_QUEUES"), cpus as u64)
        .into_iter()
        .map(|q| (q as usize).clamp(1, cpus))
        .collect();
    let max_q = *sweep.iter().max().unwrap();
    let workers = if modes.contains(&"rx") { (max_q + 1).min(cpus) } else { max_q };
    let peer_queues = env_num("VERIFLAT_ICE_PEER_QUEUES", option_env!("VERIFLAT_ICE_PEER_QUEUES"), max_q as u64) as usize;
    let pool = (env_num("VERIFLAT_ICE_POOL", option_env!("VERIFLAT_ICE_POOL"), 64) as usize).max(1);
    let link_secs = env_num("VERIFLAT_ICE_LINK_SECS", option_env!("VERIFLAT_ICE_LINK_SECS"), 15);
    log::info!(
        "ice: {:02x}:{:02x}.{} device {:04x}, BAR0 {:#x} ({} pages), {} CPUs, {} queue pairs, queue counts {:?}, modes {:?}, frames {:?} in {} copies per queue, {} s, TSC {} MHz from {}",
        f.bus, f.dev, f.fun, f.device, f.bar_phys, f.bar_pages, cpus, workers, sweep, modes, frames, pool, secs, hz / 1_000_000, source
    );

    check("ice pci_attach_dma", unsafe { sys_pci_attach_dma(f.bus, f.dev, f.fun) });
    let p: &'static Dom0Platform =
        Box::leak(Box::new(Dom0Platform { bar: bar_va(&f), bar_len: f.bar_pages * 4096, tsc_hz: hz }));
    PLATFORM.store(p as *const Dom0Platform as usize, Ordering::SeqCst);
    let config = Config { queues: workers, steering, ..Default::default() };
    let mut dev = Device::new(p, config).unwrap_or_else(|e| fail("bring-up", e));
    let link = dev.bring_link_up(link_secs * 1000).unwrap_or_else(|e| fail("link", e));
    if link.up {
        log::info!("ice: link up at {} Mb/s, max frame {}", link.speed_mbps, link.max_frame);
    } else {
        log::warn!("ice: link still down after {} s: frames will not reach the wire", link_secs);
    }

    let mac = dev.info.mac;
    for (q, (tx, rx)) in dev.take_queues().into_iter().enumerate() {
        let frame = TxFrame::pool(p, &UdpFrame { len: 60, ..frame_for(q, q, mac, steering, dst, peer, peer_queues) }, pool)
            .unwrap_or_else(|e| fail("frame buffers", e));
        // Each worker reaches its own state only through this pointer.
        let cache = if modes.contains(&"fwd") {
            p.dma_alloc(CACHE_ENTRIES * ENTRY_BYTES, 4096).unwrap_or_else(|| fail("flow cache", ice::Error::NoDmaMemory)).va as *mut [u64; 2]
        } else {
            core::ptr::null_mut()
        };
        let w = Box::into_raw(Box::new(Worker { tx, rx, frame, send: false, sender: false, do_rx: false, fwd: 0, cache, result: WorkerResult::default() }));
        WORKERS[q].store(w as usize, Ordering::SeqCst);
    }
    if modes.contains(&"fwd") {
        let Some(fwd_dst) = env_mac("VERIFLAT_ICE_FWD_DST", option_env!("VERIFLAT_ICE_FWD_DST")) else {
            log::error!("ice: mode fwd needs VERIFLAT_ICE_FWD_DST, the MAC forwarded frames go to");
            unsafe { sys_debug_exit(1) }
        };
        let lut = p.dma_alloc(TABLE_SIZE, 64).unwrap_or_else(|| fail("maglev table", ice::Error::NoDmaMemory));
        populate_lut(unsafe { core::slice::from_raw_parts_mut(lut.va as *mut i8, TABLE_SIZE) });
        FWD_LUT.store(lut.va as usize, Ordering::SeqCst);
        FWD_QUEUES.store(workers, Ordering::SeqCst);
        FWD_SRC.store(word_of(mac), Ordering::SeqCst);
        FWD_DST.store(word_of(fwd_dst), Ordering::SeqCst);
        log::info!("ice: mode fwd forwards to {}, {} queues spread over the workers of each round", ice::Mac(fwd_dst), workers);
    }
    // Mode rx: the sender sends the measured queues' frame copies (each from its queue's steering MAC) in turn.
    let sender_frames: &'static mut Vec<(u64, u16)> = Box::leak(Box::new(Vec::with_capacity(max_q * pool)));
    SENDER_FRAMES.store(sender_frames as *const Vec<(u64, u16)> as usize, Ordering::SeqCst);
    CYCLES.store((secs * hz) as usize, Ordering::SeqCst);

    // Worker k > 0: a new thread on CPU 0's shard, which CPU k pulls when it comes online (CPU 0's shard holds no
    // other queued thread, and the workers before spin on their own CPUs).
    fund("ice worker funding", 2 * workers);
    for k in 1..workers {
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

    mem_probe(p);
    let mut round = 0;
    for &frame_len in &frames {
        for &mode in &modes {
            let (send, do_rx, extra_sender) = mode_roles(mode);
            for &n in &sweep {
                if extra_sender && n >= workers {
                    log::info!("ice: mode rx needs a sender CPU besides the {} measured queues: skipped", n);
                    continue;
                }
                round += 1;
                // Measured queues 0..n; with mode rx, worker `workers - 1` sends from the steering MACs of queues
                // 0..n in turn, so that the reflector spreads its frames over them.
                let len = frame_len as usize - 4;
                for k in 0..workers {
                    let w = worker(k);
                    let fr = UdpFrame { len, ..frame_for(k, k, mac, steering, dst, peer, peer_queues) };
                    w.frame.write(&fr);
                    w.sender = extra_sender && k == workers - 1;
                    (w.send, w.do_rx) = if k < n { (send, do_rx) } else { (false, false) };
                    w.fwd = if mode == "fwd" && k < n { n } else { 0 };
                }
                sender_frames.clear();
                if extra_sender {
                    for i in 0..pool {
                        sender_frames.extend((0..n).map(|q| worker(q).frame.copy(i)));
                    }
                }
                let before = dev.port_stats();
                ROUND.store(round, Ordering::SeqCst);
                run_worker(0, round);
                let start = rdtsc();
                for k in 0..workers {
                    while WORKER_DONE[k].load(Ordering::SeqCst) != round {
                        if rdtsc() - start > 10 * hz {
                            log::error!("ice: worker {} did not finish", k);
                            unsafe { sys_debug_exit(1) };
                        }
                        core::hint::spin_loop();
                    }
                }
                let stats = dev.port_stats().since(&before);
                report(n, workers, extra_sender, mode, frame_len, hz, link.speed_mbps as u64, &stats);
            }
        }
    }
    ROUND.store(usize::MAX, Ordering::SeqCst);
    if let Err(e) = dev.shutdown() {
        log::warn!("ice: PF reset after the run: {}", e);
    }
    log::info!("ice bench passed");
}

/// BAR0's virtual address in dom0 (the one place that forms it): the loader's window over physical addresses below
/// 4 GiB.
pub(crate) fn bar_va(f: &IceFunction) -> usize {
    PCI_BAR_WINDOW_BASE + f.bar_phys
}

/// Queue q's frame: from steering MAC `src_q` (a reflector that swaps the MACs returns it to queue `src_q`), to
/// `dst`, the peer's queue q, or broadcast. The length is the caller's.
fn frame_for(
    q: usize, src_q: usize, mac: [u8; 6], steering: RxSteering, dst: Option<[u8; 6]>, peer: Option<[u8; 6]>, peer_queues: usize,
) -> UdpFrame {
    let dst = match (dst, peer) {
        (Some(d), _) => d,
        (None, Some(peer)) => steering_mac(peer, q % peer_queues.max(1)),
        (None, None) => [0xff; 6],
    };
    UdpFrame {
        dst_mac: dst,
        src_mac: if steering == RxSteering::PerQueueMac { steering_mac(mac, src_q) } else { mac },
        src_ip: [10, 10, 0, 1 + q as u8],
        dst_ip: [10, 10, 1, 1 + q as u8],
        src_port: 1024 + q as u16,
        dst_port: 5000 + q as u16,
        len: 60,
    }
}

#[allow(clippy::too_many_arguments)]
fn report(n: usize, workers: usize, extra_sender: bool, mode: &str, frame_len: u64, hz: u64, mbps: u64, stats: &ice::PortStats) {
    let (mut tx_total, mut rx_total) = (0, 0);
    for q in 0..n {
        let r = worker(q).result;
        let (tpps, rpps) = (rate(r.tx_packets, r.cycles, hz), rate(r.rx.packets, r.cycles, hz));
        tx_total += tpps;
        rx_total += rpps;
        log::info!("ice queue {} cpu {}: tx {} pps, rx {} pps, rx errors {}", q, q, tpps, rpps, r.rx.errors);
    }
    if extra_sender {
        let r = worker(workers - 1).result;
        log::info!("ice sender cpu {}: tx {} pps (not in the total)", workers - 1, rate(r.tx_packets, r.cycles, hz));
    }
    let line = if mbps != 0 { line_rate_pps(frame_len, mbps) } else { 0 };
    log::info!(
        "ice total: mode {} queues {} frame {}: tx {} pps, rx {} pps over {} queues; line rate of {}-byte frames at {} Mb/s is {} pps",
        mode, n, frame_len, tx_total, rx_total, n, frame_len, mbps, line
    );
    if mode == "fwd" {
        log::info!("ice fwd: {} workers, {} pps forwarded, {} TSC cycles per forwarded frame per worker", n, tx_total, if tx_total > 0 { hz * n as u64 / tx_total } else { 0 });
    }
    log::info!(
        "ice port: rx {} unicast {} multicast {} broadcast {} bytes, tx {} unicast {} multicast {} broadcast {} bytes, {} CRC errors, flow control rx xoff {} xon {} pfc xoff {} tx xoff {}, rx drops no-desc {} buffer {}",
        stats.rx_unicast, stats.rx_multicast, stats.rx_broadcast, stats.rx_bytes, stats.tx_unicast, stats.tx_multicast,
        stats.tx_broadcast, stats.tx_bytes, stats.crc_errors, stats.rx_xoff, stats.rx_xon, stats.rx_pfc_xoff, stats.tx_xoff, stats.rx_no_desc, stats.rx_buf_drops
    );
}

/// TSC cycles per 16-byte volatile store (as a Tx descriptor write) and per volatile load, in DMA memory from the
/// heap and in a stack buffer, to tell CPU-side memory cost from device-side cost.
fn mem_probe(p: &Dom0Platform) {
    const N: usize = 1 << 20;
    let dma = p.dma_alloc(16 * 1024, 4096).unwrap_or_else(|| fail("probe buffer", ice::Error::NoDmaMemory));
    let mut stack = [0u128; 1024];
    let mut time = |base: *mut u128| {
        let t0 = rdtsc();
        for i in 0..N {
            unsafe { core::ptr::write_volatile(base.add(i & 1023), i as u128) };
        }
        let t1 = rdtsc();
        let mut sum = 0u128;
        for i in 0..N {
            sum = sum.wrapping_add(unsafe { core::ptr::read_volatile(base.add(i & 1023)) });
        }
        let t2 = rdtsc();
        core::hint::black_box(sum);
        ((t1 - t0) as f64 / N as f64, (t2 - t1) as f64 / N as f64)
    };
    let (dw, dr) = time(dma.va as *mut u128);
    let (sw, sr) = time(stack.as_mut_ptr());
    log::info!(
        "ice mem probe: DMA memory (IOVA {:#x}) store {:.1} load {:.1} cycles per 16 bytes; stack store {:.1} load {:.1}",
        dma.iova, dw, dr, sw, sr
    );
}
