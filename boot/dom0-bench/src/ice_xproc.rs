//! The E810 (ice) benchmark with the driver in a process of its own (feature `ice-xproc`, `ICE_XPROC=1 boot/bench/run.sh`,
//! on a kernel without the timer for the reason the line-rate benchmark gives):
//! `ice_linked` with the driver linked into the application, then `ice_xproc` with the driver in a child process, both
//! moving the same batches of frames through the same zero-copy exchange (`ice::xfer`), so that their ratio is the
//! cost of the IPC round trip per batch at each core count.
//!
//! Application thread k is a thread of dom0 on CPU k (dom0's first thread for k = 0), placed as the line-rate
//! benchmark places its workers. Per batch it writes up to `batch` frames (1 or 32) into its pair's Tx slots, hands
//! them to the driver's queue pair k, and reads the frames that queue pair received, each frame's sequence number at
//! least. In `ice_linked` the hand-over is a function call into the driver on the same thread (`DriverQueue::serve`).
//! In `ice_xproc` it is one IPC round trip: `call` on the pair's endpoint, which switches CPU k directly to driver
//! thread k blocked in `receive_call`/`reply_and_receive` (the call queues nothing: the driver thread is waiting), the
//! driver thread serves the request and answers with `reply_and_receive`, which switches back.
//!
//! The driver process is a child of dom0 with an IOMMU table of its own (`new_process_with_iommu_and_endpoint`), as
//! the single-queue NVMe `ipc` configuration: it receives the E810 function (`send_pci`, then attaches it to its
//! table with `pci_attach_dma`), BAR0 (`send_pages` of dom0's window pages), the shared region (`send_pages`, which
//! maps the same pages in both processes; the driver maps them into its IOMMU table at IOVA = VA) and the pair
//! endpoints (`send_endpoint`); its rings and admin buffers come from its own heap (IOVA = VA). The shared region
//! holds, per pair, the mailbox page and the Tx slots, then every queue's Rx buffers, which the driver allocates
//! from it, so frames go to and from the device without a copy. The driver's first thread brings the device up with
//! one queue pair per application thread and creates driver thread k for each other pair; every driver thread blocks
//! in `receive_call` on its pair endpoint, so the first call of application thread k brings it to CPU k and each
//! round trip keeps both on that CPU.
//!
//! Endpoints: dom0's first thread holds pair endpoint k in descriptor `PAIR_EP + k` and gives it to application
//! thread k (its descriptor 0) and to the driver's first thread (descriptor k), which gives it to driver thread k
//! (descriptor 0). A thread has 32 descriptors, so `ice_xproc` times at most `MAX_XPROC` pairs; `ice_linked` times
//! one per CPU.
//!
//! Each pair runs alone, then all pairs at once over one shared TSC window, per batch size; the lines are
//! `ice_linked|ice_xproc cpu=k batch=b alone=<pps> conc=<pps> ratio=<alone/conc> rx_alone=<pps> rx_conc=<pps>` with
//! pps the frames the application handed over per second, a summary per batch size with the total, and
//! `ice_ipc_cost` lines comparing the two.
//!
//! With feature `ice-mock` (`ICE_MOCK=1`) the device is the software model of `ice::mock` instead of an E810: one
//! model in dom0 for `ice_linked`, another in the driver process for `ice_xproc`, each looping every transmitted
//! frame back to the queue it came from (each queue sends to its own steering MAC), which the application checks
//! frame by frame. Such numbers measure the IPC, the threads and the model, not a NIC.
//!
//! Build-time settings (environment of the dom0 build), besides those of the line-rate benchmark that apply
//! (`VERIFLAT_ICE_FRAME`, `VERIFLAT_ICE_DST`, `VERIFLAT_ICE_PEER`, `VERIFLAT_ICE_PEER_QUEUES`, `VERIFLAT_ICE_STEER`,
//! `VERIFLAT_ICE_BDF`, `VERIFLAT_ICE_LINK_SECS`): `VERIFLAT_ICE_WINDOW_MS`, the timed window of each phase (default
//! 100); `VERIFLAT_ICE_QUEUES`, pair counts (comma-separated) at which the first pairs also run at once before all of
//! them do, one `ice_linked|ice_xproc conc batch=b n=c total_conc=.. rx_total_conc=.. overlap=..` line each.

use crate::ice_bench::{bar_va, count_cpus, env_list, env_mac, env_num, fail, find_e810, pick, IceFunction, MAX_WORKERS};
use crate::nvme::time::{rdtsc, tsc_rate};
use crate::{check, current_cpu, entry, fund, quiet, stack_top, wait_for, wait_yield};
use alloc::boxed::Box;
use alloc::vec::Vec;
use core::alloc::Layout;
use core::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use ice::packet::{steering_mac, UdpFrame};
use ice::xfer::{AppQueue, BadFrame, DriverQueue, Mailbox, MAX_BATCH, SLOT_BYTES};
use ice::{Config, Device, DmaRegion, Mac, Platform, RxSteering};
use vsys::*;

#[cfg(feature = "mock-device")]
type Model = ice::mock::Mock;

/// Batch sizes, in the order they run.
const BATCHES: [usize; 2] = [1, 32];
/// Pairs `ice_xproc` times at most: dom0's first thread holds their endpoints in descriptors 1..32.
const MAX_XPROC: usize = 31;
/// dom0's first thread holds pair endpoint k in descriptor `PAIR_EP + k`.
const PAIR_EP: usize = 1;
const TX_SLOTS: usize = 128;
const TX_RING: usize = 512;
const RX_RING: usize = 512;
const RX_BUF: usize = 2048;
/// Per pair in the shared region: the mailbox page, then the Tx slots.
const PAIR_BYTES: usize = 4096 + TX_SLOTS * SLOT_BYTES;
/// Every queue's Rx buffers after the pair areas.
const RX_BYTES: usize = RX_RING * RX_BUF;
/// The shared region, at the same address in dom0 and in the driver process.
const SHARED_VA: usize = 0xdc_0000_0000;
const STACK_BYTES: usize = 64 * 1024;

const MODE_LINKED: usize = 0;
const MODE_XPROC: usize = 1;
const MODE_NAMES: [&str; 2] = ["ice_linked", "ice_xproc"];

fn shared_pages(m: usize) -> usize {
    (m * (PAIR_BYTES + RX_BYTES)).div_ceil(4096)
}

fn mailbox(k: usize) -> *mut Mailbox {
    (SHARED_VA + k * PAIR_BYTES) as *mut Mailbox
}

fn shared_slots(k: usize) -> DmaRegion {
    let va = SHARED_VA + k * PAIR_BYTES + 4096;
    DmaRegion { va: va as *mut u8, iova: va as u64, len: TX_SLOTS * SLOT_BYTES }
}

/// BAR0 (or the device model), DMA memory from the process's heap at IOVA = VA, and, once `packets_in` set it, the
/// packet buffers from a part of the shared region.
pub struct XPlatform {
    bar: usize,
    tsc_hz: u64,
    #[cfg(feature = "mock-device")]
    model: &'static Model,
    packets_next: AtomicUsize,
    packets_end: AtomicUsize,
}

impl XPlatform {
    pub(crate) fn new(bar: usize, tsc_hz: u64) -> &'static XPlatform {
        Box::leak(Box::new(XPlatform {
            bar,
            tsc_hz,
            #[cfg(feature = "mock-device")]
            model: Box::leak(Box::new(Model::new_unchecked(true))),
            packets_next: AtomicUsize::new(0),
            packets_end: AtomicUsize::new(0),
        }))
    }

    /// Takes the packet buffers from `[va, va + len)`, already mapped at IOVA = VA.
    pub(crate) fn packets_in(&self, va: usize, len: usize) {
        self.packets_next.store(va, Ordering::SeqCst);
        self.packets_end.store(va + len, Ordering::SeqCst);
    }

    fn noted(&self, region: DmaRegion) -> DmaRegion {
        #[cfg(feature = "mock-device")]
        self.model.note_dma(&region);
        region
    }
}

impl Platform for XPlatform {
    #[cfg(feature = "mock-device")]
    fn read32(&self, offset: usize) -> u32 {
        let _ = self.bar;
        self.model.read32(offset)
    }

    #[cfg(feature = "mock-device")]
    fn write32(&self, offset: usize, value: u32) {
        self.model.write32(offset, value)
    }

    #[cfg(not(feature = "mock-device"))]
    fn read32(&self, offset: usize) -> u32 {
        unsafe { core::ptr::read_volatile((self.bar + offset) as *const u32) }
    }

    #[cfg(not(feature = "mock-device"))]
    fn write32(&self, offset: usize, value: u32) {
        unsafe { core::ptr::write_volatile((self.bar + offset) as *mut u32, value) }
    }

    fn dma_alloc(&self, len: usize, align: usize) -> Option<DmaRegion> {
        let layout = Layout::from_size_align(len, align.min(4096)).ok()?;
        let va = unsafe { alloc::alloc::alloc_zeroed(layout) };
        (!va.is_null()).then(|| self.noted(DmaRegion { va, iova: va as u64, len }))
    }

    fn dma_alloc_packets(&self, len: usize, align: usize) -> Option<DmaRegion> {
        if self.packets_end.load(Ordering::SeqCst) == 0 {
            return self.dma_alloc(len, align);
        }
        let align = align.clamp(1, 4096);
        let next = self.packets_next.load(Ordering::SeqCst).next_multiple_of(align);
        if next + len > self.packets_end.load(Ordering::SeqCst) {
            return None;
        }
        self.packets_next.store(next + len, Ordering::SeqCst);
        let va = next as *mut u8;
        unsafe { core::ptr::write_bytes(va, 0, len) };
        Some(self.noted(DmaRegion { va, iova: next as u64, len }))
    }

    fn delay_us(&self, us: u64) {
        if cfg!(feature = "mock-device") {
            return;
        }
        let end = rdtsc() + us * self.tsc_hz / 1_000_000;
        while rdtsc() < end {
            core::hint::spin_loop();
        }
    }

    fn tsc(&self) -> u64 {
        rdtsc()
    }
}

/// What the benchmark sends: from the build environment, fixed before anything runs.
#[derive(Clone, Copy)]
struct Settings {
    frame_len: usize,
    dst: Option<[u8; 6]>,
    peer: Option<[u8; 6]>,
    peer_queues: usize,
    steering: RxSteering,
    link_secs: u64,
    /// The timed window of each phase, in ms and in TSC cycles.
    window_ms: u64,
    window: u64,
}

impl Settings {
    /// The frame application thread `q` sends from a device whose MAC is `mac`: with the model to its own queue's
    /// steering MAC (a loopback to the same queue); otherwise as the line-rate benchmark.
    fn frame(&self, q: usize, mac: [u8; 6]) -> UdpFrame {
        let dst = match (cfg!(feature = "mock-device"), self.dst, self.peer) {
            (true, _, _) => steering_mac(mac, q),
            (false, Some(d), _) => d,
            (false, None, Some(peer)) => steering_mac(peer, q % self.peer_queues.max(1)),
            (false, None, None) => [0xff; 6],
        };
        UdpFrame {
            dst_mac: dst,
            // On the NIC queue q sends from its own steering MAC, so a reflector that swaps the MACs returns it to q.
            src_mac: if !cfg!(feature = "mock-device") && self.steering == RxSteering::PerQueueMac { steering_mac(mac, q) } else { mac },
            src_ip: [10, 10, 0, 1 + q as u8],
            dst_ip: [10, 10, 1, 1 + q as u8],
            src_port: 1024 + q as u16,
            dst_port: 5000 + q as u16,
            len: self.frame_len - 4,
        }
    }

    fn config(&self, queues: usize) -> Config {
        Config { queues, tx_ring: TX_RING, rx_ring: RX_RING, tx_batch: 32, rx_buf: RX_BUF, steering: self.steering }
    }
}

/// One application thread's phase control and results, on cache lines of its own.
#[repr(C, align(128))]
struct Pair {
    /// One plus the CPU the thread first ran on; 0 until then.
    cpu: AtomicUsize,
    /// The phase dom0 released the thread into and the last phase it finished.
    go: AtomicUsize,
    done: AtomicUsize,
    /// The window of the released phase: batches before `start` are untimed.
    start: AtomicU64,
    end: AtomicU64,
    /// The result of the last finished phase: frames handed over and received, the TSC at the first and the last
    /// timed batch.
    sent: AtomicU64,
    received: AtomicU64,
    begin: AtomicU64,
    finish: AtomicU64,
    batches: AtomicU64,
}

impl Pair {
    const fn new() -> Pair {
        Pair {
            cpu: AtomicUsize::new(0), go: AtomicUsize::new(0), done: AtomicUsize::new(0), start: AtomicU64::new(0),
            end: AtomicU64::new(0), sent: AtomicU64::new(0), received: AtomicU64::new(0), begin: AtomicU64::new(0),
            finish: AtomicU64::new(0), batches: AtomicU64::new(0),
        }
    }
}

static PAIRS: [Pair; MAX_WORKERS] = [const { Pair::new() }; MAX_WORKERS];
static NEXT_PAIR: AtomicUsize = AtomicUsize::new(0);
/// dom0's side: application thread k's linked pair (`Linked`) and its cross-process queue (`AppQueue`).
static LINKED: [AtomicUsize; MAX_WORKERS] = [const { AtomicUsize::new(0) }; MAX_WORKERS];
static XAPP: [AtomicUsize; MAX_WORKERS] = [const { AtomicUsize::new(0) }; MAX_WORKERS];
static TSC_HZ: AtomicU64 = AtomicU64::new(0);

/// The driver process's side, in the image both processes share: what dom0 tells the driver, and what the driver
/// publishes. The queue pointers point into the driver's heap and are used only there.
static DRV_PAIRS: AtomicUsize = AtomicUsize::new(0);
static DRV_BDF: AtomicUsize = AtomicUsize::new(0);
static DRV_BAR_PHYS: AtomicUsize = AtomicUsize::new(0);
static DRV_BAR_PAGES: AtomicUsize = AtomicUsize::new(0);
static DRV_MAC: AtomicU64 = AtomicU64::new(0);
static DRV_READY: AtomicBool = AtomicBool::new(false);
static DRV_NEXT: AtomicUsize = AtomicUsize::new(0);
static DRV_STARTED: [AtomicBool; MAX_XPROC] = [const { AtomicBool::new(false) }; MAX_XPROC];
/// One plus the CPU driver thread k served its first request on; 0 until then.
static DRV_SERVED_ON: [AtomicUsize; MAX_XPROC] = [const { AtomicUsize::new(0) }; MAX_XPROC];
static DRV_QUEUES: [AtomicUsize; MAX_XPROC] = [const { AtomicUsize::new(0) }; MAX_XPROC];
static DRV_DEVICE: AtomicUsize = AtomicUsize::new(0);
static DRV_STOP: AtomicBool = AtomicBool::new(false);
static DRV_STOPPED: AtomicBool = AtomicBool::new(false);
static mut DRIVER_STACK: [u8; 128 * 1024] = [0; 128 * 1024];

/// Application thread k's linked pair: the mailbox and both sides, all in dom0's heap.
struct Linked {
    mb: *mut Mailbox,
    app: AppQueue,
    drv: DriverQueue<'static, XPlatform>,
}

/// Phases per repetition: alone and at once, per mode and batch size.
const PHASES: usize = MODE_NAMES.len() * BATCHES.len() * 2;

/// The phase number of `mode` at batch size `BATCHES[batch]`, alone or at once, in repetition `rep` (each pair count
/// of an at-once sweep is a repetition of its own, so that a waiting thread sees a new number).
fn phase_of(mode: usize, batch: usize, conc: bool, rep: usize) -> usize {
    1 + rep * PHASES + (mode * BATCHES.len() + batch) * 2 + conc as usize
}

fn bad_frame(k: usize, e: BadFrame) -> ! {
    log::error!("ice pair {}: received frame with sequence {} (length {}), expected {}", k, e.seq, e.len, e.expected_seq);
    unsafe { sys_debug_exit(1) }
}

/// Runs phase `phase` of application thread k, whose descriptor `ep` holds its pair endpoint.
fn run_phase(k: usize, ep: usize, phase: usize) {
    let index = (phase - 1) % PHASES;
    let (mode, batch) = (index / 2 / BATCHES.len(), BATCHES[index / 2 % BATCHES.len()]);
    if mode == MODE_LINKED {
        let l = unsafe { &mut *(LINKED[k].load(Ordering::SeqCst) as *mut Linked) };
        timed(k, phase, || {
            let sent = l.app.prepare(batch);
            l.drv.serve(unsafe { &mut *l.mb });
            (sent, l.app.finish().unwrap_or_else(|e| bad_frame(k, e)))
        });
    } else {
        let app = unsafe { &mut *(XAPP[k].load(Ordering::SeqCst) as *mut AppQueue) };
        timed(k, phase, || {
            let sent = app.prepare(batch);
            quiet("ice_xproc call", unsafe { sys_call(ep) });
            (sent, app.finish().unwrap_or_else(|e| bad_frame(k, e)))
        });
    }
}

/// Runs batches (`step`, which returns the frames handed over and received) of application thread k until the TSC
/// reaches the pair's `start`, then times them until its `end`, and records the result of `phase`.
fn timed(k: usize, phase: usize, mut step: impl FnMut() -> (usize, usize)) {
    let pair = &PAIRS[k];
    let (start, end) = (pair.start.load(Ordering::SeqCst), pair.end.load(Ordering::SeqCst));
    while rdtsc() < start {
        step();
    }
    let (mut sent, mut received, mut batches) = (0u64, 0u64, 0u64);
    let begin = rdtsc();
    let mut now = begin;
    while now < end {
        let (s, r) = step();
        sent += s as u64;
        received += r as u64;
        batches += 1;
        now = rdtsc();
    }
    if current_cpu() != k {
        log::error!("ice pair {} moved to CPU {}", k, current_cpu());
        unsafe { sys_debug_exit(1) };
    }
    pair.sent.store(sent, Ordering::SeqCst);
    pair.received.store(received, Ordering::SeqCst);
    pair.batches.store(batches, Ordering::SeqCst);
    pair.begin.store(begin, Ordering::SeqCst);
    pair.finish.store(now, Ordering::SeqCst);
    pair.done.store(phase, Ordering::SeqCst);
}

/// Application thread k > 0, holding pair endpoint k (if any) in descriptor 0: records its CPU and runs each phase
/// dom0 releases it into, spinning in between; dom0 exits at the end.
extern "C" fn app_thread() -> ! {
    let k = NEXT_PAIR.load(Ordering::SeqCst);
    let pair = &PAIRS[k];
    pair.cpu.store(current_cpu() + 1, Ordering::SeqCst);
    let mut last = 0;
    loop {
        let phase = pair.go.load(Ordering::SeqCst);
        if phase == last {
            core::hint::spin_loop();
            continue;
        }
        last = phase;
        run_phase(k, 0, phase);
    }
}

fn pps(frames: u64, cycles: u64) -> u64 {
    ice::bench::rate(frames, cycles, TSC_HZ.load(Ordering::SeqCst))
}

/// A ratio in hundredths, displayed with two decimals.
struct Hundredths(u64);

impl core::fmt::Display for Hundredths {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "{}.{:02}", self.0 / 100, self.0 % 100)
    }
}

fn hundredths(num: u64, den: u64) -> u64 {
    if den == 0 {
        return 0;
    }
    (200 * num + den) / (2 * den)
}

/// What one mode measured at one batch size, per pair: frames per second handed over and received, alone and all at
/// once, and TSC cycles per batch alone.
#[derive(Clone, Copy, Default)]
struct Measured {
    alone: u64,
    conc: u64,
    rx_alone: u64,
    rx_conc: u64,
    cycles_per_batch: u64,
}

/// Times `n` pairs in `mode` at batch size `BATCHES[b]`: each alone, then all at once in one window, and logs them.
/// Before all n at once, the first c pairs run at once for each c of `counts` below n, each logged as one
/// `<mode> conc batch=b n=c` line.
fn time_mode(n: usize, mode: usize, b: usize, window: u64, counts: &[usize], out: &mut [Measured]) {
    let name = MODE_NAMES[mode];
    let ep0 = PAIR_EP;
    for k in 0..n {
        let pair = &PAIRS[k];
        let start = rdtsc() + window / 4;
        pair.start.store(start, Ordering::SeqCst);
        pair.end.store(start + window, Ordering::SeqCst);
        let phase = phase_of(mode, b, false, 0);
        if k == 0 {
            run_phase(0, ep0, phase);
        } else {
            pair.go.store(phase, Ordering::SeqCst);
            wait_for("an ice pair alone", || pair.done.load(Ordering::SeqCst) == phase);
        }
        let cycles = pair.finish.load(Ordering::SeqCst) - pair.begin.load(Ordering::SeqCst);
        out[k].alone = pps(pair.sent.load(Ordering::SeqCst), cycles);
        out[k].rx_alone = pps(pair.received.load(Ordering::SeqCst), cycles);
        out[k].cycles_per_batch = cycles / pair.batches.load(Ordering::SeqCst).max(1);
    }
    let batch = BATCHES[b];
    let mut sweep: Vec<usize> = counts.iter().copied().filter(|&c| 0 < c && c < n).collect();
    sweep.push(n);
    for (rep, &c) in sweep.iter().enumerate() {
        // One window for the first c pairs, far enough that every pair is released before it opens.
        let start = rdtsc() + (window / 4).max(TSC_HZ.load(Ordering::SeqCst) / 1000);
        let phase = phase_of(mode, b, true, rep);
        for pair in &PAIRS[..c] {
            pair.start.store(start, Ordering::SeqCst);
            pair.end.store(start + window, Ordering::SeqCst);
        }
        for pair in &PAIRS[1..c] {
            pair.go.store(phase, Ordering::SeqCst);
        }
        run_phase(0, ep0, phase);
        for pair in &PAIRS[1..c] {
            wait_for("the ice pairs at once", || pair.done.load(Ordering::SeqCst) == phase);
        }
        let (mut total_conc, mut rx_total) = (0, 0);
        let (mut max_begin, mut min_finish, mut min_begin, mut max_finish) = (0, u64::MAX, u64::MAX, 0);
        for k in 0..c {
            let pair = &PAIRS[k];
            let (begin, finish) = (pair.begin.load(Ordering::SeqCst), pair.finish.load(Ordering::SeqCst));
            (max_begin, min_finish, min_begin, max_finish) = (max_begin.max(begin), min_finish.min(finish), min_begin.min(begin), max_finish.max(finish));
            out[k].conc = pps(pair.sent.load(Ordering::SeqCst), finish - begin);
            out[k].rx_conc = pps(pair.received.load(Ordering::SeqCst), finish - begin);
            total_conc += out[k].conc;
            rx_total += out[k].rx_conc;
        }
        let overlap = if max_begin < min_finish { hundredths(min_finish - max_begin, max_finish - min_begin) } else { 0 };
        if c < n {
            log::info!("{} conc batch={} n={} total_conc={} rx_total_conc={} overlap={}", name, batch, c, total_conc, rx_total, Hundredths(overlap));
            continue;
        }
        let (mut total_alone, mut ratios) = (0, [0u64; MAX_WORKERS]);
        for k in 0..n {
            ratios[k] = hundredths(out[k].alone, out[k].conc);
            total_alone += out[k].alone;
            log::info!(
                "{} cpu={} batch={} alone={} conc={} ratio={} rx_alone={} rx_conc={} cycles_per_batch_alone={}",
                name, k, batch, out[k].alone, out[k].conc, Hundredths(ratios[k]), out[k].rx_alone, out[k].rx_conc, out[k].cycles_per_batch
            );
        }
        let ratios = &mut ratios[..n];
        ratios.sort_unstable();
        log::info!(
            "{} summary batch={} n={} total_alone={} total_conc={} rx_total_conc={} min_ratio={} max_ratio={} median_ratio={} overlap={}",
            name, batch, n, total_alone, total_conc, rx_total, Hundredths(ratios[0]), Hundredths(ratios[n - 1]),
            Hundredths((ratios[(n - 1) / 2] + ratios[n / 2]) / 2), Hundredths(overlap)
        );
    }
}

/// The settings of this build for `n` pairs at TSC rate `hz`.
fn settings(n: usize, hz: u64) -> Settings {
    let frame_len = env_num("VERIFLAT_ICE_FRAME", option_env!("VERIFLAT_ICE_FRAME"), 64) as usize;
    if !(64..=1518).contains(&frame_len) {
        log::error!("ice: VERIFLAT_ICE_FRAME must be 64..1518");
        unsafe { sys_debug_exit(1) };
    }
    let steering = match option_env!("VERIFLAT_ICE_STEER").unwrap_or("mac") {
        "mac" => RxSteering::PerQueueMac,
        "promisc" => RxSteering::Promiscuous,
        s => {
            log::error!("ice: VERIFLAT_ICE_STEER={} is not mac or promisc", s);
            unsafe { sys_debug_exit(1) }
        }
    };
    let window_ms = env_num("VERIFLAT_ICE_WINDOW_MS", option_env!("VERIFLAT_ICE_WINDOW_MS"), 100).max(1);
    Settings {
        frame_len,
        dst: env_mac("VERIFLAT_ICE_DST", option_env!("VERIFLAT_ICE_DST")),
        peer: env_mac("VERIFLAT_ICE_PEER", option_env!("VERIFLAT_ICE_PEER")),
        peer_queues: env_num("VERIFLAT_ICE_PEER_QUEUES", option_env!("VERIFLAT_ICE_PEER_QUEUES"), n as u64) as usize,
        steering,
        link_secs: env_num("VERIFLAT_ICE_LINK_SECS", option_env!("VERIFLAT_ICE_LINK_SECS"), 15),
        window_ms,
        window: window_ms * hz / 1000,
    }
}

/// The benchmark (feature `ice-xproc`): logs that it is skipped when the loader recorded no E810 function, unless
/// it runs on the device model (feature `ice-mock`).
pub fn run() {
    // find_e810 allocates once an E810 is recorded: the heap comes first (init is idempotent).
    crate::slab_alloc::init();
    let f = if cfg!(feature = "mock-device") {
        None
    } else {
        let Some(f) = pick(&find_e810()) else {
            log::info!("ice xproc bench skipped: no E810 function recorded");
            return;
        };
        Some(f)
    };
    let Some((hz, source)) = tsc_rate() else {
        log::error!("ice xproc bench: no CPUID source gives the TSC rate; build dom0 with VERIFLAT_TSC_MHZ set to it");
        unsafe { sys_debug_exit(1) };
    };
    TSC_HZ.store(hz, Ordering::SeqCst);
    let n = count_cpus();
    let s = settings(n, hz);
    let m = n.min(MAX_XPROC);
    match f {
        Some(f) => log::info!(
            "ice xproc: E810 {:02x}:{:02x}.{} device {:04x}, BAR0 {:#x} ({} pages), {} CPUs, {} linked and {} cross-process pairs, {}-byte frames, {} ms windows, TSC {} MHz from {}",
            f.bus, f.dev, f.fun, f.device, f.bar_phys, f.bar_pages, n, n, m, s.frame_len, s.window_ms, hz / 1_000_000, source
        ),
        None => log::info!(
            "ice xproc: on the software device model, so the numbers measure the IPC, the threads and the model, not a NIC; {} CPUs, {} linked and {} cross-process pairs, {}-byte frames, {} ms windows, TSC {} MHz from {}",
            n, n, m, s.frame_len, s.window_ms, hz / 1_000_000, source
        ),
    }

    crate::slab_alloc::init();
    // The pair endpoints and the application threads; dom0's first thread is application thread 0.
    fund("ice xproc endpoint and thread funding", m + 2 * n);
    for k in 0..m {
        quiet("ice xproc new_endpoint", unsafe { sys_new_endpoint(PAIR_EP + k) });
    }
    PAIRS[0].cpu.store(1, Ordering::SeqCst);
    for k in 1..n {
        // A new thread queues on CPU 0's shard, which holds no other thread, so CPU k pulls it when it comes online.
        NEXT_PAIR.store(k, Ordering::SeqCst);
        let (ip, sp) = (entry(app_thread), stack());
        if k < m {
            quiet("ice xproc new_thread_with_endpoint (application)", unsafe { sys_new_thread_with_endpoint(PAIR_EP + k, ip, sp) });
        } else {
            quiet("ice xproc new_thread (application)", unsafe { sys_new_thread(ip, sp) });
        }
        quiet("ice xproc cpu_online", unsafe { sys_cpu_online(k) });
        wait_for("an ice application thread to start", || PAIRS[k].cpu.load(Ordering::SeqCst) != 0);
        let cpu = PAIRS[k].cpu.load(Ordering::SeqCst) - 1;
        if cpu != k {
            log::error!("ice xproc: application thread {} runs on CPU {}", k, cpu);
            unsafe { sys_debug_exit(1) };
        }
    }

    let counts: Vec<usize> = env_list("VERIFLAT_ICE_QUEUES", option_env!("VERIFLAT_ICE_QUEUES"), n as u64).into_iter().map(|c| c as usize).collect();
    let mut results = [[[Measured::default(); MAX_WORKERS]; 2]; 2];
    run_linked(f, &s, n, &counts, &mut results[MODE_LINKED]);
    run_xproc(f, &s, m, &counts, &mut results[MODE_XPROC]);

    // The cost of the round trip: totals over the pairs both modes ran, and per pair the TSC cycles per batch alone.
    for (b, batch) in BATCHES.iter().enumerate() {
        let (linked, xproc) = (&results[MODE_LINKED][b][..m], &results[MODE_XPROC][b][..m]);
        let (linked_conc, xproc_conc) = (linked.iter().map(|x| x.conc).sum::<u64>(), xproc.iter().map(|x| x.conc).sum::<u64>());
        let mut ipc = [0u64; MAX_WORKERS];
        for k in 0..m {
            ipc[k] = xproc[k].cycles_per_batch.saturating_sub(linked[k].cycles_per_batch);
        }
        log::info!(
            "ice_ipc_cost batch={} n={} linked_total_conc={} xproc_total_conc={} linked/xproc={} median_cycles_per_batch_alone: linked={} xproc={} difference={}{}",
            batch, m, linked_conc, xproc_conc, Hundredths(hundredths(linked_conc, xproc_conc)), median(linked.iter().map(|x| x.cycles_per_batch)),
            median(xproc.iter().map(|x| x.cycles_per_batch)), median(ipc[..m].iter().copied()),
            if m < n { " (linked_total_conc over the first n pairs of a run of all CPUs)" } else { "" }
        );
    }
    log::info!("ice xproc bench passed");
}

fn median(values: impl Iterator<Item = u64>) -> u64 {
    let mut v = [0u64; MAX_WORKERS];
    let mut n = 0;
    for x in values {
        v[n] = x;
        n += 1;
    }
    let v = &mut v[..n];
    v.sort_unstable();
    (v[(n - 1) / 2] + v[n / 2]) / 2
}

/// A thread stack from the calling process's heap; returns its top.
fn stack() -> usize {
    let stack = unsafe { alloc::alloc::alloc(Layout::from_size_align(STACK_BYTES, 4096).unwrap()) } as usize;
    if stack == 0 {
        log::error!("ice xproc: no memory for a thread stack");
        unsafe { sys_debug_exit(1) };
    }
    stack + STACK_BYTES - 8
}

fn bring_link_up(dev: &mut Device<'static, XPlatform>, s: &Settings) -> [u8; 6] {
    let link = dev.bring_link_up(s.link_secs * 1000).unwrap_or_else(|e| fail("link", e));
    if link.up {
        log::info!("ice: link up at {} Mb/s, max frame {}", link.speed_mbps, link.max_frame);
    } else {
        log::warn!("ice: link still down after {} s: frames will not reach the wire", s.link_secs);
    }
    dev.info.mac
}

fn empty_mailbox() -> Mailbox {
    Mailbox { tx_first: 0, tx_count: 0, rx_budget: 0, tx_len: [0; MAX_BATCH], rx_count: 0, tx_completed: 0, rx: [Default::default(); MAX_BATCH] }
}

/// `ice_linked`: the driver linked into dom0 with one queue pair per CPU; each pair's mailbox, Tx slots and Rx
/// buffers in dom0's heap. Resets the PF afterwards.
fn run_linked(f: Option<IceFunction>, s: &Settings, n: usize, counts: &[usize], out: &mut [[Measured; MAX_WORKERS]; 2]) {
    let bar = f.map_or(0, |f| bar_va(&f));
    if let Some(f) = f {
        check("ice pci_attach_dma (dom0)", unsafe { sys_pci_attach_dma(f.bus, f.dev, f.fun) });
    }
    let p = XPlatform::new(bar, TSC_HZ.load(Ordering::SeqCst));
    let mut dev = Device::new(p, s.config(n)).unwrap_or_else(|e| fail("bring-up", e));
    let mac = bring_link_up(&mut dev, s);
    log::info!("ice_linked: {} queue pairs, MAC {}", n, Mac(mac));
    for (k, (tx, rx)) in dev.take_queues().into_iter().enumerate() {
        let slots = p.dma_alloc(TX_SLOTS * SLOT_BYTES, 4096).unwrap_or_else(|| fail("Tx slots", ice::Error::NoDmaMemory));
        let mb = Box::into_raw(Box::new(empty_mailbox()));
        let app = AppQueue::new(mb, slots, TX_SLOTS, &s.frame(k, mac), cfg!(feature = "mock-device"));
        let drv = DriverQueue::new(tx, rx, slots.iova, TX_SLOTS, TX_RING);
        LINKED[k].store(Box::into_raw(Box::new(Linked { mb, app, drv })) as usize, Ordering::SeqCst);
    }
    for (b, measured) in out.iter_mut().enumerate() {
        time_mode(n, MODE_LINKED, b, s.window, counts, measured);
    }
    if let Err(e) = dev.shutdown() {
        log::warn!("ice: PF reset after ice_linked: {}", e);
    }
}

/// `ice_xproc`: the driver in a child process with one thread per pair, `m` pairs. dom0 maps the shared region,
/// starts the driver process and hands it the function, BAR0, the shared region and the pair endpoints over pair
/// endpoint 0, then times the pairs, and at the end has the driver reset the PF and kills it.
fn run_xproc(f: Option<IceFunction>, s: &Settings, m: usize, counts: &[usize], out: &mut [[Measured; MAX_WORKERS]; 2]) {
    let pages = shared_pages(m);
    fund("ice xproc shared region funding", 4 * pages);
    check("ice xproc mmap_4k (shared region)", unsafe { sys_mmap_4k(SHARED_VA, pages) });
    DRV_PAIRS.store(m, Ordering::SeqCst);
    if let Some(f) = f {
        DRV_BDF.store(f.bus << 8 | f.dev << 3 | f.fun, Ordering::SeqCst);
        DRV_BAR_PHYS.store(f.bar_phys, Ordering::SeqCst);
        DRV_BAR_PAGES.store(f.bar_pages, Ordering::SeqCst);
    }
    let (image, image_pages) = crate::image_range();
    fund("ice xproc driver process funding", 6 + 3 * image_pages);
    let sp = stack_top(&raw const DRIVER_STACK);
    check("ice xproc new_process_with_iommu_and_endpoint (driver)", unsafe {
        sys_new_process_with_iommu_and_endpoint(image, image_pages, PAIR_EP, entry(driver_main), sp)
    });
    if let Some(f) = f {
        check("ice xproc send_pci", unsafe { sys_send_pci(PAIR_EP, f.bus, f.dev, f.fun) });
        check("ice xproc send_pages (BAR0)", unsafe { sys_send_pages(PAIR_EP, bar_va(&f), f.bar_pages) });
    }
    check("ice xproc send_pages (shared region)", unsafe { sys_send_pages(PAIR_EP, SHARED_VA, pages) });
    for k in 1..m {
        quiet("ice xproc send_endpoint", unsafe { sys_send_endpoint(PAIR_EP, PAIR_EP + k) });
    }
    wait_yield("the ice driver process to bring the device up", || DRV_READY.load(Ordering::SeqCst));
    // Every driver thread set its start flag right before receive_call: a few more yields let one preempted in
    // between block there, so that none is still queued on CPU 0 when its first call comes.
    for _ in 0..4 {
        unsafe { sys_schedule() };
    }
    let mac = DRV_MAC.load(Ordering::SeqCst).to_le_bytes();
    let mac = [mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]];
    log::info!("ice_xproc: driver process up with {} queue pairs, MAC {}, {} shared pages", m, Mac(mac), pages);
    for k in 0..m {
        let app = AppQueue::new(mailbox(k), shared_slots(k), TX_SLOTS, &s.frame(k, mac), cfg!(feature = "mock-device"));
        XAPP[k].store(Box::into_raw(Box::new(app)) as usize, Ordering::SeqCst);
    }
    for (b, measured) in out.iter_mut().enumerate() {
        time_mode(m, MODE_XPROC, b, s.window, counts, measured);
        for k in 0..m {
            let cpu = DRV_SERVED_ON[k].load(Ordering::SeqCst);
            if cpu != k + 1 {
                log::error!("ice_xproc: driver thread {} served on CPU {}", k, cpu as isize - 1);
                unsafe { sys_debug_exit(1) };
            }
        }
    }
    DRV_STOP.store(true, Ordering::SeqCst);
    quiet("ice xproc call (stop)", unsafe { sys_call(PAIR_EP) });
    wait_for("the ice driver to reset the PF", || DRV_STOPPED.load(Ordering::SeqCst));
    check("ice xproc kill_process(0) (driver)", unsafe { sys_kill_process(0) });
}

/// First thread of the driver process, holding pair endpoint 0 in descriptor 0: takes what dom0 sends, brings the
/// device up with one queue pair per pair, starts driver thread k for each other pair, and serves pair 0.
extern "C" fn driver_main() -> ! {
    let m = DRV_PAIRS.load(Ordering::SeqCst);
    let pages = shared_pages(m);
    let bar_pages = DRV_BAR_PAGES.load(Ordering::SeqCst);
    let bar = PCI_BAR_WINDOW_BASE + DRV_BAR_PHYS.load(Ordering::SeqCst);
    let bdf = DRV_BDF.load(Ordering::SeqCst);
    let (bus, dev, fun) = (bdf >> 8, (bdf >> 3) & 0x1f, bdf & 7);
    let hw = !cfg!(feature = "mock-device");
    // A receiver holds 3 4K quota per page for the worst case of page tables (as do mmap and IOMMU maps).
    fund("ice driver receive funding", 3 * (if hw { bar_pages } else { 0 } + pages));
    if hw {
        quiet("ice driver receive_pci", unsafe { sys_receive_pci(0, bus, dev, fun) });
        quiet("ice driver receive_pages (BAR0)", unsafe { sys_receive_pages(0, bar, bar_pages) });
    }
    quiet("ice driver receive_pages (shared region)", unsafe { sys_receive_pages(0, SHARED_VA, pages) });
    for k in 1..m {
        quiet("ice driver receive_endpoint", unsafe { sys_receive_endpoint(0, k) });
    }
    crate::slab_alloc::init();
    fund("ice driver IOMMU funding", 3 * pages);
    quiet("ice driver iommu_map_4k (shared region)", unsafe { sys_iommu_map_4k(SHARED_VA, SHARED_VA, pages) });
    if hw {
        quiet("ice driver pci_attach_dma", unsafe { sys_pci_attach_dma(bus, dev, fun) });
    }
    let hz = TSC_HZ.load(Ordering::SeqCst);
    let s = settings(m, hz);
    let p = XPlatform::new(bar, hz);
    p.packets_in(SHARED_VA + m * PAIR_BYTES, m * RX_BYTES);
    let mut device = Device::new(p, s.config(m)).unwrap_or_else(|e| fail("bring-up (driver process)", e));
    let mac = bring_link_up(&mut device, &s);
    for (k, (tx, rx)) in device.take_queues().into_iter().enumerate() {
        let q = DriverQueue::new(tx, rx, shared_slots(k).iova, TX_SLOTS, TX_RING);
        DRV_QUEUES[k].store(Box::into_raw(Box::new(q)) as usize, Ordering::SeqCst);
    }
    DRV_DEVICE.store(Box::into_raw(Box::new(Some(device))) as usize, Ordering::SeqCst);
    let mut word = [0u8; 8];
    word[..6].copy_from_slice(&mac);
    DRV_MAC.store(u64::from_le_bytes(word), Ordering::SeqCst);
    // Driver thread k: queued on this CPU's shard with pair endpoint k in its descriptor 0; it runs until it blocks
    // in receive_call.
    fund("ice driver thread funding", 2 * m);
    for k in 1..m {
        DRV_NEXT.store(k, Ordering::SeqCst);
        quiet("ice driver new_thread_with_endpoint", unsafe { sys_new_thread_with_endpoint(k, entry(driver_thread), stack()) });
        wait_yield("an ice driver thread to start", || DRV_STARTED[k].load(Ordering::SeqCst));
    }
    DRV_READY.store(true, Ordering::SeqCst);
    serve(0)
}

/// Driver thread k > 0, holding pair endpoint k in descriptor 0.
extern "C" fn driver_thread() -> ! {
    let k = DRV_NEXT.load(Ordering::SeqCst);
    DRV_STARTED[k].store(true, Ordering::SeqCst);
    serve(k)
}

/// Serves pair k: one request per call on descriptor 0, answered with reply_and_receive. Driver thread 0 instead
/// resets the PF when dom0 calls it after setting `DRV_STOP`.
fn serve(k: usize) -> ! {
    let q = unsafe { &mut *(DRV_QUEUES[k].load(Ordering::SeqCst) as *mut DriverQueue<'static, XPlatform>) };
    let mb = unsafe { &mut *mailbox(k) };
    quiet("ice driver receive_call", unsafe { sys_receive_call(0) });
    DRV_SERVED_ON[k].store(current_cpu() + 1, Ordering::SeqCst);
    loop {
        if k == 0 && DRV_STOP.load(Ordering::SeqCst) {
            let device = unsafe { &mut *(DRV_DEVICE.load(Ordering::SeqCst) as *mut Option<Device<'static, XPlatform>>) };
            if let Some(device) = device.take() {
                if let Err(e) = device.shutdown() {
                    log::warn!("ice: PF reset after ice_xproc: {}", e);
                }
            }
            DRV_STOPPED.store(true, Ordering::SeqCst);
        } else {
            q.serve(mb);
        }
        quiet("ice driver reply_and_receive", unsafe { sys_reply_and_receive(0) });
    }
}

