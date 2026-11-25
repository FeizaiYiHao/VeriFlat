//! The two-process E810 (ice) shapes (feature `ice-chan`, on a kernel without the timer for the reason the
//! line-rate benchmark gives): application threads in dom0, driver threads in a child process with an IOMMU table of
//! its own, exchanging frames through `ice::chan` (the code Atmosphere's front end runs too), in modes `tx`, `rx`,
//! `fwd` and `maglev`. `VERIFLAT_ICE_SHAPE` picks the shape:
//!
//! - `linked`: the application linked to its driver: thread k of the driver process on CPU k + 1 loops over both
//!   sides of pair k (`App::step`, then `Driver::control` + `Driver::step` as one IPC call would run them, and the
//!   same Rx hold-off), with no IPC and no second core.
//! - `ring`: two cores per pair and no IPC: application thread k on CPU k and driver thread k on CPU P + k (P = half
//!   the CPUs) each loop over their side of pair k's shared rings (`App::step`, `Driver::run_once`), as Atmosphere's
//!   ixgbe ring-buffer tests and the NVMe benchmark's `twocore` configuration.
//! - `ipc` (default): one IPC round trip per batch: application thread k on CPU k calls driver thread k, blocked in
//!   `receive_call`/`reply_and_receive` on pair k's endpoint, which runs one `Driver::control` + `Driver::step` on CPU
//!   k and answers, as `ice_xproc` does.
//!
//! `VERIFLAT_ICE_PATH` picks the data path (`ice::chan::Path`):
//!
//! - `zero` (default): zero copy both ways. The shared region holds per pair its `ice::chan::Shared` block and Tx
//!   slots, then every queue's Rx buffers; dom0 and the driver map it at the same VA, the driver's IOMMU table at
//!   IOVA = VA.
//! - `copy`: the same shared region as a bounce area; the application copies each frame into a shared Tx slot from a
//!   private one, and out of each shared Rx buffer into a private one (one copy per direction per frame).
//! - `map`: page hand-off. The Rx buffers live in a region of their own at `M_VA`, one buffer per page group of
//!   `ppf` pages (1 up to a 4 KiB frame, 3 for 9000 bytes), that dom0 maps, sends to the driver and unmaps again, so
//!   that each page is mapped in exactly one of the two processes. Per step, for every run of contiguous pages
//!   (`ice::chan::page_runs`) of the frames it hands over, the driver gives the run to the application
//!   (`courier::give`: `send_pages`, then `unmap_4k` of its own mapping) and removes it from its IOMMU table
//!   (`iommu_unmap_4k`), then pushes the frames. The application, after its work on a step's frames, gives each run
//!   back (`send_pages`, `unmap_4k`), records it in pair k's return ring, and only then releases (`rx`) or pushes
//!   (`fwd`) the frames; the driver maps every returned run into its IOMMU table again (`iommu_map_4k`) before it
//!   re-arms or transmits anything. So per run and direction: one `send_pages` (with one `receive_pages` of the courier
//!   and two context switches on the giver's CPU, see `courier`), one `unmap_4k`; and per run one `iommu_unmap_4k`
//!   and one `iommu_map_4k`. `VERIFLAT_ICE_MAP_IOMMU=0` leaves the pages in the IOMMU table (the device keeps access
//!   to pages the application holds: not an isolating hand-off; for the cost split only). Mode `tx` runs zero copy
//!   (the application's Tx slots are shared); `linked` has no second process and refuses `map`; at most
//!   `M_MAX_PAIRS` pairs. Endpoints: in the IPC shape the driver gives over the pair endpoint (the application's
//!   courier for pair k is a dom0 thread holding pair k's endpoint, parked behind the blocked driver thread), the
//!   application over endpoint `E_D0 + k` (dom0's descriptor; application thread k > 0 receives it into its
//!   descriptor 1 before it moves to CPU k); in the ring shape the driver over `E_A0 + j` (its thread j's descriptor
//!   0) and the application over `E_D0 + k` (application thread k's descriptor 0).
//!
//! `VERIFLAT_ICE_TOUCH` (a list of `off`, `read`, `write`; default `off`) adds the application's pass over every payload
//! byte (`ice::chan::Touch`); each listed pass runs over every batch size and pair count of each mode.
//!
//! The driver process gets the E810 function (`send_pci` of the function dom0 claimed; it maps BAR0 and attaches the
//! function with its own `pci_attach_dma`), the shared region (`send_pages`; it maps the region into its IOMMU table at
//! IOVA = VA), with path `map` the Rx region, and the endpoints above. It brings the device up with one queue pair
//! per CPU, so that a generator spreading its frames over the steering MACs of all of them loads every pair count
//! (pair k of c polls queues k, k + c, ..); driver k sends on Tx queue k.
//!
//! Per mode, batch size and pair count c (`VERIFLAT_ICE_QUEUES`), pairs 0..c run one phase over one shared TSC window
//! after a quarter window of warm-up: each starts the phase on its driver, steps until the window closes counting
//! the frames its application side moved (pushed for transmission, received, forwarded), and ends the phase. The line
//! is `ice_linked|ice_ring|ice_ipc mode=<m> batch=<b> n=<c> total=<pps> min=<pps> max=<pps> overlap=<..> pairs=<pps>,..
//! path=<p> touch=<t> frame=<bytes>`; with path `map` a line `ice_map_counts` follows with the gives and pages per
//! side over the phase.
//!
//! Build-time settings: `VERIFLAT_ICE_SHAPE` (`ipc`), `VERIFLAT_ICE_MODE` (`tx,rx,fwd,maglev`), `VERIFLAT_ICE_BATCH`
//! (`1,32`), `VERIFLAT_ICE_QUEUES` (pair counts; default 1, 2, 4, .. up to every pair), `VERIFLAT_ICE_PATH`,
//! `VERIFLAT_ICE_TOUCH`, `VERIFLAT_ICE_MAP_IOMMU`, `VERIFLAT_ICE_WINDOW_MS` (1000), `VERIFLAT_ICE_FRAME` (64, with CRC;
//! 64..9000: above 1518 the port is set to jumbo frames and the Rx buffers and Tx slots hold a whole frame),
//! `VERIFLAT_ICE_DST` (destination of mode tx's frames, else `VERIFLAT_ICE_PEER`'s steering MACs, else broadcast),
//! `VERIFLAT_ICE_FWD_DST` (destination of forwarded frames, needed for modes fwd and maglev), `VERIFLAT_ICE_STEER`,
//! `VERIFLAT_ICE_BDF`, `VERIFLAT_ICE_LINK_SECS`. With feature `ice-chan-mock` the device is `ice::mock`: mode tx's
//! frames and forwarded frames go to the pair's own queue (so a fwd phase after a tx phase forwards the frames the tx
//! phase left in the Rx rings, over and over); numbers of the model, not a NIC.

use crate::courier::{self, Mailbox};
use crate::ice_bench::{count_cpus, env_list, env_mac, env_num, fail, find_e810, pick, IceFunction, MAX_WORKERS};
use crate::ice_xproc::XPlatform;
use crate::nvme::time::{rdtsc, tsc_rate};
use crate::{check, current_cpu, entry, fund, quiet, stack_top, wait_for, wait_yield};
use alloc::boxed::Box;
use alloc::vec::Vec;
use core::alloc::Layout;
use core::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use ice::chan::{page_runs, App, Driver, Entry, Mode, Path, Shared, Spsc, Touch, MAX_BATCH, RING, RX_HOLDOFF_CYCLES, SHARED_BYTES, SLOT_BYTES};
use ice::maglev::{populate_lut, Maglev, CACHE_ENTRIES, TABLE_SIZE};
use ice::packet::{steering_mac, UdpFrame, JUMBO_MAX_FRAME};
use ice::{Config, Device, DmaRegion, Mac, RxQueue, RxSteering};
use vsys::*;

const MOCK: bool = cfg!(feature = "mock-device");
/// Pairs at most: in the IPC shape dom0's first thread holds their endpoints in descriptors 1..32.
const MAX_PAIRS: usize = 31;
const PAIR_EP: usize = 1;
const TX_SLOTS: usize = 128;
const TX_RING: usize = 512;
const RX_RING: usize = 512;
/// The shared region, at the same address in dom0 and in the driver process.
const SHARED_VA: usize = 0xde_0000_0000;
/// Path `map`: the Rx buffers, at the same address in whichever process holds a page.
const M_VA: usize = 0xdf_0000_0000;
/// Path `map`: pairs at most, and the descriptors (in dom0's first thread and in the driver process's) of the
/// endpoints the application gives over (`E_D0 + k`) and, in the ring shape, the driver (`E_A0 + j`).
const M_MAX_PAIRS: usize = 8;
const E_D0: usize = 9;
const E_A0: usize = 17;
/// 4K quota of each courier and of each driver thread of path `map` (3 per page of a run, page tables).
const M_FUNDING: usize = 1024;
const STACK_BYTES: usize = 64 * 1024;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Shape {
    Linked,
    Ring,
    Ipc,
}

fn shape() -> Shape {
    match option_env!("VERIFLAT_ICE_SHAPE").unwrap_or("ipc") {
        "linked" => Shape::Linked,
        "ring" => Shape::Ring,
        "ipc" => Shape::Ipc,
        s => {
            log::error!("ice: VERIFLAT_ICE_SHAPE={} is not linked, ring or ipc", s);
            unsafe { sys_debug_exit(1) }
        }
    }
}

fn shape_name() -> &'static str {
    match shape() {
        Shape::Linked => "ice_linked",
        Shape::Ring => "ice_ring",
        Shape::Ipc => "ice_ipc",
    }
}

fn path() -> Path {
    let s = option_env!("VERIFLAT_ICE_PATH").unwrap_or("zero");
    Path::parse(s).unwrap_or_else(|| {
        log::error!("ice: VERIFLAT_ICE_PATH={} is not zero, copy or map", s);
        unsafe { sys_debug_exit(1) }
    })
}

/// The payload passes to run, each over every mode, batch and pair count: `VERIFLAT_ICE_TOUCH`, a list of `off`,
/// `read`, `write` (default `off`).
fn touches() -> Vec<Touch> {
    option_env!("VERIFLAT_ICE_TOUCH")
        .unwrap_or("off")
        .split(',')
        .map(|t| {
            Touch::parse(t.trim()).unwrap_or_else(|| {
                log::error!("ice: VERIFLAT_ICE_TOUCH={} is not a list of off, read and write", t);
                unsafe { sys_debug_exit(1) }
            })
        })
        .collect()
}

fn touch_of(code: usize) -> Touch {
    [Touch::Off, Touch::Read, Touch::Write][code.min(2)]
}

fn touch_code(t: Touch) -> usize {
    match t {
        Touch::Off => 0,
        Touch::Read => 1,
        Touch::Write => 2,
    }
}

/// Path `map`: whether the pages leave and re-enter the driver's IOMMU table.
fn map_iommu() -> bool {
    env_num("VERIFLAT_ICE_MAP_IOMMU", option_env!("VERIFLAT_ICE_MAP_IOMMU"), 1) != 0
}

fn frame_len() -> usize {
    env_num("VERIFLAT_ICE_FRAME", option_env!("VERIFLAT_ICE_FRAME"), 64) as usize
}

/// Bytes per Tx slot: 2048, or the frame rounded up to 128 bytes.
fn slot_bytes() -> usize {
    SLOT_BYTES.max(frame_len().next_multiple_of(128))
}

/// Path `map`: pages per Rx buffer.
fn ppf() -> usize {
    frame_len().div_ceil(4096)
}

/// Bytes per Rx buffer: whole pages with path `map`, else as a Tx slot.
fn rx_buf() -> usize {
    if path() == Path::Map { ppf() * 4096 } else { slot_bytes() }
}

fn pair_bytes() -> usize {
    SHARED_BYTES + TX_SLOTS * slot_bytes()
}

/// Bytes of one queue's Rx buffers, with room for the 4 KiB alignment of each 1 MiB chunk the driver allocates them
/// in (`Device::add_rx_queue`) when a chunk is not a whole number of pages (none for the 2048-byte buffers, whose
/// queues stay back to back as before jumbo frames).
fn rx_bytes() -> usize {
    let per_chunk = ((1 << 20) / rx_buf()).max(1);
    let whole_pages = (per_chunk * rx_buf()) % 4096 == 0 && (RX_RING * rx_buf()) % 4096 == 0;
    RX_RING * rx_buf() + if whole_pages { 0 } else { RX_RING.div_ceil(per_chunk) * 4096 }
}

/// Pages per `mmap_4k`, `send_pages`/`receive_pages` and `iommu_map_4k` call of the setup when `chunked`, so that the
/// 4K quota each call wants at hand (3 or 4 per page) stays small.
const CHUNK: usize = 512;

/// Whether the setup maps, sends and IOMMU-maps its regions in chunks of `CHUNK` pages: path `map` and jumbo frames,
/// whose regions are larger; every other run does each in one call with the funding it had before both existed.
fn chunked() -> bool {
    path() == Path::Map || frame_len() > 1518
}

/// `[0, total)` in chunks of `CHUNK` pages (one chunk unless `chunked`): (first page, pages).
fn chunks(total: usize) -> impl Iterator<Item = (usize, usize)> {
    let c = if chunked() { CHUNK } else { total.max(1) };
    (0..total).step_by(c).map(move |o| (o, c.min(total - o)))
}

/// Pages of the shared region: the pairs' blocks and Tx slots, and the Rx buffers unless path `map` has them apart.
fn shared_pages(pairs: usize, queues: usize) -> usize {
    let rx = if path() == Path::Map { 0 } else { queues * rx_bytes() };
    (pairs * pair_bytes() + rx).div_ceil(4096)
}

/// Path `map`: pages of the Rx region.
fn m_pages(queues: usize) -> usize {
    if path() == Path::Map { queues * rx_bytes() / 4096 } else { 0 }
}

fn shared(k: usize) -> &'static Shared {
    unsafe { &*((SHARED_VA + k * pair_bytes()) as *const Shared) }
}

fn slots(k: usize) -> DmaRegion {
    let va = SHARED_VA + k * pair_bytes() + SHARED_BYTES;
    DmaRegion { va: va as *mut u8, iova: va as u64, len: TX_SLOTS * slot_bytes() }
}

const MODES: [Mode; 4] = [Mode::Tx, Mode::Rx, Mode::Fwd, Mode::Maglev];

fn mac_of(word: u64) -> [u8; 6] {
    let b = word.to_le_bytes();
    [b[0], b[1], b[2], b[3], b[4], b[5]]
}

fn word_of(mac: [u8; 6]) -> u64 {
    let mut b = [0u8; 8];
    b[..6].copy_from_slice(&mac);
    u64::from_le_bytes(b)
}

/// From the build environment, fixed before anything runs.
struct Settings {
    frame_len: usize,
    dst: Option<[u8; 6]>,
    peer: Option<[u8; 6]>,
    peer_queues: usize,
    fwd_dst: Option<[u8; 6]>,
    steering: RxSteering,
    link_secs: u64,
    window_ms: u64,
}

impl Settings {
    fn new(queues: usize) -> Settings {
        let frame_len = frame_len();
        if !(64..=9000).contains(&frame_len) {
            log::error!("ice: VERIFLAT_ICE_FRAME must be 64..9000");
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
        Settings {
            frame_len,
            dst: env_mac("VERIFLAT_ICE_DST", option_env!("VERIFLAT_ICE_DST")),
            peer: env_mac("VERIFLAT_ICE_PEER", option_env!("VERIFLAT_ICE_PEER")),
            peer_queues: env_num("VERIFLAT_ICE_PEER_QUEUES", option_env!("VERIFLAT_ICE_PEER_QUEUES"), queues as u64) as usize,
            fwd_dst: env_mac("VERIFLAT_ICE_FWD_DST", option_env!("VERIFLAT_ICE_FWD_DST")),
            steering,
            link_secs: env_num("VERIFLAT_ICE_LINK_SECS", option_env!("VERIFLAT_ICE_LINK_SECS"), 15),
            window_ms: env_num("VERIFLAT_ICE_WINDOW_MS", option_env!("VERIFLAT_ICE_WINDOW_MS"), 1000).max(1),
        }
    }

    /// Mode tx's frame of pair k from a port whose MAC is `mac`: from the pair's steering MAC, to `VERIFLAT_ICE_DST`,
    /// the peer's queue k, or broadcast; on the model to the pair's own queue.
    fn frame(&self, k: usize, mac: [u8; 6]) -> UdpFrame {
        let dst = match (MOCK, self.dst, self.peer) {
            (true, _, _) => steering_mac(mac, k),
            (false, Some(d), _) => d,
            (false, None, Some(peer)) => steering_mac(peer, k % self.peer_queues.max(1)),
            (false, None, None) => [0xff; 6],
        };
        UdpFrame {
            dst_mac: dst,
            src_mac: if !MOCK && self.steering == RxSteering::PerQueueMac { steering_mac(mac, k) } else { mac },
            src_ip: [10, 10, 0, 1 + k as u8],
            dst_ip: [10, 10, 1, 1 + k as u8],
            src_port: 1024 + k as u16,
            dst_port: 5000 + k as u16,
            len: self.frame_len - 4,
        }
    }

    fn fwd_dst(&self, k: usize, mac: [u8; 6]) -> [u8; 6] {
        if MOCK { steering_mac(mac, k) } else { self.fwd_dst.unwrap_or([0xff; 6]) }
    }

    fn config(&self, queues: usize) -> Config {
        Config {
            queues, tx_ring: TX_RING, rx_ring: RX_RING, tx_batch: 32, rx_buf: rx_buf(), steering: self.steering,
            max_frame: if self.frame_len > 1518 { JUMBO_MAX_FRAME } else { 0 },
        }
    }
}

/// One application thread's phase control and result, on cache lines of its own.
#[repr(C, align(128))]
struct Pair {
    cpu: AtomicUsize,
    go: AtomicUsize,
    done: AtomicUsize,
    start: AtomicU64,
    end: AtomicU64,
    moved: AtomicU64,
    begin: AtomicU64,
    finish: AtomicU64,
    /// Path `map`, the last phase: runs and pages given by the application and by the driver of this pair.
    app_gives: AtomicU64,
    app_pages: AtomicU64,
    drv_gives: AtomicU64,
    drv_pages: AtomicU64,
    /// Path `map`, IPC shape: set by application thread k just before it waits for its second endpoint.
    wants_ep: AtomicBool,
}

impl Pair {
    const fn new() -> Pair {
        Pair {
            cpu: AtomicUsize::new(0), go: AtomicUsize::new(0), done: AtomicUsize::new(0), start: AtomicU64::new(0), end: AtomicU64::new(0),
            moved: AtomicU64::new(0), begin: AtomicU64::new(0), finish: AtomicU64::new(0), app_gives: AtomicU64::new(0), app_pages: AtomicU64::new(0),
            drv_gives: AtomicU64::new(0), drv_pages: AtomicU64::new(0), wants_ep: AtomicBool::new(false),
        }
    }
}

static PAIRS: [Pair; MAX_WORKERS] = [const { Pair::new() }; MAX_WORKERS];
static NEXT_PAIR: AtomicUsize = AtomicUsize::new(0);
/// dom0's side (ring and IPC shapes): application k (`App`), its flow cache, and the shared maglev lookup table.
static APPS: [AtomicUsize; MAX_PAIRS] = [const { AtomicUsize::new(0) }; MAX_PAIRS];
static CACHES: [AtomicUsize; MAX_PAIRS] = [const { AtomicUsize::new(0) }; MAX_PAIRS];
static LUT: AtomicUsize = AtomicUsize::new(0);
/// The phase dom0 releases the pairs into: mode, batch, pair count.
static PH_MODE: AtomicUsize = AtomicUsize::new(0);
static PH_BATCH: AtomicUsize = AtomicUsize::new(1);
static PH_PAIRS: AtomicUsize = AtomicUsize::new(1);
static PH_TOUCH: AtomicUsize = AtomicUsize::new(0);
static TSC_HZ: AtomicU64 = AtomicU64::new(0);

/// Path `map`: the couriers of dom0 (`MB_A`, receiving from the driver: pair k in the IPC shape, driver thread j in
/// the ring shape) and of the driver process (`MB_D`, receiving from application k), and per pair the runs the
/// application gave back (`Entry { va, iova: pages }`) for the driver to map into its IOMMU table.
static MB_A: [Mailbox; M_MAX_PAIRS] = [const { Mailbox::new() }; M_MAX_PAIRS];
static MB_D: [Mailbox; M_MAX_PAIRS] = [const { Mailbox::new() }; M_MAX_PAIRS];
static RET: [Spsc; M_MAX_PAIRS] = unsafe { core::mem::zeroed() };

/// The driver process's side: what dom0 tells it and what it publishes; the pointers point into its heap.
static DRV_PAIRS: AtomicUsize = AtomicUsize::new(0);
static DRV_QUEUES: AtomicUsize = AtomicUsize::new(0);
static DRV_BDF: AtomicUsize = AtomicUsize::new(0);
static DRV_BAR_PHYS: AtomicUsize = AtomicUsize::new(0);
static DRV_MAC: AtomicU64 = AtomicU64::new(0);
static DRV_READY: AtomicBool = AtomicBool::new(false);
static DRV_NEXT: AtomicUsize = AtomicUsize::new(0);
static DRV_STARTED: AtomicUsize = AtomicUsize::new(0);
/// One plus the CPU driver thread k serves (IPC: its first request) or polls on; 0 until then.
static DRV_CPU: [AtomicUsize; MAX_PAIRS] = [const { AtomicUsize::new(0) }; MAX_PAIRS];
static DRIVERS: [AtomicUsize; MAX_PAIRS] = [const { AtomicUsize::new(0) }; MAX_PAIRS];
/// A leaked `Vec<*mut RxQueue>` of every Rx queue.
static DRV_RXQ: AtomicUsize = AtomicUsize::new(0);
static DRV_PLATFORM: AtomicUsize = AtomicUsize::new(0);
static DRV_DEVICE: AtomicUsize = AtomicUsize::new(0);
static DRV_STOP: AtomicBool = AtomicBool::new(false);
static DRV_STOPPED: AtomicBool = AtomicBool::new(false);
static mut DRIVER_STACK: [u8; 128 * 1024] = [0; 128 * 1024];

type Drv = Driver<'static, XPlatform>;

fn driver(k: usize) -> &'static mut Drv {
    unsafe { &mut *(DRIVERS[k].load(Ordering::SeqCst) as *mut Drv) }
}

fn rx_queues() -> &'static [*mut RxQueue<'static, XPlatform>] {
    unsafe { &*(DRV_RXQ.load(Ordering::SeqCst) as *const Vec<*mut RxQueue<'static, XPlatform>>) }
}

fn app(k: usize) -> &'static mut App {
    unsafe { &mut *(APPS[k].load(Ordering::SeqCst) as *mut App) }
}

fn pps(frames: u64, cycles: u64) -> u64 {
    ice::bench::rate(frames, cycles, TSC_HZ.load(Ordering::SeqCst))
}

fn stack() -> usize {
    let stack = unsafe { alloc::alloc::alloc(Layout::from_size_align(STACK_BYTES, 4096).unwrap()) } as usize;
    if stack == 0 {
        log::error!("ice chan: no memory for a thread stack");
        unsafe { sys_debug_exit(1) };
    }
    stack + STACK_BYTES - 8
}

/// Path `map`, the application side of pair k: the descriptor of its endpoint to the driver's courier.
#[derive(Clone, Copy)]
struct MApp {
    k: usize,
    ep: usize,
}

impl MApp {
    /// Gives the pages of `ents` back to the driver, run by run, and records each run in the pair's return ring.
    fn give_back(&self, ents: &[Entry]) {
        let (mb, ret, pair) = (&MB_D[self.k], &RET[self.k], &PAIRS[self.k]);
        page_runs(ents, ppf(), |va, n| {
            courier::give(mb, self.ep, va as usize, va as usize, n, true);
            let e = [Entry { va, iova: n as u64, len: 0, _pad: 0 }];
            while ret.push(&e) == 0 {
                core::hint::spin_loop();
            }
            pair.app_gives.fetch_add(1, Ordering::Relaxed);
            pair.app_pages.fetch_add(n as u64, Ordering::Relaxed);
        });
    }
}

/// Path `map`, the driver side of pair k: its endpoint descriptor to the application's courier `mb`, and the pages it
/// gave out and got back in this phase.
struct MDrv {
    k: usize,
    mb: &'static Mailbox,
    ep: usize,
    out: u64,
    back: u64,
}

impl MDrv {
    /// Maps every run the application gave back into the IOMMU table again.
    fn drain(&mut self) {
        let iommu = map_iommu();
        let mut back = 0;
        RET[self.k].pop(RING, |e| {
            if iommu {
                quiet("ice map iommu_map_4k (returned run)", unsafe { sys_iommu_map_4k(e.va as usize, e.va as usize, e.iova as usize) });
            }
            back += e.iova;
        });
        self.back += back;
    }

    /// Waits until the application gave back every page it got (it does before and while it ends a phase).
    fn reclaim_all(&mut self) {
        let start = rdtsc();
        loop {
            self.drain();
            if self.back == self.out {
                return;
            }
            if rdtsc() - start > 10 * TSC_HZ.load(Ordering::SeqCst) {
                log::error!("ice map: pair {} holds {} pages the application never gave back", self.k, self.out - self.back);
                unsafe { sys_debug_exit(1) };
            }
            core::hint::spin_loop();
        }
    }

    /// One `control` + `step` of path `map`: the hooks map returned runs; the frames handed over go to the application
    /// run by run before they are pushed. Returns the frames handed over.
    fn round(&mut self, d: &mut Drv, sh: &Shared, queues: &[*mut RxQueue<'static, XPlatform>]) -> usize {
        if d.control_with(sh, queues, || self.reclaim_all()) {
            (self.out, self.back) = (0, 0);
        }
        let (_, handed) = d.step_with(sh, || self.drain());
        if !d.pending().is_empty() {
            let (iommu, pair) = (map_iommu(), &PAIRS[self.k]);
            page_runs(d.pending(), ppf(), |va, n| {
                courier::give(self.mb, self.ep, va as usize, va as usize, n, true);
                if iommu {
                    quiet("ice map iommu_unmap_4k (given run)", unsafe { sys_iommu_unmap_4k(va as usize, n) });
                }
                self.out += n as u64;
                pair.drv_gives.fetch_add(1, Ordering::Relaxed);
                pair.drv_pages.fetch_add(n as u64, Ordering::Relaxed);
            });
            d.commit(sh);
        }
        handed
    }
}

/// Waits until the driver of application `a` (pair k) applied command `seq`: in the IPC shape one call carries it, in
/// the linked shape `kick` runs the driver; with path `map` in the ring shape the application gives back what the
/// driver hands until then.
fn hand_over(k: usize, a: &mut App, kick: &mut Option<&mut dyn FnMut()>, seq: u64, m: Option<MApp>) {
    if let Some(kick) = kick {
        kick();
    }
    let limit = rdtsc() + 5 * TSC_HZ.load(Ordering::SeqCst);
    while !a.acked(seq) {
        if rdtsc() > limit {
            log::error!("ice chan: the driver of pair {} did not apply command {}", k, seq);
            unsafe { sys_debug_exit(1) };
        }
        if let Some(m) = m {
            a.drain_rx(|ents| m.give_back(ents));
        }
        core::hint::spin_loop();
    }
}

/// After an application step: `kick` (one IPC call to the driver, or the driver's own step), then the Rx hold-off
/// after a step that brought fewer frames than asked for (`ice::chan::holdoff`); the ring shape has neither.
#[inline(always)]
fn after_step(kick: &mut Option<&mut dyn FnMut()>, a: &App, mode: Mode, batch: usize) {
    if let Some(kick) = kick.as_mut() {
        kick();
        if mode.polls() && a.shared().rx.len() < batch.min(MAX_BATCH) {
            let until = rdtsc() + RX_HOLDOFF_CYCLES;
            while rdtsc() < until {
                core::hint::spin_loop();
            }
        }
    }
}

/// Steps until `start` (warm-up), then counts what the steps moved until `end`; returns (moved, first TSC, last TSC).
#[inline(always)]
fn timed(a: &mut App, start: u64, end: u64, mut step: impl FnMut(&mut App) -> u64) -> (u64, u64, u64) {
    while rdtsc() < start {
        step(a);
    }
    let mut moved = 0u64;
    let begin = rdtsc();
    let mut now = begin;
    while now < end {
        moved += step(a);
        now = rdtsc();
    }
    (moved, begin, now)
}

/// Runs phase `phase` of application k on CPU `cpu`, with the maglev lookup table `lut` and flow cache `cache` (mode
/// maglev); `kick`, after each step, is one IPC call to the driver (IPC shape) or the driver's own step (linked shape),
/// and is followed by the Rx hold-off; the ring shape has none. `m`: path `map`.
fn run_phase(k: usize, cpu: usize, phase: usize, a: &mut App, lut: usize, cache: usize, mut kick: Option<&mut dyn FnMut()>, m: Option<MApp>) {
    let mode = MODES[PH_MODE.load(Ordering::SeqCst)];
    let (batch, c) = (PH_BATCH.load(Ordering::SeqCst), PH_PAIRS.load(Ordering::SeqCst));
    let mut mg = (mode == Mode::Maglev).then(|| {
        let lut = unsafe { core::slice::from_raw_parts(lut as *const i8, TABLE_SIZE) };
        Maglev::new(lut, unsafe { core::slice::from_raw_parts_mut(cache as *mut [u64; 2], CACHE_ENTRIES) })
    });
    let pair = &PAIRS[k];
    for x in [&pair.app_gives, &pair.app_pages, &pair.drv_gives, &pair.drv_pages] {
        x.store(0, Ordering::SeqCst);
    }
    a.set_touch(touch_of(PH_TOUCH.load(Ordering::SeqCst)));
    let seq = a.begin(mode, batch, c);
    hand_over(k, a, &mut kick, seq, m);
    let (start, end) = (pair.start.load(Ordering::SeqCst), pair.end.load(Ordering::SeqCst));
    // The step loop is picked once per phase, so that a phase without path `map` runs the loop it ran before the map
    // path existed.
    let (moved, begin, now) = match m {
        None => timed(a, start, end, |a: &mut App| {
            let n = a.step(mg.as_mut());
            after_step(&mut kick, a, mode, batch);
            n as u64
        }),
        Some(m) => timed(a, start, end, |a: &mut App| {
            let n = a.step(mg.as_mut());
            if !a.pending().is_empty() {
                m.give_back(a.pending());
            }
            a.commit();
            after_step(&mut kick, a, mode, batch);
            n as u64
        }),
    };
    if let Some(m) = m {
        a.drain_rx(|ents| m.give_back(ents));
    }
    let seq = a.end();
    hand_over(k, a, &mut kick, seq, m);
    if let Some(m) = m {
        a.drain_rx(|ents| m.give_back(ents));
    }
    a.after_end();
    if current_cpu() != cpu {
        log::error!("ice chan pair {} moved to CPU {}", k, current_cpu());
        unsafe { sys_debug_exit(1) };
    }
    pair.moved.store(moved, Ordering::SeqCst);
    pair.begin.store(begin, Ordering::SeqCst);
    pair.finish.store(now, Ordering::SeqCst);
    pair.done.store(phase, Ordering::SeqCst);
}

/// Phase `phase` of dom0's application k (ring and IPC shapes), whose descriptor `ep` holds its pair endpoint (IPC)
/// and `m_ep` its endpoint to the driver's courier (path `map`).
fn run_app_phase(k: usize, ep: usize, m_ep: usize, phase: usize) {
    let mut call = || quiet("ice chan call", unsafe { sys_call(ep) });
    let kick: Option<&mut dyn FnMut()> = if shape() == Shape::Ipc { Some(&mut call) } else { None };
    let m = (path() == Path::Map).then_some(MApp { k, ep: m_ep });
    run_phase(k, k, phase, app(k), LUT.load(Ordering::SeqCst), CACHES[k].load(Ordering::SeqCst), kick, m);
}

/// Application thread k > 0, holding pair endpoint k (IPC shape) or, with path `map` in the ring shape, its endpoint
/// to the driver's courier in descriptor 0; with path `map` in the IPC shape it first receives the latter into
/// descriptor 1, while it still runs on CPU 0.
extern "C" fn app_thread() -> ! {
    let k = NEXT_PAIR.load(Ordering::SeqCst);
    let pair = &PAIRS[k];
    let map = path() == Path::Map;
    if map && shape() == Shape::Ipc {
        pair.wants_ep.store(true, Ordering::SeqCst);
        quiet("ice map receive_endpoint (application)", unsafe { sys_receive_endpoint(0, 1) });
    }
    pair.cpu.store(current_cpu() + 1, Ordering::SeqCst);
    let m_ep = if shape() == Shape::Ipc { 1 } else { 0 };
    let mut last = 0;
    loop {
        let phase = pair.go.load(Ordering::SeqCst);
        if phase == last {
            core::hint::spin_loop();
            continue;
        }
        last = phase;
        run_app_phase(k, 0, m_ep, phase);
    }
}

/// Runs pairs 0..c in one phase and logs it.
fn time_phase(phase: usize, mode: usize, touch: Touch, batch: usize, c: usize, window: u64) {
    PH_MODE.store(mode, Ordering::SeqCst);
    PH_TOUCH.store(touch_code(touch), Ordering::SeqCst);
    PH_BATCH.store(batch, Ordering::SeqCst);
    PH_PAIRS.store(c, Ordering::SeqCst);
    let start = rdtsc() + (window / 4).max(TSC_HZ.load(Ordering::SeqCst) / 1000);
    for pair in &PAIRS[..c] {
        pair.start.store(start, Ordering::SeqCst);
        pair.end.store(start + window, Ordering::SeqCst);
    }
    let first = if shape() == Shape::Linked { 0 } else { 1 };
    for pair in &PAIRS[first..c] {
        pair.go.store(phase, Ordering::SeqCst);
    }
    if first == 1 {
        run_app_phase(0, PAIR_EP, E_D0, phase);
    }
    for pair in &PAIRS[first..c] {
        wait_for("the ice chan pairs", || pair.done.load(Ordering::SeqCst) == phase);
    }
    let (mut total, mut min, mut max) = (0u64, u64::MAX, 0u64);
    let (mut max_begin, mut min_finish, mut min_begin, mut max_finish) = (0, u64::MAX, u64::MAX, 0);
    let mut list = alloc::string::String::new();
    for (k, pair) in PAIRS[..c].iter().enumerate() {
        let (begin, finish) = (pair.begin.load(Ordering::SeqCst), pair.finish.load(Ordering::SeqCst));
        (max_begin, min_finish, min_begin, max_finish) = (max_begin.max(begin), min_finish.min(finish), min_begin.min(begin), max_finish.max(finish));
        let r = pps(pair.moved.load(Ordering::SeqCst), finish - begin);
        (total, min, max) = (total + r, min.min(r), max.max(r));
        if k > 0 {
            list.push(',');
        }
        let _ = core::fmt::write(&mut list, format_args!("{}", r));
    }
    let overlap = if max_begin < min_finish { (100 * (min_finish - max_begin)) / (max_finish - min_begin).max(1) } else { 0 };
    log::info!(
        "{} mode={} batch={} n={} total={} min={} max={} overlap=0.{:02} pairs={} path={} touch={} frame={}",
        shape_name(), MODES[mode].name(), batch, c, total, min, max, overlap.min(99), list, path().name(), touch.name(), frame_len()
    );
    if path() == Path::Map {
        let sum = |f: fn(&Pair) -> &AtomicU64| PAIRS[..c].iter().map(|p| f(p).load(Ordering::SeqCst)).sum::<u64>();
        let moved: u64 = PAIRS[..c].iter().map(|p| p.moved.load(Ordering::SeqCst)).sum();
        log::info!(
            "ice_map_counts {} mode={} batch={} n={} touch={} frames_timed={} app_gives={} app_pages={} drv_gives={} drv_pages={} iommu={}",
            shape_name(), MODES[mode].name(), batch, c, touch.name(), moved, sum(|p| &p.app_gives), sum(|p| &p.app_pages), sum(|p| &p.drv_gives), sum(|p| &p.drv_pages),
            map_iommu() as u8
        );
    }
}

/// The benchmark (feature `ice-chan`): skipped without an E810 function unless it runs on the device model.
pub fn run() {
    crate::slab_alloc::init();
    let f = if MOCK {
        None
    } else {
        let Some(f) = pick(&find_e810()) else {
            log::info!("ice chan bench skipped: no E810 function recorded");
            return;
        };
        Some(f)
    };
    let Some((hz, source)) = tsc_rate() else {
        log::error!("ice chan bench: no CPUID source gives the TSC rate; build dom0 with VERIFLAT_TSC_MHZ set to it");
        unsafe { sys_debug_exit(1) };
    };
    TSC_HZ.store(hz, Ordering::SeqCst);
    let n = count_cpus();
    let queues = n;
    let map = path() == Path::Map;
    if map && shape() == Shape::Linked {
        log::error!("ice chan: path map needs two processes: shape ring or ipc");
        unsafe { sys_debug_exit(1) };
    }
    let pairs = match shape() {
        Shape::Linked => n - 1,
        Shape::Ring => n / 2,
        Shape::Ipc => n,
    }
    .min(MAX_PAIRS)
    .min(if map { M_MAX_PAIRS } else { MAX_PAIRS });
    if pairs == 0 {
        log::error!("ice chan: the linked and ring shapes need at least 2 CPUs");
        unsafe { sys_debug_exit(1) };
    }
    let s = Settings::new(queues);
    let modes: Vec<usize> = option_env!("VERIFLAT_ICE_MODE")
        .unwrap_or("tx,rx,fwd,maglev")
        .split(',')
        .map(|m| match Mode::parse(m.trim()).and_then(|m| MODES.iter().position(|&x| x == m)) {
            Some(i) => i,
            None => {
                log::error!("ice chan: mode {} is not tx, rx, fwd or maglev", m);
                unsafe { sys_debug_exit(1) }
            }
        })
        .collect();
    let batches: Vec<usize> = match option_env!("VERIFLAT_ICE_BATCH") {
        Some(v) => env_list("VERIFLAT_ICE_BATCH", Some(v), 1).into_iter().map(|b| (b as usize).clamp(1, MAX_BATCH)).collect(),
        None => alloc::vec![1, 32],
    };
    let counts: Vec<usize> = match option_env!("VERIFLAT_ICE_QUEUES") {
        Some(v) => env_list("VERIFLAT_ICE_QUEUES", Some(v), 1).into_iter().map(|c| c as usize).filter(|&c| 0 < c && c <= pairs).collect(),
        None => {
            let mut v: Vec<usize> = core::iter::successors(Some(1usize), |c| Some(c * 2)).take_while(|&c| c < pairs).collect();
            v.push(pairs);
            v
        }
    };
    if (modes.contains(&2) || modes.contains(&3)) && !MOCK && s.fwd_dst.is_none() {
        log::error!("ice chan: modes fwd and maglev need VERIFLAT_ICE_FWD_DST, the MAC forwarded frames go to");
        unsafe { sys_debug_exit(1) };
    }
    let window = s.window_ms * hz / 1000;
    match f {
        Some(f) => log::info!(
            "ice chan: {} shape, E810 {:02x}:{:02x}.{} device {:04x}, BAR0 {:#x}, {} CPUs, {} queue pairs, {} pairs, {}-byte frames, {} ms windows, TSC {} MHz from {}",
            shape_name(), f.bus, f.dev, f.fun, f.device, f.bar_phys, n, queues, pairs, s.frame_len, s.window_ms, hz / 1_000_000, source
        ),
        None => log::info!(
            "ice chan: {} shape on the software device model (numbers of the model, not a NIC), {} CPUs, {} queue pairs, {} pairs, {}-byte frames, {} ms windows, TSC {} MHz from {}",
            shape_name(), n, queues, pairs, s.frame_len, s.window_ms, hz / 1_000_000, source
        ),
    }
    log::info!(
        "ice chan: path {}, touch {:?}, Tx slot {} bytes, Rx buffer {} bytes{}",
        path().name(), touches().iter().map(|t| t.name()).collect::<Vec<_>>(), slot_bytes(), rx_buf(),
        if map { if map_iommu() { ", map: pages leave and re-enter the IOMMU table" } else { ", map: pages stay in the IOMMU table (not isolating)" } } else { "" }
    );
    if map && modes.contains(&0) {
        log::info!("ice chan: path map runs mode tx zero copy (the Tx slots are shared)");
    }

    // Endpoints and application threads 1..pairs on CPUs 1..pairs; dom0's first thread is application thread 0 (ring
    // and IPC shapes; the linked shape's applications are the driver process's threads).
    let ipc = shape() == Shape::Ipc;
    let linked = shape() == Shape::Linked;
    let eps = if ipc { pairs } else { 1 };
    let m_eps = if map { pairs * if ipc { 1 } else { 2 } } else { 0 };
    fund("ice chan endpoint and thread funding", eps + m_eps + 2 * pairs);
    for k in 0..eps {
        quiet("ice chan new_endpoint", unsafe { sys_new_endpoint(PAIR_EP + k) });
    }
    if map {
        for k in 0..pairs {
            quiet("ice map new_endpoint (application to driver)", unsafe { sys_new_endpoint(E_D0 + k) });
            if !ipc {
                quiet("ice map new_endpoint (driver to application)", unsafe { sys_new_endpoint(E_A0 + k) });
            }
        }
    }
    PAIRS[0].cpu.store(1, Ordering::SeqCst);
    for k in (1..pairs).filter(|_| !linked) {
        // A new thread queues on CPU 0's shard, which holds no other thread, so CPU k pulls it when it comes online.
        NEXT_PAIR.store(k, Ordering::SeqCst);
        if ipc {
            quiet("ice chan new_thread_with_endpoint (application)", unsafe { sys_new_thread_with_endpoint(PAIR_EP + k, entry(app_thread), stack()) });
            if map {
                // While the thread still runs on CPU 0: its endpoint to the driver's courier, over the pair endpoint
                // nobody else uses yet; the rendezvous queues it on this CPU again, for CPU k to pull.
                wait_yield("an ice map application thread to wait for its endpoint", || PAIRS[k].wants_ep.load(Ordering::SeqCst));
                quiet("ice map send_endpoint (application)", unsafe { sys_send_endpoint(PAIR_EP + k, E_D0 + k) });
            }
        } else if map {
            quiet("ice map new_thread_with_endpoint (application)", unsafe { sys_new_thread_with_endpoint(E_D0 + k, entry(app_thread), stack()) });
        } else {
            quiet("ice chan new_thread (application)", unsafe { sys_new_thread(entry(app_thread), stack()) });
        }
        quiet("ice chan cpu_online", unsafe { sys_cpu_online(k) });
        wait_for("an ice chan application thread to start", || PAIRS[k].cpu.load(Ordering::SeqCst) != 0);
        if PAIRS[k].cpu.load(Ordering::SeqCst) - 1 != k {
            log::error!("ice chan: application thread {} runs on CPU {}", k, PAIRS[k].cpu.load(Ordering::SeqCst) - 1);
            unsafe { sys_debug_exit(1) };
        }
    }

    // Mode maglev's lookup table and flow caches.
    if modes.contains(&3) && !linked {
        let lut = Box::leak(alloc::vec![0i8; TABLE_SIZE].into_boxed_slice());
        populate_lut(lut);
        LUT.store(lut.as_ptr() as usize, Ordering::SeqCst);
        for cache in &CACHES[..pairs] {
            cache.store(Box::leak(alloc::vec![[0u64; 2]; CACHE_ENTRIES].into_boxed_slice()).as_mut_ptr() as usize, Ordering::SeqCst);
        }
    }

    // The shared region, path map's Rx region, and the driver process.
    let pages = shared_pages(pairs, queues);
    let mpages = m_pages(queues);
    // Chunked: the pages, their page tables, and what one chunk's map wants at hand.
    let funding = if chunked() { pages + mpages + 4 * CHUNK + (pages + mpages) / 512 + 16 } else { 4 * pages };
    fund("ice chan shared region funding", funding);
    for (o, c) in chunks(pages) {
        quiet("ice chan mmap_4k (shared region)", unsafe { sys_mmap_4k(SHARED_VA + o * 4096, c) });
    }
    for (o, c) in chunks(mpages) {
        quiet("ice map mmap_4k (Rx region)", unsafe { sys_mmap_4k(M_VA + o * 4096, c) });
    }
    DRV_PAIRS.store(pairs, Ordering::SeqCst);
    DRV_QUEUES.store(queues, Ordering::SeqCst);
    if let Some(f) = f {
        DRV_BDF.store(f.bus << 8 | f.dev << 3 | f.fun, Ordering::SeqCst);
        DRV_BAR_PHYS.store(f.bar_phys, Ordering::SeqCst);
    }
    let (image, image_pages) = crate::image_range();
    fund("ice chan driver process funding", 6 + 3 * image_pages);
    let sp = stack_top(&raw const DRIVER_STACK);
    check("ice chan new_process_with_iommu_and_endpoint (driver)", unsafe {
        sys_new_process_with_iommu_and_endpoint(image, image_pages, PAIR_EP, entry(driver_main), sp)
    });
    if let Some(f) = f {
        send_function(&f);
    }
    for (o, c) in chunks(pages) {
        quiet("ice chan send_pages (shared region)", unsafe { sys_send_pages(PAIR_EP, SHARED_VA + o * 4096, c) });
    }
    for (o, c) in chunks(mpages) {
        quiet("ice map send_pages (Rx region)", unsafe { sys_send_pages(PAIR_EP, M_VA + o * 4096, c) });
    }
    if map {
        // The Rx pages are the driver's alone from now on.
        check("ice map unmap_4k (Rx region)", unsafe { sys_unmap_4k(M_VA, mpages) });
    }
    for k in 1..eps {
        quiet("ice chan send_endpoint", unsafe { sys_send_endpoint(PAIR_EP, PAIR_EP + k) });
    }
    if map {
        for k in 0..pairs {
            quiet("ice map send_endpoint (application to driver)", unsafe { sys_send_endpoint(PAIR_EP, E_D0 + k) });
            if !ipc {
                quiet("ice map send_endpoint (driver to application)", unsafe { sys_send_endpoint(PAIR_EP, E_A0 + k) });
            }
        }
    }
    wait_yield("the ice chan driver process to bring the device up", || DRV_READY.load(Ordering::SeqCst));
    for _ in 0..4 {
        unsafe { sys_schedule() };
    }
    if map {
        // dom0's couriers, parked on CPU 0: in the IPC shape on pair k's endpoint behind the driver thread that blocks
        // in receive_call there (so the first call meets the driver), in the ring shape on endpoint E_A0 + j.
        for j in 0..pairs {
            courier::start(&MB_A[j], if ipc { PAIR_EP + j } else { E_A0 + j }, M_FUNDING);
        }
    }
    if !ipc {
        // Every driver thread yields on CPU 0 until it runs on a CPU of its own: CPU first + j pulls the head of
        // CPU 0's shard, a driver thread (this thread runs), which takes pair j.
        let first = if linked { 1 } else { pairs };
        for j in 0..pairs {
            quiet("ice chan cpu_online (driver)", unsafe { sys_cpu_online(first + j) });
            wait_for("an ice chan driver thread on its CPU", || DRV_CPU[j].load(Ordering::SeqCst) != 0);
        }
    }
    let mac = mac_of(DRV_MAC.load(Ordering::SeqCst));
    log::info!("{}: driver process up with {} queue pairs, MAC {}, {} shared pages, {} Rx region pages", shape_name(), queues, Mac(mac), pages, mpages);
    for k in (0..pairs).filter(|_| !linked) {
        let a = App::new_with(shared(k), slots(k), TX_SLOTS, slot_bytes(), &s.frame(k, mac), mac, s.fwd_dst(k, mac), path(), Touch::Off);
        APPS[k].store(Box::into_raw(Box::new(a)) as usize, Ordering::SeqCst);
    }

    let mut phase = 0;
    for &mode in &modes {
        for &touch in &touches() {
            for &batch in &batches {
                for &c in &counts {
                    phase += 1;
                    time_phase(phase, mode, touch, batch, c, window);
                }
            }
        }
    }
    // The driver threads of pairs that ran (an IPC driver thread records its CPU at its first call).
    for k in 0..counts.iter().copied().max().unwrap_or(0) {
        let cpu = DRV_CPU[k].load(Ordering::SeqCst);
        let want = match shape() {
            Shape::Linked => k + 2,
            Shape::Ring => pairs + k + 1,
            Shape::Ipc => k + 1,
        };
        if cpu != want {
            log::error!("{}: driver thread {} ran on CPU {}, expected {}", shape_name(), k, cpu as isize - 1, want - 1);
            unsafe { sys_debug_exit(1) };
        }
    }
    DRV_STOP.store(true, Ordering::SeqCst);
    if ipc {
        quiet("ice chan call (stop)", unsafe { sys_call(PAIR_EP) });
    }
    wait_for("the ice chan driver to reset the PF", || DRV_STOPPED.load(Ordering::SeqCst));
    if ipc {
        check("ice chan kill_process(0) (driver)", unsafe { sys_kill_process(0) });
        if let Some(f) = f {
            crate::bar::claim("ice chan pci_claim after the driver's kill", f.bus, f.dev, f.fun);
        }
    }
    log::info!("ice chan bench passed");
}

fn send_function(f: &IceFunction) {
    crate::bar::claim("ice chan pci_claim", f.bus, f.dev, f.fun);
    check("ice chan send_pci", unsafe { sys_send_pci(PAIR_EP, f.bus, f.dev, f.fun) });
}

/// First thread of the driver process (pair endpoint 0 in descriptor 0): takes what dom0 sends, brings the device up
/// with one queue pair per CPU and one `Driver` per pair, starts the other driver threads (and with path `map` its
/// couriers) and serves pair 0 (IPC) or becomes one of the polling driver threads (ring).
extern "C" fn driver_main() -> ! {
    let (pairs, queues) = (DRV_PAIRS.load(Ordering::SeqCst), DRV_QUEUES.load(Ordering::SeqCst));
    let pages = shared_pages(pairs, queues);
    let mpages = m_pages(queues);
    let map = path() == Path::Map;
    let bar = crate::bar::bar_va(DRV_BAR_PHYS.load(Ordering::SeqCst));
    let bdf = DRV_BDF.load(Ordering::SeqCst);
    let (bus, dev, fun) = (bdf >> 8, (bdf >> 3) & 0x1f, bdf & 7);
    let ipc = shape() == Shape::Ipc;
    // Chunked: what one chunk's receive and IOMMU map want at hand, and the page tables they add.
    fund("ice chan driver receive funding", if chunked() { 3 * CHUNK + 2 * ((pages + mpages) / 512 + 16) } else { 3 * pages });
    if !MOCK {
        quiet("ice chan driver receive_pci", unsafe { sys_receive_pci(0, bus, dev, fun) });
        crate::bar::map_bar0("ice chan driver map BAR0", bus, dev, fun);
    }
    for (o, c) in chunks(pages) {
        quiet("ice chan driver receive_pages (shared region)", unsafe { sys_receive_pages(0, SHARED_VA + o * 4096, c) });
    }
    for (o, c) in chunks(mpages) {
        quiet("ice map driver receive_pages (Rx region)", unsafe { sys_receive_pages(0, M_VA + o * 4096, c) });
    }
    if ipc {
        for k in 1..pairs {
            quiet("ice chan driver receive_endpoint", unsafe { sys_receive_endpoint(0, k) });
        }
    }
    if map {
        for k in 0..pairs {
            quiet("ice map driver receive_endpoint (application to driver)", unsafe { sys_receive_endpoint(0, E_D0 + k) });
            if !ipc {
                quiet("ice map driver receive_endpoint (driver to application)", unsafe { sys_receive_endpoint(0, E_A0 + k) });
            }
        }
    }
    crate::slab_alloc::init();
    fund("ice chan driver IOMMU funding", if chunked() { 3 * CHUNK + (pages + mpages) / 512 + 16 } else { 3 * pages });
    for (o, c) in chunks(pages) {
        quiet("ice chan driver iommu_map_4k (shared region)", unsafe { sys_iommu_map_4k(SHARED_VA + o * 4096, SHARED_VA + o * 4096, c) });
    }
    for (o, c) in chunks(mpages) {
        quiet("ice map driver iommu_map_4k (Rx region)", unsafe { sys_iommu_map_4k(M_VA + o * 4096, M_VA + o * 4096, c) });
    }
    if !MOCK {
        quiet("ice chan driver pci_attach_dma", unsafe { sys_pci_attach_dma(bus, dev, fun) });
    }
    let hz = TSC_HZ.load(Ordering::SeqCst);
    let s = Settings::new(queues);
    let p = XPlatform::new(bar, hz);
    DRV_PLATFORM.store(p as *const XPlatform as usize, Ordering::SeqCst);
    if map {
        p.packets_in(M_VA, queues * rx_bytes());
    } else {
        p.packets_in(SHARED_VA + pairs * pair_bytes(), queues * rx_bytes());
    }
    let mut device = Device::new(p, s.config(queues)).unwrap_or_else(|e| fail("bring-up (driver process)", e));
    let link = device.bring_link_up(s.link_secs * 1000).unwrap_or_else(|e| fail("link", e));
    if link.up {
        log::info!("ice: link up at {} Mb/s, max frame {}", link.speed_mbps, link.max_frame);
    } else {
        log::warn!("ice: link still down after {} s: frames will not reach the wire", s.link_secs);
    }
    if (link.max_frame as usize) < s.frame_len {
        log::warn!("ice: the port's max frame {} is below the {}-byte frames", link.max_frame, s.frame_len);
    }
    let mac = device.info.mac;
    let mut rxq: Vec<*mut RxQueue<'static, XPlatform>> = Vec::with_capacity(queues);
    for (q, (tx, rx)) in device.take_queues().into_iter().enumerate() {
        if q < pairs {
            DRIVERS[q].store(Box::into_raw(Box::new(Driver::new(tx, q))) as usize, Ordering::SeqCst);
        }
        rxq.push(Box::into_raw(Box::new(rx)));
    }
    DRV_RXQ.store(Box::into_raw(Box::new(rxq)) as usize, Ordering::SeqCst);
    DRV_DEVICE.store(Box::into_raw(Box::new(Some(device))) as usize, Ordering::SeqCst);
    DRV_MAC.store(word_of(mac), Ordering::SeqCst);
    if map {
        // The driver's couriers, parked on CPU 0 on endpoint E_D0 + k until application k first gives.
        for k in 0..pairs {
            courier::start(&MB_D[k], E_D0 + k, M_FUNDING);
        }
        fund("ice map driver thread funding", M_FUNDING);
    }
    fund("ice chan driver thread funding", 2 * pairs);
    for k in 1..pairs {
        DRV_NEXT.store(k, Ordering::SeqCst);
        if ipc {
            quiet("ice chan driver new_thread_with_endpoint", unsafe { sys_new_thread_with_endpoint(k, entry(driver_ipc_thread), stack()) });
        } else if map {
            quiet("ice map driver new_thread_with_endpoint", unsafe { sys_new_thread_with_endpoint(E_A0 + k, entry(driver_poll_thread), stack()) });
        } else {
            quiet("ice chan driver new_thread", unsafe { sys_new_thread(entry(driver_poll_thread), stack()) });
        }
        wait_yield("an ice chan driver thread to start", || DRV_STARTED.load(Ordering::SeqCst) == k);
    }
    DRV_READY.store(true, Ordering::SeqCst);
    match shape() {
        Shape::Linked => run_linked(),
        Shape::Ring => poll_ring(0, E_A0),
        Shape::Ipc => serve_ipc(0),
    }
}

extern "C" fn driver_ipc_thread() -> ! {
    let k = DRV_NEXT.load(Ordering::SeqCst);
    if path() == Path::Map {
        fund("ice map driver thread funding", M_FUNDING);
    }
    DRV_STARTED.fetch_add(1, Ordering::SeqCst);
    serve_ipc(k)
}

extern "C" fn driver_poll_thread() -> ! {
    let j = DRV_NEXT.load(Ordering::SeqCst);
    if path() == Path::Map {
        fund("ice map driver thread funding", M_FUNDING);
    }
    DRV_STARTED.fetch_add(1, Ordering::SeqCst);
    if shape() == Shape::Linked { run_linked() } else { poll_ring(j, 0) }
}

fn reset_pf() {
    let device = unsafe { &mut *(DRV_DEVICE.load(Ordering::SeqCst) as *mut Option<Device<'static, XPlatform>>) };
    if let Some(device) = device.take() {
        if let Err(e) = device.shutdown() {
            log::warn!("ice: PF reset after {}: {}", shape_name(), e);
        }
    }
    DRV_STOPPED.store(true, Ordering::SeqCst);
}

/// IPC shape, driver thread k (pair endpoint k in descriptor 0): one `control` + `step` per call (with path `map`
/// `MDrv::round`, giving over the pair endpoint); driver thread 0 resets the PF when dom0 calls it after setting
/// `DRV_STOP`.
fn serve_ipc(k: usize) -> ! {
    let d = driver(k);
    let (sh, queues) = (shared(k), rx_queues());
    let mut m = (path() == Path::Map).then(|| MDrv { k, mb: &MB_A[k], ep: 0, out: 0, back: 0 });
    quiet("ice chan driver receive_call", unsafe { sys_receive_call(0) });
    DRV_CPU[k].store(current_cpu() + 1, Ordering::SeqCst);
    if let Some(m) = m.as_ref() {
        // dom0's courier of this pair is parked on the pair endpoint, where reply_and_receive would queue this thread
        // behind it: wake it now, onto this CPU, while the queue holds only the courier.
        courier::wake(m.mb, 0);
    }
    // The loop is picked once, so that a run without path `map` serves the calls as before the map path existed.
    match m.as_mut() {
        Some(m) => loop {
            if k == 0 && DRV_STOP.load(Ordering::SeqCst) {
                reset_pf();
            } else {
                m.round(d, sh, queues);
            }
            quiet("ice chan driver reply_and_receive", unsafe { sys_reply_and_receive(0) });
        },
        None => loop {
            if k == 0 && DRV_STOP.load(Ordering::SeqCst) {
                reset_pf();
            } else {
                d.control(sh, queues);
                d.step(sh);
            }
            quiet("ice chan driver reply_and_receive", unsafe { sys_reply_and_receive(0) });
        },
    }
}

/// Ring shape, driver thread j (with path `map` holding endpoint E_A0 + j in descriptor `ep`): yields until it runs
/// on a CPU of the driver half (dom0 brings them online one by one), takes the pair of that CPU and polls it; the
/// pair-0 thread resets the PF once dom0 sets `DRV_STOP`.
fn poll_ring(j: usize, ep: usize) -> ! {
    let pairs = DRV_PAIRS.load(Ordering::SeqCst);
    while current_cpu() < pairs {
        unsafe { sys_schedule() };
    }
    let k = current_cpu() - pairs;
    DRV_CPU[k].store(current_cpu() + 1, Ordering::SeqCst);
    let p = unsafe { &*(DRV_PLATFORM.load(Ordering::SeqCst) as *const XPlatform) };
    let (d, sh, queues) = (driver(k), shared(k), rx_queues());
    let mut m = (path() == Path::Map).then(|| MDrv { k, mb: &MB_A[j], ep, out: 0, back: 0 });
    // The loop is picked once, so that a run without path `map` polls as before the map path existed.
    match m.as_mut() {
        Some(m) => {
            while !DRV_STOP.load(Ordering::SeqCst) {
                let handed = m.round(d, sh, queues);
                if d.should_hold_off(handed) {
                    ice::chan::holdoff(p);
                }
            }
        }
        None => {
            while !DRV_STOP.load(Ordering::SeqCst) {
                d.run_once(p, sh, queues);
            }
        }
    }
    if k == 0 {
        // Every driver is idle by now (dom0 ended every phase), so none touches the device any more.
        reset_pf();
    }
    loop {
        core::hint::spin_loop();
    }
}

/// Linked shape, a thread of the driver process: yields until it runs on a CPU other than 0 (dom0 brings them online
/// one by one), takes pair k of CPU k + 1, and runs both sides of it in each phase dom0 releases; the pair-0 thread
/// resets the PF once dom0 sets `DRV_STOP`.
fn run_linked() -> ! {
    while current_cpu() == 0 {
        unsafe { sys_schedule() };
    }
    let (cpu, queues) = (current_cpu(), DRV_QUEUES.load(Ordering::SeqCst));
    let k = cpu - 1;
    let (d, sh, rxq) = (driver(k), shared(k), rx_queues());
    let s = Settings::new(queues);
    let mac = mac_of(DRV_MAC.load(Ordering::SeqCst));
    let mut a = App::new_with(sh, slots(k), TX_SLOTS, slot_bytes(), &s.frame(k, mac), mac, s.fwd_dst(k, mac), path(), Touch::Off);
    let lut = Box::leak(alloc::vec![0i8; TABLE_SIZE].into_boxed_slice());
    populate_lut(lut);
    let cache = Box::leak(alloc::vec![[0u64; 2]; CACHE_ENTRIES].into_boxed_slice());
    let (lut, cache) = (lut.as_ptr() as usize, cache.as_mut_ptr() as usize);
    DRV_CPU[k].store(cpu + 1, Ordering::SeqCst);
    let pair = &PAIRS[k];
    let mut last = 0;
    loop {
        let phase = pair.go.load(Ordering::SeqCst);
        if phase == last {
            if k == 0 && DRV_STOP.load(Ordering::SeqCst) {
                reset_pf();
                loop {
                    core::hint::spin_loop();
                }
            }
            core::hint::spin_loop();
            continue;
        }
        last = phase;
        let mut kick = || {
            d.control(sh, rxq);
            d.step(sh);
        };
        run_phase(k, cpu, phase, &mut a, lut, cache, Some(&mut kick), None);
    }
}
