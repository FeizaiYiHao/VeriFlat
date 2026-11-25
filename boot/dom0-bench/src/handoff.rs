//! NIC-independent timings of the payload paths and of the primitives behind them (run first and alone, then dom0
//! exits; for a `no-timer` build). `VERIFLAT_PARALLEL` lists them: `iommu` and `handoff` (in this order, in one boot),
//! or `flushcpus` (a boot of its own: its spinning threads keep every CPU).
//!
//! `handoff`: payload hand-off between dom0 (the sender S) and a child process R sharing dom0's image, for payloads of
//! 4 KiB, 64 KiB, 1 MiB and 2 MiB (`VERIFLAT_HANDOFF_SIZES`, in pages: `1,16,256,512`). One round: S writes the whole
//! payload, hands it to R, R reads every byte (sums it), and the buffer comes back to S for the next round; the round
//! time is the cost per hand-off. Variants:
//!
//! - `local`: S writes and reads its own private buffer (no hand-off): the work every variant contains.
//! - `pool`: zero copy: the payload lives in a region both processes map; only a descriptor moves.
//! - `copy`: R copies the payload out of the shared region into a private buffer and reads the copy (one copy).
//! - `copy2`: S writes into a private buffer and copies it into the shared region; R copies it out (copy in and out).
//! - `map`: the payload's pages move: S `send_pages` them to R, which maps them at the same VA, and `unmap_4k`s its own
//!   mapping; R reads them and gives them back the same way. 4K pages: the kernel's page IPC moves only 4K pages, so
//!   there is no 2M-page variant (a 2 MiB payload moves as 512 4K pages).
//!
//! Same core (S and R on CPU 0): `pool`/`copy`/`copy2` notify with one `call_usize` round trip per hand-off (R's
//! server thread does its side inside the call); `map` meets R's thread waiting in `receive_pages` directly: per round
//! S `send_pages` + `unmap_4k` + `receive_pages` (blocks), R `send_pages` + `unmap_4k` + `receive_pages` (blocks).
//! Two cores (S on CPU 0, R's polling thread on CPU 1): `pool`/`copy`/`copy2` publish a sequence number and spin for the
//! acknowledgement (no syscall); `map` gives through couriers (`courier`: the receiving process's thread on the giver's
//! CPU), since a page IPC rendezvous wakes the waiting side on the giver's CPU and sends no IPI.
//! Lines: `handoff core=same|two variant=<v> bytes=<b> rounds=<r> min=<c> median=<c> mean=<c> per_kib=<c>` (TSC cycles
//! per round, the median per KiB of payload), for `map` followed by the means of its parts (`send=`, `unmap=`, `wait=`).
//!
//! `iommu`: `iommu_map_4k` and `iommu_unmap_4k` of n = 1, 8, 32, 64 pages in a child process with an IOMMU table of its
//! own, first with no device attached to the table (no domain, so `iommu_unmap_4k` invalidates no IOTLB), then with
//! one (an E810 function, else QEMU's `edu`) attached: lines `iommu_prim attached=0|1 pages=<n> map_min= map_median=
//! unmap_min= unmap_median= rounds=`.
//!
//! `flushcpus`: `unmap_4k` of 1 page (per-VA flush) and of 16 pages (whole-PCID flush) by dom0's root thread on CPU 0
//! while dom0 threads spin on CPUs 1..c-1, for c = 1, 2, 4, 8, 16, 28 (up to the CPUs present): the TLB flush must
//! reach every CPU that runs dom0. Lines `flushcpus cpus=<c> pages=<n> mmap_median= unmap_min= unmap_median=
//! unmap_mean= rounds=`.

use alloc::vec::Vec;
use core::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};

use vsys::*;

use crate::courier::{self, Mailbox};
use crate::ice_bench::{count_cpus, env_list, find_e810, pick};
use crate::nvme::time::rdtsc;
use crate::{current_cpu, entry, fund, image_range, quiet, quiet_value, stack_top, wait_for, wait_yield};

/// dom0's descriptors of the hand-off endpoints; R holds them in descriptors 0, 1, 2, 3.
const H_CALL: usize = 1;
const H_PAGES: usize = 2;
const H_BACK: usize = 3;
const H_M: usize = 4;
/// The iommu timing's endpoint to its child.
const H_IO: usize = 5;
/// The payload regions: map's pages, the shared pool, S's and R's private buffers; one GiB each.
const VA_M: usize = 0xe0_0000_0000;
const VA_SH: usize = 0xe0_4000_0000;
const VA_PS: usize = 0xe0_8000_0000;
const VA_PR: usize = 0xe0_c000_0000;
const VA_IO: usize = 0xe1_0000_0000;
const VA_F: usize = 0xe1_4000_0000;
const MAX_PAGES: usize = 512;
const FUNDING: usize = 3 * MAX_PAGES + 64;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Var {
    Local,
    Pool,
    Copy,
    Copy2,
    Map,
}

impl Var {
    fn name(self) -> &'static str {
        match self {
            Var::Local => "local",
            Var::Pool => "pool",
            Var::Copy => "copy",
            Var::Copy2 => "copy2",
            Var::Map => "map",
        }
    }

    fn code(self) -> usize {
        self as usize
    }

    fn of(c: usize) -> Var {
        [Var::Local, Var::Pool, Var::Copy, Var::Copy2, Var::Map][c.min(4)]
    }
}

/// The call value that makes R's server start its polling thread, and the two-core stop.
const SPAWN: usize = 0xf << 20;
const STOP: u64 = u64::MAX;

static R_READY: AtomicBool = AtomicBool::new(false);
static RM_WAITING: AtomicBool = AtomicBool::new(false);
static R_POLL_CPU: AtomicUsize = AtomicUsize::new(0);
/// Pages of the next map round R's map thread waits for (0: none, it parks).
static PH_N: AtomicUsize = AtomicUsize::new(0);
/// Two cores: S's request (`seq`, variant, pages) and R's acknowledgement.
static MSG_SEQ: AtomicU64 = AtomicU64::new(0);
static MSG_VAR: AtomicUsize = AtomicUsize::new(0);
static MSG_N: AtomicUsize = AtomicUsize::new(0);
static ACK_SEQ: AtomicU64 = AtomicU64::new(0);
/// Sums of what R read, so that the reads stay.
static SUM: AtomicU64 = AtomicU64::new(0);
static MB_R: Mailbox = Mailbox::new();
static MB_S: Mailbox = Mailbox::new();
static mut R_STACK: [u8; 64 * 1024] = [0; 64 * 1024];
static mut IO_STACK: [u8; 64 * 1024] = [0; 64 * 1024];

static IO_DEV: AtomicUsize = AtomicUsize::new(0);
static IO_READY: AtomicBool = AtomicBool::new(false);
static IO_DONE: AtomicBool = AtomicBool::new(false);
static IO_HAS_DEV: AtomicBool = AtomicBool::new(false);

fn fill(va: usize, bytes: usize, v: u64) {
    let p = va as *mut u64;
    for i in 0..bytes / 8 {
        unsafe { p.add(i).write_volatile(v ^ i as u64) };
    }
}

fn sum(va: usize, bytes: usize) -> u64 {
    let p = va as *const u64;
    let mut s = 0u64;
    for i in 0..bytes / 8 {
        s = s.wrapping_add(unsafe { p.add(i).read() });
    }
    s
}

fn copy(from: usize, to: usize, bytes: usize) {
    unsafe { core::ptr::copy_nonoverlapping(from as *const u8, to as *mut u8, bytes) };
}

/// Minimum, median and mean of `v`, which it sorts.
fn stats(v: &mut [u64]) -> (u64, u64, u64) {
    v.sort_unstable();
    (v[0], v[v.len() / 2], v.iter().sum::<u64>() / v.len() as u64)
}

fn sizes() -> Vec<usize> {
    match option_env!("VERIFLAT_HANDOFF_SIZES") {
        Some(v) => env_list("VERIFLAT_HANDOFF_SIZES", Some(v), 1).into_iter().map(|p| (p as usize).clamp(1, MAX_PAGES)).collect(),
        None => alloc::vec![1, 16, 256, 512],
    }
}

/// Timed rounds for a payload of `pages` pages (and a tenth of them untimed before).
fn rounds(pages: usize) -> usize {
    (20_000 / pages).clamp(200, 20_000)
}

/// R's side of one hand-off of `n` pages of variant `v`, on whichever core.
fn r_work(v: Var, n: usize) -> u64 {
    let bytes = n * 4096;
    match v {
        Var::Pool => sum(VA_SH, bytes),
        Var::Copy | Var::Copy2 => {
            copy(VA_SH, VA_PR, bytes);
            sum(VA_PR, bytes)
        }
        Var::Map => sum(VA_M, bytes),
        Var::Local => 0,
    }
}

/// R's first thread (H_CALL in descriptor 0): receives the other endpoints and the shared pool, maps its private
/// buffer, starts its courier (for S's two-core gives) and its map thread, then serves S's same-core calls.
extern "C" fn r_main() -> ! {
    for i in 1..=3 {
        quiet("handoff R receive_endpoint", unsafe { sys_receive_endpoint(0, i) });
    }
    fund("handoff R funding", 4 * MAX_PAGES + FUNDING + 64);
    quiet("handoff R receive_pages (pool)", unsafe { sys_receive_pages(0, VA_SH, MAX_PAGES) });
    quiet("handoff R mmap_4k (private)", unsafe { sys_mmap_4k(VA_PR, MAX_PAGES) });
    fill(VA_PR, MAX_PAGES * 4096, 1);
    crate::slab_alloc::init();
    courier::start(&MB_R, 1, FUNDING);
    fund("handoff R map thread funding", 1);
    let stack = alloc::boxed::Box::leak(alloc::vec![0u8; 32 * 1024].into_boxed_slice());
    quiet("handoff R new_thread_with_endpoint (map)", unsafe { sys_new_thread_with_endpoint(3, entry(r_map), stack.as_ptr() as usize + stack.len() - 8) });
    wait_yield("R's map thread to wait", || RM_WAITING.load(Ordering::SeqCst));
    R_READY.store(true, Ordering::SeqCst);
    let mut value = quiet_value("handoff R receive_call", unsafe { sys_receive_call(0) });
    loop {
        let reply = if value == SPAWN {
            fund("handoff R poll thread funding", 1);
            let stack = alloc::boxed::Box::leak(alloc::vec![0u8; 32 * 1024].into_boxed_slice());
            quiet("handoff R new_thread_with_endpoint (poll)", unsafe { sys_new_thread_with_endpoint(2, entry(r_poll), stack.as_ptr() as usize + stack.len() - 8) });
            0
        } else {
            r_work(Var::of(value >> 20), value & 0xfffff) as usize & 0xffff
        };
        value = quiet_value("handoff R reply_and_receive_usize", unsafe { sys_reply_and_receive_usize(0, reply) });
    }
}

/// R's map thread (H_M in descriptor 0): same-core map rounds; parks for good once `PH_N` is 0.
extern "C" fn r_map() -> ! {
    fund("handoff R map funding", FUNDING);
    loop {
        let n = PH_N.load(Ordering::SeqCst);
        if n == 0 {
            quiet("handoff R map park", unsafe { sys_receive_empty(0) });
            continue;
        }
        RM_WAITING.store(true, Ordering::SeqCst);
        quiet("handoff R receive_pages", unsafe { sys_receive_pages(0, VA_M, n) });
        SUM.fetch_add(sum(VA_M, n * 4096), Ordering::Relaxed);
        quiet("handoff R send_pages", unsafe { sys_send_pages(0, VA_M, n) });
        quiet("handoff R unmap_4k", unsafe { sys_unmap_4k(VA_M, n) });
    }
}

/// R's polling thread (H_BACK in descriptor 0) on CPU 1: two-core rounds; map gives the pages back through S's
/// courier.
extern "C" fn r_poll() -> ! {
    R_POLL_CPU.store(current_cpu() + 1, Ordering::SeqCst);
    let mut last = 0;
    loop {
        let seq = MSG_SEQ.load(Ordering::Acquire);
        if seq == last {
            core::hint::spin_loop();
            continue;
        }
        last = seq;
        if seq == STOP {
            ACK_SEQ.store(seq, Ordering::Release);
            quiet("handoff R poll park", unsafe { sys_receive_empty(0) });
            continue;
        }
        let (v, n) = (Var::of(MSG_VAR.load(Ordering::Relaxed)), MSG_N.load(Ordering::Relaxed));
        SUM.fetch_add(r_work(v, n), Ordering::Relaxed);
        if v == Var::Map {
            courier::give(&MB_S, 0, VA_M, VA_M, n, true);
        }
        ACK_SEQ.store(seq, Ordering::Release);
    }
}

/// Times `rounds(n)` rounds of variant `v` with `n` pages and logs the line.
fn time_variant(core: &str, v: Var, n: usize, next_map: usize) {
    let bytes = n * 4096;
    let (warm, timed) = (rounds(n) / 10, rounds(n));
    let mut samples = Vec::with_capacity(timed);
    let (mut send, mut unmap, mut wait) = (0u64, 0u64, 0u64);
    let two = core == "two";
    for r in 0..warm + timed {
        let seq = MSG_SEQ.load(Ordering::Relaxed) + 1;
        let t0 = rdtsc();
        match (v, two) {
            (Var::Local, _) => {
                fill(VA_PS, bytes, r as u64);
                SUM.fetch_add(sum(VA_PS, bytes), Ordering::Relaxed);
            }
            (Var::Pool | Var::Copy, false) => {
                fill(VA_SH, bytes, r as u64);
                quiet("handoff call_usize", unsafe { sys_call_usize(H_CALL, v.code() << 20 | n) });
            }
            (Var::Copy2, false) => {
                fill(VA_PS, bytes, r as u64);
                copy(VA_PS, VA_SH, bytes);
                quiet("handoff call_usize", unsafe { sys_call_usize(H_CALL, v.code() << 20 | n) });
            }
            (Var::Map, false) => {
                fill(VA_M, bytes, r as u64);
                if r == warm + timed - 1 {
                    // R's map thread posts its next receive for the next size once this round ends.
                    PH_N.store(next_map, Ordering::SeqCst);
                }
                let s0 = rdtsc();
                quiet("handoff send_pages", unsafe { sys_send_pages(H_M, VA_M, n) });
                let a = rdtsc();
                quiet("handoff unmap_4k", unsafe { sys_unmap_4k(VA_M, n) });
                let b = rdtsc();
                quiet("handoff receive_pages", unsafe { sys_receive_pages(H_M, VA_M, n) });
                send += a - s0;
                unmap += b - a;
            }
            (Var::Pool | Var::Copy | Var::Copy2 | Var::Map, true) => {
                match v {
                    Var::Copy2 => {
                        fill(VA_PS, bytes, r as u64);
                        copy(VA_PS, VA_SH, bytes);
                    }
                    Var::Map => {
                        fill(VA_M, bytes, r as u64);
                        let s0 = rdtsc();
                        courier::give(&MB_R, H_PAGES, VA_M, VA_M, n, true);
                        send += rdtsc() - s0;
                    }
                    _ => fill(VA_SH, bytes, r as u64),
                }
                MSG_VAR.store(v.code(), Ordering::Relaxed);
                MSG_N.store(n, Ordering::Relaxed);
                MSG_SEQ.store(seq, Ordering::Release);
                let w0 = rdtsc();
                let limit = w0 + crate::WAIT_LIMIT;
                while ACK_SEQ.load(Ordering::Acquire) != seq {
                    if rdtsc() > limit {
                        log::error!("handoff: R did not acknowledge round {}", seq);
                        unsafe { sys_debug_exit(1) };
                    }
                    core::hint::spin_loop();
                }
                wait += rdtsc() - w0;
            }
        }
        let t1 = rdtsc();
        if r >= warm {
            samples.push(t1 - t0);
        } else {
            (send, unmap, wait) = (0, 0, 0);
        }
    }
    let (min, median, mean) = stats(&mut samples);
    let mut line = alloc::format!(
        "handoff core={} variant={} bytes={} rounds={} min={} median={} mean={} per_kib={}",
        core, v.name(), bytes, timed, min, median, mean, median * 1024 / bytes as u64
    );
    if v == Var::Map {
        let t = timed as u64;
        if two {
            line += &alloc::format!(" give={} wait={}", send / t, wait / t);
        } else {
            line += &alloc::format!(" send={} unmap={} rest={}", send / t, unmap / t, mean.saturating_sub((send + unmap) / t));
        }
    }
    log::info!("{}", line);
}

/// The `handoff` timing (see the module comment).
pub fn run_handoff() {
    crate::slab_alloc::init();
    let sizes = sizes();
    let cpus = count_cpus();
    log::info!("handoff: payloads of {:?} pages, {} CPUs, rounds 20000/pages (200 at least)", sizes, cpus);
    fund("handoff endpoints and mappings", 4 + 4 * 3 * MAX_PAGES + FUNDING);
    for ep in [H_CALL, H_PAGES, H_BACK, H_M] {
        quiet("handoff new_endpoint", unsafe { sys_new_endpoint(ep) });
    }
    for va in [VA_SH, VA_M, VA_PS] {
        quiet("handoff mmap_4k", unsafe { sys_mmap_4k(va, MAX_PAGES) });
        fill(va, MAX_PAGES * 4096, 7);
    }
    PH_N.store(sizes[0], Ordering::SeqCst);
    let (image, pages) = image_range();
    fund("handoff R process funding", 6 + 3 * pages);
    // With an IOMMU table only because the heap's pager maps every heap page into it (`slab_alloc`).
    quiet("handoff new_process_with_iommu_and_endpoint (R)", unsafe {
        sys_new_process_with_iommu_and_endpoint(image, pages, H_CALL, entry(r_main), stack_top(&raw const R_STACK))
    });
    for ep in [H_PAGES, H_BACK, H_M] {
        quiet("handoff send_endpoint", unsafe { sys_send_endpoint(H_CALL, ep) });
    }
    quiet("handoff send_pages (pool)", unsafe { sys_send_pages(H_CALL, VA_SH, MAX_PAGES) });
    wait_yield("handoff R to be ready", || R_READY.load(Ordering::SeqCst));
    courier::start(&MB_S, H_BACK, FUNDING);

    // Same core: everything on CPU 0.
    for v in [Var::Local, Var::Pool, Var::Copy, Var::Copy2] {
        for &n in &sizes {
            time_variant("same", v, n, 0);
        }
    }
    for (i, &n) in sizes.iter().enumerate() {
        time_variant("same", Var::Map, n, sizes.get(i + 1).copied().unwrap_or(0));
    }
    if cpus < 2 {
        log::info!("handoff: one CPU, no two-core rounds");
        log::info!("handoff passed (sum {:#x})", SUM.load(Ordering::Relaxed));
        return;
    }
    // Two cores: R's polling thread, queued on CPU 0 by the call, moves to CPU 1 when it comes online.
    quiet("handoff call_usize (spawn)", unsafe { sys_call_usize(H_CALL, SPAWN) });
    quiet("handoff cpu_online(1)", unsafe { sys_cpu_online(1) });
    wait_for("handoff R's polling thread", || R_POLL_CPU.load(Ordering::SeqCst) != 0);
    if R_POLL_CPU.load(Ordering::SeqCst) != 2 {
        log::error!("handoff: R's polling thread runs on CPU {}", R_POLL_CPU.load(Ordering::SeqCst) - 1);
        unsafe { sys_debug_exit(1) };
    }
    for v in [Var::Pool, Var::Copy, Var::Copy2, Var::Map] {
        for &n in &sizes {
            time_variant("two", v, n, 0);
        }
    }
    MSG_SEQ.store(STOP, Ordering::Release);
    wait_for("handoff R's polling thread to stop", || ACK_SEQ.load(Ordering::SeqCst) == STOP);
    if current_cpu() != 0 {
        log::error!("handoff: S moved to CPU {}", current_cpu());
        unsafe { sys_debug_exit(1) };
    }
    log::info!("handoff passed (sum {:#x})", SUM.load(Ordering::Relaxed));
}

const IO_PAGES: [usize; 4] = [1, 8, 32, 64];
const IO_ROUNDS: usize = 2000;
const IO_WARMUP: usize = 200;

/// The iommu timing's child (H_IO in descriptor 0, an IOMMU table of its own).
extern "C" fn io_child() -> ! {
    crate::slab_alloc::init();
    fund("iommu child funding", 4 * 64 + 3 * 64 + 64);
    quiet("iommu child mmap_4k", unsafe { sys_mmap_4k(VA_IO, 64) });
    fill(VA_IO, 64 * 4096, 3);
    io_points(false);
    IO_READY.store(true, Ordering::SeqCst);
    if IO_HAS_DEV.load(Ordering::SeqCst) {
        let bdf = IO_DEV.load(Ordering::SeqCst);
        let (bus, dev, fun) = (bdf >> 8, (bdf >> 3) & 0x1f, bdf & 7);
        quiet("iommu child receive_pci", unsafe { sys_receive_pci(0, bus, dev, fun) });
        quiet("iommu child pci_attach_dma", unsafe { sys_pci_attach_dma(bus, dev, fun) });
        io_points(true);
    }
    IO_DONE.store(true, Ordering::SeqCst);
    loop {
        quiet("iommu child park", unsafe { sys_receive_empty(0) });
    }
}

fn io_points(attached: bool) {
    let mut map = Vec::with_capacity(IO_ROUNDS);
    let mut unmap = Vec::with_capacity(IO_ROUNDS);
    for n in IO_PAGES {
        map.clear();
        unmap.clear();
        for r in 0..IO_WARMUP + IO_ROUNDS {
            let t0 = rdtsc();
            let a = unsafe { sys_iommu_map_4k(VA_IO, VA_IO, n) };
            let t1 = rdtsc();
            quiet("iommu_map_4k", a);
            let t2 = rdtsc();
            let b = unsafe { sys_iommu_unmap_4k(VA_IO, n) };
            let t3 = rdtsc();
            quiet("iommu_unmap_4k", b);
            if r >= IO_WARMUP {
                map.push(t1 - t0);
                unmap.push(t3 - t2);
            }
        }
        let (m, u) = (stats(&mut map), stats(&mut unmap));
        log::info!(
            "iommu_prim attached={} pages={} map_min={} map_median={} map_mean={} unmap_min={} unmap_median={} unmap_mean={} rounds={}",
            attached as u8, n, m.0, m.1, m.2, u.0, u.1, u.2, IO_ROUNDS
        );
    }
}

/// The `iommu` timing (see the module comment).
pub fn run_iommu() {
    crate::slab_alloc::init();
    let dev = match pick(&find_e810()) {
        Some(f) => Some((f.bus, f.dev, f.fun, "E810")),
        None => {
            let bdf = unsafe { sys_debug_dma_device() };
            (bdf >= 0).then(|| ((bdf as usize >> 8) & 0xff, (bdf as usize >> 3) & 0x1f, bdf as usize & 7, "edu"))
        }
    };
    if let Some((bus, d, fun, what)) = dev {
        log::info!("iommu: attaching {} {:02x}:{:02x}.{} for the second series", what, bus, d, fun);
        IO_DEV.store(bus << 8 | d << 3 | fun, Ordering::SeqCst);
        IO_HAS_DEV.store(true, Ordering::SeqCst);
    } else {
        log::info!("iommu: no device to attach: only the series without one");
    }
    fund("iommu endpoint and child funding", 1);
    quiet("iommu new_endpoint", unsafe { sys_new_endpoint(H_IO) });
    let (image, pages) = image_range();
    fund("iommu child process funding", 6 + 3 * pages);
    quiet("iommu new_process_with_iommu_and_endpoint", unsafe {
        sys_new_process_with_iommu_and_endpoint(image, pages, H_IO, entry(io_child), stack_top(&raw const IO_STACK))
    });
    wait_yield("the iommu child's first series", || IO_READY.load(Ordering::SeqCst));
    if let Some((bus, d, fun, _)) = dev {
        crate::bar::claim("iommu pci_claim", bus, d, fun);
        quiet("iommu send_pci", unsafe { sys_send_pci(H_IO, bus, d, fun) });
    }
    wait_yield("the iommu child", || IO_DONE.load(Ordering::SeqCst));
    log::info!("iommu passed");
}

/// One plus the CPU each spinner of `flushcpus` runs on, and the word it spins on (own cache line each).
#[repr(C, align(64))]
struct Spin {
    cpu: AtomicUsize,
    beat: AtomicU64,
}

static SPINS: [Spin; 64] = [const { Spin { cpu: AtomicUsize::new(0), beat: AtomicU64::new(0) } }; 64];
static NEXT_SPIN: AtomicUsize = AtomicUsize::new(0);

extern "C" fn spinner() -> ! {
    let s = &SPINS[NEXT_SPIN.load(Ordering::SeqCst)];
    s.cpu.store(current_cpu() + 1, Ordering::SeqCst);
    loop {
        s.beat.fetch_add(1, Ordering::Relaxed);
        core::hint::spin_loop();
    }
}

fn flush_point(c: usize, pages: usize, rounds: usize) {
    let (mut map, mut unmap) = (Vec::with_capacity(rounds), Vec::with_capacity(rounds));
    for r in 0..rounds / 10 + rounds {
        let t0 = rdtsc();
        let a = unsafe { sys_mmap_4k(VA_F, pages) };
        let t1 = rdtsc();
        quiet("flushcpus mmap_4k", a);
        for i in 0..pages {
            unsafe { ((VA_F + i * 4096) as *mut u64).write_volatile(r as u64) };
        }
        let t2 = rdtsc();
        let b = unsafe { sys_unmap_4k(VA_F, pages) };
        let t3 = rdtsc();
        quiet("flushcpus unmap_4k", b);
        if r >= rounds / 10 {
            map.push(t1 - t0);
            unmap.push(t3 - t2);
        }
    }
    let (m, u) = (stats(&mut map), stats(&mut unmap));
    log::info!(
        "flushcpus cpus={} pages={} mmap_median={} unmap_min={} unmap_median={} unmap_mean={} rounds={}",
        c, pages, m.1, u.0, u.1, u.2, rounds
    );
}

/// The `flushcpus` timing (see the module comment).
pub fn run_flushcpus() {
    crate::slab_alloc::init();
    let n = count_cpus();
    fund("flushcpus funding", 4 * 16 + 64);
    let points: Vec<usize> = [1, 2, 4, 8, 16, 28].into_iter().filter(|&c| c <= n).collect();
    let mut online = 1;
    for &c in &points {
        while online < c {
            let k = online;
            NEXT_SPIN.store(k, Ordering::SeqCst);
            fund("flushcpus spinner funding", 1);
            let stack = alloc::boxed::Box::leak(alloc::vec![0u8; 16 * 1024].into_boxed_slice());
            quiet("flushcpus new_thread", unsafe { sys_new_thread(entry(spinner), stack.as_ptr() as usize + stack.len() - 8) });
            quiet("flushcpus cpu_online", unsafe { sys_cpu_online(k) });
            wait_for("a flushcpus spinner", || SPINS[k].cpu.load(Ordering::SeqCst) != 0);
            if SPINS[k].cpu.load(Ordering::SeqCst) != k + 1 {
                log::error!("flushcpus: spinner {} runs on CPU {}", k, SPINS[k].cpu.load(Ordering::SeqCst) - 1);
                unsafe { sys_debug_exit(1) };
            }
            online += 1;
        }
        flush_point(c, 1, 5000);
        flush_point(c, 16, 2000);
    }
    log::info!("flushcpus passed");
}
