//! `VERIFLAT_PARALLEL=unmapcpus` (run first and alone, then dom0 exits; meant for a `no-timer` build): the TSC cycles of
//! `mmap_4k` and `unmap_4k` of one page against the number of CPU ids in the calling thread's container's cpu set,
//! which `unmap_4k`'s TLB flush walks.
//!
//! dom0's root thread maps and unmaps one page at `VA` (its window present after the warm-up), each call timed on
//! its own, `WARMUP` + `ROUNDS` rounds per point; its thread holds `FUNDING` 4K quota, so every unmap refunds the page
//! to the thread. The first point has the root container's cpu set of all `NUM_CPU_IDS` ids. A helper thread of dom0
//! on CPU 0 then gives the ids away one at a time from the highest down, each as the transfer CPU of a new child
//! container that never runs, and the root thread times one point after each, down to the set {0}. The CPU ids at or
//! above the kernel's "CPUs present" count have no processor; the ids below it are processors parked Off. The last
//! child, the one given CPU `CHILD_CPU`, runs `timed_child` once CPU `CHILD_CPU` comes online for it: the same loop,
//! the same funding, in its own process (own page table and PCID) of a container whose cpu set is {`CHILD_CPU`}.
//!
//! Before the points: the cycles of an empty `rdtsc` pair and of an uncontended `compare_exchange` plus a store on a
//! cache-hot word. Lines: `unmapcpus calibration ...`, `unmapcpus root set=n ...` per point, `unmapcpus child set=1 ...`.

use core::fmt::Write;
use core::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};

use vsys::*;

use crate::{current_cpu, entry, exit_thread, fund, image_range, quiet, stack_top, wait_for, WAIT_LIMIT};

/// The timed page, in a GiB no other dom0 timing maps.
const VA: usize = 0xc7_0000_0000;
const ROUNDS: usize = 20_000;
const WARMUP: usize = 2_000;
/// The timing thread's 4K quota: four at hand for the map, one for the page and the page tables of the first map.
const FUNDING: usize = 16;
/// The CPU ids of the kernel (`NUM_CPUS`), all in the root container's cpu set at boot.
const NUM_CPU_IDS: usize = 40;
/// The CPU of the child container that runs the loop.
const CHILD_CPU: usize = 1;
/// Funding and process quota of the containers that never run, and of the one that does: its thread moves
/// `FUNDING` to itself, as dom0's root thread holds.
const IDLE_FUNDING: usize = 8;
const IDLE_PROCESS_QUOTA: usize = 4;
const CHILD_FUNDING: usize = FUNDING + 8;
const CHILD_PROCESS_QUOTA: usize = 8;
const CALIBRATION_ITERATIONS: u64 = 1_000_000;

static mut MAP_CYCLES: [u64; ROUNDS] = [0; ROUNDS];
static mut UNMAP_CYCLES: [u64; ROUNDS] = [0; ROUNDS];
static mut HELPER_STACK: [u8; 64 * 1024] = [0; 64 * 1024];
static mut CHILD_STACK: [u8; 64 * 1024] = [0; 64 * 1024];
/// One plus the CPU id the helper is to give away; 0 once it did.
static GIVE: AtomicUsize = AtomicUsize::new(0);
static CHILD_DONE: AtomicBool = AtomicBool::new(false);
static CALIBRATION_WORD: AtomicU64 = AtomicU64::new(0);

fn rdtsc() -> u64 {
    unsafe { core::arch::x86_64::_rdtsc() }
}

/// Minimum, median, and mean of `samples`, which it sorts.
fn stats(samples: &mut [u64]) -> (u64, u64, u64) {
    samples.sort_unstable();
    (samples[0], samples[samples.len() / 2], samples.iter().sum::<u64>() / samples.len() as u64)
}

/// The loop of every point; logs one line led by `who`.
fn time_point(who: &str) {
    let (map, unmap) = unsafe { (&mut *(&raw mut MAP_CYCLES), &mut *(&raw mut UNMAP_CYCLES)) };
    for round in 0..WARMUP + ROUNDS {
        let start = rdtsc();
        let ret = unsafe { sys_mmap_4k(VA, 1) };
        let mapped = rdtsc();
        quiet("unmapcpus mmap_4k", ret);
        let p = VA as *mut u64;
        unsafe { p.write_volatile(round as u64) };
        if unsafe { p.read_volatile() } != round as u64 {
            log::error!("unmapcpus: the mapped page does not hold what was written");
            unsafe { sys_debug_exit(1) };
        }
        let unmap_start = rdtsc();
        let ret = unsafe { sys_unmap_4k(VA, 1) };
        let end = rdtsc();
        quiet("unmapcpus unmap_4k", ret);
        if round >= WARMUP {
            (map[round - WARMUP], unmap[round - WARMUP]) = (mapped - start, end - unmap_start);
        }
    }
    let (m, u) = (stats(map), stats(unmap));
    log::info!("unmapcpus {} cpu={}: mmap_4k min {} median {} mean {}, unmap_4k min {} median {} mean {} TSC cycles over {} rounds",
        who, current_cpu(), m.0, m.1, m.2, u.0, u.1, u.2, ROUNDS);
}

fn calibrate() {
    let samples = unsafe { &mut *(&raw mut MAP_CYCLES) };
    for sample in samples.iter_mut() {
        let start = rdtsc();
        *sample = rdtsc() - start;
    }
    let pair = stats(samples);
    let mut best = u64::MAX;
    for _ in 0..5 {
        let start = rdtsc();
        for _ in 0..CALIBRATION_ITERATIONS {
            let _ = CALIBRATION_WORD.compare_exchange(0, 1, Ordering::Acquire, Ordering::Relaxed);
            CALIBRATION_WORD.store(0, Ordering::Release);
        }
        best = best.min((rdtsc() - start) * 100 / CALIBRATION_ITERATIONS);
    }
    log::info!("unmapcpus calibration: empty rdtsc pair min {} median {} TSC cycles; compare_exchange + store {}.{:02} TSC cycles per iteration (best of 5 x {})",
        pair.0, pair.1, best / 100, best % 100, CALIBRATION_ITERATIONS);
}

/// dom0's helper on CPU 0: gives away each id dom0 asks for as the transfer CPU of a new child container, funding
/// its thread's 4K quota only when the container creation finds too little at hand, and yields in between.
extern "C" fn helper() -> ! {
    let (image, pages) = image_range();
    loop {
        let give = GIVE.load(Ordering::SeqCst);
        if give != 0 {
            let id = give - 1;
            let (funding, process_quota, ip, sp) = if id == CHILD_CPU {
                (CHILD_FUNDING, CHILD_PROCESS_QUOTA, entry(timed_child), stack_top(&raw const CHILD_STACK))
            } else {
                (IDLE_FUNDING, IDLE_PROCESS_QUOTA, entry(idle_child), stack_top(&raw const CHILD_STACK))
            };
            let create = || unsafe { sys_new_container(image, pages, funding, process_quota, id, ip, sp).rax };
            // Each new container takes two 2M quota (its container structures), so the kernel build needs
            // VERIFLAT_BOOT_2M_BLOCKS >= 2 * 39 = 78 (build-parallel-call-image.sh sets 128).
            quiet("unmapcpus helper alloc_quota_2m", unsafe { sys_alloc_quota_2m(2) });
            quiet("unmapcpus helper alloc_thread_quota_2m", unsafe { sys_alloc_thread_quota_2m(2) });
            let mut ret = create();
            if ret < 0 && error_name(ret) == "ErrorNoQuota" {
                fund("unmapcpus helper funding", 9 + funding + 3 * pages);
                ret = create();
            }
            quiet("unmapcpus new_container", ret);
            GIVE.store(0, Ordering::SeqCst);
        }
        unsafe { sys_schedule() };
    }
}

/// The root thread of a child container that never runs: its CPU stays Off.
extern "C" fn idle_child() -> ! {
    log::error!("unmapcpus: a child container that should never run ran on CPU {}", current_cpu());
    unsafe { sys_debug_exit(1) }
}

/// The root thread of the child container whose cpu set is {`CHILD_CPU`}: funds itself as dom0's root thread is
/// funded, times the loop, and exits.
extern "C" fn timed_child() -> ! {
    quiet("unmapcpus child alloc_quota_4k", unsafe { sys_alloc_quota_4k(CHILD_FUNDING - CHILD_PROCESS_QUOTA) });
    quiet("unmapcpus child alloc_thread_quota_4k", unsafe { sys_alloc_thread_quota_4k(FUNDING) });
    time_point("child set=1 ids=1");
    CHILD_DONE.store(true, Ordering::SeqCst);
    exit_thread("unmapcpus child")
}

/// Has the helper give away CPU id `id` and waits until it did.
fn give_away(id: usize) {
    GIVE.store(id + 1, Ordering::SeqCst);
    let start = rdtsc();
    while GIVE.load(Ordering::SeqCst) != 0 {
        if rdtsc() - start > WAIT_LIMIT {
            log::error!("unmapcpus: timed out waiting for the helper to give away CPU {}", id);
            unsafe { sys_debug_exit(1) };
        }
        unsafe { sys_schedule() };
    }
}

pub fn run() {
    calibrate();
    fund("unmapcpus helper thread funding", 1);
    quiet("unmapcpus new_thread (helper)", unsafe { sys_new_thread(entry(helper), stack_top(&raw const HELPER_STACK)) });
    fund("unmapcpus funding", FUNDING);
    time_point("root set=40 ids=0..39");
    for id in (1..NUM_CPU_IDS).rev() {
        give_away(id);
        let mut who = Label { bytes: [0; 48], len: 0 };
        let _ = write!(who, "root set={} ids=0..{}", id, id - 1);
        time_point(who.as_str());
    }
    // The last child, given CPU `CHILD_CPU`, is the only one dom0 brings a CPU online for; its index among the
    // root container's children is whichever accepts it.
    let mut onlined = false;
    for child in 0..NUM_CPU_IDS {
        if unsafe { sys_cpu_online_child(child, CHILD_CPU) } >= 0 {
            onlined = true;
            break;
        }
    }
    if !onlined {
        log::error!("unmapcpus: no child container accepted cpu_online_child for CPU {}", CHILD_CPU);
        unsafe { sys_debug_exit(1) };
    }
    wait_for("the unmapcpus child", || CHILD_DONE.load(Ordering::SeqCst));
    log::info!("unmapcpus passed");
}

/// A fixed-capacity line label, since dom0 sets up no heap here.
struct Label {
    bytes: [u8; 48],
    len: usize,
}

impl Label {
    fn as_str(&self) -> &str {
        core::str::from_utf8(&self.bytes[..self.len]).unwrap_or("?")
    }
}

impl core::fmt::Write for Label {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        let end = self.len + s.len();
        if end > self.bytes.len() {
            return Err(core::fmt::Error);
        }
        self.bytes[self.len..end].copy_from_slice(s.as_bytes());
        self.len = end;
        Ok(())
    }
}
