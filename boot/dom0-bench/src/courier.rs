//! Page hand-off between two processes with the kernel's page IPC (`send_pages` / `receive_pages`), for the
//! map / unmap data paths of `ice_chan` (path `map`) and of `handoff`.
//!
//! The page IPC is a rendezvous: the pages move only while a thread of the receiving process waits in
//! `receive_pages` with the same page count, and a thread the rendezvous wakes is queued on the waker's CPU when both
//! are in one container (SystemCalls.md §11), with no IPI. So the receiving side keeps a courier: a thread of the
//! receiving process that lives on the giver's CPU and waits in `receive_pages` exactly when the giver is about to
//! send. One hand-off (`give`) on the giver's CPU:
//!
//! 1. the giver writes the target VA and page count into the courier's `Mailbox` and yields (`schedule`);
//! 2. the courier, queued on that CPU, runs, sees the new request and calls `receive_pages` (it blocks);
//! 3. the giver runs again and calls `send_pages`, which maps the pages into the receiver at the target VA and wakes
//!    the courier (queued again on this CPU);
//! 4. the giver unmaps its own copy (`unmap_4k`, whose TLB flush reaches every CPU the giver's process runs on).
//!
//! A courier that runs while its mailbox holds nothing new yields again (several couriers may share a CPU). A courier
//! starts parked in `receive_empty` on its endpoint; the first `give` wakes it with `send_empty`, which queues it on
//! the giver's CPU, where it stays. Mailboxes are statics of dom0's image, which every process of the benchmark shares.

use core::alloc::Layout;
use core::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};

use vsys::*;

use crate::{entry, fund, quiet, wait_yield};

/// One courier's requests and progress, on cache lines of its own.
#[repr(C, align(128))]
pub struct Mailbox {
    /// Giver: the request number, the target VA and the page count of the last request.
    seq: AtomicU64,
    va: AtomicUsize,
    n: AtomicUsize,
    /// Courier: the request it waits in `receive_pages` for (or received).
    posted: AtomicU64,
    /// Courier: set just before it parks; giver: set once it woke the courier.
    parked: AtomicBool,
    started: AtomicBool,
}

impl Mailbox {
    pub const fn new() -> Mailbox {
        Mailbox {
            seq: AtomicU64::new(0), va: AtomicUsize::new(0), n: AtomicUsize::new(0), posted: AtomicU64::new(0), parked: AtomicBool::new(false),
            started: AtomicBool::new(false),
        }
    }
}

/// The mailbox of the courier being started, and its 4K funding.
static NEXT: AtomicUsize = AtomicUsize::new(0);
static NEXT_FUNDING: AtomicUsize = AtomicUsize::new(0);
const STACK_BYTES: usize = 32 * 1024;
const GIVE_LIMIT: u64 = 20_000_000_000;

/// Starts a courier in the calling process (its heap must be set up) for `mb`, holding the calling thread's endpoint
/// descriptor `ep` in its descriptor 0 and `funding` 4K quota (it needs 3 per page of the largest request at hand,
/// and one per page-table page its target range still lacks); returns once it parked.
pub fn start(mb: &'static Mailbox, ep: usize, funding: usize) {
    NEXT.store(mb as *const Mailbox as usize, Ordering::SeqCst);
    NEXT_FUNDING.store(funding, Ordering::SeqCst);
    let stack = unsafe { alloc::alloc::alloc(Layout::from_size_align(STACK_BYTES, 4096).unwrap()) } as usize;
    if stack == 0 {
        log::error!("courier: no memory for a stack");
        unsafe { sys_debug_exit(1) };
    }
    fund("courier thread funding", 1);
    quiet("courier new_thread_with_endpoint", unsafe { sys_new_thread_with_endpoint(ep, entry(courier), stack + STACK_BYTES - 8) });
    wait_yield("a courier to park", || mb.parked.load(Ordering::SeqCst));
}

extern "C" fn courier() -> ! {
    let mb = unsafe { &*(NEXT.load(Ordering::SeqCst) as *const Mailbox) };
    fund("courier funding", NEXT_FUNDING.load(Ordering::SeqCst));
    mb.parked.store(true, Ordering::SeqCst);
    quiet("courier receive_empty (park)", unsafe { sys_receive_empty(0) });
    let mut last = 0;
    loop {
        let seq = mb.seq.load(Ordering::Acquire);
        if seq == last {
            unsafe { sys_schedule() };
            continue;
        }
        let (va, n) = (mb.va.load(Ordering::Relaxed), mb.n.load(Ordering::Relaxed));
        mb.posted.store(seq, Ordering::Release);
        quiet("courier receive_pages", unsafe { sys_receive_pages(0, va, n) });
        last = seq;
    }
}

/// Wakes the parked courier of `mb` (endpoint descriptor `ep` of the caller) onto the calling CPU, unless done before.
/// `give` does it at its first hand-off; a giver whose endpoint also serves other rendezvous (the IPC shape's pair
/// endpoint, where `reply_and_receive` queues the driver behind a parked courier) calls it at once instead.
pub fn wake(mb: &Mailbox, ep: usize) {
    if !mb.started.load(Ordering::Relaxed) {
        mb.started.store(true, Ordering::Relaxed);
        quiet("courier wake send_empty", unsafe { sys_send_empty(ep) });
    }
}

/// Hands the `n` pages at `src` of the calling process to the courier of `mb` (endpoint descriptor `ep` of the caller),
/// which maps them at `dst` of its process; then unmaps them here when `unmap`. Returns once both are done.
pub fn give(mb: &Mailbox, ep: usize, src: usize, dst: usize, n: usize, unmap: bool) {
    let seq = mb.seq.load(Ordering::Relaxed) + 1;
    mb.va.store(dst, Ordering::Relaxed);
    mb.n.store(n, Ordering::Relaxed);
    mb.seq.store(seq, Ordering::Release);
    wake(mb, ep);
    let start = unsafe { core::arch::x86_64::_rdtsc() };
    while mb.posted.load(Ordering::Acquire) != seq {
        unsafe { sys_schedule() };
        if unsafe { core::arch::x86_64::_rdtsc() } - start > GIVE_LIMIT {
            log::error!("courier: no courier took request {} on CPU {}", seq, crate::current_cpu());
            unsafe { sys_debug_exit(1) };
        }
    }
    quiet("give send_pages", unsafe { sys_send_pages(ep, src, n) });
    if unmap {
        quiet("give unmap_4k", unsafe { sys_unmap_4k(src, n) });
    }
}
