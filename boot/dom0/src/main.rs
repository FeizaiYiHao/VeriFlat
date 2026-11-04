//! Dom0 test program: exercises the VeriFlat syscalls over the trap layer.

#![no_std]
#![no_main]

use core::panic::PanicInfo;
use core::sync::atomic::{AtomicBool, AtomicU64, AtomicU8, AtomicUsize, Ordering};

use vsys::*;

/// A mapping target inside dom0's user half (L4 index 1): 32 GiB above the base.
const TEST_VA: usize = 0x80_0000_0000 + 0x8_0000_0000;
const TEST_PAGES: usize = 4;

/// Endpoint descriptor 0 is the root endpoint given to dom0's first thread.
const ENDPOINT: usize = 0;

static mut THREAD_STACK: [u8; 64 * 1024] = [0; 64 * 1024];
static mut WORKER_STACK: [u8; 64 * 1024] = [0; 64 * 1024];
static PINGS: AtomicUsize = AtomicUsize::new(0);

/// Bit `n` is set once a dom0 thread ran on CPU `n`.
static SEEN_CPUS: AtomicUsize = AtomicUsize::new(0);
static STOP_WORKER: AtomicBool = AtomicBool::new(false);
static WORKER_STOPPED: AtomicBool = AtomicBool::new(false);
/// While set, the worker spins without touching its page, so the page's TLB entry stays cached
/// on the worker's CPU; `WORKER_PAUSED` acknowledges it and `WORKER_CPU` is where it spins.
static PAUSE_WORKER: AtomicBool = AtomicBool::new(false);
static WORKER_PAUSED: AtomicBool = AtomicBool::new(false);
static WORKER_CPU: AtomicUsize = AtomicUsize::new(usize::MAX);

/// TSC cycles a wait loop may spin before the test fails.
const WAIT_LIMIT: u64 = 20_000_000_000;

static mut CHILD_STACK: [u8; 64 * 1024] = [0; 64 * 1024];
/// `bus << 8 | device << 3 | function` of the kernel's DMA test device.
static DMA_BDF: AtomicUsize = AtomicUsize::new(0);
static CHILD_MAY_ATTACH: AtomicBool = AtomicBool::new(false);
static CHILD_ATTACHED: AtomicBool = AtomicBool::new(false);

/// VT-d fault reasons the DMA probe reports.
const FAULT_CONTEXT_NOT_PRESENT: isize = 2;
const FAULT_READ_NOT_PRESENT: isize = 6;

static mut PLAIN_STACK: [u8; 64 * 1024] = [0; 64 * 1024];
static mut PEER_STACK: [u8; 64 * 1024] = [0; 64 * 1024];
static PLAIN_CHILD_RAN: AtomicBool = AtomicBool::new(false);
static PEER_DONE: AtomicBool = AtomicBool::new(false);

static mut CONTAINER_STACK: [u8; 64 * 1024] = [0; 64 * 1024];
/// One plus the CPU the child container's root thread first ran on; 0 until it runs.
static CONTAINER_CHILD_CPU: AtomicUsize = AtomicUsize::new(0);
static CONTAINER_CHILD_ONLINED: AtomicBool = AtomicBool::new(false);
/// The child container keeps `CONTAINER_FUNDING - CONTAINER_PROCESS_QUOTA` of its 4K funding and
/// its root process gets `CONTAINER_PROCESS_QUOTA`.
const CONTAINER_FUNDING: usize = 8;
const CONTAINER_PROCESS_QUOTA: usize = 4;

static mut ENDPOINT_STACK: [u8; 64 * 1024] = [0; 64 * 1024];
static NEW_ENDPOINT_USED: AtomicBool = AtomicBool::new(false);
/// The empty descriptor where dom0 creates a new endpoint.
const NEW_ENDPOINT: usize = 2;
/// Endpoint nobody sends on: the worker blocks on it once done, so its CPU goes idle again.
const PARK_ENDPOINT: usize = 3;
/// The user data segment (GDT index 3, RPL 3): a selector ring 3 may load into fs/gs.
const USER_DATA_SELECTOR: u16 = 0x1b;

/// Interleaved rounds of the syscall return timing, and null syscalls per path in each round.
const RETURN_ROUNDS: usize = 5;
const RETURN_CALLS: u64 = 100_000;

static mut SPINNER_STACK: [u8; 64 * 1024] = [0; 64 * 1024];
/// The register spinner spins in phase 0, then in phase 1, and stops at 2.
static SPINNER_PHASE: AtomicU8 = AtomicU8::new(0);
/// 0 while the register spinner runs, then `SPINNER_OK` or `SPINNER_FAILED`.
static SPINNER_RESULT: AtomicUsize = AtomicUsize::new(0);
const SPINNER_OK: usize = 1;
const SPINNER_FAILED: usize = 2;
/// The spinner's r11 in phase 0: IF and DF set, which no rflags of dom0 has (Rust code keeps DF clear).
const SPINNER_R11: u64 = 0x602;
/// dom0 yields this many times in each spinner phase, so the spinner is preempted and resumed repeatedly.
const SPINNER_ROUNDS: usize = 10;
/// Threads created back to back to time `new_thread`.
const TIMED_THREADS: usize = 32;
/// Ping-pong round trips over the root endpoint to time IPC.
const IPC_ROUNDS: u64 = 1000;
/// Fresh 4K pages mapped, touched, and unmapped per round, and the timed rounds, to time `mmap_4k`
/// and `unmap_4k`.
const MMAP_PAGES: usize = 64;
const MMAP_ROUNDS: u64 = 1000;
/// Fresh 4K pages mapped and touched by each variant of the mmap-only timing, and the region of each
/// variant: a separate GiB of dom0's user half that nothing mapped before, so every variant builds its
/// own page tables.
const MMAP_ONLY_PAGES: usize = 16384;
const MMAP_ONLY_VA: [usize; 2] = [0xc0_0000_0000, 0xc0_4000_0000];
static mut PONG_STACK: [u8; 64 * 1024] = [0; 64 * 1024];
static mut CALL_SERVER_STACK: [u8; 64 * 1024] = [0; 64 * 1024];
/// Untimed call round trips before the timed ones of the cross-process call timing.
const CROSS_CALL_WARMUP: usize = 100;
static mut CROSS_CALL_SERVER_STACK: [u8; 64 * 1024] = [0; 64 * 1024];

/// One page of dom0's image that a child process sends back to dom0 over IPC.
#[repr(C, align(4096))]
struct PageBuffer([u64; 512]);
static mut SHARED_PAGE: PageBuffer = PageBuffer([0; 512]);
/// Where dom0 receives that page: free in dom0's user half.
const PAGES_VA: usize = TEST_VA + 0x10_0000;
const PAGE_MAGIC: u64 = 0x5afe_9a9e;

extern "C" {
    /// The first and one-past-last bytes of dom0's loaded image (linker-defined).
    static __ehdr_start: u8;
    static _end: u8;
}

/// The CPU this thread runs on: the kernel stores the CPU ID in `IA32_TSC_AUX`.
fn current_cpu() -> usize {
    let mut aux = 0u32;
    unsafe { core::arch::x86_64::__rdtscp(&mut aux) };
    aux as usize
}

fn note_cpu() {
    SEEN_CPUS.fetch_or(1 << current_cpu(), Ordering::SeqCst);
}

/// Spins until `done` holds, recording the CPUs this thread runs on.
fn wait_for(what: &str, done: impl Fn() -> bool) {
    let start = unsafe { core::arch::x86_64::_rdtsc() };
    while !done() {
        note_cpu();
        if unsafe { core::arch::x86_64::_rdtsc() } - start > WAIT_LIMIT {
            log::error!("timed out waiting for {}", what);
            unsafe { sys_debug_exit(1) };
        }
        core::hint::spin_loop();
    }
}

/// `check` without the success log: for timed loops, where a serial line costs more than the call.
fn quiet(name: &str, ret: isize) {
    if ret < 0 {
        log::error!("{} failed: {} ({})", name, ret, error_name(ret));
        unsafe { sys_debug_exit(1) };
    }
}

/// `quiet` returning the value of a successful call.
fn quiet_value(name: &str, ret: isize) -> usize {
    quiet(name, ret);
    ret as usize
}

fn check(name: &str, ret: isize) -> usize {
    if ret < 0 {
        log::error!("{} failed: {} ({})", name, ret, error_name(ret));
        unsafe { sys_debug_exit(1) };
    }
    log::info!("{} -> {}", name, ret);
    ret as usize
}

/// Logs a syscall result without failing the test.
/// Fails the test unless the syscall returned the model error `expected`.
fn expect_error(name: &str, ret: isize, expected: &str) {
    log::info!("{} -> {} ({})", name, ret, if ret < 0 { error_name(ret) } else { "ok" });
    if ret >= 0 || error_name(ret) != expected {
        log::error!("{}: expected {}", name, expected);
        unsafe { sys_debug_exit(1) };
    }
}

fn dma_bdf() -> (usize, usize, usize) {
    let bdf = DMA_BDF.load(Ordering::SeqCst);
    (bdf >> 8, (bdf >> 3) & 0x1f, bdf & 0x7)
}

/// Has the DMA test device read through the IOMMU and fails unless it faulted with `reason`.
fn expect_dma_fault(when: &str, reason: isize) {
    let ret = unsafe { sys_debug_dma_probe() };
    log::info!("DMA {} -> fault reason {}", when, ret);
    if ret != reason {
        log::error!("DMA {}: expected fault reason {}", when, reason);
        unsafe { sys_debug_exit(1) };
    }
}

/// First thread of the child process, which shares dom0's image: takes the DMA test device over
/// the root endpoint and attaches it to its own IOMMU table.
extern "C" fn child_process() -> ! {
    let (bus, dev, fun) = dma_bdf();
    check("child receive_pci", unsafe { sys_receive_pci(ENDPOINT, bus, dev, fun) });
    // dom0 first checks that the transfer detached the function.
    while !CHILD_MAY_ATTACH.load(Ordering::SeqCst) {
        unsafe { sys_schedule() };
    }
    check("child pci_attach_dma", unsafe { sys_pci_attach_dma(bus, dev, fun) });
    CHILD_ATTACHED.store(true, Ordering::SeqCst);
    loop {
        unsafe { sys_schedule() };
    }
}

/// Second thread: answers two empty messages on the root endpoint and sends one, then yields until
/// retired.
extern "C" fn second_thread() -> ! {
    log::info!("second thread running");
    for _ in 0..2 {
        check("receive_empty", unsafe { sys_receive_empty(ENDPOINT) });
        PINGS.fetch_add(1, Ordering::SeqCst);
    }
    log::info!("second thread done, pings = {}", PINGS.load(Ordering::SeqCst));
    check("send_empty", unsafe { sys_send_empty(ENDPOINT) });
    // An idle CPU that comes online pulls this thread, so it records where it runs.
    retire_when_asked()
}

/// Worker thread: keeps a mapped page in its TLB on whatever CPU it runs, until told to stop.
extern "C" fn worker_thread() -> ! {
    let p = TEST_VA as *mut u64;
    while !STOP_WORKER.load(Ordering::SeqCst) {
        note_cpu();
        if PAUSE_WORKER.load(Ordering::SeqCst) {
            WORKER_CPU.store(current_cpu(), Ordering::SeqCst);
            WORKER_PAUSED.store(true, Ordering::SeqCst);
            core::hint::spin_loop();
            continue;
        }
        WORKER_PAUSED.store(false, Ordering::SeqCst);
        unsafe { p.write_volatile(p.read_volatile() + 1) };
    }
    WORKER_STOPPED.store(true, Ordering::SeqCst);
    // Descriptor 0 of this thread is `PARK_ENDPOINT`.
    check("worker receive_empty on the park endpoint", unsafe { sys_receive_empty(0) });
    loop {
        unsafe { sys_schedule() };
    }
}

/// First thread of a child process created without an endpoint.
extern "C" fn plain_child() -> ! {
    PLAIN_CHILD_RAN.store(true, Ordering::SeqCst);
    loop {
        unsafe { sys_schedule() };
    }
}

/// First thread of a child process sharing the root endpoint: receives that endpoint again into
/// slot 1 and uses it, sends a page of the shared image to dom0, and tries to take a CPU from dom0.
extern "C" fn peer_child() -> ! {
    check("peer receive_endpoint", unsafe { sys_receive_endpoint(ENDPOINT, 1) });
    check("peer send_empty on slot 1", unsafe { sys_send_empty(1) });
    check("peer send_pages", unsafe { sys_send_pages(ENDPOINT, (&raw const SHARED_PAGE) as usize, 1) });
    expect_error("peer receive_cpu", unsafe { sys_receive_cpu(ENDPOINT) }, "ErrorIpcSameContainer");
    PEER_DONE.store(true, Ordering::SeqCst);
    loop {
        unsafe { sys_schedule() };
    }
}

/// Root thread of the child container, which shares dom0's image and holds the root endpoint in
/// descriptor 0: spends its funding, receives a CPU from dom0 over the endpoint, and brings it online.
extern "C" fn container_child() -> ! {
    CONTAINER_CHILD_CPU.store(current_cpu() + 1, Ordering::SeqCst);
    check("container child alloc_quota_4k", unsafe { sys_alloc_quota_4k(CONTAINER_FUNDING - CONTAINER_PROCESS_QUOTA) });
    check("container child alloc_thread_quota_4k", unsafe { sys_alloc_thread_quota_4k(CONTAINER_FUNDING) });
    expect_error("container child alloc_quota_2m", unsafe { sys_alloc_quota_2m(1) }, "ErrorContainerQuotaInsufficient");
    let cpu = check("container child receive_cpu", unsafe { sys_receive_cpu(ENDPOINT) });
    check("container child cpu_online", unsafe { sys_cpu_online(cpu) });
    CONTAINER_CHILD_ONLINED.store(true, Ordering::SeqCst);
    loop {
        unsafe { sys_schedule() };
    }
}

/// Thread holding dom0's new endpoint in descriptor 0: without thread quota it cannot create an
/// endpoint of its own, and it receives one empty message on the new endpoint, then yields until
/// retired.
extern "C" fn endpoint_thread() -> ! {
    expect_error("endpoint thread new_endpoint without quota", unsafe { sys_new_endpoint(1) }, "ErrorNoQuota");
    check("endpoint thread receive_empty", unsafe { sys_receive_empty(ENDPOINT) });
    NEW_ENDPOINT_USED.store(true, Ordering::SeqCst);
    retire_when_asked()
}

/// Spins in two phases while dom0 resumes it from preempted frames, then checks its registers and
/// yields until retired.
/// Phase 0 keeps rcx at the loop head and r11 = `SPINNER_R11`: a resume through `sysretq` at the loop
/// head would load r11 into rflags, setting DF. Phase 1 keeps rcx = 0 and r11 = the loop's own
/// rflags: a resume through `sysretq` would jump to address 0.
extern "C" fn register_spinner() -> ! {
    let ok: u32;
    unsafe {
        core::arch::asm!(
            "lea rcx, [rip + 2f]",
            "mov r11, {magic}",
            "2:",
            "cmp byte ptr [{phase}], 0",
            "je 2b",
            "xor {ok:e}, {ok:e}",
            "lea {tmp}, [rip + 2b]",
            "cmp rcx, {tmp}",
            "jne 4f",
            "cmp r11, {magic}",
            "jne 4f",
            "pushfq",
            "pop {tmp}",
            "test {tmp}, {df}",
            "jnz 4f",
            "xor ecx, ecx",
            "cmp byte ptr [{phase}], 1",
            "pushfq",
            "pop {tmp}",
            "mov r11, {tmp}",
            "3:",
            "cmp byte ptr [{phase}], 1",
            "je 3b",
            "test rcx, rcx",
            "jnz 4f",
            "cmp r11, {tmp}",
            "jne 4f",
            "mov {ok:e}, 1",
            "4:",
            "cld",
            phase = in(reg) SPINNER_PHASE.as_ptr(),
            magic = const SPINNER_R11,
            df = const 1 << 10,
            ok = out(reg) ok,
            tmp = out(reg) _,
            out("rcx") _,
            out("r11") _,
        );
    }
    SPINNER_RESULT.store(if ok == 1 { SPINNER_OK } else { SPINNER_FAILED }, Ordering::SeqCst);
    retire_when_asked()
}

/// Answers `IPC_ROUNDS` pings on the root endpoint, then yields until retired.
extern "C" fn pong_thread() -> ! {
    for _ in 0..IPC_ROUNDS {
        quiet("pong receive_empty", unsafe { sys_receive_empty(ENDPOINT) });
        quiet("pong send_empty", unsafe { sys_send_empty(ENDPOINT) });
    }
    retire_when_asked()
}

/// Serves calls on the root endpoint, replying each value plus one, until a plain `send_empty` from
/// dom0 meets its receive-call wait and fails the rendezvous with ErrorIpcTypeMismatch; then yields
/// until retired. It runs as a dom0 thread, and as the first thread of the cross-process timing's
/// child, which holds the root endpoint in descriptor 0 too.
extern "C" fn call_server_thread() -> ! {
    let mut value = quiet_value("server receive_call", unsafe { sys_receive_call(ENDPOINT) });
    loop {
        let ret = unsafe { sys_reply_and_receive_usize(ENDPOINT, value + 1) };
        if ret < 0 {
            expect_error("server reply_and_receive_usize after the last call", ret, "ErrorIpcTypeMismatch");
            break;
        }
        value = ret as usize;
    }
    retire_when_asked()
}

/// Times one call round trip (call_usize, answered by `call_server_thread`'s reply_and_receive_usize,
/// each a direct switch to the other thread) while only these threads are runnable on this CPU, and
/// checks that each reply is the sent value plus one.
fn time_call_round_trip() {
    expect_error("reply_and_receive without a caller", unsafe { sys_reply_and_receive(ENDPOINT) }, "ErrorReplyOutOfPhase");
    let sp = (&raw const CALL_SERVER_STACK) as usize + 64 * 1024 - 8;
    check("new_thread_with_endpoint (call server)", unsafe { sys_new_thread_with_endpoint(ENDPOINT, call_server_thread as *const () as usize, sp) });
    let start = unsafe { core::arch::x86_64::_rdtsc() };
    for i in 0..IPC_ROUNDS as usize {
        let reply = quiet_value("call_usize", unsafe { sys_call_usize(ENDPOINT, i) });
        if reply != i + 1 {
            log::error!("call_usize({}) replied {}", i, reply);
            unsafe { sys_debug_exit(1) };
        }
    }
    let cycles = (unsafe { core::arch::x86_64::_rdtsc() } - start) / IPC_ROUNDS;
    log::info!("call round trip: {} TSC cycles (2 syscalls, 2 direct switches) over {} rounds", cycles, IPC_ROUNDS);
    expect_error("send_empty to a receive_call waiter", unsafe { sys_send_empty(ENDPOINT) }, "ErrorIpcTypeMismatch");
}

/// Times one call round trip as `time_call_round_trip` does, but against `call_server_thread` as the
/// first thread of a child process that shares dom0's image and holds the root endpoint: each direct
/// switch also loads the other process's cr3 (its own page table and PCID). The timed rounds follow
/// `CROSS_CALL_WARMUP` untimed ones, the first of which lets the child start. The child, waiting for
/// the next call, is killed afterwards, which returns its quota to dom0's container.
fn time_call_round_trip_cross_process() {
    let (image, pages) = image_range();
    fund("cross-process call server funding", 4 + 3 * pages);
    let sp = stack_top(&raw const CROSS_CALL_SERVER_STACK);
    check("new_process_with_endpoint (call server)", unsafe { sys_new_process_with_endpoint(image, pages, ENDPOINT, entry(call_server_thread), sp) });
    let call = |i: usize| {
        let reply = quiet_value("cross-process call_usize", unsafe { sys_call_usize(ENDPOINT, i) });
        if reply != i + 1 {
            log::error!("cross-process call_usize({}) replied {}", i, reply);
            unsafe { sys_debug_exit(1) };
        }
    };
    for i in 0..CROSS_CALL_WARMUP {
        call(i);
    }
    let start = unsafe { core::arch::x86_64::_rdtsc() };
    for i in 0..IPC_ROUNDS as usize {
        call(i);
    }
    let cycles = (unsafe { core::arch::x86_64::_rdtsc() } - start) / IPC_ROUNDS;
    log::info!("call round trip cross process: {} TSC cycles (2 syscalls, 2 direct switches with cr3 loads) over {} rounds", cycles, IPC_ROUNDS);
    check("kill_process(0) (call server child)", unsafe { sys_kill_process(0) });
}

/// Times one IPC round trip (send_empty, then receive_empty, each a rendezvous with `pong_thread`
/// and a thread switch) while only the two threads are runnable on this CPU.
fn time_ipc_round_trip() {
    let sp = (&raw const PONG_STACK) as usize + 64 * 1024 - 8;
    check("new_thread_with_endpoint (pong)", unsafe { sys_new_thread_with_endpoint(ENDPOINT, pong_thread as *const () as usize, sp) });
    let start = unsafe { core::arch::x86_64::_rdtsc() };
    for _ in 0..IPC_ROUNDS {
        quiet("ping send_empty", unsafe { sys_send_empty(ENDPOINT) });
        quiet("ping receive_empty", unsafe { sys_receive_empty(ENDPOINT) });
    }
    let cycles = (unsafe { core::arch::x86_64::_rdtsc() } - start) / IPC_ROUNDS;
    log::info!("IPC round trip: {} TSC cycles (4 syscalls, 2 thread switches) over {} rounds", cycles, IPC_ROUNDS);
}

/// A thread that only yields. It never touches its stack, so every timed thread shares one.
#[unsafe(naked)]
extern "C" fn yield_forever() -> ! {
    core::arch::naked_asm!("2:", "mov eax, {nr}", "syscall", "jmp 2b", nr = const NR_SCHEDULE);
}

/// Times `new_thread` over `TIMED_THREADS` creations and logs the best and the mean in TSC cycles.
fn time_new_thread() {
    check("alloc_quota_4k", unsafe { sys_alloc_quota_4k(TIMED_THREADS) });
    check("alloc_thread_quota_4k", unsafe { sys_alloc_thread_quota_4k(TIMED_THREADS) });
    let sp = (&raw const SPINNER_STACK) as usize + 64 * 1024 - 8;
    let (mut best, mut total) = (u64::MAX, 0);
    for _ in 0..TIMED_THREADS {
        let start = unsafe { core::arch::x86_64::_rdtsc() };
        let ret = unsafe { sys_new_thread(yield_forever as *const () as usize, sp) };
        let cycles = unsafe { core::arch::x86_64::_rdtsc() } - start;
        quiet("new_thread (timed)", ret);
        best = best.min(cycles);
        total += cycles;
    }
    log::info!("new_thread: best {} TSC cycles, mean {} over {} threads", best, total / TIMED_THREADS as u64, TIMED_THREADS);
}

/// Times a null syscall returning through `sysretq` and one forced through `iretq`, interleaved, and
/// logs the best round of each in TSC cycles per call.
fn time_syscall_returns() {
    let mut best = [u64::MAX; 2];
    for _ in 0..RETURN_ROUNDS {
        for (path, force_iret) in [false, true].into_iter().enumerate() {
            let start = unsafe { core::arch::x86_64::_rdtsc() };
            for _ in 0..RETURN_CALLS {
                unsafe { sys_debug_null(force_iret) };
            }
            let cycles = (unsafe { core::arch::x86_64::_rdtsc() } - start) / RETURN_CALLS;
            best[path] = best[path].min(cycles);
        }
    }
    log::info!("null syscall: {} TSC cycles returning through sysretq, {} through iretq", best[0], best[1]);
}

/// Times `MMAP_ROUNDS` rounds that map and touch `MMAP_PAGES` fresh 4K pages at `KILL_VA` and unmap
/// them, after one untimed round that builds the page tables, and logs the mean TSC cycles per page.
fn time_mmap_unmap() {
    // mmap_4k needs four 4K quota per page at hand and takes one per page, plus the page tables of
    // the first round, from the thread; unmap_4k refunds the pages to the container, so every round
    // first moves one quota per page back to the thread, untimed.
    fund("mmap timer funding", 3 * MMAP_PAGES + 3);
    let mut total = 0;
    for round in 0..=MMAP_ROUNDS {
        fund("mmap timer funding", MMAP_PAGES);
        let start = unsafe { core::arch::x86_64::_rdtsc() };
        map_and_touch("mmap_4k (timed)", MMAP_PAGES);
        quiet("unmap_4k (timed)", unsafe { sys_unmap_4k(KILL_VA, MMAP_PAGES) });
        if round > 0 {
            total += unsafe { core::arch::x86_64::_rdtsc() } - start;
        }
    }
    let cycles = total / (MMAP_ROUNDS * MMAP_PAGES as u64);
    log::info!("mmap+unmap 4K: {} TSC cycles per page over {} rounds", cycles, MMAP_ROUNDS);
}

/// Times mapping and touching `MMAP_ONLY_PAGES` fresh 4K pages without unmapping them, once with
/// `MMAP_PAGES` pages per mmap_4k and once with one page per call, and logs the mean TSC cycles per
/// page of each. The pages are unmapped afterwards, untimed.
fn time_mmap_only() {
    for (va, per_call) in [(MMAP_ONLY_VA[0], MMAP_PAGES), (MMAP_ONLY_VA[1], 1)] {
        // As in `time_mmap_unmap`: three extra quota per page of a call keep four at hand, plus one per
        // page and the page tables (an L1 per 512 pages, an L2, and slack), all moved to the thread
        // before the timed loop.
        fund("mmap-only timer funding", 3 * per_call + MMAP_ONLY_PAGES + MMAP_ONLY_PAGES / 512 + 3);
        let start = unsafe { core::arch::x86_64::_rdtsc() };
        for call in 0..MMAP_ONLY_PAGES / per_call {
            let base = va + call * per_call * 4096;
            quiet("mmap_4k (mmap-only)", unsafe { sys_mmap_4k(base, per_call) });
            for i in 0..per_call {
                let p = (base + i * 4096) as *mut u64;
                unsafe { p.write_volatile(PAGE_MAGIC ^ i as u64) };
                if unsafe { p.read_volatile() } != PAGE_MAGIC ^ i as u64 {
                    log::error!("mmap-only: page {} at {:#x} does not hold what was written", i, base);
                    unsafe { sys_debug_exit(1) };
                }
            }
        }
        let cycles = (unsafe { core::arch::x86_64::_rdtsc() } - start) / MMAP_ONLY_PAGES as u64;
        log::info!("mmap 4K: {} TSC cycles per page, {} pages per call, over {} pages", cycles, per_call, MMAP_ONLY_PAGES);
        quiet("unmap_4k (mmap-only)", unsafe { sys_unmap_4k(va, MMAP_ONLY_PAGES) });
    }
}

/// Client/server pairs of the parallel call timing: at most one per CPU.
const MAX_PAIRS: usize = 32;
/// dom0's descriptor of pair k's endpoint is `PAIR_ENDPOINT + k`; the pair's other threads hold it in
/// descriptor 0.
const PAIR_ENDPOINT: usize = 8;
/// Untimed call round trips of each pair before its timed window in each phase.
const PAIR_WARMUP: usize = 2_000;
/// TSC cycles from a pair's release to the deadline that ends its timed window, about 45 ms at the
/// 2.2 GHz TSC of the test machine. A window of fixed length rather than of fixed round trips: the pairs
/// at once share one deadline, so they stop together and time side by side however late each started.
const PAIR_WINDOW: u64 = 100_000_000;
/// Timed round trips between two deadline checks, so reading the TSC adds little to a round trip.
const PAIR_BATCH: u64 = 64;
/// The least share, in hundredths, of the concurrent phase's span in which every pair must be timing.
const PAIR_MIN_OVERLAP: u64 = 50;
/// Rounds the concurrent phase's window leaves each pair room for even if the pairs took turns, so that
/// a round far slower than a call round trip still ends the window together with the others, up to a
/// window of `PAIR_MAX_WINDOW` cycles.
const PAIR_MIN_ROUNDS: u64 = 32;
const PAIR_MAX_WINDOW: u64 = 20 * PAIR_WINDOW;
/// The phases dom0 releases a pair's client into, in this order (dom0 may skip any of them): the call
/// timing alone and with all pairs at once, then in the cross-process mode the start of its child server
/// and the same two timing phases against it; the parallel mmap timing's map+unmap and mmap-only modes in
/// dom0, then the start of its mmap child, the same two modes in the child, and the child's mmap-only mode
/// within the per-CPU page cache; and stop.
const PHASE_ALONE: usize = 1;
const PHASE_CONCURRENT: usize = 2;
const PHASE_XPROC_SETUP: usize = 3;
const PHASE_XPROC_ALONE: usize = 4;
const PHASE_XPROC_CONCURRENT: usize = 5;
const PHASE_MMAP_ALONE: usize = 6;
const PHASE_MMAP_CONCURRENT: usize = 7;
const PHASE_MMAP_ONLY_ALONE: usize = 8;
const PHASE_MMAP_ONLY_CONCURRENT: usize = 9;
const PHASE_MMAP_XPROC_SETUP: usize = 10;
const PHASE_MMAP_XPROC_ALONE: usize = 11;
const PHASE_MMAP_XPROC_CONCURRENT: usize = 12;
const PHASE_MMAP_ONLY_XPROC_ALONE: usize = 13;
const PHASE_MMAP_ONLY_XPROC_CONCURRENT: usize = 14;
const PHASE_MMAP_CACHED_XPROC_ALONE: usize = 15;
const PHASE_MMAP_CACHED_XPROC_CONCURRENT: usize = 16;
const PHASE_STOP: usize = 17;
/// The descriptor where each client of the cross-process mode, dom0 as client 0 included, creates the
/// endpoint of its child server, which holds it in descriptor 0. The pair's endpoint cannot serve: the
/// same-process server stays blocked in receive_call on it.
const XPROC_ENDPOINT: usize = 1;
/// The same for the child of the parallel mmap timing's cross-process modes: a descriptor no earlier
/// child used, since a killed child's endpoint stays in its client's descriptor.
const MMAP_XPROC_ENDPOINT: usize = 5;
/// The parallel timings this build runs, from the build environment: `call`, `mmap`, or both
/// (`VERIFLAT_PARALLEL=call,mmap`); `call` when unset.
const PARALLEL: &str = match option_env!("VERIFLAT_PARALLEL") {
    Some(modes) => modes,
    None => "call",
};

/// One client/server pair of the parallel call timing, alone on its cache lines, so the pairs share
/// nothing but the kernel.
#[repr(C, align(64))]
struct Pair {
    /// One plus the CPU the client, and the server of the current mode, first ran on; 0 until it ran.
    client_cpu: AtomicUsize,
    server_cpu: AtomicUsize,
    /// Set once the client's server of the current mode blocks in receive_call.
    ready: AtomicBool,
    /// The phase dom0 released the client into, and the last phase the pair finished.
    go: AtomicUsize,
    done: AtomicUsize,
    /// The TSC that ends the timed window of the phase dom0 released the client into, published
    /// before the release.
    deadline: AtomicU64,
    /// The TSC before the first and after the last timed round trip of the last finished phase, its
    /// timed round trips, and the TSC cycles per round trip.
    begin: AtomicU64,
    end: AtomicU64,
    rounds: AtomicU64,
    cycles: AtomicU64,
}

impl Pair {
    const fn new() -> Self {
        Pair {
            client_cpu: AtomicUsize::new(0), server_cpu: AtomicUsize::new(0), ready: AtomicBool::new(false), go: AtomicUsize::new(0),
            done: AtomicUsize::new(0), deadline: AtomicU64::new(0), begin: AtomicU64::new(0), end: AtomicU64::new(0),
            rounds: AtomicU64::new(0), cycles: AtomicU64::new(0),
        }
    }
}

static PAIRS: [Pair; MAX_PAIRS] = [const { Pair::new() }; MAX_PAIRS];
/// The pair whose threads dom0 is creating: each new thread of a pair reads it once it runs.
static NEXT_PAIR: AtomicUsize = AtomicUsize::new(0);
static mut PAIR_CLIENT_STACKS: [[u8; 16 * 1024]; MAX_PAIRS] = [[0; 16 * 1024]; MAX_PAIRS];
static mut PAIR_SERVER_STACKS: [[u8; 16 * 1024]; MAX_PAIRS] = [[0; 16 * 1024]; MAX_PAIRS];
/// Stacks of the cross-process mode's child servers, in dom0's image that every child shares.
static mut PAIR_CHILD_STACKS: [[u8; 16 * 1024]; MAX_PAIRS] = [[0; 16 * 1024]; MAX_PAIRS];

/// A fraction in hundredths, displayed with two decimals.
struct Hundredths(u64);

impl core::fmt::Display for Hundredths {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "{}.{:02}", self.0 / 100, self.0 % 100)
    }
}

/// `num / den` in hundredths, rounded.
fn hundredths(num: u64, den: u64) -> u64 {
    (200 * num + den) / (2 * den)
}

/// Server of a parallel call pair, holding the pair's endpoint in descriptor 0: a thread of dom0, or in
/// the cross-process mode the first thread of a child process that shares dom0's image. Records its CPU
/// at the first call and replies each value plus one, forever.
extern "C" fn pair_server() -> ! {
    let pair = &PAIRS[NEXT_PAIR.load(Ordering::SeqCst)];
    let mut value = quiet_value("pair server receive_call", unsafe { sys_receive_call(0) });
    pair.server_cpu.store(current_cpu() + 1, Ordering::SeqCst);
    loop {
        value = quiet_value("pair server reply_and_receive_usize", unsafe { sys_reply_and_receive_usize(0, value + 1) });
    }
}

/// The 4K quota a client of the cross-process mode moves to its thread: one for its child's endpoint
/// and `4 + 3 * pages` for the child, which shares dom0's image of `pages` pages.
fn pair_child_quota() -> usize {
    1 + 4 + 3 * image_range().1
}

/// Starts a child of pair `k` from the pair's client on CPU `k`, once dom0's process holds the quota: a
/// fresh endpoint in the client's descriptor `endpoint`, and a child process holding it in descriptor 0,
/// whose first thread, `server` queued on the creator's shard, runs until it blocks.
fn start_pair_child(k: usize, endpoint: usize, server: extern "C" fn() -> !) {
    quiet("pair child alloc_thread_quota_4k", unsafe { sys_alloc_thread_quota_4k(pair_child_quota()) });
    quiet("pair child new_endpoint", unsafe { sys_new_endpoint(endpoint) });
    let (image, pages) = image_range();
    let sp = stack_top(unsafe { &raw const PAIR_CHILD_STACKS[k] });
    quiet("pair child new_process_with_endpoint", unsafe { sys_new_process_with_endpoint(image, pages, endpoint, entry(server), sp) });
    // The child's first thread, the only other thread of this CPU's shard, runs until it blocks.
    unsafe { sys_schedule() };
}

/// Client of parallel call pair k >= 1, holding the pair's endpoint in descriptor 0. Once CPU k pulled
/// it, it records that CPU, creates its server there, and lets the server block in receive_call; then
/// it serves each phase dom0 releases it into, spinning in between: it times the pair in the call
/// phases, starts its child server and times the pair against it in the cross-process ones, runs the
/// parallel mmap timing's worker k in dom0's mmap phases, and starts its mmap child and has it run
/// worker k in the cross-process mmap phases. dom0 skips the phases of the timings it does not run and
/// the cross-process ones of the pairs its quota does not cover. At the stop it yields until its CPU
/// goes Off.
extern "C" fn pair_client() -> ! {
    let k = NEXT_PAIR.load(Ordering::SeqCst);
    let pair = &PAIRS[k];
    pair.client_cpu.store(current_cpu() + 1, Ordering::SeqCst);
    fund("pair client funding", 1);
    let sp = stack_top(unsafe { &raw const PAIR_SERVER_STACKS[k] });
    quiet("pair client new_thread_with_endpoint (server)", unsafe { sys_new_thread_with_endpoint(0, entry(pair_server), sp) });
    // The server, the only other thread of this CPU's shard, runs until it blocks.
    unsafe { sys_schedule() };
    pair.ready.store(true, Ordering::SeqCst);
    // dom0 releases the next phase only once this client finished the last one, so none is missed.
    let mut last = 0;
    loop {
        let phase = loop {
            let go = pair.go.load(Ordering::SeqCst);
            if go != last {
                break go;
            }
            core::hint::spin_loop();
        };
        last = phase;
        match phase {
            PHASE_ALONE | PHASE_CONCURRENT => time_pair(k, 0, phase),
            PHASE_XPROC_SETUP => {
                start_pair_child(k, XPROC_ENDPOINT, pair_server);
                pair.ready.store(true, Ordering::SeqCst);
            }
            PHASE_XPROC_ALONE | PHASE_XPROC_CONCURRENT => time_pair(k, XPROC_ENDPOINT, phase),
            PHASE_MMAP_ALONE | PHASE_MMAP_CONCURRENT | PHASE_MMAP_ONLY_ALONE | PHASE_MMAP_ONLY_CONCURRENT => time_mmap(k, phase),
            PHASE_MMAP_XPROC_SETUP => {
                start_pair_child(k, MMAP_XPROC_ENDPOINT, mmap_server);
                pair.ready.store(true, Ordering::SeqCst);
            }
            PHASE_MMAP_XPROC_ALONE..=PHASE_MMAP_CACHED_XPROC_CONCURRENT => call_mmap_child(phase),
            PHASE_STOP => break,
            _ => {
                log::error!("pair {}: released into unknown phase {}", k, phase);
                unsafe { sys_debug_exit(1) };
            }
        }
    }
    // dom0 asked this CPU to go Off: the schedule check of a yield takes it Off and requeues this thread
    // on its shard.
    loop {
        unsafe { sys_schedule() };
    }
}

/// Times call round trips of pair `k` on `endpoint` after `PAIR_WARMUP` untimed ones, in batches of
/// `PAIR_BATCH` until the TSC reaches the pair's deadline (at least one batch), checks each reply and
/// that the pair is still on CPU `k`, and records the result of `phase`.
fn time_pair(k: usize, endpoint: usize, phase: usize) {
    let pair = &PAIRS[k];
    let deadline = pair.deadline.load(Ordering::SeqCst);
    let call = |i: usize| {
        let reply = quiet_value("pair call_usize", unsafe { sys_call_usize(endpoint, i) });
        if reply != i + 1 {
            log::error!("pair {}: call_usize({}) replied {}", k, i, reply);
            unsafe { sys_debug_exit(1) };
        }
    };
    for i in 0..PAIR_WARMUP {
        call(i);
    }
    let begin = unsafe { core::arch::x86_64::_rdtsc() };
    let mut rounds = 0;
    let end = loop {
        for i in 0..PAIR_BATCH as usize {
            call(i);
        }
        rounds += PAIR_BATCH;
        let now = unsafe { core::arch::x86_64::_rdtsc() };
        if now >= deadline {
            break now;
        }
    };
    if current_cpu() != k {
        log::error!("pair {} moved to CPU {}", k, current_cpu());
        unsafe { sys_debug_exit(1) };
    }
    pair.begin.store(begin, Ordering::SeqCst);
    pair.end.store(end, Ordering::SeqCst);
    pair.rounds.store(rounds, Ordering::SeqCst);
    pair.cycles.store((end - begin) / rounds, Ordering::SeqCst);
    pair.done.store(phase, Ordering::SeqCst);
}

/// Times call round trips of one client/server pair per CPU in two modes (`time_pairs`): first with each
/// server a thread of dom0, then, in the cross-process mode, with each server the first thread of a child
/// process that shares dom0's image, so every round trip also loads both cr3s. Pair 0 is dom0 itself with
/// its server on CPU 0. The client of pair k comes to CPU k when dom0 brings that CPU online, which pulls
/// the only queued thread, and creates its server, and later its child, there; each round trip is a
/// direct switch between the pair's threads, so no pair leaves its CPU. The cross-process mode times as
/// many pairs as dom0's container quota funds children for. Afterwards the children are killed. Then,
/// when this build runs it (`PARALLEL`), the parallel mmap timing (`time_parallel_mmap`) uses the same
/// clients as its workers; without `call` in `PARALLEL` the call timing is skipped and the pairs only
/// place the workers. Finally every CPU but 0 is Off again.
fn time_parallel_call() {
    // Every CPU but 0 is Off, so an offline request fails without effect until the first missing CPU.
    let mut n = 1;
    while n < MAX_PAIRS {
        let ret = unsafe { sys_cpu_offline_request(n) };
        if error_name(ret) == "InvalidArgument" {
            break;
        }
        expect_quiet("cpu_offline_request to count the CPUs", ret, "ErrorCpuAlreadyOff");
        n += 1;
    }
    // The endpoints, the n - 1 clients, and server 0; each client funds its own server.
    fund("parallel call funding", 2 * n);
    for k in 0..n {
        quiet("new_endpoint (pair)", unsafe { sys_new_endpoint(PAIR_ENDPOINT + k) });
    }
    NEXT_PAIR.store(0, Ordering::SeqCst);
    let sp = stack_top(unsafe { &raw const PAIR_SERVER_STACKS[0] });
    quiet("new_thread_with_endpoint (pair server 0)", unsafe { sys_new_thread_with_endpoint(PAIR_ENDPOINT, entry(pair_server), sp) });
    // Server 0 runs until it blocks, which empties CPU 0's shard: a CPU coming online pulls the head
    // of the lowest-numbered other nonempty shard, which must be the next client.
    unsafe { sys_schedule() };
    for k in 1..n {
        let pair = &PAIRS[k];
        NEXT_PAIR.store(k, Ordering::SeqCst);
        let sp = stack_top(unsafe { &raw const PAIR_CLIENT_STACKS[k] });
        quiet("new_thread_with_endpoint (pair client)", unsafe { sys_new_thread_with_endpoint(PAIR_ENDPOINT + k, entry(pair_client), sp) });
        quiet("cpu_online (pair client)", unsafe { sys_cpu_online(k) });
        wait_for("a pair client", || pair.client_cpu.load(Ordering::SeqCst) != 0);
        let cpu = pair.client_cpu.load(Ordering::SeqCst) - 1;
        if cpu != k {
            log::error!("the client of pair {} ran on CPU {}", k, cpu);
            unsafe { sys_debug_exit(1) };
        }
        wait_for("a pair server to block", || pair.ready.load(Ordering::SeqCst));
    }
    if PARALLEL.contains("call") {
        time_pairs(n, [PHASE_ALONE, PHASE_CONCURRENT], "parallel_call", true, &|phase| time_pair(0, PAIR_ENDPOINT, phase));
        let m = start_pair_children(n, XPROC_ENDPOINT, pair_server, PHASE_XPROC_SETUP, "parallel_call_xproc");
        time_pairs(m, [PHASE_XPROC_ALONE, PHASE_XPROC_CONCURRENT], "parallel_call_xproc", true, &|phase| time_pair(0, XPROC_ENDPOINT, phase));
        kill_pair_children(m);
    }
    if PARALLEL.contains("mmap") {
        time_parallel_mmap(n);
    }

    // The clients take their CPUs Off, so the timings after this one run on CPU 0 alone.
    for k in 1..n {
        quiet("cpu_offline_request (pair client)", unsafe { sys_cpu_offline_request(k) });
        PAIRS[k].go.store(PHASE_STOP, Ordering::SeqCst);
    }
    for k in 1..n {
        let start = unsafe { core::arch::x86_64::_rdtsc() };
        loop {
            let ret = unsafe { sys_cpu_offline_request(k) };
            if error_name(ret) == "ErrorCpuAlreadyOff" {
                break;
            }
            if ret < 0 || unsafe { core::arch::x86_64::_rdtsc() } - start > WAIT_LIMIT {
                expect_error("cpu_offline_request until a pair CPU is Off", ret, "ErrorCpuAlreadyOff");
            }
            core::hint::spin_loop();
        }
    }
}

/// Times the first `n` pairs in one mode, dom0 doing pair 0's share of a phase with `run0`: each pair
/// alone in the first of `phases` while the other clients spin, then all pairs at once in the second,
/// and logs with `prefix` per CPU the TSC cycles per round (a call round trip, or a round of the
/// parallel mmap timing) of both phases and their ratio, then a summary. Each pair alone times a window
/// of `PAIR_WINDOW` cycles from its release; the pairs at once share one deadline, at least as far.
/// Fails unless every server (or mmap worker) ran on its pair's CPU and, when `overlap_fatal`, every
/// pair was timing in at least `PAIR_MIN_OVERLAP` hundredths of the concurrent phase's span; otherwise a
/// shorter overlap is only logged as an error.
fn time_pairs(n: usize, [alone_phase, concurrent_phase]: [usize; 2], prefix: &str, overlap_fatal: bool, run0: &dyn Fn(usize)) {
    let (mut alone, mut alone_rounds) = ([0; MAX_PAIRS], [0; MAX_PAIRS]);
    for k in 0..n {
        let pair = &PAIRS[k];
        pair.deadline.store(unsafe { core::arch::x86_64::_rdtsc() } + PAIR_WINDOW, Ordering::SeqCst);
        if k == 0 {
            run0(alone_phase);
        } else {
            pair.go.store(alone_phase, Ordering::SeqCst);
            wait_for("a pair alone", || pair.done.load(Ordering::SeqCst) == alone_phase);
        }
        (alone[k], alone_rounds[k]) = (pair.cycles.load(Ordering::SeqCst), pair.rounds.load(Ordering::SeqCst));
        let server_cpu = pair.server_cpu.load(Ordering::SeqCst);
        if server_cpu != k + 1 {
            log::error!("{}: the server of pair {} ran on CPU {}", prefix, k, server_cpu as isize - 1);
            unsafe { sys_debug_exit(1) };
        }
    }
    // One deadline for all pairs, published before any release: `PAIR_WINDOW` away, or further (up to
    // `PAIR_MAX_WINDOW`) when needed for `PAIR_MIN_ROUNDS` rounds of each pair even if the pairs took
    // turns at their alone pace.
    let window = (PAIR_MIN_ROUNDS * n as u64 * alone[..n].iter().max().unwrap()).clamp(PAIR_WINDOW, PAIR_MAX_WINDOW);
    let deadline = unsafe { core::arch::x86_64::_rdtsc() } + window;
    for pair in &PAIRS[..n] {
        pair.deadline.store(deadline, Ordering::SeqCst);
    }
    for pair in &PAIRS[1..n] {
        pair.go.store(concurrent_phase, Ordering::SeqCst);
    }
    run0(concurrent_phase);
    for pair in &PAIRS[1..n] {
        wait_for("the pairs at once", || pair.done.load(Ordering::SeqCst) == concurrent_phase);
    }

    let mut ratios = [0; MAX_PAIRS];
    let (mut min_begin, mut max_begin, mut min_end, mut max_end) = (u64::MAX, 0, u64::MAX, 0);
    let (mut min_conc_rounds, mut max_conc_rounds) = (u64::MAX, 0);
    for k in 0..n {
        let pair = &PAIRS[k];
        let (begin, end, conc) = (pair.begin.load(Ordering::SeqCst), pair.end.load(Ordering::SeqCst), pair.cycles.load(Ordering::SeqCst));
        (min_begin, max_begin, min_end, max_end) = (min_begin.min(begin), max_begin.max(begin), min_end.min(end), max_end.max(end));
        let rounds = pair.rounds.load(Ordering::SeqCst);
        (min_conc_rounds, max_conc_rounds) = (min_conc_rounds.min(rounds), max_conc_rounds.max(rounds));
        ratios[k] = hundredths(conc, alone[k]);
        log::info!("{} cpu={} alone={} conc={} ratio={}", prefix, k, alone[k], conc, Hundredths(ratios[k]));
    }
    // The share of the concurrent phase's span in which every pair was timing.
    let overlap = if max_begin < min_end { hundredths(min_end - max_begin, max_end - min_begin) } else { 0 };
    let ratios = &mut ratios[..n];
    ratios.sort_unstable();
    let median = (ratios[(n - 1) / 2] + ratios[n / 2]) / 2;
    let alone_rounds = &alone_rounds[..n];
    let (min_alone_rounds, max_alone_rounds) = (alone_rounds.iter().min().unwrap(), alone_rounds.iter().max().unwrap());
    log::info!(
        "{} summary n={} min_ratio={} max_ratio={} median_ratio={} overlap={} (rounds per pair: alone {}..{}, conc {}..{})",
        prefix, n, Hundredths(ratios[0]), Hundredths(ratios[n - 1]), Hundredths(median), Hundredths(overlap), min_alone_rounds,
        max_alone_rounds, min_conc_rounds, max_conc_rounds
    );
    if overlap < PAIR_MIN_OVERLAP {
        log::error!(
            "{}: the concurrent pairs overlapped in only {} of their span: last begin {}, first end {}",
            prefix, Hundredths(overlap), max_begin, min_end
        );
        if overlap_fatal {
            unsafe { sys_debug_exit(1) };
        }
    }
}

/// Starts a child of each of the first pairs that dom0's container quota covers, at most `n`, from the
/// pair's client, as `start_pair_child` does with `endpoint` and `server`: dom0 starts pair 0's itself
/// and releases each other client into `setup_phase` in turn. Logs with `prefix` how many pairs got one,
/// and returns that number.
fn start_pair_children(n: usize, endpoint: usize, server: extern "C" fn() -> !, setup_phase: usize, prefix: &str) -> usize {
    // dom0's process takes the children's quota from its container, for as many pairs as it covers.
    let quota = pair_child_quota();
    let mut m = n;
    let mut ret = unsafe { sys_alloc_quota_4k(m * quota) };
    while ret < 0 && m > 1 {
        expect_quiet("alloc_quota_4k (pair children)", ret, "ErrorContainerQuotaInsufficient");
        m -= 1;
        ret = unsafe { sys_alloc_quota_4k(m * quota) };
    }
    quiet("alloc_quota_4k (pair children)", ret);
    log::info!("{} funding: {} 4K quota per pair for {} of {} pairs", prefix, quota, m, n);
    // The pairs start their children in turn, as their servers, so each child finds its pair in
    // `NEXT_PAIR`. The same-process servers stay blocked on the pair endpoints.
    NEXT_PAIR.store(0, Ordering::SeqCst);
    PAIRS[0].server_cpu.store(0, Ordering::SeqCst);
    start_pair_child(0, endpoint, server);
    for k in 1..m {
        let pair = &PAIRS[k];
        pair.server_cpu.store(0, Ordering::SeqCst);
        pair.ready.store(false, Ordering::SeqCst);
        NEXT_PAIR.store(k, Ordering::SeqCst);
        pair.go.store(setup_phase, Ordering::SeqCst);
        wait_for("a pair child to block", || pair.ready.load(Ordering::SeqCst));
    }
    m
}

/// Kills the `m` pair children, each waiting for its next call, which returns their quota to dom0's
/// container.
fn kill_pair_children(m: usize) {
    for _ in 0..m {
        quiet("kill_process(0) (pair child)", unsafe { sys_kill_process(0) });
    }
    expect_quiet("kill_process(0) after the pair children", unsafe { sys_kill_process(0) }, "ErrorInvalidChild");
}

/// The parallel mmap timing's regions. In the map+unmap modes worker k maps, touches, and unmaps one 4K
/// page at `PAR_MMAP_VA + k * PAR_MMAP_STRIDE`, alone in its 2M window (its own L2 entry and L1 table);
/// the windows of neighbouring workers are 16M apart, so each worker's L2 entry has its own cache line.
const PAR_MMAP_VA: usize = 0xc0_8000_0000;
const PAR_MMAP_STRIDE: usize = 1 << 24;
/// In the mmap-only modes worker k maps and touches a fresh 4K page each round, upwards from
/// `PAR_ONLY_VA + k * PAR_ONLY_STRIDE` (four 2M windows, their L2 entries in a cache line of their own),
/// and unmaps the whole region, untimed, once it is full or the container runs out of quota.
const PAR_ONLY_VA: usize = 0xc0_c000_0000;
const PAR_ONLY_STRIDE: usize = 1 << 24;
const PAR_ONLY_PAGES: usize = 2048;
/// The cross-process cached mode is the mmap-only mode with a region small enough that, after the first
/// region unmap, the pages it maps and unmaps stay in the per-CPU page cache: the cache gives pages to the
/// global pool only once it holds `ALLOCATOR_MAX_WATERMARK` (4096) and takes them from it only when empty,
/// so a region of this size never touches the global pool, which the mmap-only mode visits every 64 pages
/// until its first region unmap.
const PAR_CACHED_PAGES: usize = 128;
/// 4K quota a worker moves to its thread at a time, untimed.
const PAR_FUND: usize = 512;
/// Thread quota a worker keeps on top of the four one mmap_4k of a page needs at hand: it does not count
/// the page tables its mappings build, fewer than this many over the whole timing.
const PAR_TABLE_SLACK: usize = 16;
/// Untimed rounds before the timed window of each alone phase, cut short after an eighth of the window.
const PAR_WARMUP: usize = 16;
/// Timed rounds a worker alone runs past its deadline if needed, for rounds slower than the window.
const PAR_MIN_ALONE_ROUNDS: u64 = 8;
/// Per worker, the 4K quota the worker's thread holds by its own count, carried from one phase to the
/// next, and the region unmaps the container's quota forced early in the current mode.
static PAR_QUOTA: [AtomicUsize; MAX_PAIRS] = [const { AtomicUsize::new(0) }; MAX_PAIRS];
static PAR_SHORT: [AtomicUsize; MAX_PAIRS] = [const { AtomicUsize::new(0) }; MAX_PAIRS];

/// Times one worker per CPU (`time_pairs`) looping over `mmap_4k` of one page in four modes: first with
/// worker k a thread of dom0 on CPU k (dom0 itself for worker 0, a pair's client otherwise), each round
/// also unmapping the page and then mapping a fresh one without unmapping; then with worker k the first
/// thread of a child process of pair k's client, sharing dom0's image, so each worker has its own page
/// table and PCID, in the same two modes, for as many pairs as dom0's container quota funds children
/// for. The children run their phases while their clients wait in a call to them, and are killed
/// afterwards. A round's TSC cycles leave out the quota moves and region unmaps between rounds.
fn time_parallel_mmap(n: usize) {
    // dom0 builds the page directory of each region's GiB, so that no timed mmap_4k of dom0 takes the
    // page table's write lock; each worker builds its own L1 tables in its warm-up rounds.
    fund("parallel mmap page directories", 16);
    for va in [PAR_MMAP_VA, PAR_ONLY_VA] {
        quiet("mmap_4k (parallel mmap page directory)", unsafe { sys_mmap_4k(va, 1) });
        quiet("unmap_4k (parallel mmap page directory)", unsafe { sys_unmap_4k(va, 1) });
    }
    let in_dom0 = |phase: usize| time_mmap(0, phase);
    time_pairs(n, [PHASE_MMAP_ALONE, PHASE_MMAP_CONCURRENT], "parallel_mmap_same", false, &in_dom0);
    time_pairs(n, [PHASE_MMAP_ONLY_ALONE, PHASE_MMAP_ONLY_CONCURRENT], "parallel_mmap_only_same", false, &in_dom0);
    report_quota_short("parallel_mmap_only_same", n, PAR_ONLY_PAGES);
    // The children's threads start without quota of their own.
    for quota in &PAR_QUOTA {
        quota.store(0, Ordering::SeqCst);
    }
    let m = start_pair_children(n, MMAP_XPROC_ENDPOINT, mmap_server, PHASE_MMAP_XPROC_SETUP, "parallel_mmap_xproc");
    time_pairs(m, [PHASE_MMAP_XPROC_ALONE, PHASE_MMAP_XPROC_CONCURRENT], "parallel_mmap_xproc", false, &call_mmap_child);
    time_pairs(m, [PHASE_MMAP_ONLY_XPROC_ALONE, PHASE_MMAP_ONLY_XPROC_CONCURRENT], "parallel_mmap_only_xproc", false, &call_mmap_child);
    report_quota_short("parallel_mmap_only_xproc", m, PAR_ONLY_PAGES);
    time_pairs(m, [PHASE_MMAP_CACHED_XPROC_ALONE, PHASE_MMAP_CACHED_XPROC_CONCURRENT], "parallel_mmap_cached_xproc", false, &call_mmap_child);
    report_quota_short("parallel_mmap_cached_xproc", m, PAR_CACHED_PAGES);
    kill_pair_children(m);
}

/// Logs with `prefix` the region unmaps that the container's quota forced early in the last mode of `n`
/// workers with regions of `region` pages, and resets their count.
fn report_quota_short(prefix: &str, n: usize, region: usize) {
    let short: usize = PAR_SHORT[..n].iter().map(|short| short.swap(0, Ordering::SeqCst)).sum();
    log::info!("{} quota: region {} pages per worker, {} early region unmaps for want of container quota", prefix, region, short);
}

/// First thread of a child of the parallel mmap timing's cross-process modes, holding its client's
/// endpoint in descriptor 0: runs worker k, its pair, in this process in each phase its client calls it
/// with, and replies the phase once done.
extern "C" fn mmap_server() -> ! {
    let k = NEXT_PAIR.load(Ordering::SeqCst);
    let mut phase = quiet_value("mmap server receive_call", unsafe { sys_receive_call(0) });
    loop {
        time_mmap(k, phase);
        phase = quiet_value("mmap server reply_and_receive_usize", unsafe { sys_reply_and_receive_usize(0, phase) });
    }
}

/// Has the calling client's mmap child run `phase`, waiting in the call until it is done.
fn call_mmap_child(phase: usize) {
    let reply = quiet_value("call_usize (mmap child)", unsafe { sys_call_usize(MMAP_XPROC_ENDPOINT, phase) });
    if reply != phase {
        log::error!("the mmap child replied {} to phase {}", reply, phase);
        unsafe { sys_debug_exit(1) };
    }
}

/// Runs worker `k` of the parallel mmap timing in `phase`, in the calling process (dom0, or in the
/// cross-process modes the worker's child): alone, `PAR_WARMUP` untimed rounds first; then timed rounds
/// until the TSC reaches the pair's deadline (alone, at least `PAR_MIN_ALONE_ROUNDS`; at once, at least
/// one). Checks that the worker is still on CPU `k`, unmaps what is left mapped, and records the result
/// as `time_pair` does, the cycles per round without the cycles spent between rounds.
fn time_mmap(k: usize, phase: usize) {
    let pair = &PAIRS[k];
    pair.server_cpu.store(current_cpu() + 1, Ordering::SeqCst);
    let deadline = pair.deadline.load(Ordering::SeqCst);
    let unmaps = matches!(phase, PHASE_MMAP_ALONE | PHASE_MMAP_CONCURRENT | PHASE_MMAP_XPROC_ALONE | PHASE_MMAP_XPROC_CONCURRENT);
    let alone = matches!(
        phase,
        PHASE_MMAP_ALONE | PHASE_MMAP_ONLY_ALONE | PHASE_MMAP_XPROC_ALONE | PHASE_MMAP_ONLY_XPROC_ALONE | PHASE_MMAP_CACHED_XPROC_ALONE
    );
    let region = if matches!(phase, PHASE_MMAP_CACHED_XPROC_ALONE | PHASE_MMAP_CACHED_XPROC_CONCURRENT) { PAR_CACHED_PAGES } else { PAR_ONLY_PAGES };
    let base = if unmaps { PAR_MMAP_VA + k * PAR_MMAP_STRIDE } else { PAR_ONLY_VA + k * PAR_ONLY_STRIDE };
    let quota = PAR_QUOTA[k].load(Ordering::SeqCst);
    let mut worker = MmapWorker { base, region, unmaps, mapped: 0, quota, untimed: 0, short: 0 };
    // Only alone: the phase at once follows the same worker's alone phase in the same region.
    let start = unsafe { core::arch::x86_64::_rdtsc() };
    let warmup_end = start + deadline.saturating_sub(start) / 8;
    for _ in 0..if alone { PAR_WARMUP } else { 0 } {
        worker.round();
        if unsafe { core::arch::x86_64::_rdtsc() } >= warmup_end {
            break;
        }
    }
    worker.untimed = 0;
    let begin = unsafe { core::arch::x86_64::_rdtsc() };
    let mut rounds = 0;
    let end = loop {
        worker.round();
        rounds += 1;
        let now = unsafe { core::arch::x86_64::_rdtsc() };
        if now >= deadline && (!alone || rounds >= PAR_MIN_ALONE_ROUNDS) {
            break now;
        }
    };
    if current_cpu() != k {
        log::error!("mmap worker {} moved to CPU {}", k, current_cpu());
        unsafe { sys_debug_exit(1) };
    }
    if worker.mapped > 0 {
        worker.unmap_region();
    }
    PAR_QUOTA[k].store(worker.quota, Ordering::SeqCst);
    PAR_SHORT[k].fetch_add(worker.short, Ordering::SeqCst);
    pair.begin.store(begin, Ordering::SeqCst);
    pair.end.store(end, Ordering::SeqCst);
    pair.rounds.store(rounds, Ordering::SeqCst);
    pair.cycles.store((end - begin - worker.untimed) / rounds, Ordering::SeqCst);
    pair.done.store(phase, Ordering::SeqCst);
}

/// A worker of the parallel mmap timing within one phase: its region's start and size in pages, its
/// pages mapped there, its thread's 4K quota by its own count, the TSC cycles spent between rounds, and
/// its early region unmaps.
struct MmapWorker {
    base: usize,
    region: usize,
    unmaps: bool,
    mapped: usize,
    quota: usize,
    untimed: u64,
    short: usize,
}

impl MmapWorker {
    /// One round: maps the next 4K page of the region, writes and reads it back, and in the map+unmap
    /// modes unmaps it. Before, when needed, it unmaps a full region and tops up the thread quota,
    /// counting the cycles as `untimed`.
    fn round(&mut self) {
        if self.quota < 4 + PAR_TABLE_SLACK || self.mapped == self.region {
            let start = unsafe { core::arch::x86_64::_rdtsc() };
            self.make_room();
            self.untimed += unsafe { core::arch::x86_64::_rdtsc() } - start;
        }
        let va = self.base + self.mapped * 4096;
        quiet("parallel mmap_4k", unsafe { sys_mmap_4k(va, 1) });
        self.quota -= 1;
        let (p, value) = (va as *mut u64, PAGE_MAGIC ^ va as u64);
        unsafe { p.write_volatile(value) };
        if unsafe { p.read_volatile() } != value {
            log::error!("parallel mmap: the page at {:#x} does not hold what was written", va);
            unsafe { sys_debug_exit(1) };
        }
        if self.unmaps {
            quiet("parallel unmap_4k", retry_lock_order(|| unsafe { sys_unmap_4k(va, 1) }));
        } else {
            self.mapped += 1;
        }
    }

    /// Unmaps a full region, then moves `PAR_FUND` quota to the thread until it holds enough; when the
    /// container lacks it, unmaps the region early, which refunds its pages to the container.
    fn make_room(&mut self) {
        if self.mapped == self.region {
            self.unmap_region();
        }
        while self.quota < 4 + PAR_TABLE_SLACK {
            if try_fund(PAR_FUND) {
                self.quota += PAR_FUND;
            } else if self.mapped > 0 {
                self.short += 1;
                self.unmap_region();
            } else {
                log::error!("parallel mmap: the container holds less than {} 4K quota", PAR_FUND);
                unsafe { sys_debug_exit(1) };
            }
        }
    }

    fn unmap_region(&mut self) {
        quiet("parallel unmap_4k (region)", retry_lock_order(|| unsafe { sys_unmap_4k(self.base, self.mapped) }));
        self.mapped = 0;
    }
}

/// Moves `amount` 4K quota from the container through the calling process to the calling thread, as
/// `fund` does, unless the container holds less: then it moves nothing and returns false.
fn try_fund(amount: usize) -> bool {
    let ret = retry_lock_order(|| unsafe { sys_alloc_quota_4k(amount) });
    if error_name(ret) == "ErrorContainerQuotaInsufficient" {
        return false;
    }
    quiet("parallel mmap alloc_quota_4k", ret);
    quiet("parallel mmap alloc_thread_quota_4k", unsafe { sys_alloc_thread_quota_4k(amount) });
    true
}

/// Repeats `syscall`, one that write-locks the caller's container, while it fails with
/// ErrorContainerLockOrderConflict: a child's request fails at once while a thread of dom0 holds that lock.
fn retry_lock_order(syscall: impl Fn() -> isize) -> isize {
    let start = unsafe { core::arch::x86_64::_rdtsc() };
    loop {
        let ret = syscall();
        if ret >= 0 || error_name(ret) != "ErrorContainerLockOrderConflict" || unsafe { core::arch::x86_64::_rdtsc() } - start > WAIT_LIMIT {
            return ret;
        }
        core::hint::spin_loop();
    }
}

/// Retries `online` while it fails with `ErrorCpuNotOff`, until the CPU has gone Off and is back.
fn online_after_offline(name: &str, online: impl Fn() -> isize) {
    let start = unsafe { core::arch::x86_64::_rdtsc() };
    loop {
        let ret = online();
        if ret == 0 {
            return;
        }
        if error_name(ret) != "ErrorCpuNotOff" || unsafe { core::arch::x86_64::_rdtsc() } - start > WAIT_LIMIT {
            check(name, ret);
        }
        unsafe { sys_schedule() };
    }
}

// ---- 9. kill_process ----

/// Set once dom0 retires its helper threads: each then serves one call and exits.
static RETIRE: AtomicBool = AtomicBool::new(false);
/// Helper threads that `retire_when_asked` on the root endpoint, and on dom0's new endpoint.
const ROOT_ENDPOINT_HELPERS: usize = 4;

/// dom0's descriptor for the kill endpoint. Every thread of the kill tests holds it in descriptor 0.
const KILL_ENDPOINT: usize = 4;
/// Where the processes of the kill tests map their own pages.
const KILL_VA: usize = TEST_VA;
const VICTIM_PAGES: usize = 4;
const GRANDCHILD_PAGES: usize = 3;
const ZOMBIE_PAGES: usize = 2;
/// Kills of a child spinning on the other CPU of dom0's container.
const RUNNING_TO_IDLE_ROUNDS: usize = 8;
/// Rounds of the kill loop. Each round kills two live processes and reaps a zombie, so a reclaim that
/// leaked the PCIDs of the live ones would exhaust the container's `PCID_MAX` (4096) before the end.
const KILL_ROUNDS: usize = 2100;
/// TSC cycles a killed process's threads must stay silent.
const FROZEN_CYCLES: u64 = 2_000_000;

static mut DRIVER_STACK: [u8; 16 * 1024] = [0; 16 * 1024];
static mut VICTIM_STACK: [u8; 16 * 1024] = [0; 16 * 1024];
static mut ZOMBIE_STACK: [u8; 16 * 1024] = [0; 16 * 1024];
static mut GRANDCHILD_STACK: [u8; 16 * 1024] = [0; 16 * 1024];
static mut GRANDCHILD_BEAT_STACK: [u8; 16 * 1024] = [0; 16 * 1024];
static mut CALLER_STACK: [u8; 16 * 1024] = [0; 16 * 1024];
static mut RECEIVER_STACK: [u8; 16 * 1024] = [0; 16 * 1024];
static mut VICTIM_BEAT_STACK: [u8; 16 * 1024] = [0; 16 * 1024];
static mut SPIN_CHILD_STACK: [u8; 16 * 1024] = [0; 16 * 1024];

/// The spinning child's CPU and progress.
static SPIN_CPU: AtomicUsize = AtomicUsize::new(usize::MAX);
static SPIN_BEAT: AtomicUsize = AtomicUsize::new(0);

/// The round of the kill loop; bit 0 gives the victim an IOMMU table, bit 1 the grandchild, bit 2
/// the zombie.
static KILL_ROUND: AtomicUsize = AtomicUsize::new(0);
/// One plus the container quota the victim drained before the kill; 0 until then.
static VICTIM_DRAINED: AtomicUsize = AtomicUsize::new(0);
/// One plus dom0's process quota the kill driver drained after the kill; 0 until then.
static DRIVER_DRAINED: AtomicUsize = AtomicUsize::new(0);
static GRANDCHILD_READY: AtomicBool = AtomicBool::new(false);
static CALL_TAKEN: AtomicBool = AtomicBool::new(false);
static RECEIVER_ARMED: AtomicBool = AtomicBool::new(false);
/// Bumped by every yielding thread of the victim's subtree.
static HEARTBEAT: AtomicUsize = AtomicUsize::new(0);

/// dom0's loaded image as `(start, pages)`; every child process shares it.
fn image_range() -> (usize, usize) {
    let image = (&raw const __ehdr_start) as usize;
    (image, ((&raw const _end) as usize - image).div_ceil(4096))
}

/// The entry stack pointer on `stack`: the entry sees the stack as if just called.
fn stack_top<const N: usize>(stack: *const [u8; N]) -> usize {
    stack as usize + N - 8
}

fn entry(f: extern "C" fn() -> !) -> usize {
    f as *const () as usize
}

/// `expect_error` without the success log, for the kill loop.
fn expect_quiet(name: &str, ret: isize, expected: &str) {
    if error_name(ret) != expected {
        log::error!("{} -> {} ({}): expected {}", name, ret, error_name(ret), expected);
        unsafe { sys_debug_exit(1) };
    }
}

/// `wait_for` that yields between checks, for waits on threads that may share this CPU.
fn wait_yield(what: &str, done: impl Fn() -> bool) {
    let start = unsafe { core::arch::x86_64::_rdtsc() };
    while !done() {
        if unsafe { core::arch::x86_64::_rdtsc() } - start > WAIT_LIMIT {
            log::error!("timed out waiting for {}", what);
            unsafe { sys_debug_exit(1) };
        }
        unsafe { sys_schedule() };
    }
}

fn exit_thread(who: &str) -> ! {
    let ret = unsafe { syscall0(NR_THREAD_EXIT) }.rax;
    log::error!("{} thread_exit returned {} ({})", who, ret, error_name(ret));
    unsafe { sys_debug_exit(1) }
}

/// Tail of a helper thread holding an endpoint in descriptor 0: yields until dom0 retires the
/// helpers, then serves one call and exits, which fails that call with ErrorIpcCalleeExited.
fn retire_when_asked() -> ! {
    while !RETIRE.load(Ordering::SeqCst) {
        note_cpu();
        unsafe { sys_schedule() };
    }
    quiet("retiring helper receive_call", unsafe { sys_receive_call(0) });
    exit_thread("retiring helper")
}

/// Moves a whole quota to the caller with `alloc`, largest power of two first, and returns the
/// amount. Each refused amount must fail with `shortfall`; the last, 1, leaves nothing behind.
fn drain(name: &str, alloc: unsafe fn(usize) -> isize, shortfall: &str) -> usize {
    let mut total = 0;
    for bit in (0..31).rev() {
        let ret = unsafe { alloc(1 << bit) };
        if ret >= 0 {
            total += 1 << bit;
        } else {
            expect_quiet(name, ret, shortfall);
        }
    }
    total
}

/// Funds the calling thread with `amount` of 4K quota through its process.
fn fund(who: &str, amount: usize) {
    quiet(who, unsafe { sys_alloc_quota_4k(amount) });
    quiet(who, unsafe { sys_alloc_thread_quota_4k(amount) });
}

/// Maps `count` pages at `KILL_VA` in the calling process and checks that they hold what is written.
fn map_and_touch(who: &str, count: usize) {
    quiet(who, unsafe { sys_mmap_4k(KILL_VA, count) });
    for i in 0..count {
        let p = (KILL_VA + i * 4096) as *mut u64;
        unsafe { p.write_volatile(PAGE_MAGIC ^ i as u64) };
        if unsafe { p.read_volatile() } != PAGE_MAGIC ^ i as u64 {
            log::error!("{}: page {} at {:#x} does not hold what was written", who, i, KILL_VA);
            unsafe { sys_debug_exit(1) };
        }
    }
}

/// Fails unless `beat` stays put across two yields and `FROZEN_CYCLES`: no thread of a killed
/// process runs any more, here or on the other CPU.
fn expect_frozen(what: &str, beat: &AtomicUsize) {
    let before = beat.load(Ordering::SeqCst);
    for _ in 0..2 {
        unsafe { sys_schedule() };
    }
    let start = unsafe { core::arch::x86_64::_rdtsc() };
    while unsafe { core::arch::x86_64::_rdtsc() } - start < FROZEN_CYCLES {
        core::hint::spin_loop();
    }
    let after = beat.load(Ordering::SeqCst);
    if after != before {
        log::error!("{} still runs after the kill: {} -> {}", what, before, after);
        unsafe { sys_debug_exit(1) };
    }
}

/// Yields forever, bumping `HEARTBEAT`: a thread the kill must stop.
extern "C" fn beat_forever() -> ! {
    loop {
        HEARTBEAT.fetch_add(1, Ordering::SeqCst);
        unsafe { sys_schedule() };
    }
}

/// First thread of a child that spins without syscalls, so a kill finds it running.
extern "C" fn spin_child() -> ! {
    loop {
        SPIN_CPU.store(current_cpu(), Ordering::SeqCst);
        SPIN_BEAT.fetch_add(1, Ordering::SeqCst);
    }
}

/// The only thread of a child that becomes a zombie: maps pages, then exits while serving one call
/// on descriptor 0, which fails that call with ErrorIpcCalleeExited. Its process stays a zombie
/// until a kill reaps it.
extern "C" fn zombie_main() -> ! {
    fund("zombie funding", 4 * ZOMBIE_PAGES);
    map_and_touch("zombie mmap_4k", ZOMBIE_PAGES);
    quiet("zombie receive_call", unsafe { sys_receive_call(0) });
    exit_thread("zombie")
}

/// First thread of the grandchild: maps pages and starts a second thread; both yield until killed.
extern "C" fn grandchild_main() -> ! {
    fund("grandchild funding", 4 * GRANDCHILD_PAGES + 1);
    map_and_touch("grandchild mmap_4k", GRANDCHILD_PAGES);
    quiet("grandchild new_thread", unsafe { sys_new_thread(entry(beat_forever), stack_top(&raw const GRANDCHILD_BEAT_STACK)) });
    GRANDCHILD_READY.store(true, Ordering::SeqCst);
    beat_forever()
}

/// A victim thread calling the kill driver, which takes the call and never replies: the kill turns
/// it into a dangling thread waiting for the reply.
extern "C" fn victim_caller() -> ! {
    let ret = unsafe { sys_call(0) };
    log::error!("the victim's call returned {} ({})", ret, error_name(ret));
    unsafe { sys_debug_exit(1) }
}

/// A victim thread that waits on the kill endpoint once the driver took the caller's call.
extern "C" fn victim_receiver() -> ! {
    wait_yield("the driver to take the victim's call", || CALL_TAKEN.load(Ordering::SeqCst));
    RECEIVER_ARMED.store(true, Ordering::SeqCst);
    let ret = unsafe { sys_receive_empty(0) };
    log::error!("the victim's receive_empty returned {} ({})", ret, error_name(ret));
    unsafe { sys_debug_exit(1) }
}

/// First thread of the victim, a child of dom0 holding the kill endpoint in descriptor 0. It maps
/// pages, creates a child that becomes a zombie, a grandchild with two threads, a caller, a
/// receiver, and a yielding thread, then drains its container's quota into the victim, so the
/// leak check sees it only if the kill returns it.
extern "C" fn victim_main() -> ! {
    let round = KILL_ROUND.load(Ordering::SeqCst);
    let (image, pages) = image_range();
    fund("victim funding", 4 * VICTIM_PAGES + 2 * (6 + 3 * pages) + 3);
    map_and_touch("victim mmap_4k", VICTIM_PAGES);
    let (ip, sp) = (entry(zombie_main), stack_top(&raw const ZOMBIE_STACK));
    let ret = if round & 4 != 0 {
        unsafe { sys_new_process_with_iommu_and_endpoint(image, pages, 0, ip, sp) }
    } else {
        unsafe { sys_new_process_with_endpoint(image, pages, 0, ip, sp) }
    };
    quiet("victim new_process (zombie)", ret);
    expect_quiet("victim call to the exiting zombie thread", unsafe { sys_call(0) }, "ErrorIpcCalleeExited");
    let (ip, sp) = (entry(grandchild_main), stack_top(&raw const GRANDCHILD_STACK));
    let ret = if round & 2 != 0 {
        unsafe { sys_new_process_with_iommu_and_endpoint(image, pages, 0, ip, sp) }
    } else {
        unsafe { sys_new_process(image, pages, ip, sp) }
    };
    quiet("victim new_process (grandchild)", ret);
    wait_yield("the grandchild", || GRANDCHILD_READY.load(Ordering::SeqCst));
    quiet("victim new_thread (caller)", unsafe { sys_new_thread_with_endpoint(0, entry(victim_caller), stack_top(&raw const CALLER_STACK)) });
    quiet("victim new_thread (receiver)", unsafe { sys_new_thread_with_endpoint(0, entry(victim_receiver), stack_top(&raw const RECEIVER_STACK)) });
    quiet("victim new_thread (beat)", unsafe { sys_new_thread(entry(beat_forever), stack_top(&raw const VICTIM_BEAT_STACK)) });
    // The zombie's exit holds the container until it has returned the zombie's quota, and every
    // alloc_quota_4k waits for that lock, so the drain sees the container settled.
    let drained = drain("victim alloc_quota_4k", sys_alloc_quota_4k, "ErrorContainerQuotaInsufficient");
    VICTIM_DRAINED.store(drained + 1, Ordering::SeqCst);
    beat_forever()
}

/// Kill driver of one round, a dom0 thread holding the kill endpoint in descriptor 0: creates the
/// victim, takes the victim's call, kills the victim's subtree, checks what the kill left behind,
/// drains dom0's process quota for the leak check, and exits serving dom0's call.
extern "C" fn kill_driver() -> ! {
    let round = KILL_ROUND.load(Ordering::SeqCst);
    let (image, pages) = image_range();
    let cost = 6 + 3 * pages;
    let ret = unsafe { sys_alloc_thread_quota_4k(cost) };
    if ret < 0 {
        expect_quiet("driver alloc_thread_quota_4k", ret, "ErrorNoQuota");
        fund("driver funding", cost);
    }
    let (ip, sp) = (entry(victim_main), stack_top(&raw const VICTIM_STACK));
    let ret = if round & 1 != 0 {
        unsafe { sys_new_process_with_iommu_and_endpoint(image, pages, 0, ip, sp) }
    } else {
        unsafe { sys_new_process_with_endpoint(image, pages, 0, ip, sp) }
    };
    quiet("driver new_process (victim)", ret);
    wait_yield("the victim to drain the container", || VICTIM_DRAINED.load(Ordering::SeqCst) != 0);
    quiet("driver receive_call (victim)", unsafe { sys_receive_call(0) });
    CALL_TAKEN.store(true, Ordering::SeqCst);
    wait_yield("the victim's receiver", || RECEIVER_ARMED.load(Ordering::SeqCst));
    // Lets the receiver block on the kill endpoint.
    for _ in 0..4 {
        unsafe { sys_schedule() };
    }
    quiet("driver kill_process", unsafe { sys_kill_process(0) });
    expect_quiet("driver kill_process again", unsafe { sys_kill_process(0) }, "ErrorInvalidChild");
    expect_frozen("the victim's subtree", &HEARTBEAT);
    expect_quiet("driver reply_and_receive to the killed caller", unsafe { sys_reply_and_receive(0) }, "ErrorIpcCallerKilled");
    expect_quiet("driver send_empty_no_block after the kill", unsafe { sys_send_empty_no_block(0) }, "ErrorIpcNoPeer");
    let drained = drain("driver alloc_thread_quota_4k", sys_alloc_thread_quota_4k, "ErrorNoQuota");
    DRIVER_DRAINED.store(drained + 1, Ordering::SeqCst);
    quiet("driver receive_call (dom0)", unsafe { sys_receive_call(0) });
    exit_thread("kill driver")
}

/// Phase 9. (a) dom0's three children: the IOMMU child's DMA function comes back to dom0 detached;
/// a zombie child is reaped. (b) The helper threads exit, so dom0's other CPU idles. (c) Children
/// spinning on that CPU are killed through running-to-idle IPIs. (d) The kill loop: each round a
/// fresh driver thread kills a victim subtree with every thread state, a zombie, and a grandchild,
/// and the free 4K quota of dom0's container and process must grow by exactly the driver's thread
/// page.
fn test_kill_process(image: usize, pages: usize) {
    let (bus, dev, fun) = dma_bdf();
    expect_error("kill_process past the children", unsafe { sys_kill_process(3) }, "ErrorInvalidChild");
    expect_error("pci_attach_dma before the kill", unsafe { sys_pci_attach_dma(bus, dev, fun) }, "ErrorPciOwnerMismatch");
    check("kill_process(0) (IOMMU child)", unsafe { sys_kill_process(0) });
    expect_dma_fault("after the kill", FAULT_CONTEXT_NOT_PRESENT);
    check("pci_attach_dma of the reassigned function", unsafe { sys_pci_attach_dma(bus, dev, fun) });
    expect_dma_fault("after dom0 attached it again", FAULT_READ_NOT_PRESENT);
    check("kill_process(1) (peer child)", unsafe { sys_kill_process(1) });
    check("kill_process(0) (plain child)", unsafe { sys_kill_process(0) });
    expect_error("kill_process(0) without children", unsafe { sys_kill_process(0) }, "ErrorInvalidChild");
    expect_error("kill_process(usize::MAX)", unsafe { sys_kill_process(usize::MAX) }, "ErrorInvalidChild");

    let cost = 4 + 3 * pages;
    check("alloc_quota_4k", unsafe { sys_alloc_quota_4k(1 + cost) });
    check("alloc_thread_quota_4k", unsafe { sys_alloc_thread_quota_4k(1 + cost) });
    check("new_endpoint (kill)", unsafe { sys_new_endpoint(KILL_ENDPOINT) });
    let sp = stack_top(&raw const ZOMBIE_STACK);
    check("new_process_with_endpoint (zombie)", unsafe { sys_new_process_with_endpoint(image, pages, KILL_ENDPOINT, entry(zombie_main), sp) });
    expect_error("call to the exiting zombie thread", unsafe { sys_call(KILL_ENDPOINT) }, "ErrorIpcCalleeExited");
    check("kill_process(0) (zombie)", unsafe { sys_kill_process(0) });
    expect_error("kill_process(0) after the zombie", unsafe { sys_kill_process(0) }, "ErrorInvalidChild");

    RETIRE.store(true, Ordering::SeqCst);
    for _ in 0..ROOT_ENDPOINT_HELPERS {
        expect_error("call to retire a helper", unsafe { sys_call(ENDPOINT) }, "ErrorIpcCalleeExited");
    }
    expect_error("call to retire the endpoint thread", unsafe { sys_call(NEW_ENDPOINT) }, "ErrorIpcCalleeExited");

    let sp = stack_top(&raw const SPIN_CHILD_STACK);
    for _ in 0..RUNNING_TO_IDLE_ROUNDS {
        fund("alloc_quota_4k (spinning child)", cost);
        SPIN_CPU.store(usize::MAX, Ordering::SeqCst);
        SPIN_BEAT.store(0, Ordering::SeqCst);
        quiet("new_process (spinning child)", unsafe { sys_new_process(image, pages, entry(spin_child), sp) });
        wait_for("the spinning child on the other CPU", || {
            let cpu = SPIN_CPU.load(Ordering::SeqCst);
            cpu != usize::MAX && cpu != current_cpu()
        });
        quiet("kill_process (spinning child)", unsafe { sys_kill_process(0) });
        expect_frozen("the spinning child", &SPIN_BEAT);
    }
    expect_error("kill_process(0) after the running-to-idle IPIs", unsafe { sys_kill_process(0) }, "ErrorInvalidChild");
    log::info!("killed a child running on the other CPU {} times", RUNNING_TO_IDLE_ROUNDS);

    check("alloc_quota_4k", unsafe { sys_alloc_quota_4k(KILL_ROUNDS) });
    check("alloc_thread_quota_4k", unsafe { sys_alloc_thread_quota_4k(KILL_ROUNDS) });
    let sp = stack_top(&raw const DRIVER_STACK);
    let mut first = 0;
    for round in 0..KILL_ROUNDS {
        KILL_ROUND.store(round, Ordering::SeqCst);
        VICTIM_DRAINED.store(0, Ordering::SeqCst);
        DRIVER_DRAINED.store(0, Ordering::SeqCst);
        for flag in [&GRANDCHILD_READY, &CALL_TAKEN, &RECEIVER_ARMED] {
            flag.store(false, Ordering::SeqCst);
        }
        quiet("new_thread_with_endpoint (kill driver)", unsafe { sys_new_thread_with_endpoint(KILL_ENDPOINT, entry(kill_driver), sp) });
        wait_yield("the kill driver", || DRIVER_DRAINED.load(Ordering::SeqCst) != 0);
        let free = VICTIM_DRAINED.load(Ordering::SeqCst) - 1 + DRIVER_DRAINED.load(Ordering::SeqCst) - 1;
        // Each round moves one page of dom0's thread quota into the driver's thread, whose exit
        // returns it to the container.
        if round == 0 {
            first = free;
        } else if free != first + round {
            log::error!("kill round {}: {} free 4K quota, expected {}", round, free, first + round);
            unsafe { sys_debug_exit(1) };
        }
        // The driver's exit holds dom0's process until it finishes, so the next driver starts after it.
        expect_quiet("call to the exiting kill driver", unsafe { sys_call(KILL_ENDPOINT) }, "ErrorIpcCalleeExited");
        if (round + 1) % 256 == 0 {
            log::info!("kill round {}: {} free 4K quota", round + 1, free);
        }
    }
    expect_error("kill_process(0) after the kill loop", unsafe { sys_kill_process(0) }, "ErrorInvalidChild");
    log::info!("kill loop: {} rounds, free 4K quota {} -> {} with no leak", KILL_ROUNDS, first, first + KILL_ROUNDS - 1);
}

#[no_mangle]
pub extern "C" fn _start() -> ! {
    vsys::logger::init_logging_with_level(log::Level::Info);
    log::info!("Hello from dom0!");

    // 0. paths that need no thread quota
    for _ in 0..2 {
        check("schedule", unsafe { sys_schedule() });
    }
    expect_error("send_empty_no_block", unsafe { sys_send_empty_no_block(ENDPOINT) }, "ErrorIpcNoPeer");
    expect_error("receive_empty_no_block", unsafe { sys_receive_empty_no_block(ENDPOINT) }, "ErrorIpcNoPeer");
    expect_error("bad syscall arg", unsafe { sys_send_empty_no_block(usize::MAX) }, "InvalidArgument");
    // Loading a selector into fs/gs zeroes their bases. The kernel must not depend on the user's
    // gs, so everything from here on runs with it clobbered, syscalls and timer preemptions alike.
    unsafe { core::arch::asm!("mov fs, {0:x}", "mov gs, {0:x}", in(reg) USER_DATA_SELECTOR, options(nostack, preserves_flags)) };
    check("schedule after the user loaded gs", unsafe { sys_schedule() });
    expect_error("new_thread at a non-canonical ip", unsafe { sys_new_thread(1 << 63, 0) }, "InvalidArgument");
    time_syscall_returns();
    time_mmap_unmap();
    time_mmap_only();

    // Without the timer (feature `no-timer`) nothing preempts a spinning thread, an idle CPU wakes only
    // at an IPI (queuing a thread sends none), and a CPU notices an offline request only when its thread
    // yields. The remaining timings need none of these: the parallel call timing brings each other CPU
    // online once, with the IPI of `cpu_online`, kills its children while they block in receive (so does
    // the parallel mmap timing, which runs on the same clients), and its clients yield to take their CPUs
    // Off again; after it only CPU 0 runs, the pong and call server threads block in receive, the call
    // server child is killed while it blocks in receive, and the timed threads are only created. The
    // phases below rely on them (spinning waits for other threads, CPU offline cycles, the register
    // spinner), so this build skips them. The parallel call timing comes first, while CPU 0's shard holds
    // no thread that a CPU coming online could pull instead.
    if cfg!(feature = "no-timer") {
        time_parallel_call();
        fund("timing helper threads funding", 2);
        time_ipc_round_trip();
        time_call_round_trip();
        time_call_round_trip_cross_process();
        time_new_thread();
        log::info!("dom0 timings passed without the timer");
        unsafe { sys_debug_exit(0) };
    }

    // 1. quota + mmap + touch + unmap
    check("alloc_quota_4k", unsafe { sys_alloc_quota_4k(64) });
    check("alloc_thread_quota_4k", unsafe { sys_alloc_thread_quota_4k(64) });
    check("mmap_4k", unsafe { sys_mmap_4k(TEST_VA, TEST_PAGES) });
    unsafe {
        let p = TEST_VA as *mut u64;
        for i in 0..(TEST_PAGES * 512) {
            p.add(i).write_volatile(i as u64 ^ 0xdead_beef);
        }
        for i in 0..(TEST_PAGES * 512) {
            let v = p.add(i).read_volatile();
            if v != (i as u64 ^ 0xdead_beef) {
                log::error!("page content mismatch at {}: {:#x}", i, v);
                sys_debug_exit(1);
            }
        }
    }
    log::info!("mapped pages read back correctly");
    check("unmap_4k", unsafe { sys_unmap_4k(TEST_VA, TEST_PAGES) });

    // 2. SMP, before any other thread exists: CPU 1 comes online and pulls the worker, unmapping
    // a page the worker touched there flushes CPU 1's TLB, and CPU 1 goes Off and comes back.
    check("cpu_online(1)", unsafe { sys_cpu_online(1) });
    expect_error("cpu_online(1) while online", unsafe { sys_cpu_online(1) }, "ErrorCpuNotOff");
    expect_error("cpu_online(99)", unsafe { sys_cpu_online(99) }, "InvalidArgument");
    check("mmap_4k", unsafe { sys_mmap_4k(TEST_VA, 1) });
    check("new_endpoint (park)", unsafe { sys_new_endpoint(PARK_ENDPOINT) });
    let sp = (&raw const WORKER_STACK) as usize + 64 * 1024 - 8;
    check("new_thread_with_endpoint (worker)", unsafe { sys_new_thread_with_endpoint(PARK_ENDPOINT, worker_thread as *const () as usize, sp) });
    wait_for("a dom0 thread on CPU 1", || SEEN_CPUS.load(Ordering::SeqCst) & 0b11 == 0b11);
    log::info!("dom0 threads ran on CPUs {:#b}", SEEN_CPUS.load(Ordering::SeqCst));
    // Shootdown check: the worker pauses with its page's TLB entry cached, the page is replaced
    // at the same address, and the resumed worker must write the new page. A stale entry would
    // keep it writing the old one. Repeated until two rounds replaced the page from a CPU other
    // than the worker's, which needs the remote flush. An idle CPU only pulls queued threads
    // when it wakes, so if both threads share CPU 0, CPU 1 is cycled Off and On to make it pull
    // the paused worker.
    let mut remote_rounds = 0;
    for _ in 0..16 {
        PAUSE_WORKER.store(true, Ordering::SeqCst);
        wait_for("the worker to pause", || WORKER_PAUSED.load(Ordering::SeqCst));
        if current_cpu() == 0 && WORKER_CPU.load(Ordering::SeqCst) == 0 {
            check("cpu_offline_request(1) to move the worker", unsafe { sys_cpu_offline_request(1) });
            online_after_offline("cpu_online(1) to move the worker", || unsafe { sys_cpu_online(1) });
            wait_for("the worker to move to CPU 1", || WORKER_CPU.load(Ordering::SeqCst) == 1);
        }
        let (here, there) = (current_cpu(), WORKER_CPU.load(Ordering::SeqCst));
        log::info!("shootdown round: unmapping on CPU {}, worker paused on CPU {}", here, there);
        check("unmap_4k", unsafe { sys_unmap_4k(TEST_VA, 1) });
        let remote = here != there;
        check("mmap_4k", unsafe { sys_mmap_4k(TEST_VA, 1) });
        let before = unsafe { (TEST_VA as *const u64).read_volatile() };
        PAUSE_WORKER.store(false, Ordering::SeqCst);
        wait_for("the worker to write the remapped page", || unsafe { (TEST_VA as *const u64).read_volatile() } != before);
        remote_rounds += remote as usize;
        if remote_rounds >= 2 {
            break;
        }
    }
    if remote_rounds == 0 {
        log::error!("no round replaced the page from a CPU other than the worker's");
        unsafe { sys_debug_exit(1) };
    }
    log::info!("TLB shootdown: the worker wrote the remapped page in every round ({} remote)", remote_rounds);
    STOP_WORKER.store(true, Ordering::SeqCst);
    wait_for("the worker to stop", || WORKER_STOPPED.load(Ordering::SeqCst));
    check("unmap_4k", unsafe { sys_unmap_4k(TEST_VA, 1) });

    check("cpu_offline_request(1)", unsafe { sys_cpu_offline_request(1) });
    online_after_offline("cpu_online(1) after offline", || unsafe { sys_cpu_online(1) });
    log::info!("CPU 1 went Off and is online again");

    // 3. IPC timing against a pong thread, then a second thread sharing the root endpoint, two
    // IPC round trips
    time_ipc_round_trip();
    time_call_round_trip();
    // The entry sees the stack as if just called: rsp + 8 is 16-byte aligned.
    let sp = (&raw const THREAD_STACK) as usize + 64 * 1024 - 8;
    check("new_thread_with_endpoint", unsafe { sys_new_thread_with_endpoint(ENDPOINT, second_thread as *const () as usize, sp) });
    for _ in 0..2 {
        check("send_empty", unsafe { sys_send_empty(ENDPOINT) });
    }
    check("receive_empty", unsafe { sys_receive_empty(ENDPOINT) });
    log::info!("IPC done, pings = {}", PINGS.load(Ordering::SeqCst));

    // 4. VT-d: DMA of an unattached function faults at its context entry; once attached it
    // faults inside dom0's empty IOMMU table. Sending the function to a child process detaches it
    // (the context-cache invalidation must drop the stale entry) until the child attaches it.
    let bdf = unsafe { sys_debug_dma_device() };
    check("debug_dma_device", bdf);
    DMA_BDF.store(bdf as usize, Ordering::SeqCst);
    let (bus, dev, fun) = dma_bdf();
    expect_dma_fault("before attach", FAULT_CONTEXT_NOT_PRESENT);
    check("pci_attach_dma", unsafe { sys_pci_attach_dma(bus, dev, fun) });
    expect_dma_fault("after attach", FAULT_READ_NOT_PRESENT);
    expect_error("pci_attach_dma again", unsafe { sys_pci_attach_dma(bus, dev, fun) }, "ErrorPciAlreadyAttached");

    let (image, pages) = image_range();
    check("alloc_quota_4k", unsafe { sys_alloc_quota_4k(6 + 3 * pages) });
    check("alloc_thread_quota_4k", unsafe { sys_alloc_thread_quota_4k(6 + 3 * pages) });
    let sp = (&raw const CHILD_STACK) as usize + 64 * 1024 - 8;
    let child = unsafe { sys_new_process_with_iommu_and_endpoint(image, pages, ENDPOINT, child_process as *const () as usize, sp) };
    check("new_process_with_iommu_and_endpoint", child);
    check("send_pci", unsafe { sys_send_pci(ENDPOINT, bus, dev, fun) });
    expect_dma_fault("after the transfer", FAULT_CONTEXT_NOT_PRESENT);
    expect_error("pci_attach_dma by the old owner", unsafe { sys_pci_attach_dma(bus, dev, fun) }, "ErrorPciOwnerMismatch");
    CHILD_MAY_ATTACH.store(true, Ordering::SeqCst);
    wait_for("the child to attach", || CHILD_ATTACHED.load(Ordering::SeqCst));
    expect_dma_fault("after the child attached", FAULT_READ_NOT_PRESENT);

    // 5. The remaining payloads inside dom0's container: a plain child process, then a child
    // sharing the root endpoint that receives it again, sends a page of the image back, and
    // takes part in a CPU transfer that fails because both sides are in one container. Without
    // 2M quota a new container is refused.
    let cost = 4 + 3 * pages;
    check("alloc_quota_4k", unsafe { sys_alloc_quota_4k(2 * cost + 3) });
    check("alloc_thread_quota_4k", unsafe { sys_alloc_thread_quota_4k(2 * cost + 3) });
    let sp = (&raw const PLAIN_STACK) as usize + 64 * 1024 - 8;
    check("new_process", unsafe { sys_new_process(image, pages, plain_child as *const () as usize, sp) });
    wait_for("the plain child", || PLAIN_CHILD_RAN.load(Ordering::SeqCst));
    let sp = (&raw const PEER_STACK) as usize + 64 * 1024 - 8;
    check("new_process_with_endpoint", unsafe { sys_new_process_with_endpoint(image, pages, ENDPOINT, peer_child as *const () as usize, sp) });
    check("send_endpoint", unsafe { sys_send_endpoint(ENDPOINT, ENDPOINT) });
    check("receive_empty", unsafe { sys_receive_empty(ENDPOINT) });
    check("receive_pages", unsafe { sys_receive_pages(ENDPOINT, PAGES_VA, 1) });
    unsafe { (PAGES_VA as *mut u64).write_volatile(PAGE_MAGIC) };
    let seen = unsafe { (&raw const SHARED_PAGE.0[0]).read_volatile() };
    if seen != PAGE_MAGIC {
        log::error!("received page does not alias the sent page: {:#x}", seen);
        unsafe { sys_debug_exit(1) };
    }
    log::info!("received page aliases the sent page");
    expect_error("send_cpu", unsafe { sys_send_cpu(ENDPOINT, 2) }, "ErrorIpcSameContainer");
    wait_for("the peer child", || PEER_DONE.load(Ordering::SeqCst));
    expect_error("new_container", unsafe { sys_new_container(image, pages, 0, 0, 2, plain_child as *const () as usize, sp).rax }, "ErrorNoQuota");

    // 6. A child container. 2M quota flows from dom0's container to its thread; the child gets
    // Off CPU 2 and the root endpoint; dom0 brings CPU 2 online for it, sends it CPU 3 over the
    // endpoint, and once the child has brought CPU 3 online, takes it Off and online again.
    expect_error("alloc_quota_2m beyond the container", unsafe { sys_alloc_quota_2m(usize::MAX) }, "ErrorContainerQuotaInsufficient");
    check("alloc_quota_2m", unsafe { sys_alloc_quota_2m(2) });
    expect_error("alloc_thread_quota_2m beyond the process", unsafe { sys_alloc_thread_quota_2m(3) }, "ErrorNoQuota");
    check("alloc_thread_quota_2m", unsafe { sys_alloc_thread_quota_2m(2) });
    let cost = 9 + CONTAINER_FUNDING + 3 * pages;
    check("alloc_quota_4k", unsafe { sys_alloc_quota_4k(cost) });
    check("alloc_thread_quota_4k", unsafe { sys_alloc_thread_quota_4k(cost) });
    let ip = container_child as *const () as usize;
    let sp = (&raw const CONTAINER_STACK) as usize + 64 * 1024 - 8;
    let new_container = |transfer_cpu, ep_idx| unsafe {
        sys_new_container_with_endpoint(image, pages, CONTAINER_FUNDING, CONTAINER_PROCESS_QUOTA, transfer_cpu, ep_idx, ip, sp).rax
    };
    expect_error("new_container_with_endpoint with an empty descriptor", new_container(2, 7), "Error");
    expect_error("new_container_with_endpoint with an online cpu", new_container(1, ENDPOINT), "ErrorIpcCpuNotOff");
    check("new_container_with_endpoint", new_container(2, ENDPOINT));
    expect_error("cpu_online(2) after the transfer", unsafe { sys_cpu_online(2) }, "ErrorCpuOwnerMismatch");
    expect_error("cpu_online_child(1, 2)", unsafe { sys_cpu_online_child(1, 2) }, "ErrorCpuOwnerMismatch");
    expect_error("cpu_online_child(0, 3)", unsafe { sys_cpu_online_child(0, 3) }, "ErrorCpuOwnerMismatch");
    check("cpu_online_child(0, 2)", unsafe { sys_cpu_online_child(0, 2) });
    expect_error("cpu_online_child(0, 2) again", unsafe { sys_cpu_online_child(0, 2) }, "ErrorCpuNotOff");
    wait_for("the child container's root thread", || CONTAINER_CHILD_CPU.load(Ordering::SeqCst) != 0);
    let child_cpu = CONTAINER_CHILD_CPU.load(Ordering::SeqCst) - 1;
    if child_cpu != 2 {
        log::error!("the child container's root thread ran on CPU {}", child_cpu);
        unsafe { sys_debug_exit(1) };
    }
    check("send_cpu(3) to the child container", unsafe { sys_send_cpu(ENDPOINT, 3) });
    wait_for("the child container to bring CPU 3 online", || CONTAINER_CHILD_ONLINED.load(Ordering::SeqCst));
    expect_error("cpu_offline_request_child(0, 1)", unsafe { sys_cpu_offline_request_child(0, 1) }, "ErrorCpuOwnerMismatch");
    expect_error("cpu_offline_request_child(1, 3)", unsafe { sys_cpu_offline_request_child(1, 3) }, "ErrorCpuOwnerMismatch");
    check("cpu_offline_request_child(0, 3)", unsafe { sys_cpu_offline_request_child(0, 3) });
    online_after_offline("cpu_online_child(0, 3) after offline", || unsafe { sys_cpu_online_child(0, 3) });
    log::info!("CPU 3 of the child container went Off and is online again");

    // 7. A new endpoint: an occupied descriptor is refused; one 4K thread quota creates an endpoint
    // at an empty descriptor, which dom0 hands to a new thread and sends on.
    expect_error("new_endpoint at an occupied descriptor", unsafe { sys_new_endpoint(ENDPOINT) }, "ErrorIpcEndpointTargetInUse");
    check("alloc_quota_4k", unsafe { sys_alloc_quota_4k(2) });
    check("alloc_thread_quota_4k", unsafe { sys_alloc_thread_quota_4k(2) });
    check("new_endpoint", unsafe { sys_new_endpoint(NEW_ENDPOINT) });
    let sp = (&raw const ENDPOINT_STACK) as usize + 64 * 1024 - 8;
    check("new_thread_with_endpoint on the new endpoint", unsafe { sys_new_thread_with_endpoint(NEW_ENDPOINT, endpoint_thread as *const () as usize, sp) });
    check("send_empty on the new endpoint", unsafe { sys_send_empty(NEW_ENDPOINT) });
    wait_for("the endpoint thread", || NEW_ENDPOINT_USED.load(Ordering::SeqCst));

    // 8. A thread the timer preempted keeps rcx and r11 when another thread's syscall return resumes
    // it: its frame goes back through iretq, not sysretq.
    check("alloc_quota_4k", unsafe { sys_alloc_quota_4k(1) });
    check("alloc_thread_quota_4k", unsafe { sys_alloc_thread_quota_4k(1) });
    let sp = (&raw const SPINNER_STACK) as usize + 64 * 1024 - 8;
    check("new_thread_with_endpoint (register spinner)", unsafe { sys_new_thread_with_endpoint(ENDPOINT, register_spinner as *const () as usize, sp) });
    for phase in 1..=2 {
        for _ in 0..SPINNER_ROUNDS {
            unsafe { sys_schedule() };
        }
        SPINNER_PHASE.store(phase, Ordering::SeqCst);
    }
    wait_for("the register spinner", || SPINNER_RESULT.load(Ordering::SeqCst) != 0);
    if SPINNER_RESULT.load(Ordering::SeqCst) != SPINNER_OK {
        log::error!("a preempted thread lost rcx, r11, or its rflags when resumed");
        unsafe { sys_debug_exit(1) };
    }
    log::info!("the register spinner kept rcx, r11, and rflags across its preemptions");

    // 9. kill_process: dom0's children and a zombie, a running child killed through running-to-idle
    // IPIs, and the leak loop over victim subtrees; the helper threads exit on the way.
    test_kill_process(image, pages);

    // 10. new_thread cost, last because the threads it creates keep yielding on this CPU.
    time_new_thread();

    log::info!("dom0 test passed");
    unsafe { sys_debug_exit(0) };
}

#[panic_handler]
pub fn panic(info: &PanicInfo) -> ! {
    log::error!("dom0 panic: {}", info);
    unsafe { sys_debug_exit(1) };
}
