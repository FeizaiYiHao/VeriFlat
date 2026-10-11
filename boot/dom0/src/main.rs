//! Dom0 test program: exercises the VeriFlat syscalls over the trap layer.

#![no_std]
#![no_main]

use core::panic::PanicInfo;
use core::sync::atomic::{AtomicBool, AtomicU8, AtomicUsize, Ordering};

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
static mut PONG_STACK: [u8; 64 * 1024] = [0; 64 * 1024];
static mut CALL_SERVER_STACK: [u8; 64 * 1024] = [0; 64 * 1024];

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
fn probe(name: &str, ret: isize) {
    log::info!("{} -> {} ({})", name, ret, if ret < 0 { error_name(ret) } else { "ok" });
}

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

/// Second thread: answers two empty messages on the root endpoint, then exits.
extern "C" fn second_thread() -> ! {
    log::info!("second thread running");
    for _ in 0..2 {
        check("receive_empty", unsafe { sys_receive_empty(ENDPOINT) });
        PINGS.fetch_add(1, Ordering::SeqCst);
    }
    log::info!("second thread done, pings = {}", PINGS.load(Ordering::SeqCst));
    check("send_empty", unsafe { sys_send_empty(ENDPOINT) });
    // An idle CPU that comes online pulls this thread, so it records where it runs.
    loop {
        note_cpu();
        unsafe { sys_schedule() };
    }
}

/// Worker thread: keeps a mapped page in its TLB on whatever CPU it runs, until told to stop.
extern "C" fn worker_thread() -> ! {
    let p = TEST_VA as *mut u64;
    while !STOP_WORKER.load(Ordering::SeqCst) {
        note_cpu();
        unsafe { p.write_volatile(p.read_volatile() + 1) };
    }
    WORKER_STOPPED.store(true, Ordering::SeqCst);
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
/// endpoint of its own, and it receives one empty message on the new endpoint.
extern "C" fn endpoint_thread() -> ! {
    expect_error("endpoint thread new_endpoint without quota", unsafe { sys_new_endpoint(1) }, "ErrorNoQuota");
    check("endpoint thread receive_empty", unsafe { sys_receive_empty(ENDPOINT) });
    NEW_ENDPOINT_USED.store(true, Ordering::SeqCst);
    loop {
        unsafe { sys_schedule() };
    }
}

/// Spins in two phases while dom0 resumes it from preempted frames, then checks its registers.
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
    loop {
        note_cpu();
        unsafe { sys_schedule() };
    }
}

/// Answers `IPC_ROUNDS` pings on the root endpoint, then yields forever.
extern "C" fn pong_thread() -> ! {
    for _ in 0..IPC_ROUNDS {
        quiet("pong receive_empty", unsafe { sys_receive_empty(ENDPOINT) });
        quiet("pong send_empty", unsafe { sys_send_empty(ENDPOINT) });
    }
    loop {
        note_cpu();
        unsafe { sys_schedule() };
    }
}

/// Serves `IPC_ROUNDS` calls on the root endpoint, replying each value plus one, until a plain
/// `send_empty` from dom0 meets its receive-call wait and fails the rendezvous with
/// ErrorIpcTypeMismatch; then yields forever.
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
    loop {
        note_cpu();
        unsafe { sys_schedule() };
    }
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

#[no_mangle]
pub extern "C" fn _start() -> ! {
    vsys::logger::init_logging_with_level(log::Level::Info);
    log::info!("Hello from dom0!");

    // 0. paths that need no thread quota
    for _ in 0..2 {
        probe("schedule", unsafe { sys_schedule() });
    }
    probe("send_empty_no_block", unsafe { sys_send_empty_no_block(ENDPOINT) });
    probe("receive_empty_no_block", unsafe { sys_receive_empty_no_block(ENDPOINT) });
    probe("bad syscall arg", unsafe { sys_send_empty_no_block(usize::MAX) });
    // Loading a selector into fs/gs zeroes their bases. The kernel must not depend on the user's
    // gs, so everything from here on runs with it clobbered, syscalls and timer preemptions alike.
    unsafe { core::arch::asm!("mov fs, {0:x}", "mov gs, {0:x}", in(reg) USER_DATA_SELECTOR, options(nostack, preserves_flags)) };
    probe("schedule after the user loaded gs", unsafe { sys_schedule() });
    let ret = unsafe { sys_new_thread(1 << 63, 0) };
    probe("new_thread at a non-canonical ip", ret);
    if ret != ERR_INVALID_ARGUMENT {
        log::error!("a non-canonical thread ip was accepted");
        unsafe { sys_debug_exit(1) };
    }
    time_syscall_returns();

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

    // 2. IPC timing against a pong thread, then a second thread sharing the root endpoint, two
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

    // 3. SMP: CPU 1 comes online, dom0 threads spread over CPUs 0 and 1, unmapping a page they
    // touched flushes the other CPU's TLB, and CPU 1 goes Off and comes back.
    check("cpu_online(1)", unsafe { sys_cpu_online(1) });
    probe("cpu_online(1) while online", unsafe { sys_cpu_online(1) });
    probe("cpu_online(99)", unsafe { sys_cpu_online(99) });
    check("mmap_4k", unsafe { sys_mmap_4k(TEST_VA, 1) });
    let sp = (&raw const WORKER_STACK) as usize + 64 * 1024 - 8;
    check("new_thread", unsafe { sys_new_thread(worker_thread as *const () as usize, sp) });
    wait_for("a dom0 thread on CPU 1", || SEEN_CPUS.load(Ordering::SeqCst) & 0b11 == 0b11);
    log::info!("dom0 threads ran on CPUs {:#b}", SEEN_CPUS.load(Ordering::SeqCst));
    STOP_WORKER.store(true, Ordering::SeqCst);
    wait_for("the worker to stop", || WORKER_STOPPED.load(Ordering::SeqCst));
    check("unmap_4k", unsafe { sys_unmap_4k(TEST_VA, 1) });

    check("cpu_offline_request(1)", unsafe { sys_cpu_offline_request(1) });
    online_after_offline("cpu_online(1) after offline", || unsafe { sys_cpu_online(1) });
    log::info!("CPU 1 went Off and is online again");

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

    let image = (&raw const __ehdr_start) as usize;
    let pages = ((&raw const _end) as usize - image).div_ceil(4096);
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
    let new_container = |transfer_cpu, endpoint_index| unsafe {
        sys_new_container_with_endpoint(image, pages, CONTAINER_FUNDING, CONTAINER_PROCESS_QUOTA, transfer_cpu, endpoint_index, ip, sp).rax
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
    check("new_thread (register spinner)", unsafe { sys_new_thread(register_spinner as *const () as usize, sp) });
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

    // 9. new_thread cost, last because the threads it creates keep yielding on this CPU.
    time_new_thread();

    log::info!("dom0 test passed");
    unsafe { sys_debug_exit(0) };
}

#[panic_handler]
pub fn panic(info: &PanicInfo) -> ! {
    log::error!("dom0 panic: {}", info);
    unsafe { sys_debug_exit(1) };
}
