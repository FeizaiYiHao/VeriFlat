//! dom0: says hello, then calls every VeriFlat syscall at least once on a success path and checks
//! its result, logging `self-test: <name> ok` the first time each one succeeds. It exits with
//! `sys_debug_exit(0)` once every syscall passed and with a nonzero code at the first failure.
//!
//! Device memory: dom0's boot page table maps every BAR page at `PCI_BAR_WINDOW_BASE + p` as a 4K IO leaf; the IO
//! checks (`io_*`, `iommu_io`) read a device register through it, unmap an IO page for good, and check that an IO page
//! can be neither IOMMU-mapped nor sent to a child process.
//!
//! Nothing here waits for a timer tick, so the same binary passes on a `no-timer` kernel: threads
//! that share a CPU take turns at blocking IPC and `sys_schedule`, and every CPU that has to run a
//! thread is woken by the IPI of `cpu_online` and kept busy by a thread that only yields, since a
//! halted idle CPU without the timer wakes at an IPI only.

#![no_std]
#![no_main]

use core::panic::PanicInfo;
use core::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};

use vsys::*;

/// The verified syscalls (SystemCalls.md section 14) with the names the log uses.
const SYSCALLS: [(usize, &str); 50] = [
    (NR_ALLOC_QUOTA_4K, "alloc_quota_4k"), (NR_ALLOC_THREAD_QUOTA_4K, "alloc_thread_quota_4k"),
    (NR_ALLOC_QUOTA_2M, "alloc_quota_2m"), (NR_ALLOC_THREAD_QUOTA_2M, "alloc_thread_quota_2m"),
    (NR_ALLOC_QUOTA_1G, "alloc_quota_1g"), (NR_ALLOC_THREAD_QUOTA_1G, "alloc_thread_quota_1g"),
    (NR_SCHEDULE, "schedule"), (NR_MMAP_4K, "mmap_4k"), (NR_UNMAP_4K, "unmap_4k"), (NR_MMAP_2M, "mmap_2m"),
    (NR_UNMAP_2M, "unmap_2m"), (NR_SPLIT_2M, "split_2m"), (NR_MERGE_2M, "merge_2m"), (NR_MMAP_1G, "mmap_1g"),
    (NR_UNMAP_1G, "unmap_1g"), (NR_PCI_ATTACH_DMA, "pci_attach_dma"), (NR_IOMMU_MAP_4K, "iommu_map_4k"),
    (NR_IOMMU_UNMAP_4K, "iommu_unmap_4k"), (NR_NEW_ENDPOINT, "new_endpoint"), (NR_NEW_THREAD, "new_thread"),
    (NR_NEW_THREAD_WITH_ENDPOINT, "new_thread_with_endpoint"), (NR_SEND_EMPTY, "send_empty"),
    (NR_RECEIVE_EMPTY, "receive_empty"), (NR_SEND_EMPTY_NO_BLOCK, "send_empty_no_block"),
    (NR_RECEIVE_EMPTY_NO_BLOCK, "receive_empty_no_block"), (NR_CALL, "call"), (NR_CALL_USIZE, "call_usize"),
    (NR_RECEIVE_CALL, "receive_call"), (NR_REPLY_AND_RECEIVE, "reply_and_receive"),
    (NR_REPLY_AND_RECEIVE_USIZE, "reply_and_receive_usize"), (NR_THREAD_EXIT, "thread_exit"),
    (NR_NEW_PROCESS, "new_process"), (NR_NEW_PROCESS_WITH_ENDPOINT, "new_process_with_endpoint"),
    (NR_NEW_PROCESS_WITH_IOMMU_AND_ENDPOINT, "new_process_with_iommu_and_endpoint"),
    (NR_SEND_ENDPOINT, "send_endpoint"), (NR_RECEIVE_ENDPOINT, "receive_endpoint"), (NR_SEND_PAGES, "send_pages"),
    (NR_RECEIVE_PAGES, "receive_pages"), (NR_SEND_PCI, "send_pci"), (NR_RECEIVE_PCI, "receive_pci"),
    (NR_KILL_PROCESS, "kill_process"), (NR_CPU_ONLINE, "cpu_online"), (NR_CPU_OFFLINE_REQUEST, "cpu_offline_request"),
    (NR_NEW_CONTAINER, "new_container"), (NR_NEW_CONTAINER_WITH_ENDPOINT, "new_container_with_endpoint"),
    (NR_CPU_ONLINE_CHILD, "cpu_online_child"), (NR_CPU_OFFLINE_REQUEST_CHILD, "cpu_offline_request_child"),
    (NR_SEND_CPU, "send_cpu"), (NR_RECEIVE_CPU, "receive_cpu"), (NR_KILL_CONTAINER, "kill_container"),
];
/// The 1G syscalls, left untested when the boot found no free 1G block (no CPUID pdpe1gb).
const SYSCALLS_1G: [usize; 4] = [NR_ALLOC_QUOTA_1G, NR_ALLOC_THREAD_QUOTA_1G, NR_MMAP_1G, NR_UNMAP_1G];

/// Bit `nr` is set once syscall `nr` succeeded; dom0's child processes and containers share dom0's
/// image, so its statics too.
static PASSED: AtomicU64 = AtomicU64::new(0);
/// Bit `n` is set once a dom0 thread ran on CPU `n`.
static SEEN_CPUS: AtomicUsize = AtomicUsize::new(0);
/// TSC cycles a wait may take before the test fails.
const WAIT_LIMIT: u64 = 20_000_000_000;

/// Free in dom0's user half (L4 index 1); each test maps its own GiB.
const VA_4K: usize = 0xc0_0000_0000;
const VA_2M: usize = 0xc1_0000_0000;
const VA_1G: usize = 0xc2_0000_0000;
const VA_DMA: usize = 0xc3_0000_0000;
const VA_PAGES: usize = 0xc4_0000_0000;
/// Where the peer child receives the IO page dom0 sends it.
const VA_IO: usize = 0xc5_0000_0000;
const SIZE_2M: usize = 1 << 21;
const SIZE_1G: usize = 1 << 30;
const MAGIC: u64 = 0x5afe_9a9e;
/// The IOVA the kernel's DMA probe reads (`PROBE_IOVA` in boot/kernel/src/iommu.rs).
const PROBE_IOVA: usize = 0x80_0010_0000;
/// QEMU's `edu` device.
const EDU_VENDOR_DEVICE: usize = 0x1234_11e8;
/// QEMU's `ivshmem-plain`, whose BAR2 (shared memory) the extra high-BAR boot places above 4 GiB.
const IVSHMEM_VENDOR_DEVICE: usize = 0x1af4_1110;

/// Descriptor 0 holds dom0's root endpoint; dom0 creates a second endpoint at descriptor 1.
const ROOT_ENDPOINT: usize = 0;
const NEW_ENDPOINT: usize = 1;
/// The 4K funding of each child container, of which its root process gets `CONTAINER_PROCESS_QUOTA`.
const CONTAINER_FUNDING: usize = 8;
const CONTAINER_PROCESS_QUOTA: usize = 4;
/// A CPU id with no processor behind it under QEMU (`NUM_CPUS` is 28): it stays Off, so the container
/// it is given to never runs.
const ABSENT_CPU: usize = 27;

/// One page of dom0's image that the peer child sends back to dom0.
#[repr(C, align(4096))]
struct PageBuffer([u64; 512]);
static mut SHARED_PAGE: PageBuffer = PageBuffer([0; 512]);

static mut IPC_STACK: [u8; 16384] = [0; 16384];
static mut YIELD_STACK: [u8; 16384] = [0; 16384];
static mut IOMMU_CHILD_STACK: [u8; 16384] = [0; 16384];
static mut PEER_STACK: [u8; 16384] = [0; 16384];
static mut PLAIN_STACK: [u8; 16384] = [0; 16384];
static mut CONTAINER_STACK: [u8; 16384] = [0; 16384];
static mut CONTAINER_YIELD_STACK: [u8; 16384] = [0; 16384];
static DMA_BDF: AtomicUsize = AtomicUsize::new(0);
/// The window address of the edu BAR0 page with its identification register, the register's offset in the page,
/// and the value dom0 read there.
static IO_PAGE: AtomicUsize = AtomicUsize::new(0);
static IO_ID_OFFSET: AtomicUsize = AtomicUsize::new(0);
static IO_ID: AtomicUsize = AtomicUsize::new(0);
static IOMMU_CHILD_ATTACHED: AtomicBool = AtomicBool::new(false);
static PEER_DONE: AtomicBool = AtomicBool::new(false);
static CONTAINER_CPU_ONLINED: AtomicBool = AtomicBool::new(false);

extern "C" {
    /// The first and one-past-last bytes of dom0's loaded image (linker-defined).
    static __ehdr_start: u8;
    static _end: u8;
}

fn fail(what: &str, ret: isize) -> ! {
    log::error!("self-test: {} failed: {} ({})", what, ret, error_name(ret));
    unsafe { sys_debug_exit(1) }
}

fn name(nr: usize) -> &'static str {
    SYSCALLS.iter().find(|s| s.0 == nr).map_or("?", |s| s.1)
}

/// Records that syscall `nr` passed, logging it the first time.
fn pass(nr: usize) {
    if PASSED.fetch_or(1 << nr, Ordering::SeqCst) & (1 << nr) == 0 {
        log::info!("self-test: {} ok", name(nr));
    }
}

/// Fails unless syscall `nr` returned success; returns its value.
fn ok(nr: usize, ret: isize) -> usize {
    if ret < 0 {
        fail(name(nr), ret);
    }
    pass(nr);
    ret as usize
}

fn ok_eq(nr: usize, ret: isize, expected: usize) {
    if ok(nr, ret) != expected {
        log::error!("self-test: {} returned {}, expected {}", name(nr), ret, expected);
        unsafe { sys_debug_exit(1) };
    }
}

/// Fails unless `ret` is the model error `expected`.
fn expect_error(what: &str, ret: isize, expected: &str) {
    if ret >= 0 || error_name(ret) != expected {
        log::error!("self-test: {} returned {} ({}), expected {}", what, ret, error_name(ret), expected);
        unsafe { sys_debug_exit(1) };
    }
}

fn expect_word(what: &str, va: usize, expected: u64) {
    let v = unsafe { (va as *const u64).read_volatile() };
    if v != expected {
        log::error!("self-test: {} at {:#x} reads {:#x}, expected {:#x}", what, va, v, expected);
        unsafe { sys_debug_exit(1) };
    }
}

fn current_cpu() -> usize {
    let mut aux = 0u32;
    unsafe { core::arch::x86_64::__rdtscp(&mut aux) };
    aux as usize
}

/// Yields until `done` holds, recording where this thread runs.
fn wait_yield(what: &str, done: impl Fn() -> bool) {
    let start = unsafe { core::arch::x86_64::_rdtsc() };
    while !done() {
        if unsafe { core::arch::x86_64::_rdtsc() } - start > WAIT_LIMIT {
            log::error!("self-test: timed out waiting for {}", what);
            unsafe { sys_debug_exit(1) };
        }
        SEEN_CPUS.fetch_or(1 << current_cpu(), Ordering::SeqCst);
        ok(NR_SCHEDULE, unsafe { sys_schedule() });
    }
}

/// Repeats `syscall`, yielding in between, while it fails with `retry_on`.
fn retry(what: &str, retry_on: &str, syscall: impl Fn() -> isize) -> isize {
    let start = unsafe { core::arch::x86_64::_rdtsc() };
    loop {
        let ret = syscall();
        if ret >= 0 || error_name(ret) != retry_on || unsafe { core::arch::x86_64::_rdtsc() } - start > WAIT_LIMIT {
            return ret;
        }
        if unsafe { sys_schedule() } < 0 {
            fail(what, ret);
        }
    }
}

/// Moves `amount` 4K quota from the container through the calling process to the calling thread.
fn fund(amount: usize) {
    ok(NR_ALLOC_QUOTA_4K, unsafe { sys_alloc_quota_4k(amount) });
    ok(NR_ALLOC_THREAD_QUOTA_4K, unsafe { sys_alloc_thread_quota_4k(amount) });
}

/// dom0's loaded image as `(start, pages)`; every child process and container shares it.
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

fn dma_bdf() -> (usize, usize, usize) {
    let bdf = DMA_BDF.load(Ordering::SeqCst);
    (bdf >> 8, (bdf >> 3) & 0x1f, bdf & 0x7)
}

/// Fails unless edu's identification register, in the IO page mapped at `page`, reads what dom0 read first.
fn expect_io_id(what: &str, page: usize) {
    let id = unsafe { ((page + IO_ID_OFFSET.load(Ordering::SeqCst)) as *const u32).read_volatile() } as usize;
    if id != IO_ID.load(Ordering::SeqCst) {
        log::error!("self-test: {}: edu identification reads {:#x}, expected {:#x}", what, id, IO_ID.load(Ordering::SeqCst));
        unsafe { sys_debug_exit(1) };
    }
}

/// Yields forever, recording where it runs: keeps a CPU busy, so a thread queued there runs and the CPU
/// notices an offline request.
extern "C" fn yield_forever() -> ! {
    loop {
        SEEN_CPUS.fetch_or(1 << current_cpu(), Ordering::SeqCst);
        unsafe { sys_schedule() };
    }
}

/// dom0's second thread, holding the new endpoint in descriptor 0: the other side of every IPC test of
/// `test_ipc`, then exits while serving dom0's last call.
extern "C" fn ipc_thread() -> ! {
    ok(NR_RECEIVE_EMPTY, unsafe { sys_receive_empty(0) });
    ok(NR_SEND_EMPTY, unsafe { sys_send_empty(0) });
    ok(NR_RECEIVE_EMPTY, unsafe { sys_receive_empty(0) });
    ok(NR_SEND_EMPTY, unsafe { sys_send_empty(0) });
    let value = ok(NR_RECEIVE_CALL, unsafe { sys_receive_call(0) });
    ok_eq(NR_REPLY_AND_RECEIVE_USIZE, unsafe { sys_reply_and_receive_usize(0, value + 1) }, 0);
    ok_eq(NR_REPLY_AND_RECEIVE, unsafe { sys_reply_and_receive(0) }, 0);
    let ret = unsafe { syscall0(NR_THREAD_EXIT) }.rax;
    fail("thread_exit returned", ret)
}

/// First thread of the IOMMU child process: takes the DMA test device over the root endpoint and
/// attaches it to its own IOMMU table.
extern "C" fn iommu_child() -> ! {
    let (bus, dev, fun) = dma_bdf();
    ok(NR_RECEIVE_PCI, unsafe { sys_receive_pci(ROOT_ENDPOINT, bus, dev, fun) });
    ok(NR_PCI_ATTACH_DMA, unsafe { sys_pci_attach_dma(bus, dev, fun) });
    IOMMU_CHILD_ATTACHED.store(true, Ordering::SeqCst);
    yield_forever()
}

/// First thread of the peer child process, holding the root endpoint: receives that endpoint again
/// into descriptor 1 and sends on it, then sends dom0 a page of the shared image.
extern "C" fn peer_child() -> ! {
    ok(NR_RECEIVE_ENDPOINT, unsafe { sys_receive_endpoint(ROOT_ENDPOINT, 1) });
    ok(NR_SEND_EMPTY, unsafe { sys_send_empty(1) });
    ok(NR_SEND_PAGES, unsafe { sys_send_pages(ROOT_ENDPOINT, (&raw const SHARED_PAGE) as usize, 1) });
    // The IO page dom0 sends: device memory is never shared, so the rendezvous fails its owner check on both sides.
    fund(4);
    expect_error("receive_pages of an IO page", unsafe { sys_receive_pages(ROOT_ENDPOINT, VA_IO, 1) }, "ErrorIpcPageOwnerMismatch");
    log::info!("self-test: io_send ok (refused)");
    PEER_DONE.store(true, Ordering::SeqCst);
    yield_forever()
}

/// Root thread of the child container, holding dom0's root endpoint: moves its funding to itself,
/// starts a thread that keeps its CPU busy, receives a CPU from dom0, and brings it online.
extern "C" fn container_child() -> ! {
    ok(NR_ALLOC_QUOTA_4K, unsafe { sys_alloc_quota_4k(CONTAINER_FUNDING - CONTAINER_PROCESS_QUOTA) });
    ok(NR_ALLOC_THREAD_QUOTA_4K, unsafe { sys_alloc_thread_quota_4k(CONTAINER_FUNDING) });
    ok(NR_NEW_THREAD, unsafe { sys_new_thread(entry(yield_forever), stack_top(&raw const CONTAINER_YIELD_STACK)) });
    let cpu = ok(NR_RECEIVE_CPU, unsafe { sys_receive_cpu(ROOT_ENDPOINT) });
    if cpu != 3 {
        log::error!("self-test: receive_cpu returned CPU {}, expected 3", cpu);
        unsafe { sys_debug_exit(1) };
    }
    ok(NR_CPU_ONLINE, unsafe { sys_cpu_online(cpu) });
    CONTAINER_CPU_ONLINED.store(true, Ordering::SeqCst);
    yield_forever()
}

/// Root thread of a child container that never runs: its only CPU has no processor.
extern "C" fn never_runs() -> ! {
    log::error!("self-test: the container on an absent CPU ran");
    unsafe { sys_debug_exit(1) }
}

/// 4K, 2M, and 1G pages: fresh pages read as zero and hold what is written; 2M blocks split and merge.
/// Returns false when the boot found no free 1G block.
fn test_memory() -> bool {
    fund(256);
    ok(NR_MMAP_4K, unsafe { sys_mmap_4k(VA_4K, 4) });
    for i in 0..4 {
        expect_word("a fresh 4K page", VA_4K + i * 4096, 0);
        unsafe { ((VA_4K + i * 4096) as *mut u64).write_volatile(MAGIC ^ i as u64) };
        expect_word("a written 4K page", VA_4K + i * 4096, MAGIC ^ i as u64);
    }
    ok(NR_UNMAP_4K, unsafe { sys_unmap_4k(VA_4K, 4) });

    ok(NR_ALLOC_QUOTA_2M, unsafe { sys_alloc_quota_2m(1) });
    ok(NR_ALLOC_THREAD_QUOTA_2M, unsafe { sys_alloc_thread_quota_2m(1) });
    ok(NR_MMAP_2M, unsafe { sys_mmap_2m(VA_2M, 1) });
    for off in [0, SIZE_2M / 2, SIZE_2M - 8] {
        expect_word("a fresh 2M page", VA_2M + off, 0);
        unsafe { ((VA_2M + off) as *mut u64).write_volatile(MAGIC ^ off as u64) };
        expect_word("a written 2M page", VA_2M + off, MAGIC ^ off as u64);
    }
    // The unmap refunds the 2M quota to the thread, which splits it into 512 4K quota and merges back.
    ok(NR_UNMAP_2M, unsafe { sys_unmap_2m(VA_2M, 1) });
    ok_eq(NR_SPLIT_2M, unsafe { sys_split_2m(1) }, 1);
    ok_eq(NR_MERGE_2M, unsafe { sys_merge_2m(1) }, 1);

    let ret = unsafe { sys_alloc_quota_1g(1) };
    if error_name(ret) == "ErrorContainerQuotaInsufficient" {
        log::info!("self-test: the 1G syscalls are skipped: the boot found no free 1G block (no CPUID pdpe1gb)");
        return false;
    }
    ok(NR_ALLOC_QUOTA_1G, ret);
    ok(NR_ALLOC_THREAD_QUOTA_1G, unsafe { sys_alloc_thread_quota_1g(1) });
    ok(NR_MMAP_1G, unsafe { sys_mmap_1g(VA_1G, 1) });
    for off in [0, SIZE_1G / 2, SIZE_1G - 8] {
        expect_word("a fresh 1G page", VA_1G + off, 0);
        unsafe { ((VA_1G + off) as *mut u64).write_volatile(MAGIC ^ off as u64) };
        expect_word("a written 1G page", VA_1G + off, MAGIC ^ off as u64);
    }
    ok(NR_UNMAP_1G, unsafe { sys_unmap_1g(VA_1G, 1) });
    true
}

/// VT-d with QEMU's `edu`: once attached to dom0's IOMMU table, the device reads a page dom0 maps
/// at the probe IOVA and faults again once it is unmapped.
fn test_iommu() {
    let bdf = unsafe { sys_debug_dma_device() };
    if bdf < 0 {
        fail("finding the DMA test device (QEMU edu)", bdf);
    }
    DMA_BDF.store(bdf as usize, Ordering::SeqCst);
    let (bus, dev, fun) = dma_bdf();
    let (id, _, bar_pages) = unsafe { sys_pci_info(bus, dev, fun) };
    if id < 0 || id as usize & 0xffff_ffff != EDU_VENDOR_DEVICE || bar_pages == 0 {
        log::error!("self-test: pci_info of {:02x}:{:02x}.{} returned {:#x} with {} BAR0 pages", bus, dev, fun, id, bar_pages);
        unsafe { sys_debug_exit(1) };
    }
    log::info!("self-test: pci_info ok");
    ok(NR_PCI_ATTACH_DMA, unsafe { sys_pci_attach_dma(bus, dev, fun) });
    ok(NR_MMAP_4K, unsafe { sys_mmap_4k(VA_DMA, 1) });
    unsafe { (VA_DMA as *mut u64).write_volatile(MAGIC) };
    ok(NR_IOMMU_MAP_4K, unsafe { sys_iommu_map_4k(VA_DMA, PROBE_IOVA, 1) });
    let reason = unsafe { sys_debug_dma_probe() };
    if reason != 0 {
        fail("DMA read of the IOMMU-mapped page", reason);
    }
    ok(NR_IOMMU_UNMAP_4K, unsafe { sys_iommu_unmap_4k(PROBE_IOVA, 1) });
    let reason = unsafe { sys_debug_dma_probe() };
    if reason <= 0 {
        fail("DMA read after iommu_unmap_4k (expected a fault)", reason);
    }
    ok(NR_UNMAP_4K, unsafe { sys_unmap_4k(VA_DMA, 1) });
}

/// Device memory through the boot IO leaves of edu's BAR0, which dom0's IOMMU table has attached: reads the
/// identification register, checks that an IO page cannot be IOMMU-mapped, and unmaps another IO page, which nothing
/// maps back.
fn test_io() {
    let (bus, dev, fun) = dma_bdf();
    let (_, bar0, bar_pages) = unsafe { sys_pci_info(bus, dev, fun) };
    let page = PCI_BAR_WINDOW_BASE + (bar0 & !0xfff);
    IO_PAGE.store(page, Ordering::SeqCst);
    IO_ID_OFFSET.store(bar0 & 0xfff, Ordering::SeqCst);
    let id = unsafe { ((PCI_BAR_WINDOW_BASE + bar0) as *const u32).read_volatile() } as usize;
    if id & 0xff != 0xed {
        log::error!("self-test: edu identification at {:#x} reads {:#x}", PCI_BAR_WINDOW_BASE + bar0, id);
        unsafe { sys_debug_exit(1) };
    }
    IO_ID.store(id, Ordering::SeqCst);
    log::info!("self-test: io_read ok");

    fund(4);
    expect_error("iommu_map_4k of an IO page", unsafe { sys_iommu_map_4k(page + 4096, PROBE_IOVA, 1) }, "ErrorIommuVaNotMapped");
    log::info!("self-test: iommu_io ok (refused)");

    let last = page + (bar_pages - 1) * 4096;
    ok(NR_UNMAP_4K, unsafe { sys_unmap_4k(last, 1) });
    let ret = unsafe { sys_unmap_4k(last, 1) };
    if ret >= 0 {
        fail("unmap_4k of an unmapped IO page (expected an error)", ret);
    }
    let ret = unsafe { sys_iommu_map_4k(last, PROBE_IOVA, 1) };
    if ret >= 0 {
        fail("iommu_map_4k of an unmapped IO page (expected an error)", ret);
    }
    expect_io_id("the IO page next to an unmapped one", page);
    log::info!("self-test: io_unmap ok");
}

/// A BAR above 4 GiB, when the boot has one (QEMU ivshmem's BAR2 in the extra high-BAR boot): written and read back
/// at both ends through its boot IO leaves.
fn test_high_bar() {
    let mut i = 0;
    loop {
        let (key, base, size) = unsafe { sys_pci_bar(i) };
        if key < 0 {
            log::info!("self-test: io_high_bar skipped: no ivshmem BAR above 4 GiB");
            return;
        }
        let key = key as usize;
        if key >> 24 == IVSHMEM_VENDOR_DEVICE && key & 0xff == 2 && base >= 1 << 32 {
            for va in [PCI_BAR_WINDOW_BASE + base, PCI_BAR_WINDOW_BASE + base + size - 8] {
                unsafe { (va as *mut u64).write_volatile(MAGIC ^ va as u64) };
                expect_word("an ivshmem word above 4 GiB", va, MAGIC ^ va as u64);
            }
            log::info!("self-test: io_high_bar ok (BAR2 at {:#x}, {:#x} bytes)", base, size);
            return;
        }
        i += 1;
    }
}

/// Threads and IPC on dom0's CPU: a new endpoint, a second thread on it that answers every IPC kind
/// and exits, which fails dom0's last call with ErrorIpcCalleeExited.
fn test_ipc() {
    fund(4);
    ok(NR_NEW_ENDPOINT, unsafe { sys_new_endpoint(NEW_ENDPOINT) });
    ok(NR_NEW_THREAD_WITH_ENDPOINT, unsafe { sys_new_thread_with_endpoint(NEW_ENDPOINT, entry(ipc_thread), stack_top(&raw const IPC_STACK)) });
    let ret = retry("send_empty_no_block", "ErrorIpcNoPeer", || unsafe { sys_send_empty_no_block(NEW_ENDPOINT) });
    ok(NR_SEND_EMPTY_NO_BLOCK, ret);
    let ret = retry("receive_empty_no_block", "ErrorIpcNoPeer", || unsafe { sys_receive_empty_no_block(NEW_ENDPOINT) });
    ok(NR_RECEIVE_EMPTY_NO_BLOCK, ret);
    ok(NR_SEND_EMPTY, unsafe { sys_send_empty(NEW_ENDPOINT) });
    ok(NR_RECEIVE_EMPTY, unsafe { sys_receive_empty(NEW_ENDPOINT) });
    ok_eq(NR_CALL_USIZE, unsafe { sys_call_usize(NEW_ENDPOINT, 41) }, 42);
    ok_eq(NR_CALL, unsafe { sys_call(NEW_ENDPOINT) }, 0);
    expect_error("call to the exiting thread", unsafe { sys_call(NEW_ENDPOINT) }, "ErrorIpcCalleeExited");
    pass(NR_THREAD_EXIT);
}

/// Child processes sharing dom0's image: one with an IOMMU table that takes the DMA device, one that
/// receives the root endpoint and sends a page back, and a plain one that keeps yielding. The first
/// two are killed; the plain one and a yielding thread of dom0 keep CPUs busy for `test_cpus`.
fn test_processes() {
    let (image, pages) = image_range();
    let (bus, dev, fun) = dma_bdf();
    fund(3 * (6 + 3 * pages) + 2);
    let ret = unsafe { sys_new_process_with_iommu_and_endpoint(image, pages, ROOT_ENDPOINT, entry(iommu_child), stack_top(&raw const IOMMU_CHILD_STACK)) };
    ok(NR_NEW_PROCESS_WITH_IOMMU_AND_ENDPOINT, ret);
    ok(NR_SEND_PCI, unsafe { sys_send_pci(ROOT_ENDPOINT, bus, dev, fun) });
    wait_yield("the IOMMU child to attach the device", || IOMMU_CHILD_ATTACHED.load(Ordering::SeqCst));

    let ret = unsafe { sys_new_process_with_endpoint(image, pages, ROOT_ENDPOINT, entry(peer_child), stack_top(&raw const PEER_STACK)) };
    ok(NR_NEW_PROCESS_WITH_ENDPOINT, ret);
    ok(NR_SEND_ENDPOINT, unsafe { sys_send_endpoint(ROOT_ENDPOINT, ROOT_ENDPOINT) });
    ok(NR_RECEIVE_EMPTY, unsafe { sys_receive_empty(ROOT_ENDPOINT) });
    ok(NR_RECEIVE_PAGES, unsafe { sys_receive_pages(ROOT_ENDPOINT, VA_PAGES, 1) });
    unsafe { (VA_PAGES as *mut u64).write_volatile(MAGIC) };
    expect_word("the page sent by the peer child, through its own mapping", (&raw const SHARED_PAGE) as usize, MAGIC);
    expect_error("send_pages of an IO page", unsafe { sys_send_pages(ROOT_ENDPOINT, IO_PAGE.load(Ordering::SeqCst), 1) }, "ErrorIpcPageOwnerMismatch");
    wait_yield("the peer child", || PEER_DONE.load(Ordering::SeqCst));

    ok(NR_NEW_PROCESS, unsafe { sys_new_process(image, pages, entry(yield_forever), stack_top(&raw const PLAIN_STACK)) });
    ok(NR_NEW_THREAD, unsafe { sys_new_thread(entry(yield_forever), stack_top(&raw const YIELD_STACK)) });
    // Children are numbered in creation order: the IOMMU child, then the peer child.
    ok(NR_KILL_PROCESS, unsafe { sys_kill_process(0) });
    ok(NR_KILL_PROCESS, unsafe { sys_kill_process(0) });
}

/// CPU 1 comes online and pulls a yielding thread (or dom0's). Then whichever of CPUs 0 and 1 dom0 does
/// not run on goes Off at its yielding thread's next yield and comes back online: dom0 must not take
/// its own CPU Off, since a thread left on an Off CPU waits there until the CPU is online again.
fn test_cpus() {
    ok(NR_CPU_ONLINE, unsafe { sys_cpu_online(1) });
    wait_yield("a dom0 thread on CPU 1", || SEEN_CPUS.load(Ordering::SeqCst) & 0b10 != 0);
    let target = match current_cpu() {
        0 => 1,
        1 => 0,
        cpu => fail("dom0 runs on neither CPU 0 nor CPU 1", -(cpu as isize)),
    };
    ok(NR_CPU_OFFLINE_REQUEST, unsafe { sys_cpu_offline_request(target) });
    let ret = retry("cpu_online after cpu_offline_request", "ErrorCpuNotOff", || unsafe { sys_cpu_online(target) });
    ok(NR_CPU_ONLINE, ret);
}

/// Two child containers: one gets CPU 2 and the root endpoint, runs once dom0 brings CPU 2 online,
/// receives CPU 3 from dom0 and brings it online; the other gets an absent CPU and never runs. Both
/// are killed.
fn test_containers() {
    let (image, pages) = image_range();
    // Each container takes 2 of the thread's 2M quota: the one merge_2m left plus 3 of the boot's 4.
    fund(2 * (9 + CONTAINER_FUNDING + 3 * pages));
    ok(NR_ALLOC_QUOTA_2M, unsafe { sys_alloc_quota_2m(3) });
    ok(NR_ALLOC_THREAD_QUOTA_2M, unsafe { sys_alloc_thread_quota_2m(3) });
    let ret = unsafe {
        sys_new_container_with_endpoint(image, pages, CONTAINER_FUNDING, CONTAINER_PROCESS_QUOTA, 2, ROOT_ENDPOINT, entry(container_child), stack_top(&raw const CONTAINER_STACK))
    };
    ok(NR_NEW_CONTAINER_WITH_ENDPOINT, ret.rax);
    ok(NR_CPU_ONLINE_CHILD, unsafe { sys_cpu_online_child(0, 2) });
    ok(NR_SEND_CPU, unsafe { sys_send_cpu(ROOT_ENDPOINT, 3) });
    wait_yield("the child container to bring CPU 3 online", || CONTAINER_CPU_ONLINED.load(Ordering::SeqCst));
    ok(NR_CPU_OFFLINE_REQUEST_CHILD, unsafe { sys_cpu_offline_request_child(0, 3) });

    let ret = unsafe { sys_new_container(image, pages, CONTAINER_FUNDING, CONTAINER_PROCESS_QUOTA, ABSENT_CPU, entry(never_runs), stack_top(&raw const IOMMU_CHILD_STACK)) };
    ok(NR_NEW_CONTAINER, ret.rax);
    ok(NR_KILL_CONTAINER, unsafe { sys_kill_container(1) });
    ok(NR_KILL_CONTAINER, unsafe { sys_kill_container(0) });
    expect_error("kill_container without children", unsafe { sys_kill_container(0) }, "ErrorInvalidChild");
}

#[no_mangle]
pub extern "C" fn _start() -> ! {
    vsys::logger::init_logging_with_level(log::Level::Info);
    log::info!("Hello from dom0!");
    ok(NR_SCHEDULE, unsafe { sys_schedule() });
    if unsafe { sys_debug_null(false) } != 0 || unsafe { sys_debug_null(true) } != 0 {
        log::error!("self-test: debug_null failed");
        unsafe { sys_debug_exit(1) };
    }
    log::info!("self-test: debug_null ok");
    let has_1g = test_memory();
    test_iommu();
    test_io();
    test_high_bar();
    test_ipc();
    test_processes();
    test_cpus();
    test_containers();
    // The plain child, the last child process.
    ok(NR_KILL_PROCESS, unsafe { sys_kill_process(0) });
    expect_error("kill_process without children", unsafe { sys_kill_process(0) }, "ErrorInvalidChild");

    let passed = PASSED.load(Ordering::SeqCst);
    let mut missing = false;
    for (nr, name) in SYSCALLS {
        if passed & (1 << nr) == 0 && (has_1g || !SYSCALLS_1G.contains(&nr)) {
            log::error!("self-test: {} was not exercised", name);
            missing = true;
        }
    }
    if missing {
        unsafe { sys_debug_exit(1) };
    }
    log::info!("dom0 self-test passed");
    unsafe { sys_debug_exit(0) };
}

#[panic_handler]
pub fn panic(info: &PanicInfo) -> ! {
    log::error!("dom0 panic: {}", info);
    unsafe { sys_debug_exit(1) };
}
