//! User-side syscall stubs for VeriFlat.
//!
//! Syscall ABI (see `kernel/src/syscalls/mod.rs`):
//!
//! | Register | User            | Kernel handler        |
//! |----------|-----------------|-----------------------|
//! | rax      | syscall number  | return value          |
//! | rdi      | arg #1          | arg #1                |
//! | rsi      | arg #2          | arg #2 / return #3    |
//! | rdx      | arg #3          | arg #3 / return #2    |
//! | r8       | arg #4          | arg #4                |
//! | r9       | arg #5          | arg #5                |
//! | r12      | arg #6          | read from the frame   |
//! | r13      | arg #7          | read from the frame   |
//! | r14      | arg #8          | read from the frame   |
//!
//! Return values: `rax >= 0` is a success value (`Success` is 0). A model error is
//! `-(MODEL_ERROR_BASE + i)` where `i` is the variant's position in `RetValueType`; `-1` and
//! `-2` are trap-layer errors (see `error_name`). Pair and triple results put the second and
//! third values in `rdx` and `rsi`.

#![no_std]

pub mod logger;

use core::arch::asm;

pub use logger::init_logging;

pub const MAX_SYSCALLS: usize = 64;

// ---- trap-layer only (not part of the verified model) ----
pub const NR_DEBUG_PRINT: usize = 0;
pub const NR_DEBUG_EXIT: usize = 1;
/// The B/D/F of the kernel's DMA test device (`bus << 8 | device << 3 | function`).
pub const NR_DEBUG_DMA_DEVICE: usize = 28;
/// Has the DMA test device read through the IOMMU; returns the VT-d fault reason, 0 if none.
pub const NR_DEBUG_DMA_PROBE: usize = 29;
/// Returns 0 at once; with a nonzero argument the return goes through `iretq` instead of `sysretq`.
pub const NR_DEBUG_NULL: usize = 36;
// ---- verified entries (SystemCalls.md section 14) ----
pub const NR_ALLOC_QUOTA_4K: usize = 2;
pub const NR_SCHEDULE: usize = 3;
pub const NR_CPU_OFFLINE_REQUEST: usize = 4;
pub const NR_CPU_ONLINE: usize = 5;
pub const NR_NEW_THREAD: usize = 6;
pub const NR_NEW_THREAD_WITH_ENDPOINT: usize = 7;
pub const NR_MMAP_4K: usize = 8;
pub const NR_UNMAP_4K: usize = 9;
pub const NR_NEW_PROCESS: usize = 10;
pub const NR_NEW_PROCESS_WITH_ENDPOINT: usize = 11;
pub const NR_NEW_PROCESS_WITH_IOMMU_AND_ENDPOINT: usize = 12;
pub const NR_NEW_CONTAINER: usize = 13;
pub const NR_SEND_EMPTY: usize = 14;
pub const NR_RECEIVE_EMPTY: usize = 15;
pub const NR_SEND_EMPTY_NO_BLOCK: usize = 16;
pub const NR_RECEIVE_EMPTY_NO_BLOCK: usize = 17;
pub const NR_SEND_CPU: usize = 18;
pub const NR_RECEIVE_CPU: usize = 19;
pub const NR_SEND_PCI: usize = 20;
pub const NR_RECEIVE_PCI: usize = 21;
pub const NR_SEND_ENDPOINT: usize = 22;
pub const NR_RECEIVE_ENDPOINT: usize = 23;
pub const NR_SEND_PAGES: usize = 24;
pub const NR_RECEIVE_PAGES: usize = 25;
pub const NR_PCI_ATTACH_DMA: usize = 26;
pub const NR_ALLOC_THREAD_QUOTA_4K: usize = 27;
pub const NR_ALLOC_QUOTA_2M: usize = 30;
pub const NR_ALLOC_THREAD_QUOTA_2M: usize = 31;
pub const NR_NEW_CONTAINER_WITH_ENDPOINT: usize = 32;
pub const NR_CPU_OFFLINE_REQUEST_CHILD: usize = 33;
pub const NR_CPU_ONLINE_CHILD: usize = 34;
pub const NR_NEW_ENDPOINT: usize = 35;
pub const NR_CALL: usize = 37;
pub const NR_CALL_USIZE: usize = 38;
pub const NR_RECEIVE_CALL: usize = 39;
pub const NR_REPLY_AND_RECEIVE: usize = 40;
pub const NR_REPLY_AND_RECEIVE_USIZE: usize = 41;

/// Trap-layer error codes, returned in `rax`.
pub const ERR_INVALID_SYSCALL: isize = -1;
pub const ERR_INVALID_ARGUMENT: isize = -2;

/// Model errors are returned as `-(MODEL_ERROR_BASE + index)`.
pub const MODEL_ERROR_BASE: isize = 100;

/// `RetValueType` variants in declaration order; the kernel's `error_index` mirrors it.
const RET_VALUE_NAMES: [&str; 42] = [
    "SuccessUsize", "SuccessSeqUsize", "SuccessPairUsize", "SuccessThreeUsize", "Success", "ErrorNoQuota",
    "ErrorVaInUse", "CpuIdle", "Error", "Else", "NoQuota", "VaInUse", "ErrorContainerKilled",
    "ErrorContainerQuotaInsufficient", "ErrorProcessKilled", "ErrorThreadKilled", "ErrorNoPcid",
    "ErrorInvalidEndpoint", "ErrorIpcNoPeer", "ErrorIpcSameDirection", "ErrorIpcTypeMismatch",
    "ErrorIpcPeerKilled", "ErrorIpcSameProcess", "ErrorIpcSameContainer", "ErrorIpcCpuOwnerMismatch",
    "ErrorIpcCpuNotOff", "ErrorIpcPciOwnerMismatch", "ErrorPciOwnerMismatch", "ErrorPciNoIommuTable",
    "ErrorPciAlreadyAttached", "ErrorCpuOwnerMismatch", "ErrorCpuAlreadyOff", "ErrorCpuNotOff",
    "ErrorIpcSourceUnmapped", "ErrorIpcPageOwnerMismatch", "ErrorIpcEndpointSourceInvalid",
    "ErrorIpcEndpointTargetInUse", "ErrorIpcEndpointOwnerMismatch", "ErrorCallAcrossContainers",
    "ErrorReplyOutOfPhase", "ErrorProcessQuotaOverflow", "ErrorThreadQuotaOverflow",
];

/// Names the result in `rax`.
pub fn error_name(rax: isize) -> &'static str {
    match rax {
        r if r >= 0 => "Success",
        ERR_INVALID_SYSCALL => "InvalidSyscall",
        ERR_INVALID_ARGUMENT => "InvalidArgument",
        r => usize::try_from(-r - MODEL_ERROR_BASE).ok().and_then(|i| RET_VALUE_NAMES.get(i).copied()).unwrap_or("Unknown"),
    }
}

/// A syscall result: `rax` plus the optional second and third values.
#[derive(Debug, Clone, Copy)]
pub struct SysResult {
    pub rax: isize,
    pub rdx: usize,
    pub rsi: usize,
}

impl SysResult {
    pub fn is_ok(&self) -> bool {
        self.rax >= 0
    }
}

macro_rules! raw_syscall {
    ($nr:expr, $a:expr, $b:expr, $c:expr, $d:expr, $e:expr, $f:expr, $g:expr) => {{
        let rax: isize;
        let rdx: usize;
        let rsi: usize;
        asm!(
            "push r12",
            "push r13",
            "mov r12, {f}",
            "mov r13, {g}",
            "syscall",
            "pop r13",
            "pop r12",
            f = in(reg) $f as usize,
            g = in(reg) $g as usize,
            inout("rax") $nr as usize => rax,
            inout("rdi") $a as usize => _,
            inout("rsi") $b as usize => rsi,
            inout("rdx") $c as usize => rdx,
            inout("r8") $d as usize => _,
            inout("r9") $e as usize => _,
            out("rcx") _,
            out("r10") _,
            out("r11") _,
        );
        SysResult { rax, rdx, rsi }
    }};
}

pub unsafe fn syscall7(nr: usize, a: usize, b: usize, c: usize, d: usize, e: usize, f: usize, g: usize) -> SysResult {
    raw_syscall!(nr, a, b, c, d, e, f, g)
}

/// The eight-argument form for `NR_NEW_CONTAINER_WITH_ENDPOINT`: arguments six to eight travel in `r12`, `r13`,
/// and `r14`, which the kernel restores on return.
pub unsafe fn syscall8(nr: usize, a: usize, b: usize, c: usize, d: usize, e: usize, f: usize, g: usize, h: usize) -> SysResult {
    let rax: isize;
    let rdx: usize;
    let rsi: usize;
    asm!(
        "syscall",
        inout("rax") nr => rax,
        inout("rdi") a => _,
        inout("rsi") b => rsi,
        inout("rdx") c => rdx,
        inout("r8") d => _,
        inout("r9") e => _,
        in("r12") f,
        in("r13") g,
        in("r14") h,
        out("rcx") _,
        out("r10") _,
        out("r11") _,
    );
    SysResult { rax, rdx, rsi }
}

pub unsafe fn syscall0(nr: usize) -> SysResult {
    syscall7(nr, 0, 0, 0, 0, 0, 0, 0)
}

pub unsafe fn syscall1(nr: usize, a: usize) -> SysResult {
    syscall7(nr, a, 0, 0, 0, 0, 0, 0)
}

pub unsafe fn syscall2(nr: usize, a: usize, b: usize) -> SysResult {
    syscall7(nr, a, b, 0, 0, 0, 0, 0)
}

pub unsafe fn syscall3(nr: usize, a: usize, b: usize, c: usize) -> SysResult {
    syscall7(nr, a, b, c, 0, 0, 0, 0)
}

pub unsafe fn syscall4(nr: usize, a: usize, b: usize, c: usize, d: usize) -> SysResult {
    syscall7(nr, a, b, c, d, 0, 0, 0)
}

pub unsafe fn syscall5(nr: usize, a: usize, b: usize, c: usize, d: usize, e: usize) -> SysResult {
    syscall7(nr, a, b, c, d, e, 0, 0)
}

// ---- trap-layer debug entries ----

pub unsafe fn sys_debug_print(data: *const u8, len: usize) -> isize {
    syscall2(NR_DEBUG_PRINT, data as usize, len).rax
}

/// Shuts down the machine (QEMU exits with `(code << 1) | 1`).
pub unsafe fn sys_debug_exit(code: usize) -> ! {
    syscall1(NR_DEBUG_EXIT, code);
    loop {}
}

// ---- verified entries ----

pub unsafe fn sys_alloc_quota_4k(alloc_amount: usize) -> isize {
    syscall1(NR_ALLOC_QUOTA_4K, alloc_amount).rax
}

/// Moves `alloc_amount` 4K quota from the calling process to the calling thread.
pub unsafe fn sys_alloc_thread_quota_4k(alloc_amount: usize) -> isize {
    syscall1(NR_ALLOC_THREAD_QUOTA_4K, alloc_amount).rax
}

pub unsafe fn sys_alloc_quota_2m(alloc_amount: usize) -> isize {
    syscall1(NR_ALLOC_QUOTA_2M, alloc_amount).rax
}

/// Moves `alloc_amount` 2M quota from the calling process to the calling thread.
pub unsafe fn sys_alloc_thread_quota_2m(alloc_amount: usize) -> isize {
    syscall1(NR_ALLOC_THREAD_QUOTA_2M, alloc_amount).rax
}

pub unsafe fn sys_schedule() -> isize {
    syscall0(NR_SCHEDULE).rax
}

pub unsafe fn sys_cpu_offline_request(target: usize) -> isize {
    syscall1(NR_CPU_OFFLINE_REQUEST, target).rax
}

pub unsafe fn sys_cpu_online(target: usize) -> isize {
    syscall1(NR_CPU_ONLINE, target).rax
}

/// Asks `target`, a cpu of the `child`-th child of the caller's container, to go Off.
pub unsafe fn sys_cpu_offline_request_child(child: usize, target: usize) -> isize {
    syscall2(NR_CPU_OFFLINE_REQUEST_CHILD, child, target).rax
}

/// Brings `target`, an Off cpu of the `child`-th child of the caller's container, back to Idle.
pub unsafe fn sys_cpu_online_child(child: usize, target: usize) -> isize {
    syscall2(NR_CPU_ONLINE_CHILD, child, target).rax
}

/// The new thread starts at `ip` with stack pointer `sp`; the other registers are copied
/// from the caller at the time of the call.
pub unsafe fn sys_new_thread(ip: usize, sp: usize) -> isize {
    syscall2(NR_NEW_THREAD, ip, sp).rax
}

pub unsafe fn sys_new_thread_with_endpoint(endpoint_index: usize, ip: usize, sp: usize) -> isize {
    syscall3(NR_NEW_THREAD_WITH_ENDPOINT, endpoint_index, ip, sp).rax
}

/// Creates an empty receive endpoint of the caller's container at the caller's empty descriptor
/// `endpoint_index`, funded by one 4K quota of the calling thread.
pub unsafe fn sys_new_endpoint(endpoint_index: usize) -> isize {
    syscall1(NR_NEW_ENDPOINT, endpoint_index).rax
}

pub unsafe fn sys_mmap_4k(va: usize, range: usize) -> isize {
    syscall2(NR_MMAP_4K, va, range).rax
}

pub unsafe fn sys_unmap_4k(va: usize, range: usize) -> isize {
    syscall2(NR_UNMAP_4K, va, range).rax
}

pub unsafe fn sys_new_process(va: usize, range: usize, ip: usize, sp: usize) -> isize {
    syscall4(NR_NEW_PROCESS, va, range, ip, sp).rax
}

pub unsafe fn sys_new_process_with_endpoint(va: usize, range: usize, endpoint_index: usize, ip: usize, sp: usize) -> isize {
    syscall5(NR_NEW_PROCESS_WITH_ENDPOINT, va, range, endpoint_index, ip, sp).rax
}

pub unsafe fn sys_new_process_with_iommu_and_endpoint(va: usize, range: usize, endpoint_index: usize, ip: usize, sp: usize) -> isize {
    syscall5(NR_NEW_PROCESS_WITH_IOMMU_AND_ENDPOINT, va, range, endpoint_index, ip, sp).rax
}

/// Returns `(container, process, thread)` pointers on success.
pub unsafe fn sys_new_container(va: usize, range: usize, funding_page_count: usize, process_quota_4k: usize, transfer_cpu_id: usize, ip: usize, sp: usize) -> SysResult {
    syscall7(NR_NEW_CONTAINER, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, ip, sp)
}

/// As `sys_new_container`; the root thread of the child holds, in descriptor 0, the caller's endpoint
/// `endpoint_index`.
pub unsafe fn sys_new_container_with_endpoint(
    va: usize, range: usize, funding_page_count: usize, process_quota_4k: usize, transfer_cpu_id: usize, endpoint_index: usize, ip: usize, sp: usize,
) -> SysResult {
    syscall8(NR_NEW_CONTAINER_WITH_ENDPOINT, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index, ip, sp)
}

pub unsafe fn sys_send_empty(endpoint_index: usize) -> isize {
    syscall1(NR_SEND_EMPTY, endpoint_index).rax
}

pub unsafe fn sys_receive_empty(endpoint_index: usize) -> isize {
    syscall1(NR_RECEIVE_EMPTY, endpoint_index).rax
}

pub unsafe fn sys_send_empty_no_block(endpoint_index: usize) -> isize {
    syscall1(NR_SEND_EMPTY_NO_BLOCK, endpoint_index).rax
}

pub unsafe fn sys_receive_empty_no_block(endpoint_index: usize) -> isize {
    syscall1(NR_RECEIVE_EMPTY_NO_BLOCK, endpoint_index).rax
}

/// Calls the receive-call waiter at the head of `endpoint_index` and returns its reply.
pub unsafe fn sys_call(endpoint_index: usize) -> isize {
    syscall1(NR_CALL, endpoint_index).rax
}

/// `sys_call` carrying `value`; the callee's `receive_call` or `reply_and_receive` returns it.
pub unsafe fn sys_call_usize(endpoint_index: usize, value: usize) -> isize {
    syscall2(NR_CALL_USIZE, endpoint_index, value).rax
}

/// Waits for a call on `endpoint_index` and returns the caller's value, or 0 for a plain call.
pub unsafe fn sys_receive_call(endpoint_index: usize) -> isize {
    syscall1(NR_RECEIVE_CALL, endpoint_index).rax
}

/// Replies to the recorded caller, then waits for the next call on `endpoint_index`.
pub unsafe fn sys_reply_and_receive(endpoint_index: usize) -> isize {
    syscall1(NR_REPLY_AND_RECEIVE, endpoint_index).rax
}

/// `sys_reply_and_receive` replying `value` to the caller.
pub unsafe fn sys_reply_and_receive_usize(endpoint_index: usize, value: usize) -> isize {
    syscall2(NR_REPLY_AND_RECEIVE_USIZE, endpoint_index, value).rax
}

pub unsafe fn sys_send_cpu(endpoint_index: usize, transfer_cpu_id: usize) -> isize {
    syscall2(NR_SEND_CPU, endpoint_index, transfer_cpu_id).rax
}

pub unsafe fn sys_receive_cpu(endpoint_index: usize) -> isize {
    syscall1(NR_RECEIVE_CPU, endpoint_index).rax
}

pub unsafe fn sys_send_pci(endpoint_index: usize, bus: usize, dev: usize, fun: usize) -> isize {
    syscall4(NR_SEND_PCI, endpoint_index, bus, dev, fun).rax
}

pub unsafe fn sys_receive_pci(endpoint_index: usize, bus: usize, dev: usize, fun: usize) -> isize {
    syscall4(NR_RECEIVE_PCI, endpoint_index, bus, dev, fun).rax
}

pub unsafe fn sys_send_endpoint(endpoint_index: usize, source_endpoint_index: usize) -> isize {
    syscall2(NR_SEND_ENDPOINT, endpoint_index, source_endpoint_index).rax
}

pub unsafe fn sys_receive_endpoint(endpoint_index: usize, target_endpoint_index: usize) -> isize {
    syscall2(NR_RECEIVE_ENDPOINT, endpoint_index, target_endpoint_index).rax
}

pub unsafe fn sys_send_pages(endpoint_index: usize, va: usize, range: usize) -> isize {
    syscall3(NR_SEND_PAGES, endpoint_index, va, range).rax
}

pub unsafe fn sys_receive_pages(endpoint_index: usize, va: usize, range: usize) -> isize {
    syscall3(NR_RECEIVE_PAGES, endpoint_index, va, range).rax
}

pub unsafe fn sys_debug_dma_device() -> isize {
    syscall0(NR_DEBUG_DMA_DEVICE).rax
}

pub unsafe fn sys_debug_dma_probe() -> isize {
    syscall0(NR_DEBUG_DMA_PROBE).rax
}

pub unsafe fn sys_debug_null(force_iret: bool) -> isize {
    syscall1(NR_DEBUG_NULL, force_iret as usize).rax
}

pub unsafe fn sys_pci_attach_dma(bus: usize, dev: usize, fun: usize) -> isize {
    syscall3(NR_PCI_ATTACH_DMA, bus, dev, fun).rax
}
