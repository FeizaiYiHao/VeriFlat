use vstd::prelude::*;
use crate::*;
use super::syscall_unmap_4k_spec::*;

verus! {
/// The entry state's K facts on the running thread's cpu, process, and pagetable decide the unmap result `ret`.
pub(super) proof fn unmap_4k_result_from_k(krnl: &KernelK, cpu_id: CpuId, va: VAddr, range: usize, ret: RetValueType)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        !(range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range)),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).value;
            let thread_ptr = cpu.view().view().current_thread->Some_0;
            let thread = krnl.thr_mp.spec_index(thread_ptr);
            let process = krnl.prc_mp.spec_index(thread.view().owning_proc);
            let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), process.view().pagetable);
            let va_range = VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) };
            let mapped = spec_v2l4index(va) >= table.kernel_l4_end() && forall|j: int| #![trigger va_range.view()[j]] 0 <= j < range
                ==> table.mapping_4k().dom().contains(va_range.view()[j]) && table.mapping_4k()[va_range.view()[j]].present;
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed() && cpu.view().view().current_thread is Some
            &&& !(ret is CpuIdle) ==> krnl.thr_mp.dom().contains(thread_ptr) && krnl.prc_mp.dom().contains(thread.view().owning_proc)
            &&& ret is ErrorThreadKilled ==> thread.being_killed()
            &&& (ret is Success || ret is Error) ==> !thread.being_killed() && !process.view().zombie && krnl.pt_mp.dom().contains(process.view().pagetable)
            &&& ret is Success ==> mapped
            &&& ret is Error ==> !mapped
            &&& ret is CpuIdle || ret is ErrorThreadKilled || ret is Success || ret is Error
        },
    ensures
        unmap_4k_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, range) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).value.view().view();
    let thread = krnl.thr_mp.spec_index(c.current_thread->Some_0).view();
    kernel_cpu_projection_at(krnl, cpu_id);
    if !(ret is CpuIdle) {
        kernel_cpu_thread_projection_at(krnl, cpu_id, thread.owning_proc, c.current_thread->Some_0, None);
        if ret is Success || ret is Error {
            kernel_l4_end_projection_at(krnl, krnl.prc_mp.spec_index(thread.owning_proc).view().pagetable); kernel_process_projection_at(krnl, thread.owning_proc);
        }
    }
}

/// A rejection by `unmap_4k_lock_current_thread`, stated on the entry state, is the unmap result `ret`.
pub(super) proof fn unmap_4k_lock_rejected_result_from_k(krnl: &KernelK, cpu_id: CpuId, va: VAddr, range: usize, ret: RetValueType)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        !(range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range)),
        ({
            let cpu = krnl.cpu_arr.spec_index(cpu_id).value;
            let thread_ptr = cpu.view().view().current_thread->Some_0;
            let thread = krnl.thr_mp.spec_index(thread_ptr);
            &&& ret is CpuIdle || ret is ErrorThreadKilled
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed() && cpu.view().view().current_thread is Some
            &&& !(ret is CpuIdle) ==> krnl.thr_mp.dom().contains(thread_ptr) && krnl.prc_mp.dom().contains(thread.view().owning_proc)
            &&& ret is ErrorThreadKilled ==> thread.being_killed()
        }),
    ensures
        unmap_4k_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, range) == ret,
{ unmap_4k_result_from_k(krnl, cpu_id, va, range, ret); }

/// Write-locking the caller's cpu, with the cpu inside its kernel step, and its running thread, read-locking the pagetable
/// `pagetable_ptr` of its process, setting the table's window locks to `windows`, those of `krnl` after locking the range's
/// windows, and recording the first page is the enter step from `krnl`'s projection to `post` when the syscall succeeds there.
pub(super) proof fn unmap_4k_enter_step_from_u(
    krnl: &KernelK, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr, len: usize,
    range: VaRange4K, windows: Map<WindowVa, LockStateU>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        range == (VaRange4K { start: va, len, view: Ghost(Seq::new(len as nat, |i: int| spec_va_add_range(va, i as usize))) }),
        range.wf(),
        unmap_4k_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, len) is Success,
        krnl.prc_mp.dom().contains(process_ptr),
        !krnl.prc_mp.spec_index(process_ptr).view().zombie,
        krnl.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr,
        krnl.pt_mp.dom().contains(pagetable_ptr),
        krnl.thr_mp.dom().contains(thread_ptr),
        krnl.ctn_mp.dom().contains(krnl.thr_mp.spec_index(thread_ptr).view().owning_container),
        windows == pagetable_window_locks_after_locking_range(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, range),
        {
            let pre = kernel_k_to_kernel_u(*krnl);
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thread_ptr);
            let process = pre.process_map.spec_index(process_ptr);
            let pagetable = process.pagetable->Some_0;
            &&& cpu.lock_state is Unlocked
            &&& cpu.current_thread == Some(thread_ptr)
            &&& thread.lock_state is Unlocked
            &&& thread.syscall_progress is None
            &&& thread.owning_proc == process_ptr
            &&& !(pagetable.lock_state is WriteLocked)
            &&& post == (KernelU {
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..cpu }),
                thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, syscall_progress: Some(SyscallProgress::Unmap4k { range, unmapped: 0, flushed: false }), ..thread }),
                process_map: pre.process_map.insert(process_ptr, ProcessU { pagetable: Some(PageTableU { lock_state: LockStateU::ReadLocked, pagetable_window_locks: windows, ..pagetable }), ..process }),
                ..pre
            })
        },
    ensures
        unmap_4k_enter_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, range),
        unmap_4k_enter_step(kernel_k_to_kernel_u(*krnl), post, cpu_id, range),
{
    kernel_u_domains_projection(krnl); kernel_thread_projection_at(krnl, thread_ptr); kernel_process_projection_at(krnl, process_ptr);
    reveal(unmap_4k_enter_step_pre); reveal(unmap_4k_enter_step);
}

/// Clearing the progress, unlocking the caller's cpu, which leaves its kernel step for its trap path, and its running thread,
/// and leaving the pagetable `pagetable_ptr` of its process in `table_lock` with `windows`, the window locks of `krnl` after
/// unlocking the range's windows, after the flushed range is the exit step from `krnl`'s projection to `post`.
pub(super) proof fn unmap_4k_exit_step_from_u(
    krnl: &KernelK, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, range: VaRange4K,
    table_lock: LockStateU, windows: Map<WindowVa, LockStateU>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        krnl.prc_mp.dom().contains(process_ptr),
        !krnl.prc_mp.spec_index(process_ptr).view().zombie,
        krnl.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr,
        krnl.pt_mp.dom().contains(pagetable_ptr),
        windows == pagetable_window_locks_after_unlocking_range(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, range),
        {
            let pre = kernel_k_to_kernel_u(*krnl);
            let thread = pre.thread_map.spec_index(thread_ptr);
            let process = pre.process_map.spec_index(process_ptr);
            let progress = thread.syscall_progress->Some_0;
            &&& pre.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is WriteLocked
            &&& thread.owning_proc == process_ptr
            &&& !(process.pagetable->Some_0.lock_state is Unlocked)
            &&& thread.syscall_progress is Some
            &&& progress is Unmap4k
            &&& progress->Unmap4k_range == range
            &&& progress->Unmap4k_unmapped == progress->Unmap4k_range.len
            &&& progress->Unmap4k_flushed
            &&& post == (KernelU {
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..pre.cpu_array[cpu_id as int] }),
                thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..thread }),
                process_map: pre.process_map.insert(process_ptr, ProcessU { pagetable: Some(PageTableU { lock_state: table_lock, pagetable_window_locks: windows, ..process.pagetable->Some_0 }), ..process }),
                ..pre
            })
        },
        table_lock is Unlocked || table_lock is ReadLocked,
    ensures
        unmap_4k_exit_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        unmap_4k_exit_step(kernel_k_to_kernel_u(*krnl), post, cpu_id),
{ kernel_process_projection_at(krnl, process_ptr); reveal(unmap_4k_exit_step_pre); reveal(unmap_4k_exit_step); }

/// The enter step pushed onto an empty trace is the partial trace after entering.
pub(super) proof fn unmap_4k_trace_enter_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, range: VaRange4K)
    requires
        before.len() == 0,
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        unmap_4k_enter_step_pre(pre, cpu_id, range),
        unmap_4k_enter_step(pre, post, cpu_id, range),
    ensures
        unmap_4k_trace_after_enter(steps.view(), cpu_id, range),
{ reveal(unmap_4k_trace_after_enter); }

/// The range steps appended after the enter step give the partial trace after unmapping the range.
pub(super) proof fn unmap_4k_trace_range_steps(steps: &KernelSteps, before: Seq<KernelStep>, cpu_id: CpuId, range: VaRange4K)
    requires
        unmap_4k_trace_after_enter(before, cpu_id, range),
        before.len() + range.len + 1 <= steps.view().len() <= before.len() + range.len + NUM_CPUS + MAX_CONTAINER_TREE_DEPTH + 2,
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id),
    ensures
        unmap_4k_trace_after_range(steps.view(), cpu_id, range),
{ reveal(unmap_4k_trace_after_enter); reveal(unmap_4k_trace_after_range); }

/// The exit step pushed after the unmapped partial trace completes the syscall trace.
pub(super) proof fn unmap_4k_trace_exit_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, va: VAddr, range: usize)
    requires
        unmap_4k_trace_after_range(before, cpu_id, VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) }),
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        unmap_4k_exit_step_pre(pre, cpu_id),
        unmap_4k_exit_step(pre, post, cpu_id),
    ensures
        unmap_4k_syscall_trace(steps.view(), cpu_id, va, range),
{ reveal(unmap_4k_trace_after_range); reveal(unmap_4k_syscall_trace); }
} // verus!
