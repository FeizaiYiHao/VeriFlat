use vstd::prelude::*;
use crate::*;
use super::syscall_unmap_4k_spec::*;

verus! {
/// The entry state's K facts on the running thread's cpu, container, process, and pagetable decide the unmap result `ret`.
pub(super) proof fn unmap_4k_result_from_k(krnl: &KernelK, cpu_id: CpuId, va: VAddr, range: usize, ret: RetValueType)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        !(range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range)),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).value;
            let thread_ptr = cpu.view().view().current_thread->Some_0;
            let thread = krnl.thr_mp.spec_index(thread_ptr);
            let container = krnl.ctn_mp.spec_index(thread.view().owning_container);
            let process = krnl.prc_mp.spec_index(thread.view().owning_proc);
            let table = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), process.view().pagetable);
            let va_range = VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) };
            let unowned = container.lock_process_owner_u() is None;
            let conflict = container.lock_process_owner_u() is Some && container.lock_process_owner_u()->Some_0 < LockOwnerId::Some(process.view_rodata().view().depth);
            let live = !container.being_killed() && unowned && !container.view().zombie && !process.being_killed() && !thread.being_killed();
            let mapped = spec_v2l4index(va) >= table.kernel_l4_end() && forall|j: int| #![trigger va_range.view()[j]] 0 <= j < range
                ==> table.mapping_4k().dom().contains(va_range.view()[j]) && table.mapping_4k()[va_range.view()[j]].present;
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed() && cpu.view().view().current_thread is Some
            &&& !(ret is CpuIdle) ==> krnl.thr_mp.dom().contains(thread_ptr) && krnl.prc_mp.dom().contains(thread.view().owning_proc) && krnl.ctn_mp.dom().contains(thread.view().owning_container)
            &&& ret is ErrorContainerKilled ==> container.being_killed()
            &&& ret is ErrorContainerLockOrderConflict ==> !container.being_killed() && conflict
            &&& ret is ErrorContainerZombie ==> !container.being_killed() && unowned && container.view().zombie
            &&& ret is ErrorProcessKilled ==> !container.being_killed() && unowned && !container.view().zombie && process.being_killed()
            &&& ret is ErrorThreadKilled ==> !container.being_killed() && unowned && !container.view().zombie && !process.being_killed() && thread.being_killed()
            &&& (ret is Success || ret is Error) ==> live && !process.view().zombie && krnl.pt_mp.dom().contains(process.view().pagetable)
            &&& ret is Success ==> mapped
            &&& ret is Error ==> !mapped
            &&& ret is CpuIdle || ret is ErrorContainerKilled || ret is ErrorContainerLockOrderConflict || ret is ErrorContainerZombie || ret is ErrorProcessKilled || ret is ErrorThreadKilled
                || ret is Success || ret is Error
        },
    ensures
        unmap_4k_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, range) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).value.view().view();
    let thread = krnl.thr_mp.spec_index(c.current_thread->Some_0).view();
    kernel_cpu_projection_at(krnl, cpu_id);
    if !(ret is CpuIdle) {
        kernel_cpu_thread_projection_at(krnl, cpu_id, thread.owning_proc, c.current_thread->Some_0, None); kernel_container_projection_at(krnl, thread.owning_container);
        if ret is ErrorContainerLockOrderConflict { kernel_process_projection_at(krnl, thread.owning_proc); }
        if ret is Success || ret is Error {
            kernel_l4_end_projection_at(krnl, krnl.prc_mp.spec_index(thread.owning_proc).view().pagetable); kernel_process_projection_at(krnl, thread.owning_proc);
        }
    }
}

/// Write-locking the caller's context under its process depth and recording the first page is the enter step on `pre`/`post`.
pub(super) proof fn unmap_4k_enter_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, range: VaRange4K)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thread_ptr);
            let process = pre.process_map.spec_index(process_ptr);
            let container = pre.container_map.spec_index(container_ptr);
            let pagetable = process.pagetable->Some_0;
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& cpu.current_thread == Some(thread_ptr)
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is Unlocked
            &&& thread.syscall_progress is None
            &&& !thread.killed
            &&& thread.owning_proc == process_ptr
            &&& thread.owning_container == container_ptr
            &&& pre.process_map.dom().contains(process_ptr)
            &&& process.lock_state is Unlocked
            &&& !process.killed
            &&& process.pagetable is Some
            &&& !(pagetable.lock_state is WriteLocked)
            &&& pre.container_map.dom().contains(container_ptr)
            &&& container.lock_state is Unlocked
            &&& !container.killed
            &&& !container.zombie
            &&& range.wf()
            &&& range.len > 0
            &&& user_va_range(pre, range)
            &&& forall|i: int| #![trigger pagetable.mapping_4k.dom().contains(range.view()[i])] 0 <= i < range.len ==> pagetable.mapping_4k.dom().contains(range.view()[i])
        },
        post == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..pre.cpu_array[cpu_id as int] }),
            container_map: pre.container_map.insert(container_ptr, ContainerU {
                lock_state: LockStateU::WriteLocked, lock_process_owner: Some(LockOwnerId::Some(pre.process_map.spec_index(process_ptr).depth)), ..pre.container_map.spec_index(container_ptr)
            }),
            process_map: pre.process_map.insert(process_ptr, ProcessU {
                lock_state: LockStateU::WriteLocked,
                pagetable: Some(PageTableU { lock_state: LockStateU::ReadLocked, ..pre.process_map.spec_index(process_ptr).pagetable->Some_0 }),
                ..pre.process_map.spec_index(process_ptr)
            }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, syscall_progress: Some(SyscallProgress::Unmap4k { range, unmapped: 0, flushed: false }), ..pre.thread_map.spec_index(thread_ptr) }),
            ..pre
        }),
    ensures
        unmap_4k_enter_step_pre(pre, cpu_id, range),
        unmap_4k_enter_step(pre, post, cpu_id, range),
{ reveal(unmap_4k_enter_step_pre); reveal(unmap_4k_enter_step); }

/// Clearing the progress and releasing the unmap locks after the flushed range, leaving the pagetable in `table_lock`, is the
/// exit step on `pre`/`post`.
pub(super) proof fn unmap_4k_exit_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, table_lock: LockStateU,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let thread = pre.thread_map.spec_index(thread_ptr);
            let process = pre.process_map.spec_index(process_ptr);
            let progress = thread.syscall_progress->Some_0;
            &&& pre.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is WriteLocked
            &&& thread.owning_proc == process_ptr
            &&& thread.owning_container == container_ptr
            &&& pre.process_map.dom().contains(process_ptr)
            &&& process.lock_state is WriteLocked
            &&& process.pagetable is Some
            &&& !(process.pagetable->Some_0.lock_state is Unlocked)
            &&& pre.container_map.dom().contains(container_ptr)
            &&& pre.container_map.spec_index(container_ptr).lock_state is WriteLocked
            &&& thread.syscall_progress is Some
            &&& progress is Unmap4k
            &&& progress->Unmap4k_unmapped == progress->Unmap4k_range.len
            &&& progress->Unmap4k_flushed
        },
        table_lock is Unlocked || table_lock is ReadLocked,
        post == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..pre.cpu_array[cpu_id as int] }),
            container_map: pre.container_map.insert(container_ptr, ContainerU { lock_state: LockStateU::Unlocked, lock_process_owner: None, ..pre.container_map.spec_index(container_ptr) }),
            process_map: pre.process_map.insert(process_ptr, ProcessU {
                lock_state: LockStateU::Unlocked,
                pagetable: Some(PageTableU { lock_state: table_lock, ..pre.process_map.spec_index(process_ptr).pagetable->Some_0 }),
                ..pre.process_map.spec_index(process_ptr)
            }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..pre.thread_map.spec_index(thread_ptr) }),
            ..pre
        }),
    ensures
        unmap_4k_exit_step_pre(pre, cpu_id),
        unmap_4k_exit_step(pre, post, cpu_id),
{ reveal(unmap_4k_exit_step_pre); reveal(unmap_4k_exit_step); }

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
