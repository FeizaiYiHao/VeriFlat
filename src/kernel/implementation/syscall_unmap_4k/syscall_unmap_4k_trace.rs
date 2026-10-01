use vstd::prelude::*;
use crate::*;
use super::syscall_unmap_4k_spec::*;

verus! {
/// Write-locking the caller's context and recording the first page is the enter step on `pre`/`post`.
pub(super) proof fn unmap_4k_enter_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, range: VaRange4K,
)
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
            &&& pagetable.lock_state is Unlocked
            &&& pre.container_map.dom().contains(container_ptr)
            &&& container.lock_state is Unlocked
            &&& !container.killed
            &&& range.wf()
            &&& range.len > 0
            &&& user_va_range(pre, range)
            &&& forall|i: int| #![trigger pagetable.mapping_4k.dom().contains(range.view()[i])] 0 <= i < range.len ==> pagetable.mapping_4k.dom().contains(range.view()[i])
        },
        post == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, ..pre.cpu_array[cpu_id as int] }),
            container_map: pre.container_map.insert(container_ptr, ContainerU { lock_state: LockStateU::WriteLocked, ..pre.container_map.spec_index(container_ptr) }),
            process_map: pre.process_map.insert(process_ptr, ProcessU {
                lock_state: LockStateU::WriteLocked,
                pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..pre.process_map.spec_index(process_ptr).pagetable->Some_0 }),
                ..pre.process_map.spec_index(process_ptr)
            }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU {
                lock_state: LockStateU::WriteLocked, syscall_progress: Some(SyscallProgress::Unmap4k { range, unmapped: 0, flushed: false }),
                ..pre.thread_map.spec_index(thread_ptr)
            }),
            ..pre
        }),
    ensures
        unmap_4k_enter_step_pre(pre, cpu_id, range),
        unmap_4k_enter_step(pre, post, cpu_id, range),
{ reveal(unmap_4k_enter_step_pre); reveal(unmap_4k_enter_step); }

/// Clearing the progress and releasing the unmap locks after the flushed range is the exit step on `pre`/`post`.
pub(super) proof fn unmap_4k_exit_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
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
            &&& process.pagetable->Some_0.lock_state is WriteLocked
            &&& pre.container_map.dom().contains(container_ptr)
            &&& pre.container_map.spec_index(container_ptr).lock_state is WriteLocked
            &&& thread.syscall_progress is Some
            &&& progress is Unmap4k
            &&& progress->Unmap4k_unmapped == progress->Unmap4k_range.len
            &&& progress->Unmap4k_flushed
        },
        post == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..pre.cpu_array[cpu_id as int] }),
            container_map: pre.container_map.insert(container_ptr, ContainerU { lock_state: LockStateU::Unlocked, ..pre.container_map.spec_index(container_ptr) }),
            process_map: pre.process_map.insert(process_ptr, ProcessU {
                lock_state: LockStateU::Unlocked,
                pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..pre.process_map.spec_index(process_ptr).pagetable->Some_0 }),
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
