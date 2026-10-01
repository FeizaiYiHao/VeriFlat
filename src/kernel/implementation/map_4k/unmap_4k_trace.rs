use vstd::prelude::*;
use crate::*;
use super::unmap_4k_spec::*;

verus! {
/// Clearing the next recorded page under the unmap locks is the leaf step on `pre`/`post`.
pub proof fn unmap_4k_leaf_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, va: VAddr)
    requires
        unmap_4k_locked(pre, cpu_id),
        {
            let thread = pre.thread_map.spec_index(thread_ptr);
            let process = pre.process_map.spec_index(process_ptr);
            let progress = thread.syscall_progress->Some_0;
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& thread.owning_proc == process_ptr
            &&& thread.syscall_progress is Some
            &&& progress is Unmap4k
            &&& progress->Unmap4k_unmapped < progress->Unmap4k_range.len
            &&& !progress->Unmap4k_flushed
            &&& progress->Unmap4k_range.view()[progress->Unmap4k_unmapped as int] == va
            &&& process.pagetable->Some_0.mapping_4k.dom().contains(va)
            &&& post == (KernelU {
                process_map: pre.process_map.insert(process_ptr, ProcessU {
                    pagetable: Some(PageTableU { mapping_4k: process.pagetable->Some_0.mapping_4k.remove(va), ..process.pagetable->Some_0 }), ..process
                }),
                thread_map: pre.thread_map.insert(thread_ptr, ThreadU {
                    syscall_progress: Some(SyscallProgress::Unmap4k {
                        range: progress->Unmap4k_range, unmapped: (progress->Unmap4k_unmapped + 1) as usize, flushed: false,
                    }),
                    ..thread
                }),
                ..pre
            })
        },
    ensures
        unmap_4k_leaf_step_pre(pre, cpu_id),
        unmap_4k_leaf_step(pre, post, cpu_id),
{ reveal(unmap_4k_leaf_step_pre); reveal(unmap_4k_leaf_step); }

/// The caller holding the unmap locks after clearing the whole range and before recording the flush satisfies the flush precondition.
pub proof fn unmap_4k_flush_step_pre_from_u(pre: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr)
    requires
        unmap_4k_locked(pre, cpu_id),
        {
            let progress = pre.thread_map.spec_index(thread_ptr).syscall_progress->Some_0;
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& pre.thread_map.spec_index(thread_ptr).syscall_progress is Some
            &&& progress is Unmap4k
            &&& progress->Unmap4k_unmapped == progress->Unmap4k_range.len
            &&& !progress->Unmap4k_flushed
        },
    ensures
        unmap_4k_flush_step_pre(pre, cpu_id),
{ reveal(unmap_4k_flush_step_pre); }

/// Recording the flush in the progress is the flushed step on `pre`/`post`.
pub proof fn unmap_4k_flushed_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr)
    requires
        {
            let thread = pre.thread_map.spec_index(thread_ptr);
            let progress = thread.syscall_progress->Some_0;
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& thread.syscall_progress is Some
            &&& progress is Unmap4k
            &&& post == (KernelU {
                thread_map: pre.thread_map.insert(thread_ptr, ThreadU {
                    syscall_progress: Some(SyscallProgress::Unmap4k { range: progress->Unmap4k_range, unmapped: progress->Unmap4k_unmapped, flushed: true }), ..thread
                }),
                ..pre
            })
        },
    ensures
        unmap_4k_flushed_step(pre, post, cpu_id),
{ reveal(unmap_4k_flushed_step); }

/// A leaf step pushed after range steps that start at `start` is a range step.
pub proof fn unmap_4k_range_steps_from_leaf(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, post: KernelU, cpu_id: CpuId)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_4k_range_step(before[j], cpu_id),
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        unmap_4k_leaf_step_pre(pre, cpu_id),
        unmap_4k_leaf_step(pre, post, cpu_id),
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id),
{ reveal(unmap_4k_range_step); }

/// A recorded TLB flush of the caller's PCID after range steps that start at `start` leaves only range steps.
pub proof fn unmap_4k_range_steps_from_tlb_flush(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, post: KernelU, cpu_id: CpuId, pcid: Pcid)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_4k_range_step(before[j], cpu_id),
        steps.view() == record_user_view_change(before, pre, post),
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> kernel_u_cpu_tlb_cleared(steps.view()[j].old_u, steps.view()[j].new_u, pcid),
        unmap_4k_flush_step_pre(pre, cpu_id),
        pre.process_map.spec_index(pre.thread_map.spec_index(pre.cpu_array[cpu_id as int].current_thread->Some_0).owning_proc).pcid == pcid,
    ensures
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id),
{ reveal(unmap_4k_range_step); }

/// The flushed step pushed after range steps that start at `start` is a range step.
pub proof fn unmap_4k_range_steps_from_flushed(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, post: KernelU, cpu_id: CpuId)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_4k_range_step(before[j], cpu_id),
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        unmap_4k_flush_step_pre(pre, cpu_id),
        unmap_4k_flushed_step(pre, post, cpu_id),
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id),
{ reveal(unmap_4k_range_step); }

/// Quota refunds to the caller's container chain after range steps that start at `start` leave only range steps.
pub proof fn unmap_4k_range_steps_from_refund(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr,
    progress: Option<SyscallProgress>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        0 <= start <= before.len() <= steps.view().len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_4k_range_step(before[j], cpu_id),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        progress is Some,
        progress->Some_0 is Unmap4k,
        progress->Some_0->Unmap4k_unmapped == progress->Some_0->Unmap4k_range.len,
        progress->Some_0->Unmap4k_flushed,
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            &&& kernel_u_container_quota_4k_increased(old_u, steps.view()[j].new_u, container_ptr)
            &&& old_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& old_u.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& old_u.thread_map.dom().contains(thread_ptr)
            &&& old_u.thread_map[thread_ptr].lock_state is WriteLocked
            &&& old_u.thread_map[thread_ptr].owning_container == container_ptr
            &&& old_u.thread_map[thread_ptr].owning_proc == process_ptr
            &&& old_u.thread_map[thread_ptr].syscall_progress == progress
            &&& old_u.process_map.dom().contains(process_ptr)
            &&& old_u.process_map[process_ptr].lock_state is WriteLocked
            &&& old_u.process_map[process_ptr].pagetable is Some
            &&& old_u.process_map[process_ptr].pagetable->Some_0.lock_state is WriteLocked
            &&& old_u.container_map.dom().contains(container_ptr)
            &&& old_u.container_map[container_ptr].lock_state is WriteLocked
        },
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id),
{ reveal(unmap_4k_range_step); reveal(unmap_4k_refund_step_pre); }
} // verus!
