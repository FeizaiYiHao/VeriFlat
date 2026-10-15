use vstd::prelude::*;
use crate::*;
use super::unmap_4k_spec::*;

verus! {
/// Clearing a still-mapped page of the range under the unmap locks is the leaf step on `pre`/`post`.
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
            &&& progress->Unmap4k_range.view().contains(va)
            &&& process.pagetable->Some_0.mapping_4k.dom().contains(va)
            &&& post == (KernelU {
                process_map: pre.process_map.insert(process_ptr, ProcessU {
                    pagetable: Some(PageTableU { mapping_4k: process.pagetable->Some_0.mapping_4k.remove(va), ..process.pagetable->Some_0 }), ..process
                }),
                thread_map: pre.thread_map.insert(thread_ptr, ThreadU {
                    syscall_progress: Some(SyscallProgress::Unmap4k { range: progress->Unmap4k_range, unmapped: (progress->Unmap4k_unmapped + 1) as usize, flushed: false }), ..thread
                }),
                ..pre
            })
        },
    ensures
        unmap_4k_leaf_step_pre(pre, cpu_id, va),
        unmap_4k_leaf_step(pre, post, cpu_id, va),
{ reveal(unmap_4k_leaf_trace_step_pre); reveal(unmap_4k_leaf_step_pre); reveal(unmap_4k_leaf_step); }

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
                thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: Some(SyscallProgress::Unmap4k { range: progress->Unmap4k_range, unmapped: progress->Unmap4k_unmapped, flushed: true }), ..thread }),
                ..pre
            })
        },
    ensures
        unmap_4k_flushed_step(pre, post, cpu_id),
{ reveal(unmap_4k_flushed_step); }

/// A leaf step that clears `va`, pushed after range steps that start at `start`, is a range step: without
/// `va` it removes exactly one key of the range.
pub proof fn unmap_4k_range_steps_from_leaf(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, post: KernelU, cpu_id: CpuId, va: VAddr)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_4k_range_step(before[j], cpu_id),
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        unmap_4k_leaf_step_pre(pre, cpu_id, va),
        unmap_4k_leaf_step(pre, post, cpu_id, va),
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id),
{
    reveal(unmap_4k_range_step); reveal(unmap_4k_leaf_step_pre); reveal(unmap_4k_leaf_step); reveal(unmap_4k_leaf_trace_step);
    let thread = pre.thread_map.spec_index(pre.cpu_array[cpu_id as int].current_thread->Some_0);
    let mapping = pre.process_map.spec_index(thread.owning_proc).pagetable->Some_0.mapping_4k;
    let kept = mapping.remove(va).dom();
    assert(mapping.remove(va) =~= mapping.restrict(kept));
    assert(mapping.dom().difference(kept) =~= set![va]);
    assert(thread.syscall_progress->Some_0->Unmap4k_range.view().to_set().contains(va));
}

/// TLB flushes of the caller's PCID, recorded after range steps that start at `start` while the caller's held
/// objects keep their projection at `entry`, leave only range steps.
pub proof fn unmap_4k_range_steps_from_tlb_flush(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, entry: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr,
    container_ptr: RwLockContainerPtr, pcid: Pcid,
)
    requires
        0 <= start <= before.len() <= steps.view().len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> unmap_4k_range_step(before[j], cpu_id),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        unmap_4k_flush_step_pre(entry, cpu_id),
        entry.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        entry.thread_map[thread_ptr].owning_proc == process_ptr,
        entry.thread_map[thread_ptr].owning_container == container_ptr,
        entry.process_map[process_ptr].pcid == pcid,
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            &&& kernel_u_cpu_tlb_cleared(old_u, steps.view()[j].new_u, pcid)
            &&& old_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& old_u.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& old_u.thread_map.dom().contains(thread_ptr)
            &&& old_u.thread_map[thread_ptr] == entry.thread_map[thread_ptr]
            &&& old_u.process_map.dom().contains(process_ptr)
            &&& old_u.process_map[process_ptr] == (ProcessU { iommu_table: old_u.process_map[process_ptr].iommu_table, ..entry.process_map[process_ptr] })
            &&& old_u.container_map.dom().contains(container_ptr)
            &&& old_u.container_map[container_ptr].lock_state is WriteLocked
        },
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id),
{ reveal(unmap_4k_range_step); reveal(unmap_4k_flush_step_pre); }

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
pub proof fn unmap_4k_range_steps_from_refund(steps: &KernelSteps, before: Seq<KernelStep>, start: int, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, progress: Option<SyscallProgress>)
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
