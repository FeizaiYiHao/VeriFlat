use vstd::prelude::*;
use crate::*;
use super::share_mapping_4k_spec::*;

verus! {
/// Copying the next recorded source entry into the target table is the leaf step on `pre`/`post`.
pub proof fn share_4k_leaf_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, progress_thread: RwLockThreadPtr, source_thread: RwLockThreadPtr, source: RwLockProcessPtr, target: RwLockProcessPtr,
    source_va: VAddr, target_va: VAddr,
)
    requires
        share_4k_locked(pre, cpu_id),
        {
            let thread = pre.thread_map.spec_index(progress_thread);
            let progress = thread.syscall_progress->Some_0;
            let shared = progress->Share4k_shared;
            let source_table = pre.process_map.spec_index(source).pagetable->Some_0;
            let target_table = pre.process_map.spec_index(target).pagetable->Some_0;
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(progress_thread)
            &&& share_4k_objects(pre, cpu_id).source_thread == source_thread
            &&& share_4k_objects(pre, cpu_id).target == target
            &&& pre.process_map.spec_index(target).owning_container == share_4k_objects(pre, cpu_id).target_container
            &&& share_4k_objects(pre, cpu_id).transfer_source matches Some(s) ==> pre.container_map.dom().contains(share_4k_objects(pre, cpu_id).target_container)
                && pre.container_map[share_4k_objects(pre, cpu_id).target_container].parent == Some(s)
            &&& pre.thread_map.dom().contains(source_thread)
            &&& pre.thread_map.spec_index(source_thread).owning_proc == source
            &&& pre.thread_map.dom().contains(progress_thread)
            &&& thread.syscall_progress is Some
            &&& progress is Share4k
            &&& shared < progress->Share4k_source_range.len
            &&& shared < progress->Share4k_target_range.len
            &&& progress->Share4k_source_range.view()[shared as int] == source_va
            &&& progress->Share4k_target_range.view()[shared as int] == target_va
            &&& source != target
            &&& pre.process_map.dom().contains(source)
            &&& pre.process_map.dom().contains(target)
            &&& pre.process_map.spec_index(source).pagetable is Some
            &&& pre.process_map.spec_index(target).pagetable is Some
            &&& source_table.lock_state is WriteLocked
            &&& target_table.lock_state is WriteLocked
            &&& source_table.mapping_4k.dom().contains(source_va)
            &&& !target_table.mapping_4k.dom().contains(target_va)
            &&& post == (KernelU {
                thread_map: pre.thread_map.insert(progress_thread, ThreadU { syscall_progress: share_4k_progress_after_leaf(thread.syscall_progress), ..thread }),
                process_map: pre.process_map.insert(target, ProcessU {
                    pagetable: Some(PageTableU { mapping_4k: target_table.mapping_4k.insert(target_va, source_table.mapping_4k.spec_index(source_va)), ..target_table }),
                    ..pre.process_map.spec_index(target)
                }),
                ..pre
            })
        },
    ensures
        share_4k_leaf_step_pre(pre, cpu_id),
        share_4k_leaf_step(pre, post, cpu_id),
{ reveal(share_4k_leaf_step_pre); reveal(share_4k_leaf_step); reveal(share_4k_leaf_pre_at); reveal(share_4k_leaf_at); }

/// Directory steps appended after range steps that start at `start` are range steps.
pub proof fn share_4k_range_steps_from_directory(steps: &KernelSteps, before: Seq<KernelStep>, start: int, cpu_id: CpuId)
    requires
        0 <= start <= before.len() <= steps.view().len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> share_4k_range_step(before[j], cpu_id),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            &&& share_4k_directory_step_pre(steps.view()[j].old_u, cpu_id)
            &&& share_4k_directory_step(steps.view()[j].old_u, steps.view()[j].new_u, cpu_id)
        },
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> share_4k_range_step(steps.view()[j], cpu_id),
{ reveal(share_4k_range_step); }

/// A leaf step pushed after range steps that start at `start` is a range step.
pub proof fn share_4k_range_steps_from_leaf(steps: &KernelSteps, before: Seq<KernelStep>, start: int, cpu_id: CpuId)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len() ==> share_4k_range_step(before[j], cpu_id),
        steps.view() == before.push(steps.view().last()),
        share_4k_leaf_step_pre(steps.view().last().old_u, cpu_id),
        share_4k_leaf_step(steps.view().last().old_u, steps.view().last().new_u, cpu_id),
    ensures
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> share_4k_range_step(steps.view()[j], cpu_id),
{ reveal(share_4k_range_step); }
} // verus!
