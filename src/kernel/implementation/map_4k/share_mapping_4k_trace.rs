use vstd::prelude::*;
use crate::*;
use super::share_mapping_4k_spec::*;

verus! {
/// The caller write-holding its cpu, the progress thread, and the share threads projects its share objects with their
/// K anchors, as a leaf step from `source` into `target` requires.
pub proof fn share_4k_leaf_step_pre_from_k(krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, progress_thread: RwLockThreadPtr, source_thread: RwLockThreadPtr, source: RwLockProcessPtr, target: RwLockProcessPtr)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(progress_thread),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), progress_thread, TypedLockMode::Write),
        krnl.thr_mp.spec_index(progress_thread).view().syscall_progress.view() matches Some(SyscallProgress::Share4k { .. }),
        krnl.thr_mp.dom().contains(source_thread),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), source_thread, TypedLockMode::Write),
        krnl.thr_mp.dom().contains(share_4k_objects_k(*krnl, cpu_id).quota_thread),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), share_4k_objects_k(*krnl, cpu_id).quota_thread, TypedLockMode::Write),
        krnl.ctn_mp.dom().contains(share_4k_objects_k(*krnl, cpu_id).target_container),
        share_4k_objects_k(*krnl, cpu_id).source_thread == source_thread,
        share_4k_objects_k(*krnl, cpu_id).target == target,
        krnl.thr_mp.spec_index(source_thread).view().owning_proc == source,
        krnl.prc_mp.dom().contains(target),
        krnl.prc_mp.spec_index(target).view_rodata().view().owning_container == share_4k_objects_k(*krnl, cpu_id).target_container,
        share_4k_objects_k(*krnl, cpu_id).transfer_source matches Some(s) ==> krnl.ctn_mp.spec_index(share_4k_objects_k(*krnl, cpu_id).target_container).view_rodata().view().parent == Some(s),
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            let objects = share_4k_objects(u, cpu_id);
            &&& share_4k_locked(u, cpu_id)
            &&& u.cpu_array[cpu_id as int].current_thread == Some(progress_thread)
            &&& objects.source_thread == source_thread
            &&& objects.target == target
            &&& u.process_map[target].owning_container == objects.target_container
            &&& objects.transfer_source matches Some(s) ==> u.container_map.dom().contains(objects.target_container) && u.container_map[objects.target_container].parent == Some(s)
            &&& u.thread_map.dom().contains(source_thread)
            &&& u.thread_map[source_thread].owning_proc == source
        }),
{ kernel_share_4k_objects_projection(krnl, lctx, cpu_id); }

/// Copying the next recorded source entry into the target table is the leaf step on `pre`/`post`.
pub proof fn share_4k_leaf_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, progress_thread: RwLockThreadPtr, source_thread: RwLockThreadPtr, source: RwLockProcessPtr, target: RwLockProcessPtr, source_va: VAddr,
    target_va: VAddr, progress: Option<SyscallProgress>, new_progress: Option<SyscallProgress>,
)
    requires
        ({
            let objects = share_4k_objects(pre, cpu_id);
            &&& share_4k_locked(pre, cpu_id)
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(progress_thread)
            &&& objects.source_thread == source_thread
            &&& objects.target == target
            &&& pre.process_map[target].owning_container == objects.target_container
            &&& objects.transfer_source matches Some(s) ==> pre.container_map.dom().contains(objects.target_container) && pre.container_map[objects.target_container].parent == Some(s)
            &&& pre.thread_map.dom().contains(source_thread)
            &&& pre.thread_map[source_thread].owning_proc == source
        }),
        progress is Some,
        progress->Some_0 is Share4k,
        progress->Some_0->Share4k_shared < progress->Some_0->Share4k_source_range.len,
        progress->Some_0->Share4k_shared < progress->Some_0->Share4k_target_range.len,
        progress->Some_0->Share4k_source_range.view()[progress->Some_0->Share4k_shared as int] == source_va,
        progress->Some_0->Share4k_target_range.view()[progress->Some_0->Share4k_shared as int] == target_va,
        new_progress == share_4k_progress_after_leaf(progress),
        source != target,
        ({
            &&& pre.process_map.dom().contains(source) && pre.process_map.dom().contains(target)
            &&& pre.process_map[source].pagetable is Some && pre.process_map[target].pagetable is Some
            &&& pre.process_map[source].pagetable->Some_0.lock_state is WriteLocked
            &&& pre.process_map[target].pagetable->Some_0.lock_state is WriteLocked
            &&& pre.process_map[source].pagetable->Some_0.mapping_4k.dom().contains(source_va)
            &&& !pre.process_map[target].pagetable->Some_0.mapping_4k.dom().contains(target_va)
            &&& pre.thread_map.dom().contains(progress_thread)
            &&& pre.thread_map[progress_thread].syscall_progress == progress
            &&& post == (KernelU {
                thread_map: pre.thread_map.insert(progress_thread, ThreadU { syscall_progress: new_progress, ..pre.thread_map[progress_thread] }),
                process_map: pre.process_map.insert(target, ProcessU {
                    pagetable: Some(PageTableU { mapping_4k: pre.process_map[target].pagetable->Some_0.mapping_4k.insert(target_va, pre.process_map[source].pagetable->Some_0.mapping_4k[source_va]),
                        ..pre.process_map[target].pagetable->Some_0 }), ..pre.process_map[target]
                }),
                ..pre
            })
        }),
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

/// The running thread's share installs one target directory page funded by `quota_thread_ptr`, moving its backing page
/// to the target container when there is a transfer source; the transition is one share directory step.
pub proof fn share_4k_directory_step_from_k(
    pre: &KernelK, post: &KernelK, pre_lctx: &LocalContext, lctx: &LocalContext, cpu_id: CpuId, progress_thread: RwLockThreadPtr,
    quota_thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, pagetable_ptr: RwLockPageTableRoot,
    transfer_source: Option<RwLockContainerPtr>, page_ptr: PagePtr,
)
    requires
        pre.inv(),
        typed_lock_maps_aligned(pre, pre_lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(pre_lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(progress_thread),
        pre.prc_mp.dom().contains(process_ptr),
        pre.thr_mp.dom().contains(progress_thread),
        typed_lock_map_contains_mode(pre_lctx.thread_lock_map(), progress_thread, TypedLockMode::Write),
        pre.thr_mp.spec_index(progress_thread).view().syscall_progress.view() is Some && pre.thr_mp.spec_index(progress_thread).view().syscall_progress.view()->Some_0 is Share4k,
        pre.thr_mp.spec_index(progress_thread).view().syscall_progress.view()->Some_0->Share4k_shared < pre.thr_mp.spec_index(progress_thread).view().syscall_progress.view()->Some_0->Share4k_source_range.len,
        share_4k_objects_k(*pre, cpu_id).target == process_ptr && share_4k_objects_k(*pre, cpu_id).quota_thread == quota_thread_ptr,
        share_4k_objects_k(*pre, cpu_id).target_container == container_ptr && share_4k_objects_k(*pre, cpu_id).transfer_source == transfer_source,
        pre.thr_mp.dom().contains(share_4k_objects_k(*pre, cpu_id).source_thread),
        typed_lock_map_contains_mode(pre_lctx.thread_lock_map(), share_4k_objects_k(*pre, cpu_id).source_thread, TypedLockMode::Write),
        pre.thr_mp.dom().contains(quota_thread_ptr),
        typed_lock_map_contains_mode(pre_lctx.thread_lock_map(), quota_thread_ptr, TypedLockMode::Write),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        transfer_source matches Some(source) ==> pre.ctn_mp.spec_index(container_ptr).view_rodata().view().parent == Some(source),
        !pre.prc_mp.spec_index(process_ptr).view().zombie && pre.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr,
        typed_lock_map_contains_mode(pre_lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        transfer_source matches Some(source)
            ==> typed_lock_map_contains_mode(pre_lctx.container_lock_map(), source, TypedLockMode::Write) && typed_lock_map_contains_mode(pre_lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        kernel_thread_quota_4k_changed(pre, post, quota_thread_ptr, -1),
        post.thr_mp.spec_index(quota_thread_ptr).view().syscall_progress == pre.thr_mp.spec_index(quota_thread_ptr).view().syscall_progress,
        transfer_source is None ==> {
            &&& typed_lock_maps_aligned(post, lctx)
            &&& pre.thr_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id())
            &&& pre.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id())
            &&& typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(lctx.thread_lock_map(), quota_thread_ptr, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write)
            &&& *post == (KernelK { pt_mp: post.pt_mp, pg_arr: post.pg_arr, thr_mp: post.thr_mp, ..*pre })
            &&& post.thr_mp.unchanged_except(&pre.thr_mp, quota_thread_ptr)
            &&& post.thr_mp.spec_index(quota_thread_ptr).view() == (Thread {
                quota_4k: post.thr_mp.spec_index(quota_thread_ptr).view().quota_4k, temp_alloc_cache_4k: post.thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k,
                syscall_progress: post.thr_mp.spec_index(quota_thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(quota_thread_ptr).view()
            })
            &&& post.thr_mp.spec_index(quota_thread_ptr).being_killed() == pre.thr_mp.spec_index(quota_thread_ptr).being_killed()
            &&& pre.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr
            &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr)
            &&& post.pt_mp.spec_index(pagetable_ptr).view().mapping_4k() == pre.pt_mp.spec_index(pagetable_ptr).view().mapping_4k()
            &&& post.pt_mp.spec_index(pagetable_ptr).view().mapping_2m() == pre.pt_mp.spec_index(pagetable_ptr).view().mapping_2m()
            &&& post.pt_mp.spec_index(pagetable_ptr).view().mapping_1g() == pre.pt_mp.spec_index(pagetable_ptr).view().mapping_1g()
        },
        transfer_source matches Some(source) ==> {
            &&& pre.thr_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id())
            &&& post.thr_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id())
            &&& typed_lock_map_contains_mode(lctx.thread_lock_map(), quota_thread_ptr, TypedLockMode::Write)
            &&& *post == (KernelK { pg_arr: post.pg_arr, ctn_mp: post.ctn_mp, thr_mp: post.thr_mp, pt_mp: post.pt_mp, ..*pre })
            &&& source != container_ptr
            &&& pre.ctn_mp.dom().contains(source)
            &&& pre.ctn_mp.spec_index(source).view().owned_pages.view().contains(page_ptr)
            &&& post.ctn_mp.dom() == pre.ctn_mp.dom()
            &&& forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)] pre.ctn_mp.dom().contains(c) ==> {
                &&& post.ctn_mp.spec_index(c).view_rodata() == pre.ctn_mp.spec_index(c).view_rodata()
                &&& post.ctn_mp.spec_index(c).view_ghost() == pre.ctn_mp.spec_index(c).view_ghost()
                &&& post.ctn_mp.spec_index(c).locking_thread() == pre.ctn_mp.spec_index(c).locking_thread()
                &&& post.ctn_mp.spec_index(c).being_killed() == pre.ctn_mp.spec_index(c).being_killed()
                &&& post.ctn_mp.spec_index(c).view() == (Container { owned_pages: post.ctn_mp.spec_index(c).view().owned_pages, ..pre.ctn_mp.spec_index(c).view() })
                &&& post.ctn_mp.spec_index(c).view().owned_pages.view() == if c == source { pre.ctn_mp.spec_index(c).view().owned_pages.view().remove(page_ptr) }
                    else if c == container_ptr { pre.ctn_mp.spec_index(c).view().owned_pages.view().insert(page_ptr) } else { pre.ctn_mp.spec_index(c).view().owned_pages.view() }
            }
            &&& post.thr_mp.unchanged_except(&pre.thr_mp, quota_thread_ptr)
            &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr)
            &&& pre.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id())
            &&& post.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id())
            &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write)
            &&& post.pt_mp.spec_index(pagetable_ptr).view().mapping_4k() == pre.pt_mp.spec_index(pagetable_ptr).view().mapping_4k()
            &&& post.pt_mp.spec_index(pagetable_ptr).view().mapping_2m() == pre.pt_mp.spec_index(pagetable_ptr).view().mapping_2m()
            &&& post.pt_mp.spec_index(pagetable_ptr).view().mapping_1g() == pre.pt_mp.spec_index(pagetable_ptr).view().mapping_1g()
        },
    ensures
        share_4k_directory_step_pre(kernel_k_to_kernel_u(*pre), cpu_id),
        share_4k_directory_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id),
        share_4k_objects_k(*post, cpu_id) == share_4k_objects_k(*pre, cpu_id),
{
    reveal(share_4k_directory_step_pre); reveal(share_4k_directory_step); reveal(share_4k_directory_pre_at); reveal(share_4k_directory_at); reveal(kernel_thread_quota_4k_changed);
    match transfer_source {
        Some(source) => { kernel_thread_quota_and_page_owner_changed_implies_u_step(pre, post, lctx, quota_thread_ptr, source, container_ptr, page_ptr, pagetable_ptr); },
        None => { kernel_thread_quota_4k_and_progress_changed_implies_u_step(pre, post, lctx, cpu_id, quota_thread_ptr, process_ptr, pagetable_ptr); },
    }
    kernel_share_4k_objects_projection(pre, pre_lctx, cpu_id);
    reveal(share_4k_objects_k);
}
} // verus!
