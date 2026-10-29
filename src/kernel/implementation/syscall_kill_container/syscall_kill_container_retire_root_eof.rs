use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_process::syscall_kill_process_retire_spec::{kill_retire_eof_transition_framing, kill_retire_pages, kill_retire_tables_emptied};
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_process::syscall_kill_process_retire_pages::kill_retire_pages_held_and_owned;
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_process::syscall_kill_process_retire_eof_memory::kill_retire_eof_memory;
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_process::syscall_kill_process_retire_eof_process::{kill_retire_eof_container_relations, kill_retire_eof_iommu, kill_retire_eof_process_relations, kill_retire_eof_tlb};

verus! {
/// Every member of the tree whose root `root_process` has no child is that root.
broadcast proof fn kill_container_retire_root_eof_only_root(process_perms: ProcessLockedMap, root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, p_ptr: RwLockProcessPtr)
    requires
        process_tree_wf(root_process, process_tree_dom, process_perms),
        process_perms.spec_index(root_process).view().children.view().len() == 0,
    ensures #![trigger process_tree_wf(root_process, process_tree_dom, process_perms), process_tree_dom.contains(p_ptr)] process_tree_dom.contains(p_ptr) ==> p_ptr == root_process,
    decreases process_perms.spec_index(p_ptr).view_rodata().view().depth,
{
    if process_tree_dom.contains(p_ptr) && p_ptr != root_process {
        process_root_wf_at(root_process, process_tree_dom, process_perms, p_ptr); process_children_parent_wf_parent_at(root_process, process_tree_dom, process_perms, p_ptr);
        let parent_ptr = process_perms.spec_index(p_ptr).view_rodata().view().parent->Some_0;
        process_children_parent_wf_at(root_process, process_tree_dom, process_perms, parent_ptr, p_ptr);
        kill_container_retire_root_eof_only_root(process_perms, root_process, process_tree_dom, parent_ptr);
    }
}

/// Retiring the childless root `target`, the only process of its container `container_ptr`, which is write-held and not
/// the root container, leaves that container without processes and keeps every container's process set consistent with
/// the process map, every process tree well formed, and the root container's root process.
pub(crate) proof fn kill_container_retire_root_eof_tree(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_retire_eof_transition_framing(pre, post, cpu_id, target, None, container_ptr, allocator_ptr),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).view().children.view().len() == 0,
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
        0 < pre.prc_mp.spec_index(target).view_rodata().view().container_depth,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view().root_process == target,
        pre.ctn_mp.spec_index(container_ptr).locking_thread() is Write,
    ensures
        post.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
        container_process_wf(post.ctn_mp, post.prc_mp),
        per_container_process_tree_wf(post.ctn_mp, post.prc_mp),
        post.ctn_mp.spec_index(post.rt_ctn).view_ghost().owned_processes.view().contains(post.ctn_mp.spec_index(post.rt_ctn).view().root_process),
{
    reveal(kill_retire_eof_transition_framing);
    let tree = pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view();
    container_process_wf_process_at(pre.ctn_mp, pre.prc_mp, target); per_container_process_tree_wf_at(pre.ctn_mp, pre.prc_mp, container_ptr);
    assert(process_tree_wf(target, tree, pre.prc_mp));
    assert(tree.remove(target) =~= Set::<RwLockProcessPtr>::empty()) by { broadcast use kill_container_retire_root_eof_only_root; };
    assert(container_ptr != pre.rt_ctn && pre.ctn_mp.dom().contains(pre.rt_ctn)) by { reveal(container_root_wf); };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); broadcast use kill_container_retire_root_eof_only_root; };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by {
        reveal(per_container_process_tree_wf); reveal(container_process_wf); process_no_change_to_tree_fields_imply_wf_forall();
    };
}

/// Retiring the empty zombie root process `target` of the marked, write-held container `container_ptr`, and returning
/// its pages to that container's 4K allocator, keeps the kernel invariant.
pub(crate) proof fn kill_container_retire_root_eof(
    pre: KernelK, post: KernelK, lctx: LocalContext, cpu_id: CpuId, target: RwLockProcessPtr, container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_retire_eof_transition_framing(pre, post, cpu_id, target, None, container_ptr, allocator_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).locking_thread() is Write,
        pre.prc_mp.spec_index(target).being_killed(),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().children.view().len() == 0,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        pre.prc_mp.spec_index(target).view_rodata().view().parent is None,
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
        0 < pre.prc_mp.spec_index(target).view_rodata().view().container_depth,
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).locking_thread() is Write,
        kill_retire_tables_emptied(pre, target),
        pre.prc_mp.spec_index(target).view().iommu_table is Some ==> pre.it_mp.dom().contains(pre.prc_mp.spec_index(target).view().iommu_table->Some_0) && pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).locking_thread() is Write,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view().root_process == target,
        pre.ctn_mp.spec_index(container_ptr).locking_thread() is Write,
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        pre.allc_4k_mp.dom().contains(allocator_ptr),
        kill_retire_pages(pre, target).no_duplicates(),
        page_array_wf(post.pg_arr),
        post.ctn_mp.perms_wf(),
        post.prc_mp.perms_wf(),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        iommu_table_perms_wf(post.it_mp),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_ptr).wf(),
        pre.prc_mp.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.process_lock_map(), target, TypedLockMode::Write),
        forall|d: RwLockProcessPtr| #![trigger lctx.process_lock_map().dom().contains(d)] lctx.process_lock_map().dom().contains(d) && pre.prc_mp.spec_index(d).killer_info() is Some
            ==> pre.prc_mp.spec_index(d).killer_info()->Some_0.process != target && pre.prc_mp.spec_index(d).view_rodata().view().owning_container == container_ptr,
        pre.ctn_mp.typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id()),
        forall|c: RwLockContainerPtr| #![trigger lctx.container_lock_map().dom().contains(c)] lctx.container_lock_map().dom().contains(c) && pre.ctn_mp.spec_index(c).killer_info() is Some
            ==> pre.ctn_mp.spec_index(c).killer_info()->Some_0.process != target,
        forall|u: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(u).locking_thread()]
            pre.thr_mp.dom().contains(u) && pre.thr_mp.spec_index(u).wlocked_by_thread(lctx.thread_id()) ==> !pre.thr_mp.spec_index(u).being_killed(),
    ensures
        post.inv(),
        post.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
{
    assert(container_perms_wf(post.ctn_mp)) by { reveal(kill_retire_eof_transition_framing); reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    assert(process_perms_wf(post.prc_mp)) by { reveal(kill_retire_eof_transition_framing); reveal(process_perms_wf); };
    kill_retire_pages_held_and_owned(pre, target, kill_retire_pages(pre, target).to_set(), allocator_ptr, cpu_id);
    kill_retire_eof_memory(pre, post, cpu_id, target, None, container_ptr, allocator_ptr);
    kill_retire_eof_container_relations(pre, post, cpu_id, target, None, container_ptr, allocator_ptr);
    kill_retire_eof_process_relations(pre, post, lctx, cpu_id, target, None, container_ptr, allocator_ptr);
    kill_retire_eof_iommu(pre, post, cpu_id, target, None, container_ptr, allocator_ptr);
    kill_retire_eof_tlb(pre, post, cpu_id, target, None, container_ptr, allocator_ptr);
    kill_container_retire_root_eof_tree(pre, post, cpu_id, target, container_ptr, allocator_ptr);
}
} // verus!
