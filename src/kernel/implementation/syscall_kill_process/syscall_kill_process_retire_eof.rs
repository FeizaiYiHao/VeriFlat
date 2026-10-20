use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_retire_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_retire_eof_memory::kill_retire_eof_memory;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_retire_eof_process::{kill_retire_eof_container_relations, kill_retire_eof_iommu, kill_retire_eof_process_relations, kill_retire_eof_tlb};
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_retire_eof_tree::kill_retire_eof_tree;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_retire_pages::kill_retire_pages_held_and_owned;

verus! {
/// The retired zombie, its tables, and its pages returned to its container's 4K allocator keep the kernel invariant.
pub(crate) proof fn kill_retire_eof(
    pre: KernelK, post: KernelK, lctx: LocalContext, cpu_id: CpuId, target: RwLockProcessPtr, parent_ptr: RwLockProcessPtr,
    container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_retire_eof_transition_framing(pre, post, cpu_id, target, parent_ptr, container_ptr, allocator_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).locking_thread() is Write,
        pre.prc_mp.spec_index(target).being_killed(),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().children.view().len() == 0,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        pre.prc_mp.spec_index(target).view_rodata().view().parent == Some(parent_ptr),
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
        pre.prc_mp.dom().contains(parent_ptr),
        parent_ptr != target,
        pre.prc_mp.spec_index(target).view_ghost().uppertree_seq.view().contains(parent_ptr),
        pre.prc_mp.spec_index(parent_ptr).view().children.map().dom().contains(pre.prc_mp.spec_index(target).view().parent_linkedlist_node.addr()),
        pre.prc_mp.spec_index(parent_ptr).view().children.map().spec_index(pre.prc_mp.spec_index(target).view().parent_linkedlist_node.addr()) == target,
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).locking_thread() is Write,
        kill_retire_tables_emptied(pre, target),
        pre.prc_mp.spec_index(target).view().iommu_table is Some ==> pre.it_mp.dom().contains(pre.prc_mp.spec_index(target).view().iommu_table->Some_0) && pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).locking_thread() is Write,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        pre.allc_4k_mp.dom().contains(allocator_ptr),
        kill_retire_pages(pre, target).no_duplicates(),
        page_array_wf(post.pg_arr),
        container_perms_wf(post.ctn_mp),
        process_perms_wf(post.prc_mp),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_wlocked(post.pt_mp, post.pt_lower.view()),
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
    ensures post.inv(),
{
    kill_retire_pages_held_and_owned(pre, target, kill_retire_pages(pre, target).to_set(), allocator_ptr, cpu_id);
    kill_retire_eof_memory(pre, post, cpu_id, target, parent_ptr, container_ptr, allocator_ptr);
    kill_retire_eof_container_relations(pre, post, cpu_id, target, parent_ptr, container_ptr, allocator_ptr);
    kill_retire_eof_process_relations(pre, post, lctx, cpu_id, target, parent_ptr, container_ptr, allocator_ptr);
    kill_retire_eof_iommu(pre, post, cpu_id, target, parent_ptr, container_ptr, allocator_ptr);
    kill_retire_eof_tlb(pre, post, cpu_id, target, parent_ptr, container_ptr, allocator_ptr);
    kill_retire_eof_tree(pre, post, cpu_id, target, parent_ptr, container_ptr, allocator_ptr);
}
} // verus!
