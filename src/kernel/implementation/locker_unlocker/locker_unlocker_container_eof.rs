use vstd::prelude::*;
use crate::*;

verus! {
/// Closes `inv()` after `wlock_container_unless_killed`: only the target entry's lock state moved.
pub(super) proof fn wlock_container_eof(pre: KernelK, post: KernelK, container_ptr: RwLockContainerPtr, requested: LockOwnerId, acquired: bool)
    requires
        pre.inv(),
        post == (KernelK { ctn_mp: post.ctn_mp, ..pre }),
        post.ctn_mp.perms_wf(),
        post.ctn_mp.unchanged_except(&pre.ctn_mp, container_ptr),
        !acquired ==> post.ctn_mp.spec_index(container_ptr) == pre.ctn_mp.spec_index(container_ptr),
        acquired ==> {
            &&& !pre.ctn_mp.spec_index(container_ptr).being_killed()
            &&& !pre.ctn_mp.spec_index(container_ptr).locked()
            &&& post.ctn_mp.spec_index(container_ptr).inv()
            &&& post.ctn_mp.spec_index(container_ptr).view() == pre.ctn_mp.spec_index(container_ptr).view()
            &&& post.ctn_mp.spec_index(container_ptr).view_rodata() == pre.ctn_mp.spec_index(container_ptr).view_rodata()
            &&& post.ctn_mp.spec_index(container_ptr).view_ghost() == pre.ctn_mp.spec_index(container_ptr).view_ghost()
            &&& post.ctn_mp.spec_index(container_ptr).control() == LockControl::DynamicProcess(requested)
        },
    ensures
        post.inv(),
        acquired ==> !pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
{
    assert(acquired ==> !pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty()) by { reveal(container_process_wf); };
    assert(container_perms_wf(post.ctn_mp)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    assert(container_invariant_fields_unchanged(pre.ctn_mp, post.ctn_mp)) by { container_lock_op_preserves_invariant_fields(pre.ctn_mp, post.ctn_mp, container_ptr); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp)) by { reveal(page_object_owner_wf); reveal(container_page_owner_wf); };
    assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_kill_retire_wf); };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_container_invariant_fields(pre, post); };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
    assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
    assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
    assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
    assert(post.process_management_inv()) by { process_management_inv_preserved_for_container_invariant_fields(pre, post); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { cpu_dirty_map_wf_preserved_for_container_invariant_fields(pre, post); };
}

/// Closes `inv()` after `try_wlock_container_and_mark_kill`: the target is write-locked by the killer's thread and
/// marked for the killer, whose parent container that thread write-holds.
pub(super) proof fn mark_kill_container_eof(pre: KernelK, post: KernelK, pre_lctx: LocalContext, container_ptr: RwLockContainerPtr, killer_info: KillerInfo, marked: bool)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(container_ptr),
        ({
            let cpu = pre.cpu_arr.spec_index(pre_lctx.cpu_id()).view().view().view();
            let container = pre.ctn_mp.spec_index(container_ptr).view_rodata().view();
            &&& killer_held_context(pre, pre_lctx, cpu.current_process->Some_0, cpu.current_thread->Some_0, pre_lctx.container_lock_map().dom())
            &&& killer_info.process == cpu.current_process->Some_0
            &&& container.parent is Some
            &&& typed_lock_map_contains_mode(pre_lctx.container_lock_map(), container.parent->Some_0, TypedLockMode::Write)
        }),
        typed_lock_maps_aligned(&pre, &pre_lctx),
        post == (KernelK { ctn_mp: post.ctn_mp, ..pre }),
        post.ctn_mp.perms_wf(),
        post.ctn_mp.unchanged_except(&pre.ctn_mp, container_ptr),
        post.ctn_mp.spec_index(container_ptr).view() == pre.ctn_mp.spec_index(container_ptr).view(),
        post.ctn_mp.spec_index(container_ptr).view_rodata() == pre.ctn_mp.spec_index(container_ptr).view_rodata(),
        post.ctn_mp.spec_index(container_ptr).view_ghost() == pre.ctn_mp.spec_index(container_ptr).view_ghost(),
        !marked ==> post.ctn_mp.spec_index(container_ptr) == pre.ctn_mp.spec_index(container_ptr),
        marked ==> {
            &&& !pre.ctn_mp.spec_index(container_ptr).being_killed()
            &&& !pre.ctn_mp.spec_index(container_ptr).locked()
            &&& post.ctn_mp.spec_index(container_ptr).being_killed()
            &&& post.ctn_mp.spec_index(container_ptr).killer_info() == Some(killer_info)
            &&& post.ctn_mp.spec_index(container_ptr).inv()
            &&& post.ctn_mp.spec_index(container_ptr).locking_thread() is Write
            &&& post.ctn_mp.spec_index(container_ptr).locking_thread()->Write_thread_id == pre_lctx.thread_id()
        },
    ensures
        post.inv(),
        marked ==> !pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
{
    assert(marked ==> !pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty()) by { reveal(container_process_wf); };
    assert(container_perms_wf(post.ctn_mp)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    assert(container_invariant_fields_unchanged(pre.ctn_mp, post.ctn_mp)) by { container_lock_op_preserves_invariant_fields(pre.ctn_mp, post.ctn_mp, container_ptr); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp)) by { reveal(page_object_owner_wf); reveal(container_page_owner_wf); };
    assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_kill_retire_wf); };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_container_invariant_fields(pre, post); };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
    assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
    assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by {
        let cpu = pre.cpu_arr.spec_index(pre_lctx.cpu_id()).view().view().view();
        reveal(container_kill_mark_wf);
        pre.prc_mp.typed_lock_map_aligned_write_at(pre_lctx.process_lock_map(), pre_lctx.thread_id(), cpu.current_process->Some_0);
        pre.ctn_mp.typed_lock_map_aligned_write_at(pre_lctx.container_lock_map(), pre_lctx.thread_id(), pre.ctn_mp.spec_index(container_ptr).view_rodata().view().parent->Some_0);
    };
    assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
    assert(post.process_management_inv()) by { process_management_inv_preserved_for_container_invariant_fields(pre, post); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { cpu_dirty_map_wf_preserved_for_container_invariant_fields(pre, post); };
}

/// Closes `inv()` after `wunlock_container`: the released container still owns a process, is not marked, and is the
/// parent of no marked container this thread holds.
pub(super) proof fn wunlock_container_eof(pre: KernelK, post: KernelK, pre_lctx: LocalContext, container_ptr: RwLockContainerPtr)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).being_killed() == false,
        forall|c: RwLockContainerPtr| #![trigger pre_lctx.container_lock_map().dom().contains(c)] pre_lctx.container_lock_map().dom().contains(c) && pre.ctn_mp.spec_index(c).killer_info() is Some
            ==> pre.ctn_mp.spec_index(c).view_rodata().view().parent != Some(container_ptr),
        typed_lock_map_contains_mode(pre_lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_maps_aligned(&pre, &pre_lctx),
        !pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
        forall|t: RwLockThreadPtr, i: PageIndex| #![trigger pre.thr_mp.spec_index(t), pre.pg_arr.spec_index(i).view().view().state]
            pre.thr_mp.dom().contains(t) && pre.thr_mp.spec_index(t).wlocked_by_thread(pre_lctx.thread_id()) && !pre.thr_mp.spec_index(t).view().temp_alloc_clean() && index_valid(NUM_PAGES, i)
                && pre.pg_arr.spec_index(i).view().view().owning_container == container_ptr && {
                let state = pre.pg_arr.spec_index(i).view().view().state;
                state == (PageState::Owned4k { thread_ptr: t }) || state == (PageState::Owned2m { thread_ptr: t }) || state == (PageState::Owned1g { thread_ptr: t })
            } ==> pre.thr_mp.spec_index(t).view().owning_container == container_ptr,
        post == (KernelK { ctn_mp: post.ctn_mp, ..pre }),
        post.ctn_mp.perms_wf(),
        post.ctn_mp.unchanged_except(&pre.ctn_mp, container_ptr),
        dynamic_wunlock_ensures(pre.ctn_mp.spec_index(container_ptr), post.ctn_mp.spec_index(container_ptr)),
    ensures
        post.inv(),
{
    assert(container_perms_wf(post.ctn_mp)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    assert(container_invariant_fields_unchanged(pre.ctn_mp, post.ctn_mp)) by { container_lock_op_preserves_invariant_fields(pre.ctn_mp, post.ctn_mp, container_ptr); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp)) by {
        reveal(page_object_owner_wf); reveal(container_page_owner_wf);
        reveal(thread_staged_pages_4k_wf); reveal(thread_staged_pages_2m_wf); reveal(thread_staged_pages_1g_wf);
        broadcast use vstd::set_lib::lemma_set_empty_equivalency_len;
        pre.ctn_mp.typed_lock_map_aligned_write_at(pre_lctx.container_lock_map(), pre_lctx.thread_id(), container_ptr);
    };
    assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_kill_retire_wf); };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_container_invariant_fields(pre, post); };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
    assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
    assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); reveal(LockedMap::typed_lock_map_aligned); };
    assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); reveal(LockedMap::typed_lock_map_aligned); };
    assert(post.process_management_inv()) by { process_management_inv_preserved_for_container_invariant_fields(pre, post); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { cpu_dirty_map_wf_preserved_for_container_invariant_fields(pre, post); };
}
} // verus!
