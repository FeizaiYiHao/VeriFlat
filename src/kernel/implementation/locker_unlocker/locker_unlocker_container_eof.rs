use vstd::prelude::*;
use crate::*;

verus! {
/// Closes `inv()` after `wlock_container_unless_killed`: only the target entry's lock state moved.
pub(super) proof fn wlock_container_eof(pre: KernelK, post: KernelK, container_ptr: RwLockContainerPtr, lctx: LocalContext, ret: Option<Tracked<LockPerm>>)
    requires
        pre.inv(),
        post == (KernelK { ctn_mp: post.ctn_mp, ..pre }),
        post.ctn_mp.perms_wf(),
        post.ctn_mp.unchanged_except(&pre.ctn_mp, container_ptr),
        ret is None ==> post.ctn_mp.spec_index(container_ptr) == pre.ctn_mp.spec_index(container_ptr),
        ret is Some ==> wlock_ensures(pre.ctn_mp.spec_index(container_ptr), post.ctn_mp.spec_index(container_ptr), pre.ctn_mp.lock_id_by_key(container_ptr), &lctx, ret.unwrap().view()),
    ensures
        post.inv(),
        ret is Some ==> !pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
{
    assert(ret is Some ==> !pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty()) by { reveal(container_process_wf); };
    assert(container_perms_wf(post.ctn_mp)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    assert(container_invariant_fields_unchanged(pre.ctn_mp, post.ctn_mp)) by { container_lock_op_preserves_invariant_fields(pre.ctn_mp, post.ctn_mp, container_ptr); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_container_invariant_fields(pre, post); };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
    assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
    assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
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
        post == (KernelK { ctn_mp: post.ctn_mp, ..pre }),
        post.ctn_mp.perms_wf(),
        post.ctn_mp.unchanged_except(&pre.ctn_mp, container_ptr),
        wunlock_ensures(pre.ctn_mp.spec_index(container_ptr), post.ctn_mp.spec_index(container_ptr)),
    ensures
        post.inv(),
{
    assert(container_perms_wf(post.ctn_mp)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    assert(container_invariant_fields_unchanged(pre.ctn_mp, post.ctn_mp)) by { container_lock_op_preserves_invariant_fields(pre.ctn_mp, post.ctn_mp, container_ptr); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_container_invariant_fields(pre, post); };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
    assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
    assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); reveal(LockedMap::typed_lock_map_aligned); };
    assert(post.process_management_inv()) by { process_management_inv_preserved_for_container_invariant_fields(pre, post); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { cpu_dirty_map_wf_preserved_for_container_invariant_fields(pre, post); };
}
} // verus!
