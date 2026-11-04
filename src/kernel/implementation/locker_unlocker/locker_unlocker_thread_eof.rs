use vstd::prelude::*;
use crate::*;

verus! {
/// Closes `inv()` after `wlock_thread_unless_killed`: only the target entry's lock state moved.
pub(super) proof fn wlock_thread_eof(pre: KernelK, post: KernelK, thrd_ptr: RwLockThreadPtr, lctx: LocalContext, ret: Option<Tracked<LockPerm>>)
    requires
        pre.inv(),
        post == (KernelK { thrd_mp: post.thrd_mp, ..pre }),
        post.thrd_mp.perms_wf(),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        ret is None ==> post.thrd_mp.spec_index(thrd_ptr) == pre.thrd_mp.spec_index(thrd_ptr),
        ret is Some ==> !pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        ret is Some ==> wlock_ensures(pre.thrd_mp.spec_index(thrd_ptr), post.thrd_mp.spec_index(thrd_ptr), pre.thrd_mp.lock_id_by_key(thrd_ptr), &lctx, ret.unwrap().view()),
    ensures
        post.inv(),
        ret is Some ==> post.thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean() && post.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean() && post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is None,
        ret is Some ==> !post.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
{
    assert(thread_perms_wf(post.thrd_mp)) by {
        reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
        reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
    };
    assert(thread_invariant_fields_unchanged(pre.thrd_mp, post.thrd_mp)) by { thread_lock_op_preserves_invariant_fields(pre.thrd_mp, post.thrd_mp, thrd_ptr); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_invariant_fields(pre, post); };
    assert(process_thread_wf(post.prc_mp, post.thrd_mp)) by {
        thread_invariant_fields_unchanged_implies_process_management_fields(pre.thrd_mp, post.thrd_mp);
        process_thread_wf_preserved_for_thread_process_management_fields(post.prc_mp, pre.thrd_mp, post.thrd_mp);
    };
    assert(thread_dangling_chain_end_wf(post.thrd_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thrd_mp, post.thrd_mp); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
    assert(post.process_management_inv()) by { process_management_inv_preserved_for_thread_invariant_fields(pre, post); };
    if ret is Some {
        assert(post.thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean() && post.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean() && post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is None
            && !post.thrd_mp.spec_index(thrd_ptr).view_ghost().exited) by {
            reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked);
        };
    }
}

/// Closes `inv()` after `mark_thread_kill`: the write-held thread of a marked, write-held process is marked; its view
/// and lock state are unchanged.
pub(super) proof fn mark_thread_kill_eof(pre: KernelK, post: KernelK, pre_lctx: LocalContext, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr)
    requires
        pre.inv(),
        pre.prc_mp.dom().contains(prc_ptr),
        pre.prc_mp.spec_index(prc_ptr).being_killed(),
        typed_lock_map_contains_mode(pre_lctx.process_lock_map(), prc_ptr, TypedLockMode::Write),
        pre.prc_mp.spec_index(prc_ptr).view().owned_threads.view().contains(thrd_ptr),
        typed_lock_map_contains_mode(pre_lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        pre.thrd_mp.dom().contains(thrd_ptr),
        !pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        !pre.thrd_mp.spec_index(thrd_ptr).view().state.is_reply_waiting(),
        !(pre.thrd_mp.spec_index(thrd_ptr).view().state is IPC_TRANSIT),
        typed_lock_maps_aligned(&pre, &pre_lctx),
        post == (KernelK { thrd_mp: post.thrd_mp, ..pre }),
        post.thrd_mp.perms_wf(),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).being_killed(),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() == pre.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        post.thrd_mp.spec_index(thrd_ptr).is_init() == pre.thrd_mp.spec_index(thrd_ptr).is_init(),
        post.thrd_mp.spec_index(thrd_ptr).view() == pre.thrd_mp.spec_index(thrd_ptr).view(),
        post.thrd_mp.spec_index(thrd_ptr).view_rodata() == pre.thrd_mp.spec_index(thrd_ptr).view_rodata(),
        post.thrd_mp.spec_index(thrd_ptr).view_ghost() == pre.thrd_mp.spec_index(thrd_ptr).view_ghost(),
    ensures
        post.inv(),
{
    assert(thread_perms_wf(post.thrd_mp)) by {
        reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
        reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
    };
    assert(thread_invariant_fields_unchanged(pre.thrd_mp, post.thrd_mp)) by { thread_lock_op_preserves_invariant_fields(pre.thrd_mp, post.thrd_mp, thrd_ptr); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_invariant_fields(pre, post); };
    assert(process_thread_wf(post.prc_mp, post.thrd_mp)) by {
        reveal(process_thread_wf);
        pre.prc_mp.typed_lock_map_aligned_write_at(pre_lctx.process_lock_map(), pre_lctx.thread_id(), prc_ptr);
        pre.thrd_mp.typed_lock_map_aligned_write_at(pre_lctx.thread_lock_map(), pre_lctx.thread_id(), thrd_ptr);
    };
    assert(thread_dangling_chain_end_wf(post.thrd_mp)) by {
        process_thread_wf_process_at(pre.prc_mp, pre.thrd_mp, prc_ptr, thrd_ptr); thread_perms_wf_at(pre.thrd_mp, thrd_ptr);
        thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thrd_mp, post.thrd_mp);
    };
    assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
    assert(post.process_management_inv()) by { process_management_inv_preserved_for_thread_invariant_fields(pre, post); };
}

/// Closes `inv()` after `wunlock_thread`: the target entry is released with its pendings, temporary allocations, and
/// syscall progress already clear.
pub(super) proof fn wunlock_thread_eof(pre: KernelK, post: KernelK, thrd_ptr: RwLockThreadPtr, holder: LockThreadId)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thrd_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).wlocked_by_thread(holder),
        forall|t: RwLockThreadPtr| #![trigger pre.thrd_mp.spec_index(t).locking_thread()]
            pre.thrd_mp.dom().contains(t) && pre.thrd_mp.spec_index(t).locked_by_thread(holder) ==> !(pre.thrd_mp.spec_index(t).view().state is KILLED) || pre.thrd_mp.spec_index(t).being_killed()
                || pre.thrd_mp.spec_index(thrd_ptr).view().call_depth.view() < pre.thrd_mp.spec_index(t).view().call_depth.view(),
        pre.thrd_mp.spec_index(thrd_ptr).being_killed() == false,
        !(pre.thrd_mp.spec_index(thrd_ptr).view().state is IPC_TRANSIT),
        !(pre.thrd_mp.spec_index(thrd_ptr).view().state is KILLED),
        pre.thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        pre.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is None,
        !pre.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        post == (KernelK { thrd_mp: post.thrd_mp, ..pre }),
        post.thrd_mp.perms_wf(),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        wunlock_ensures(pre.thrd_mp.spec_index(thrd_ptr), post.thrd_mp.spec_index(thrd_ptr)),
    ensures
        post.inv(),
{
    assert(thread_perms_wf(post.thrd_mp)) by {
        reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
        reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
    };
    assert(thread_invariant_fields_unchanged(pre.thrd_mp, post.thrd_mp)) by { thread_lock_op_preserves_invariant_fields(pre.thrd_mp, post.thrd_mp, thrd_ptr); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_invariant_fields(pre, post); };
    assert(process_thread_wf(post.prc_mp, post.thrd_mp)) by {
        thread_invariant_fields_unchanged_implies_process_management_fields(pre.thrd_mp, post.thrd_mp);
        process_thread_wf_preserved_for_thread_process_management_fields(post.prc_mp, pre.thrd_mp, post.thrd_mp);
    };
    assert(thread_dangling_chain_end_wf(post.thrd_mp)) by {
        reveal(thread_dangling_chain_end_wf); reveal(thread_perms_wf);
    };
    assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
    assert(post.process_management_inv()) by { process_management_inv_preserved_for_thread_invariant_fields(pre, post); };
}

/// Closes `inv()` after `set_thread_syscall_progress`: only the write-held thread's progress changed, still naming any peer in transit with it.
pub(super) proof fn set_thread_syscall_progress_eof(pre: KernelK, post: KernelK, lctx: LocalContext, thrd_ptr: RwLockThreadPtr, progress: Ghost<Option<SyscallProgress>>)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thrd_ptr),
        post == (KernelK { thrd_mp: post.thrd_mp, ..pre }),
        post.thrd_mp.perms_wf(),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).is_init(),
        post.thrd_mp.spec_index(thrd_ptr).wlocked_by(&lctx),
        post.thrd_mp.spec_index(thrd_ptr).view_rodata() == pre.thrd_mp.spec_index(thrd_ptr).view_rodata(),
        post.thrd_mp.spec_index(thrd_ptr).view_ghost() == pre.thrd_mp.spec_index(thrd_ptr).view_ghost(),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() == pre.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        post.thrd_mp.spec_index(thrd_ptr).killer_info() == pre.thrd_mp.spec_index(thrd_ptr).killer_info(),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: progress, ..pre.thrd_mp.spec_index(thrd_ptr).view() }),
        progress_peer_of(progress.view()) == progress_peer_of(pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view())
            || (progress_peer_of(pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()) matches Some(peer_ptr) ==> !(pre.thrd_mp.spec_index(peer_ptr).view().state matches ThreadState::IPC_TRANSIT { partner, .. } && partner == thrd_ptr)),
    ensures
        post.inv(),
{
    assert(post.subsystems_inv()) by {
        assert(thread_perms_wf(post.thrd_mp)) by {
            reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
            reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
        };
        reveal(KernelK::default_pagetable_wf);
    };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_endpoint_memory_fields(pre, post); };
    assert(post.process_management_inv()) by {
        assert(thread_process_management_fields_unchanged(pre.thrd_mp, post.thrd_mp));
        thread_caller_callee_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp);
        thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.ep_mp);
        thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.ep_mp);
        container_thread_endpoint_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp, post.ep_mp);
        container_thread_scheduler_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp, post.sched_mp);
        container_thread_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp);
        process_thread_wf_preserved_for_thread_process_management_fields(post.prc_mp, pre.thrd_mp, post.thrd_mp);
        thread_cpu_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.cpu_arr);
        assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
        assert(thread_dangling_chain_end_wf(post.thrd_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thrd_mp, post.thrd_mp); };
    };
}
} // verus!
