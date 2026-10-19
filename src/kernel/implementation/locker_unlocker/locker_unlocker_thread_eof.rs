use vstd::prelude::*;
use crate::*;

verus! {
/// Closes `inv()` after `wlock_thread_unless_killed`: only the target entry's lock state moved.
pub(super) proof fn wlock_thread_eof(pre: KernelK, post: KernelK, thread_ptr: RwLockThreadPtr, lctx: LocalContext, ret: Option<Tracked<LockPerm>>)
    requires
        pre.inv(),
        post == (KernelK { thr_mp: post.thr_mp, ..pre }),
        post.thr_mp.perms_wf(),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        ret is None ==> post.thr_mp.spec_index(thread_ptr) == pre.thr_mp.spec_index(thread_ptr),
        ret is Some ==> !pre.thr_mp.spec_index(thread_ptr).being_killed(),
        ret is Some ==> wlock_ensures(pre.thr_mp.spec_index(thread_ptr), post.thr_mp.spec_index(thread_ptr), pre.thr_mp.lock_id_by_key(thread_ptr), &lctx, ret.unwrap().view()),
    ensures
        post.inv(),
        ret is Some ==> post.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean() && post.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean() && post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
        ret is Some ==> !post.thr_mp.spec_index(thread_ptr).view_ghost().exited,
{
    assert(thread_perms_wf(post.thr_mp)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked); };
    assert(thread_invariant_fields_unchanged(pre.thr_mp, post.thr_mp)) by { thread_lock_op_preserves_invariant_fields(pre.thr_mp, post.thr_mp, thread_ptr); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_invariant_fields(pre, post); };
    assert(process_thread_wf(post.prc_mp, post.thr_mp)) by {
        thread_invariant_fields_unchanged_implies_process_management_fields(pre.thr_mp, post.thr_mp);
        process_thread_wf_preserved_for_thread_process_management_fields(post.prc_mp, pre.thr_mp, post.thr_mp);
    };
    assert(thread_dangling_chain_end_wf(post.thr_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thr_mp, post.thr_mp); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
    assert(post.process_management_inv()) by { process_management_inv_preserved_for_thread_invariant_fields(pre, post); };
    if ret is Some {
        assert(post.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean() && post.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean() && post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None
            && !post.thr_mp.spec_index(thread_ptr).view_ghost().exited) by {
            reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked);
        };
    }
}

/// Closes `inv()` after `mark_thread_kill`: the write-held thread of a marked, write-held process is marked; its view
/// and lock state are unchanged.
pub(super) proof fn mark_thread_kill_eof(pre: KernelK, post: KernelK, pre_lctx: LocalContext, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr)
    requires
        pre.inv(),
        pre.prc_mp.dom().contains(process_ptr),
        pre.prc_mp.spec_index(process_ptr).being_killed(),
        typed_lock_map_contains_mode(pre_lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        pre.prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(thread_ptr),
        typed_lock_map_contains_mode(pre_lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        pre.thr_mp.dom().contains(thread_ptr),
        !pre.thr_mp.spec_index(thread_ptr).being_killed(),
        !pre.thr_mp.spec_index(thread_ptr).view().state.is_reply_waiting(),
        typed_lock_maps_aligned(&pre, &pre_lctx),
        post == (KernelK { thr_mp: post.thr_mp, ..pre }),
        post.thr_mp.perms_wf(),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).being_killed(),
        post.thr_mp.spec_index(thread_ptr).locking_thread() == pre.thr_mp.spec_index(thread_ptr).locking_thread(),
        post.thr_mp.spec_index(thread_ptr).is_init() == pre.thr_mp.spec_index(thread_ptr).is_init(),
        post.thr_mp.spec_index(thread_ptr).view() == pre.thr_mp.spec_index(thread_ptr).view(),
        post.thr_mp.spec_index(thread_ptr).view_rodata() == pre.thr_mp.spec_index(thread_ptr).view_rodata(),
        post.thr_mp.spec_index(thread_ptr).view_ghost() == pre.thr_mp.spec_index(thread_ptr).view_ghost(),
    ensures
        post.inv(),
{
    assert(thread_perms_wf(post.thr_mp)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked); };
    assert(thread_invariant_fields_unchanged(pre.thr_mp, post.thr_mp)) by { thread_lock_op_preserves_invariant_fields(pre.thr_mp, post.thr_mp, thread_ptr); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_invariant_fields(pre, post); };
    assert(process_thread_wf(post.prc_mp, post.thr_mp)) by {
        reveal(process_thread_wf);
        pre.prc_mp.typed_lock_map_aligned_write_at(pre_lctx.process_lock_map(), pre_lctx.thread_id(), process_ptr);
        pre.thr_mp.typed_lock_map_aligned_write_at(pre_lctx.thread_lock_map(), pre_lctx.thread_id(), thread_ptr);
    };
    assert(thread_dangling_chain_end_wf(post.thr_mp)) by {
        process_thread_wf_process_at(pre.prc_mp, pre.thr_mp, process_ptr, thread_ptr); thread_perms_wf_at(pre.thr_mp, thread_ptr);
        thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thr_mp, post.thr_mp);
    };
    assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
    assert(post.process_management_inv()) by { process_management_inv_preserved_for_thread_invariant_fields(pre, post); };
}

/// Closes `inv()` after `wunlock_thread`: the target entry is released with its pendings, temporary allocations, and
/// syscall progress already clear.
pub(super) proof fn wunlock_thread_eof(pre: KernelK, post: KernelK, thread_ptr: RwLockThreadPtr, holder: LockThreadId)
    requires
        pre.inv(),
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).wlocked_by_thread(holder),
        forall|t: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(t).locking_thread()]
            pre.thr_mp.dom().contains(t) && pre.thr_mp.spec_index(t).locked_by_thread(holder) ==> !(pre.thr_mp.spec_index(t).view().state is KILLED) || pre.thr_mp.spec_index(t).being_killed()
                || pre.thr_mp.spec_index(thread_ptr).view().call_depth.view() < pre.thr_mp.spec_index(t).view().call_depth.view(),
        pre.thr_mp.spec_index(thread_ptr).being_killed() == false,
        !(pre.thr_mp.spec_index(thread_ptr).view().state is IPC_ENDPOINT_TRANSIT),
        !(pre.thr_mp.spec_index(thread_ptr).view().state is KILLED),
        pre.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        pre.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
        !pre.thr_mp.spec_index(thread_ptr).view_ghost().exited,
        post == (KernelK { thr_mp: post.thr_mp, ..pre }),
        post.thr_mp.perms_wf(),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        wunlock_ensures(pre.thr_mp.spec_index(thread_ptr), post.thr_mp.spec_index(thread_ptr)),
    ensures
        post.inv(),
{
    assert(thread_perms_wf(post.thr_mp)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked); };
    assert(thread_invariant_fields_unchanged(pre.thr_mp, post.thr_mp)) by { thread_lock_op_preserves_invariant_fields(pre.thr_mp, post.thr_mp, thread_ptr); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_invariant_fields(pre, post); };
    assert(process_thread_wf(post.prc_mp, post.thr_mp)) by {
        thread_invariant_fields_unchanged_implies_process_management_fields(pre.thr_mp, post.thr_mp);
        process_thread_wf_preserved_for_thread_process_management_fields(post.prc_mp, pre.thr_mp, post.thr_mp);
    };
    assert(thread_dangling_chain_end_wf(post.thr_mp)) by {
        reveal(thread_dangling_chain_end_wf); reveal(thread_perms_wf);
    };
    assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
    assert(post.process_management_inv()) by { process_management_inv_preserved_for_thread_invariant_fields(pre, post); };
}

/// Closes `inv()` after `set_thread_syscall_progress`: only the write-held thread's syscall progress changed.
pub(super) proof fn set_thread_syscall_progress_eof(pre: KernelK, post: KernelK, lctx: LocalContext, thread_ptr: RwLockThreadPtr, progress: Ghost<Option<SyscallProgress>>)
    requires
        pre.inv(),
        pre.thr_mp.dom().contains(thread_ptr),
        post == (KernelK { thr_mp: post.thr_mp, ..pre }),
        post.thr_mp.perms_wf(),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).is_init(),
        post.thr_mp.spec_index(thread_ptr).wlocked_by(&lctx),
        post.thr_mp.spec_index(thread_ptr).view_rodata() == pre.thr_mp.spec_index(thread_ptr).view_rodata(),
        post.thr_mp.spec_index(thread_ptr).view_ghost() == pre.thr_mp.spec_index(thread_ptr).view_ghost(),
        post.thr_mp.spec_index(thread_ptr).locking_thread() == pre.thr_mp.spec_index(thread_ptr).locking_thread(),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        post.thr_mp.spec_index(thread_ptr).killer_info() == pre.thr_mp.spec_index(thread_ptr).killer_info(),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: progress, ..pre.thr_mp.spec_index(thread_ptr).view() }),
    ensures
        post.inv(),
{
    assert(post.subsystems_inv()) by {
        assert(thread_perms_wf(post.thr_mp)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked); };
        reveal(KernelK::default_pagetable_wf);
    };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_endpoint_memory_fields(pre, post); };
    assert(post.process_management_inv()) by {
        assert(thread_process_management_fields_unchanged(pre.thr_mp, post.thr_mp));
        thread_caller_callee_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp);
        thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.ep_mp);
        thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.ep_mp);
        container_thread_endpoint_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp, post.ep_mp);
        container_thread_scheduler_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp);
        container_thread_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp);
        process_thread_wf_preserved_for_thread_process_management_fields(post.prc_mp, pre.thr_mp, post.thr_mp);
        thread_cpu_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.cpu_arr);
        assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
        assert(thread_dangling_chain_end_wf(post.thr_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thr_mp, post.thr_mp); };
    };
}
} // verus!
