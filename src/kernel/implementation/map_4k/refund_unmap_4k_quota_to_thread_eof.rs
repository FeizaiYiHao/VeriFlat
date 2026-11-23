use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
pub(super) open spec fn refund_unmap_4k_quota_to_thread_eof_transition_framing(pre: KernelK, post: KernelK, thrd_ptr: RwLockThreadPtr, amount: usize) -> bool {
    let old_thread = pre.thrd_mp.spec_index(thrd_ptr);
    let new_thread = post.thrd_mp.spec_index(thrd_ptr);
    &&& post == (KernelK { thrd_mp: post.thrd_mp, ..pre })
    &&& post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr)
    &&& new_thread.view() == (Thread { quota_4k: new_thread.view().quota_4k, direct_free_quota_pending_4k: new_thread.view().direct_free_quota_pending_4k, ..old_thread.view() })
    &&& new_thread.view().quota_4k == old_thread.view().quota_4k + amount
    &&& new_thread.view().direct_free_quota_pending_4k.view() == 0
    &&& new_thread.is_init()
    &&& new_thread.view_rodata() == old_thread.view_rodata()
    &&& new_thread.view_ghost() == old_thread.view_ghost()
    &&& new_thread.locking_thread() == old_thread.locking_thread()
    &&& new_thread.being_killed() == old_thread.being_killed()
    &&& new_thread.killer_info() == old_thread.killer_info()
}

/// EOF closure leaf: the 4K allocator quota invariant after the thread's direct pending quota moves into its own 4K quota.
proof fn refund_unmap_4k_quota_to_thread_eof_memory_quota_4k(pre: KernelK, post: KernelK, thrd_ptr: RwLockThreadPtr, amount: usize)
    requires
        pre.inv(),
        refund_unmap_4k_quota_to_thread_eof_transition_framing(pre, post, thrd_ptr, amount),
        pre.thrd_mp.dom().contains(thrd_ptr),
        amount == pre.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
    ensures
        container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp),
{
    reveal(refund_unmap_4k_quota_to_thread_eof_transition_framing);
    reveal(container_process_allocator_quota_4k_wf); reveal(container_thread_wf);
    unchanged_members_implies_thread_effective_quota_4k_fold_sum_eq_forall();
    one_member_changed_implies_thread_effective_quota_4k_fold_sum_changed_by_forall(thrd_ptr, amount as int);
    one_member_changed_implies_thread_pending_4k_fold_sums_changed_by_forall(thrd_ptr, -(amount as int), 0int, 0int);
}

proof fn refund_unmap_4k_quota_to_thread_eof_memory(pre: KernelK, post: KernelK, thrd_ptr: RwLockThreadPtr, amount: usize)
    requires
        pre.inv(),
        refund_unmap_4k_quota_to_thread_eof_transition_framing(pre, post, thrd_ptr, amount),
        pre.thrd_mp.dom().contains(thrd_ptr),
        amount == pre.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
        thread_perms_wf(post.thrd_mp),
        post.subsystems_inv(),
    ensures post.memory_management_inv(),
{
    reveal(refund_unmap_4k_quota_to_thread_eof_transition_framing);
    assert(post.memory_management_inv()) by {
        assert(thread_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
        assert(page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr)) by { reveal(page_object_owner_wf); reveal(container_owned_pages_wf); };
        assert(thread_staged_pages_wf(post.thrd_mp, post.pg_arr)) by {
            thread_staged_4k_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
            thread_staged_2m_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
            thread_staged_1g_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
        };
        refund_unmap_4k_quota_to_thread_eof_memory_quota_4k(pre, post, thrd_ptr, amount);
        assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_2m_mp)) by {
            container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_2m_mp);
        };
        assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_1g_mp)) by {
            container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_1g_mp);
        };
    };
}

/// EOF closure: the kernel invariant after the thread's direct pending 4K quota `amount` moves into its own 4K quota, and the
/// move is a thread quota change by `amount`.
pub(super) proof fn refund_unmap_4k_quota_to_thread_eof(pre: KernelK, post: KernelK, thrd_ptr: RwLockThreadPtr, amount: usize)
    requires
        pre.inv(),
        refund_unmap_4k_quota_to_thread_eof_transition_framing(pre, post, thrd_ptr, amount),
        pre.thrd_mp.dom().contains(thrd_ptr),
        amount == pre.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
        thread_perms_wf(post.thrd_mp),
    ensures
        post.inv(),
        kernel_thread_quota_4k_changed(&pre, &post, thrd_ptr, amount as int),
{
    reveal(refund_unmap_4k_quota_to_thread_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    refund_unmap_4k_quota_to_thread_eof_memory(pre, post, thrd_ptr, amount);
    assert(post.process_management_inv()) by {
        thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.ep_mp);
        thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.ep_mp);
        container_thread_endpoint_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp, post.ep_mp);
        container_thread_scheduler_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp, post.sched_mp);
        container_thread_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp);
        process_thread_wf_preserved_for_thread_process_management_fields(post.prc_mp, pre.thrd_mp, post.thrd_mp);
        thread_cpu_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.cpu_arr);
        assert(thread_caller_callee_wf(post.thrd_mp)) by { reveal(thread_caller_callee_wf); };
        assert(thread_dangling_chain_end_wf(post.thrd_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thrd_mp, post.thrd_mp); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
    };
    assert(kernel_thread_quota_4k_changed(&pre, &post, thrd_ptr, amount as int)) by { reveal(kernel_thread_quota_4k_changed); };
}
} // verus!
