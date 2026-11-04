use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
pub(super) open spec fn return_free_quota_2m_eof_transition_framing(pre: KernelK, post: KernelK, thrd_ptr: RwLockThreadPtr, depth: usize, allc_ptr: RwLockPageAllocatorPtr, amount: usize) -> bool {
    let old_thread = pre.thrd_mp.spec_index(thrd_ptr);
    let new_thread = post.thrd_mp.spec_index(thrd_ptr);
    let old_allocator = pre.allc_2m_mp.spec_index(allc_ptr);
    let new_allocator = post.allc_2m_mp.spec_index(allc_ptr);
    &&& post == (KernelK { thrd_mp: post.thrd_mp, allc_2m_mp: post.allc_2m_mp, ..pre })
    &&& kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post)
    &&& post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr)
    &&& new_thread.view() == (Thread { direct_free_quota_pending_2m: new_thread.view().direct_free_quota_pending_2m, indirect_free_quota_pending_2m: new_thread.view().indirect_free_quota_pending_2m, ..old_thread.view() })
    &&& new_thread.view().direct_free_quota_pending_2m.view() == if depth == old_thread.view().container_depth { 0usize } else { old_thread.view().direct_free_quota_pending_2m.view() }
    &&& new_thread.view().indirect_free_quota_pending_2m.view()
        == if depth < old_thread.view().container_depth { old_thread.view().indirect_free_quota_pending_2m.view().update(depth as int, 0usize) } else { old_thread.view().indirect_free_quota_pending_2m.view() }
    &&& new_thread.view().free_quota_pending_2m_at_depth(depth) == 0
    &&& new_thread.is_init()
    &&& new_thread.view_rodata() == old_thread.view_rodata()
    &&& new_thread.view_ghost() == old_thread.view_ghost()
    &&& new_thread.locking_thread() == old_thread.locking_thread()
    &&& new_thread.being_killed() == old_thread.being_killed()
    &&& new_thread.killer_info() == old_thread.killer_info()
    &&& post.allc_2m_mp.unchanged_except(&pre.allc_2m_mp, allc_ptr)
    &&& new_allocator == (PageAllocator { quota: new_allocator.quota, ..old_allocator })
    &&& new_allocator.quota.view() == (AllocatorQuota { value: new_allocator.quota.view().value, ..old_allocator.quota.view() })
    &&& new_allocator.quota.view().value == old_allocator.quota.view().value + amount
    &&& new_allocator.quota.is_init()
    &&& new_allocator.quota.view_rodata() == old_allocator.quota.view_rodata()
    &&& new_allocator.quota.view_ghost() == old_allocator.quota.view_ghost()
    &&& new_allocator.quota.locking_thread() == old_allocator.quota.locking_thread()
    &&& new_allocator.quota.being_killed() == old_allocator.quota.being_killed()
}

/// EOF closure leaf: the 2m allocator quota invariant after the pending quota returns to the allocator.
proof fn return_free_quota_2m_eof_memory_quota_2m(pre: KernelK, post: KernelK, thrd_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, depth: usize, allc_ptr: RwLockPageAllocatorPtr, amount: usize)
    requires
        pre.inv(),
        return_free_quota_2m_eof_transition_framing(pre, post, thrd_ptr, depth, allc_ptr, amount),
        pre.thrd_mp.dom().contains(thrd_ptr),
        pre.ctn_mp.dom().contains(owner),
        pre.ctn_mp.spec_index(owner).view_rodata().view().depth == depth,
        pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_2m == allc_ptr,
        depth <= pre.thrd_mp.spec_index(thrd_ptr).view().container_depth,
        if depth == pre.thrd_mp.spec_index(thrd_ptr).view().container_depth { owner == pre.thrd_mp.spec_index(thrd_ptr).view().owning_container } else { pre.thrd_mp.spec_index(thrd_ptr).view().upper_container_seq.view().spec_index(depth as int) == owner },
        amount == pre.thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_2m_at_depth(depth),
        pre.allc_2m_mp.spec_index(allc_ptr).quota.view().value + amount <= pre.allc_2m_mp.spec_index(allc_ptr).total_free_pages.view(),
        thread_perms_wf(post.thrd_mp),
        post.thrd_mp.spec_index(thrd_ptr).inv(),
        post.allc_2m_mp.perms_wf(),
        post.subsystems_inv(),
    ensures
        container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_2m_mp),
{
    reveal(return_free_quota_2m_eof_transition_framing);
    reveal(container_process_allocator_quota_2m_wf); reveal(container_allocator_wf); reveal(container_thread_wf); reveal(container_uppertree_seq_wf);
    lemma_thread_effective_quota_2m_fold_sum_eq_forall();
    thread_pending_2m_change_at_one_thread_implies_folds_change_by(thrd_ptr, if depth == pre.thrd_mp.spec_index(thrd_ptr).view().container_depth { -(amount as int) } else { 0int },
        depth as int, if depth < pre.thrd_mp.spec_index(thrd_ptr).view().container_depth { -(amount as int) } else { 0int });
}

proof fn return_free_quota_2m_eof_memory(pre: KernelK, post: KernelK, thrd_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, depth: usize, allc_ptr: RwLockPageAllocatorPtr, amount: usize)
    requires
        pre.inv(),
        return_free_quota_2m_eof_transition_framing(pre, post, thrd_ptr, depth, allc_ptr, amount),
        pre.thrd_mp.dom().contains(thrd_ptr),
        pre.ctn_mp.dom().contains(owner),
        pre.ctn_mp.spec_index(owner).view_rodata().view().depth == depth,
        pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_2m == allc_ptr,
        depth <= pre.thrd_mp.spec_index(thrd_ptr).view().container_depth,
        if depth == pre.thrd_mp.spec_index(thrd_ptr).view().container_depth { owner == pre.thrd_mp.spec_index(thrd_ptr).view().owning_container } else { pre.thrd_mp.spec_index(thrd_ptr).view().upper_container_seq.view().spec_index(depth as int) == owner },
        amount == pre.thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_2m_at_depth(depth),
        pre.allc_2m_mp.spec_index(allc_ptr).quota.view().value + amount <= pre.allc_2m_mp.spec_index(allc_ptr).total_free_pages.view(),
        thread_perms_wf(post.thrd_mp),
        post.thrd_mp.spec_index(thrd_ptr).inv(),
        post.allc_2m_mp.perms_wf(),
        post.subsystems_inv(),
    ensures post.memory_management_inv(),
{
    reveal(return_free_quota_2m_eof_transition_framing);
    assert(post.memory_management_inv()) by {
        assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp); };
        assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
        assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
            let thread = pre.thrd_mp.spec_index(thrd_ptr).view();
            container_thread_wf_at(pre.ctn_mp, pre.thrd_mp, thrd_ptr); container_thread_wf_uppertree_at(pre.ctn_mp, pre.thrd_mp, thrd_ptr);
            if depth < thread.container_depth {
                container_perms_wf_at(pre.ctn_mp, thread.owning_container); assert(thread.upper_container_seq.view().contains(owner));
                container_uppertree_seq_wf_at(pre.rt_ctn, pre.ctn_mp, thread.owning_container, owner);
            }
            reveal(container_kill_retire_wf); reveal(container_allocator_wf);
        };
        assert(post.allocator_free_pages_wf()) by { reveal(allocator_free_page_ptrs_wf); };
        assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_global_free_2m_page_wf); reveal(container_allocator_cpu_cache_free_2m_page_wf); };
        assert(thread_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
        assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thrd_mp)) by { reveal(page_object_owner_wf); reveal(container_page_owner_wf); };
        assert(thread_staged_pages_wf(post.thrd_mp, post.pg_arr)) by {
            thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
            thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
            thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
        };
        return_free_quota_2m_eof_memory_quota_2m(pre, post, thrd_ptr, owner, depth, allc_ptr, amount);
        assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp)) by { container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_4k_mp); };
        assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_1g_mp)) by { container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_1g_mp); };
    };
}

pub(super) proof fn return_free_quota_2m_eof(pre: KernelK, post: KernelK, thrd_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, depth: usize, allc_ptr: RwLockPageAllocatorPtr, amount: usize)
    requires
        pre.inv(),
        return_free_quota_2m_eof_transition_framing(pre, post, thrd_ptr, depth, allc_ptr, amount),
        pre.thrd_mp.dom().contains(thrd_ptr),
        pre.ctn_mp.dom().contains(owner),
        pre.ctn_mp.spec_index(owner).view_rodata().view().depth == depth,
        pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_2m == allc_ptr,
        depth <= pre.thrd_mp.spec_index(thrd_ptr).view().container_depth,
        if depth == pre.thrd_mp.spec_index(thrd_ptr).view().container_depth { owner == pre.thrd_mp.spec_index(thrd_ptr).view().owning_container } else { pre.thrd_mp.spec_index(thrd_ptr).view().upper_container_seq.view().spec_index(depth as int) == owner },
        amount == pre.thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_2m_at_depth(depth),
        pre.allc_2m_mp.spec_index(allc_ptr).quota.view().value + amount <= pre.allc_2m_mp.spec_index(allc_ptr).total_free_pages.view(),
        thread_perms_wf(post.thrd_mp),
        post.thrd_mp.spec_index(thrd_ptr).inv(),
        post.allc_2m_mp.perms_wf(),
    ensures
        post.inv(),
        kernel_container_quota_2m_changed(&pre, &post, owner, amount as int),
{
    reveal(return_free_quota_2m_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(allocator_perms_wf); reveal(KernelK::default_pagetable_wf); };
    return_free_quota_2m_eof_memory(pre, post, thrd_ptr, owner, depth, allc_ptr, amount);
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
    assert(kernel_container_quota_2m_changed(&pre, &post, owner, amount as int)) by {
        reveal(kernel_container_quota_2m_changed); reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(container_allocator_wf);
    };
}
}
