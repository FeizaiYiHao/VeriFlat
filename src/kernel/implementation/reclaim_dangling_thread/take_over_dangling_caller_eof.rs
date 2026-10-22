use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::take_over_dangling_caller_spec::take_over_dangling_caller_eof_transition_framing;

verus! {
proof fn take_over_dangling_caller_eof_memory_management_inv(pre: KernelK, post: KernelK, thread_ptr: RwLockThreadPtr, dangling_ptr: RwLockThreadPtr)
    requires
        pre.inv(),
        take_over_dangling_caller_eof_transition_framing(pre, post, thread_ptr, dangling_ptr),
        post.subsystems_inv(),
    ensures post.memory_management_inv(),
{
    reveal(take_over_dangling_caller_eof_transition_framing);
    assert(post.memory_management_inv()) by {
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_pages_wf); };
        assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp)) by { reveal(page_object_owner_wf); reveal(container_page_owner_wf); };
        assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_2m_wf); };
        assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_1g_wf); };
        assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by {
            container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_4k_mp); reveal(container_thread_wf); reveal(container_process_wf);
            lemma_thread_effective_quota_4k_fold_sum_eq_forall();
            lemma_thread_pending_4k_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp);
        };
        assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp)) by {
            container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_2m_mp); reveal(container_thread_wf); reveal(container_process_wf);
            lemma_thread_effective_quota_2m_fold_sum_eq_forall();
            lemma_thread_pending_2m_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp);
        };
        assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp)) by {
            reveal(container_process_allocator_quota_1g_wf); reveal(container_thread_wf); reveal(container_process_wf);
            lemma_thread_effective_quota_1g_fold_sum_eq_forall();
            lemma_thread_pending_1g_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp);
        };
    };
}

proof fn take_over_dangling_caller_eof_process_management_inv(pre: KernelK, post: KernelK, thread_ptr: RwLockThreadPtr, dangling_ptr: RwLockThreadPtr)
    requires
        pre.inv(),
        thread_ptr != dangling_ptr,
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.dom().contains(dangling_ptr),
        pre.thr_mp.spec_index(thread_ptr).view().caller == Some(dangling_ptr),
        pre.thr_mp.spec_index(dangling_ptr).view().state is DANGLING,
        pre.thr_mp.spec_index(dangling_ptr).locking_thread() is Write,
        !pre.thr_mp.spec_index(dangling_ptr).being_killed(),
        pre.thr_mp.spec_index(thread_ptr).locking_thread() is Write,
        pre.thr_mp.spec_index(thread_ptr).view().state is RUNNING || pre.thr_mp.spec_index(thread_ptr).view().state is KILLED
            || pre.thr_mp.spec_index(thread_ptr).view().state is WAITING_REPLY,
        pre.thr_mp.spec_index(thread_ptr).locking_thread()->Write_thread_id == pre.thr_mp.spec_index(dangling_ptr).locking_thread()->Write_thread_id,
        take_over_dangling_caller_eof_transition_framing(pre, post, thread_ptr, dangling_ptr),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(take_over_dangling_caller_eof_transition_framing);
    assert(post.process_management_inv()) by {
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_descriptor_eq(pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
        assert(thread_caller_callee_wf(post.thr_mp)) by { reveal(thread_caller_callee_wf); };
        assert(thread_dangling_chain_end_wf(post.thr_mp)) by {
            let thread = pre.thr_mp.spec_index(thread_ptr);
            thread_perms_wf_at(pre.thr_mp, thread_ptr); thread_perms_wf_at(pre.thr_mp, dangling_ptr); thread_caller_callee_wf_at(pre.thr_mp, thread_ptr);
            thread_dangling_chain_end_wf_at(pre.thr_mp, dangling_ptr);
            if thread_is_dangling(thread) && !thread.being_killed() { thread_dangling_chain_end_wf_at(pre.thr_mp, thread_ptr); }
            reveal(thread_dangling_chain_end_wf);
        };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { reveal(container_thread_wf); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { thread_perms_wf_at(pre.thr_mp, dangling_ptr); reveal(process_thread_wf); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_running_thread_eq(pre.thr_mp, post.thr_mp, pre.cpu_arr, post.cpu_arr); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_endpoint_waiting_eq(pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { container_thread_scheduler_wf_preserved_for_scheduled_thread_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp); };
    };
}

/// The taken-over dangling thread and the cleared call links keep the kernel invariant.
pub(super) proof fn take_over_dangling_caller_eof(pre: KernelK, post: KernelK, thread_ptr: RwLockThreadPtr, dangling_ptr: RwLockThreadPtr)
    requires
        pre.inv(),
        thread_ptr != dangling_ptr,
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.dom().contains(dangling_ptr),
        pre.thr_mp.spec_index(thread_ptr).view().caller == Some(dangling_ptr),
        pre.thr_mp.spec_index(dangling_ptr).view().state is DANGLING,
        pre.thr_mp.spec_index(dangling_ptr).locking_thread() is Write,
        !pre.thr_mp.spec_index(dangling_ptr).being_killed(),
        pre.thr_mp.spec_index(thread_ptr).locking_thread() is Write,
        pre.thr_mp.spec_index(thread_ptr).view().state is RUNNING || pre.thr_mp.spec_index(thread_ptr).view().state is KILLED
            || pre.thr_mp.spec_index(thread_ptr).view().state is WAITING_REPLY,
        pre.thr_mp.spec_index(thread_ptr).locking_thread()->Write_thread_id == pre.thr_mp.spec_index(dangling_ptr).locking_thread()->Write_thread_id,
        take_over_dangling_caller_eof_transition_framing(pre, post, thread_ptr, dangling_ptr),
        post.thr_mp.perms_wf(),
    ensures post.inv(),
{
    reveal(take_over_dangling_caller_eof_transition_framing);
    assert(post.subsystems_inv()) by {
        assert(thread_perms_wf(post.thr_mp)) by {
            reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
            reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
        };
        reveal(KernelK::default_pagetable_wf);
    };
    take_over_dangling_caller_eof_memory_management_inv(pre, post, thread_ptr, dangling_ptr);
    take_over_dangling_caller_eof_process_management_inv(pre, post, thread_ptr, dangling_ptr);
}
} // verus!
