use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::wake_waiting_reply_caller_spec::wake_waiting_reply_caller_eof_transition_framing;

verus! {
proof fn wake_waiting_reply_caller_eof_memory_management_inv(
    pre: KernelK, post: KernelK, thread_ptr: RwLockThreadPtr, caller_ptr: RwLockThreadPtr, scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId,
)
    requires
        pre.inv(),
        wake_waiting_reply_caller_eof_transition_framing(pre, post, thread_ptr, caller_ptr, scheduler_ptr, cpu_id),
        post.subsystems_inv(),
    ensures post.memory_management_inv(),
{
    reveal(wake_waiting_reply_caller_eof_transition_framing);
    assert(post.memory_management_inv()) by {
        assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { reveal(scheduler_pages_wf); };
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

proof fn wake_waiting_reply_caller_eof_process_management_inv(
    pre: KernelK, post: KernelK, thread_ptr: RwLockThreadPtr, caller_ptr: RwLockThreadPtr, scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId,
)
    requires
        pre.inv(),
        thread_ptr != caller_ptr,
        index_valid(NUM_CPUS, cpu_id),
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.dom().contains(caller_ptr),
        pre.sched_mp.dom().contains(scheduler_ptr),
        pre.ctn_mp.spec_index(pre.thr_mp.spec_index(caller_ptr).view().owning_container).view_rodata().view().scheduler == scheduler_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().caller == Some(caller_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().state is WAITING_REPLY,
        !pre.sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().view().queue.dom().contains(pre.thr_mp.spec_index(caller_ptr).view().scheduler_linkedlist_node.addr()),
        wake_waiting_reply_caller_eof_transition_framing(pre, post, thread_ptr, caller_ptr, scheduler_ptr, cpu_id),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(wake_waiting_reply_caller_eof_transition_framing);
    assert(post.process_management_inv()) by {
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_descriptor_eq(pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
        assert(thread_caller_callee_wf(post.thr_mp)) by { reveal(thread_caller_callee_wf); };
        assert(thread_dangling_chain_end_wf(post.thr_mp)) by { reveal(thread_dangling_chain_end_wf); };
        assert({
            &&& container_thread_wf(post.ctn_mp, post.thr_mp)
            &&& process_thread_wf(post.prc_mp, post.thr_mp)
        }) by { reveal(container_thread_wf); reveal(process_thread_wf); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_running_thread_eq(pre.thr_mp, post.thr_mp, pre.cpu_arr, post.cpu_arr); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_endpoint_waiting_eq(pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
        assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { container_scheduler_wf_preserved_for_scheduler_owner_eq(pre.ctn_mp, post.ctn_mp, pre.sched_mp, post.sched_mp); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by {
            seq_push_lemma::<RwLockThreadPtr>();
            reveal(scheduler_perms_wf); reveal(LinkedList::wf_map); reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
        };
    };
}

/// The woken caller and the cleared caller link keep the kernel invariant.
pub(super) proof fn wake_waiting_reply_caller_eof(
    pre: KernelK, post: KernelK, thread_ptr: RwLockThreadPtr, caller_ptr: RwLockThreadPtr, scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId,
)
    requires
        pre.inv(),
        thread_ptr != caller_ptr,
        index_valid(NUM_CPUS, cpu_id),
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.dom().contains(caller_ptr),
        pre.sched_mp.dom().contains(scheduler_ptr),
        pre.ctn_mp.spec_index(pre.thr_mp.spec_index(caller_ptr).view().owning_container).view_rodata().view().scheduler == scheduler_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().caller == Some(caller_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().state is WAITING_REPLY,
        !pre.sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().view().queue.dom().contains(pre.thr_mp.spec_index(caller_ptr).view().scheduler_linkedlist_node.addr()),
        wake_waiting_reply_caller_eof_transition_framing(pre, post, thread_ptr, caller_ptr, scheduler_ptr, cpu_id),
        post.thr_mp.perms_wf(),
        scheduler_perms_wf(post.sched_mp),
    ensures post.inv(),
{
    reveal(wake_waiting_reply_caller_eof_transition_framing);
    assert(post.subsystems_inv()) by {
        assert(thread_perms_wf(post.thr_mp)) by {
            reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked);
        };
        reveal(KernelK::default_pagetable_wf);
    };
    wake_waiting_reply_caller_eof_memory_management_inv(pre, post, thread_ptr, caller_ptr, scheduler_ptr, cpu_id);
    wake_waiting_reply_caller_eof_process_management_inv(pre, post, thread_ptr, caller_ptr, scheduler_ptr, cpu_id);
}
} // verus!
