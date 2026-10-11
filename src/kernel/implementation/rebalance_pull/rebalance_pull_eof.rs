use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::rebalance_pull_spec::rebalance_pull_transition;

verus! {
#[verifier::spinoff_prover]
proof fn rebalance_pull_eof_container_thread_scheduler(pre: KernelK, post: KernelK, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr, victim: CpuId, thread_ptr: RwLockThreadPtr)
    requires
        pre.inv(),
        rebalance_pull_transition(pre, post, cpu_id, scheduler_ptr, victim, thread_ptr),
    ensures container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp),
{
    reveal(rebalance_pull_transition);
    let queue = pre.sched_mp.spec_index(scheduler_ptr).shard(victim).queue;
    assert(queue.view().no_duplicates()) by { reveal(scheduler_perms_wf); reveal(LinkedList::value_list_unique); reveal(LinkedList::wf_value_list); };
    reveal(container_thread_scheduler_wf); reveal(container_scheduler_wf); reveal(container_thread_wf);
    seq_push_lemma::<RwLockThreadPtr>(); seq_skip_lemma::<RwLockThreadPtr>();
}

#[verifier::spinoff_prover]
proof fn rebalance_pull_eof_process_management_inv(pre: KernelK, post: KernelK, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr, victim: CpuId, thread_ptr: RwLockThreadPtr)
    requires
        pre.inv(),
        rebalance_pull_transition(pre, post, cpu_id, scheduler_ptr, victim, thread_ptr),
    ensures post.process_management_inv(),
{
    reveal(rebalance_pull_transition);
    assert(post.process_management_inv()) by {
        rebalance_pull_eof_container_thread_scheduler(pre, post, cpu_id, scheduler_ptr, victim, thread_ptr);
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { reveal(thread_cpu_wf); };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { reveal(container_thread_wf); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { reveal(process_thread_wf); };
        assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { reveal(container_scheduler_wf); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_queue_wf); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(container_thread_endpoint_wf); };
        assert(thread_caller_callee_wf(post.thr_mp)) by { reveal(thread_caller_callee_wf); };
    };
}

pub(super) proof fn rebalance_pull_eof(pre: KernelK, post: KernelK, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr, victim: CpuId, thread_ptr: RwLockThreadPtr)
    requires
        pre.inv(),
        rebalance_pull_transition(pre, post, cpu_id, scheduler_ptr, victim, thread_ptr),
        post.thr_mp.perms_wf(),
        post.thr_mp.spec_index(thread_ptr).view().inv(),
        scheduler_perms_wf(post.sched_mp),
    ensures
        post.inv(),
        ({
            let queues = scheduler_shards_of(pre.sched_mp.spec_index(scheduler_ptr));
            scheduler_shards_of(post.sched_mp.spec_index(scheduler_ptr)) == queues.update(victim as int, queues[victim as int].skip(1)).update(cpu_id as int, queues[cpu_id as int].push(thread_ptr))
        }),
{
    hide(Seq::contains);
    reveal(rebalance_pull_transition);
    let queues = scheduler_shards_of(pre.sched_mp.spec_index(scheduler_ptr));
    assert(scheduler_shards_of(post.sched_mp.spec_index(scheduler_ptr)) =~= queues.update(victim as int, queues[victim as int].skip(1)).update(cpu_id as int, queues[cpu_id as int].push(thread_ptr))) by { reveal(scheduler_shards_of); };
    assert(post.subsystems_inv()) by {
        assert(thread_perms_wf(post.thr_mp)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); };
        reveal(KernelK::default_pagetable_wf);
    };
    assert(post.memory_management_inv()) by {
        assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { reveal(scheduler_pages_wf); };
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_pages_wf); };
        thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_4k_mp);
        container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_2m_mp);
        container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_1g_mp);
    };
    rebalance_pull_eof_process_management_inv(pre, post, cpu_id, scheduler_ptr, victim, thread_ptr);
}
}
