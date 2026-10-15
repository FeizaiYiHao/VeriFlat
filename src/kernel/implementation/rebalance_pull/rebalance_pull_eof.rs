use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::rebalance_pull_spec::rebalance_pull_transition;

verus! {
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

proof fn rebalance_pull_eof_thread_endpoint_ref_counter(pre: KernelK, post: KernelK, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr, victim: CpuId, thread_ptr: RwLockThreadPtr)
    requires
        thread_endpoint_ref_counter_wf(pre.thr_mp, pre.ep_mp),
        rebalance_pull_transition(pre, post, cpu_id, scheduler_ptr, victim, thread_ptr),
    ensures thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp),
{ reveal(rebalance_pull_transition); reveal(thread_endpoint_ref_counter_wf); }

proof fn rebalance_pull_eof_process_management_inv(pre: KernelK, post: KernelK, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr, victim: CpuId, thread_ptr: RwLockThreadPtr)
    requires
        pre.inv(),
        rebalance_pull_transition(pre, post, cpu_id, scheduler_ptr, victim, thread_ptr),
    ensures post.process_management_inv(),
{
    reveal(rebalance_pull_transition);
    assert(post.process_management_inv()) by {
        rebalance_pull_eof_container_thread_scheduler(pre, post, cpu_id, scheduler_ptr, victim, thread_ptr);
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_running_thread_eq(pre.thr_mp, post.thr_mp, pre.cpu_arr, post.cpu_arr); };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { container_thread_wf_preserved_for_container_thread_link_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { process_thread_wf_preserved_for_process_thread_link_eq(pre.prc_mp, post.prc_mp, pre.thr_mp, post.thr_mp); };
        assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { container_scheduler_wf_preserved_for_scheduler_owner_eq(pre.ctn_mp, post.ctn_mp, pre.sched_mp, post.sched_mp); };
        rebalance_pull_eof_thread_endpoint_ref_counter(pre, post, cpu_id, scheduler_ptr, victim, thread_ptr);
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_endpoint_waiting_eq(pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
        assert(thread_caller_callee_wf(post.thr_mp)) by { thread_caller_callee_wf_preserved_for_call_link_eq(pre.thr_mp, post.thr_mp); };
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
