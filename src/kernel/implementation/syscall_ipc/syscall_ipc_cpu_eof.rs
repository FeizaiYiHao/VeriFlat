use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_cpu_spec::ipc_cpu_and_waiter_transition_framing;

verus! {
proof fn ipc_cpu_eof_process(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr, peer_scheduler_ptr: RwLockSchedulerPtr,
    source_container: RwLockContainerPtr, target_container: RwLockContainerPtr,
    source_cpu_set: RwLockCpuSetPtr, target_cpu_set: RwLockCpuSetPtr,
    transfer_cpu_id: CpuId, transferred: bool, peer_result: RetValueType, thread_id: LockThreadId,
)
    requires
        ipc_cpu_and_waiter_transition_framing(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, source_container, target_container, source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(ipc_cpu_and_waiter_transition_framing);
    assert(post.process_management_inv()) by {
        assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
        assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); reveal(container_cpu_set_wf); reveal(cpu_array_wf); };
        assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); reveal(cpu_array_wf); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); };
        assert({
            &&& container_endpoint_wf(post.ctn_mp, post.ep_mp)
            &&& thread_caller_callee_wf(post.thr_mp)
        }) by { reveal(container_endpoint_wf); reveal(thread_caller_callee_wf); };
        assert({
            &&& container_scheduler_wf(post.ctn_mp, post.sched_mp)
            &&& container_thread_wf(post.ctn_mp, post.thr_mp)
            &&& process_thread_wf(post.prc_mp, post.thr_mp)
        }) by { reveal(container_scheduler_wf); reveal(container_thread_wf); reveal(process_thread_wf); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { reveal(thread_cpu_wf); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { seq_skip_lemma::<RwLockThreadPtr>(); reveal(endpoint_perms_wf); reveal(LinkedList::wf_value_list); reveal(LinkedList::value_list_unique); reveal(thread_endpoint_queue_wf); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); reveal(container_thread_endpoint_wf); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by {
            seq_push_lemma::<RwLockThreadPtr>();
            reveal(scheduler_perms_wf); reveal(LinkedList::wf_map); reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
        };
    };
}

pub(super) proof fn ipc_cpu_eof(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr, peer_scheduler_ptr: RwLockSchedulerPtr,
    source_container: RwLockContainerPtr, target_container: RwLockContainerPtr,
    source_cpu_set: RwLockCpuSetPtr, target_cpu_set: RwLockCpuSetPtr,
    transfer_cpu_id: CpuId, transferred: bool, peer_result: RetValueType, thread_id: LockThreadId,
)
    requires
        ipc_cpu_and_waiter_transition_framing(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, source_container, target_container, source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id),
        post.cpu_arr.inv(),
        post.pcid_needflush == pre.pcid_needflush,
        post.cpu_published == pre.cpu_published,
        post.cpu_set_mp.spec_index(source_cpu_set).view().owned_cpus.wf(),
        post.cpu_set_mp.spec_index(target_cpu_set).view().owned_cpus.wf(),
        post.ep_mp.spec_index(endpoint_ptr).view().queue.wf(),
        post.sched_mp.spec_index(peer_scheduler_ptr).view().queue.wf(),
    ensures post.inv(),
{
    reveal(ipc_cpu_and_waiter_transition_framing);
    assert(post.subsystems_inv()) by {
        assert({
            &&& thread_perms_wf(post.thr_mp)
            &&& endpoint_perms_wf(post.ep_mp)
            &&& scheduler_perms_wf(post.sched_mp)
        }) by { reveal(thread_perms_wf); reveal(endpoint_perms_wf); reveal(scheduler_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); };
        reveal(cpu_set_perms_wf); reveal(cpu_array_wf); reveal(cpu_published_wf); reveal(KernelK::default_pagetable_wf);
    };
    assert(post.memory_management_inv()) by {
        assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
        assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { reveal(scheduler_pages_wf); };
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_pages_wf); };
        assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { reveal(endpoint_pages_wf); };
        thread_staged_pages_4k_wf_preserved_for_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        thread_staged_pages_2m_wf_preserved_for_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        thread_staged_pages_1g_wf_preserved_for_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_4k_mp);
        container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_2m_mp);
        container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_1g_mp);
    };
    ipc_cpu_eof_process(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, source_container, target_container, source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id);
    assert(post.inv()) by { reveal(cpu_array_wf); reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(tlb_wf_spec); };
}
}
