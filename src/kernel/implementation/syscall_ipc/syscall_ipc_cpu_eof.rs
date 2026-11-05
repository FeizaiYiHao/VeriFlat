use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_cpu_spec::ipc_cpu_rendezvous_eof_transition_framing;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_dispatch::running_thread_not_in_endpoint_queue;

verus! {
/// Separate query: inside the combined process-management closure this leaf fails in the monolith.
proof fn ipc_cpu_rendezvous_eof_thread_endpoint_ref_counter(pre: KernelK, post: KernelK)
    requires
        thread_endpoint_ref_counter_wf(pre.thrd_mp, pre.ep_mp),
        post.thrd_mp.dom() == pre.thrd_mp.dom(),
        post.ep_mp.dom() == pre.ep_mp.dom(),
        forall|t: RwLockThreadPtr, i: EndpointIdx| #![trigger post.thrd_mp.spec_index(t).view().endpoint_descriptors.view().spec_index(i as int)]
            pre.thrd_mp.dom().contains(t) ==>
                post.thrd_mp.spec_index(t).view().endpoint_descriptors.view().spec_index(i as int) == pre.thrd_mp.spec_index(t).view().endpoint_descriptors.view().spec_index(i as int),
        forall|e: RwLockEndpointPtr, t: RwLockThreadPtr, i: EndpointIdx| #![trigger post.ep_mp.spec_index(e).view().owning_threads.view().contains((t, i))]
            pre.ep_mp.dom().contains(e) ==>
                post.ep_mp.spec_index(e).view().owning_threads.view().contains((t, i)) == pre.ep_mp.spec_index(e).view().owning_threads.view().contains((t, i)),
    ensures thread_endpoint_ref_counter_wf(post.thrd_mp, post.ep_mp),
{ reveal(thread_endpoint_ref_counter_wf); }

/// The cpu and emptied-thread relations close after the transition.
proof fn ipc_cpu_rendezvous_eof_cpu_wf(
    pre: KernelK, post: KernelK, current_thrd_ptr: RwLockThreadPtr, peer_thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr,
    peer_sched_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, source_container: RwLockContainerPtr, target_container: RwLockContainerPtr,
    source_cpu_set: RwLockCpuSetPtr, target_cpu_set: RwLockCpuSetPtr, transfer_cpu_id: CpuId, transferred: bool, peer_result: RetValueType,
    thread_id: LockThreadId,
)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, transfer_cpu_id),
        current_thrd_ptr != peer_thrd_ptr,
        source_container != target_container,
        pre.thrd_mp.spec_index(peer_thrd_ptr).view().owning_container != pre.thrd_mp.spec_index(current_thrd_ptr).view().owning_container,
        index_valid(NUM_CPUS, wake_cpu),
        wake_cpu == pre.thrd_mp.spec_index(peer_thrd_ptr).view().last_cpu,
        source_cpu_set != target_cpu_set,
        pre.ctn_mp.dom().contains(source_container),
        pre.ctn_mp.dom().contains(target_container),
        pre.thrd_mp.dom().contains(current_thrd_ptr),
        pre.thrd_mp.dom().contains(peer_thrd_ptr),
        pre.ep_mp.dom().contains(ep_ptr),
        pre.sched_mp.dom().contains(peer_sched_ptr),
        pre.cpu_set_mp.dom().contains(source_cpu_set),
        pre.cpu_set_mp.dom().contains(target_cpu_set),
        !pre.cpu_set_mp.spec_index(source_cpu_set).being_killed() && !pre.cpu_set_mp.spec_index(target_cpu_set).being_killed(),
        pre.ctn_mp.spec_index(source_container).view_rodata().view().cpu_set == source_cpu_set,
        pre.ctn_mp.spec_index(target_container).view_rodata().view().cpu_set == target_cpu_set,
        pre.ctn_mp.spec_index(pre.thrd_mp.spec_index(peer_thrd_ptr).view().owning_container).view_rodata().view().scheduler == peer_sched_ptr,
        pre.thrd_mp.spec_index(peer_thrd_ptr).view().state.is_endpoint_waiting(),
        pre.thrd_mp.spec_index(peer_thrd_ptr).view().blocking_endpoint_ptr == Some(ep_ptr),
        pre.ep_mp.spec_index(ep_ptr).view().queue.view().len() > 0,
        pre.ep_mp.spec_index(ep_ptr).view().queue.view().spec_index(0) == peer_thrd_ptr,
        transferred ==> {
            &&& pre.cpu_set_mp.spec_index(source_cpu_set).view().owned_cpus.view().contains(transfer_cpu_id)
            &&& pre.cpu_set_mp.spec_index(source_cpu_set).view().owned_cpus.closed_view().contains(transfer_cpu_id)
            &&& !pre.cpu_set_mp.spec_index(target_cpu_set).view().owned_cpus.view().contains(transfer_cpu_id)
            &&& pre.cpu_arr.spec_index(transfer_cpu_id).view().view().view().state is Off
            &&& pre.cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container == source_container
        },
        !pre.sched_mp.spec_index(peer_sched_ptr).shards.spec_index(wake_cpu).view().view().queue.dom().contains(pre.thrd_mp.spec_index(peer_thrd_ptr).view().scheduler_linkedlist_node.addr()),
        ipc_cpu_rendezvous_eof_transition_framing(pre, post, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, source_container, target_container, source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id),
        post.subsystems_inv(),
    ensures
        process_emptied_threads_wf(post.prc_mp, post.thrd_mp),
        container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp),
        cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp),
        container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr),
        process_cpu_wf(post.prc_mp, post.cpu_arr),
        thread_cpu_wf(post.thrd_mp, post.cpu_arr),
{
    reveal(ipc_cpu_rendezvous_eof_transition_framing);
    assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
    assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
    assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
    assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); reveal(container_cpu_set_wf); };
    assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); };
    assert(thread_cpu_wf(post.thrd_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_running_thread_eq(pre.thrd_mp, post.thrd_mp, pre.cpu_arr, post.cpu_arr); };
}

/// The endpoint queue, descriptor, reference-counter, and call-link relations close after the transition.
proof fn ipc_cpu_rendezvous_eof_endpoint_wf(
    pre: KernelK, post: KernelK, current_thrd_ptr: RwLockThreadPtr, peer_thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr,
    peer_sched_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, source_container: RwLockContainerPtr, target_container: RwLockContainerPtr,
    source_cpu_set: RwLockCpuSetPtr, target_cpu_set: RwLockCpuSetPtr, transfer_cpu_id: CpuId, transferred: bool, peer_result: RetValueType,
    thread_id: LockThreadId,
)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, transfer_cpu_id),
        current_thrd_ptr != peer_thrd_ptr,
        source_container != target_container,
        pre.thrd_mp.spec_index(peer_thrd_ptr).view().owning_container != pre.thrd_mp.spec_index(current_thrd_ptr).view().owning_container,
        index_valid(NUM_CPUS, wake_cpu),
        wake_cpu == pre.thrd_mp.spec_index(peer_thrd_ptr).view().last_cpu,
        source_cpu_set != target_cpu_set,
        pre.ctn_mp.dom().contains(source_container),
        pre.ctn_mp.dom().contains(target_container),
        pre.thrd_mp.dom().contains(current_thrd_ptr),
        pre.thrd_mp.dom().contains(peer_thrd_ptr),
        pre.ep_mp.dom().contains(ep_ptr),
        pre.sched_mp.dom().contains(peer_sched_ptr),
        pre.cpu_set_mp.dom().contains(source_cpu_set),
        pre.cpu_set_mp.dom().contains(target_cpu_set),
        pre.ctn_mp.spec_index(source_container).view_rodata().view().cpu_set == source_cpu_set,
        pre.ctn_mp.spec_index(target_container).view_rodata().view().cpu_set == target_cpu_set,
        pre.ctn_mp.spec_index(pre.thrd_mp.spec_index(peer_thrd_ptr).view().owning_container).view_rodata().view().scheduler == peer_sched_ptr,
        pre.thrd_mp.spec_index(peer_thrd_ptr).view().state.is_endpoint_waiting(),
        pre.thrd_mp.spec_index(peer_thrd_ptr).view().blocking_endpoint_ptr == Some(ep_ptr),
        pre.ep_mp.spec_index(ep_ptr).view().queue.view().len() > 0,
        pre.ep_mp.spec_index(ep_ptr).view().queue.view().spec_index(0) == peer_thrd_ptr,
        transferred ==> {
            &&& pre.cpu_set_mp.spec_index(source_cpu_set).view().owned_cpus.view().contains(transfer_cpu_id)
            &&& pre.cpu_set_mp.spec_index(source_cpu_set).view().owned_cpus.closed_view().contains(transfer_cpu_id)
            &&& !pre.cpu_set_mp.spec_index(target_cpu_set).view().owned_cpus.view().contains(transfer_cpu_id)
            &&& pre.cpu_arr.spec_index(transfer_cpu_id).view().view().view().state is Off
            &&& pre.cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container == source_container
        },
        !pre.sched_mp.spec_index(peer_sched_ptr).shards.spec_index(wake_cpu).view().view().queue.dom().contains(pre.thrd_mp.spec_index(peer_thrd_ptr).view().scheduler_linkedlist_node.addr()),
        ipc_cpu_rendezvous_eof_transition_framing(pre, post, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, source_container, target_container, source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id),
        post.subsystems_inv(),
    ensures
        thread_endpoint_ref_counter_wf(post.thrd_mp, post.ep_mp),
        container_endpoint_wf(post.ctn_mp, post.ep_mp),
        thread_caller_callee_wf(post.thrd_mp),
        thread_endpoint_queue_wf(post.thrd_mp, post.ep_mp),
        container_thread_endpoint_wf(post.ctn_mp, post.thrd_mp, post.ep_mp),
{
    reveal(ipc_cpu_rendezvous_eof_transition_framing);
    ipc_cpu_rendezvous_eof_thread_endpoint_ref_counter(pre, post);
    assert({
        &&& container_endpoint_wf(post.ctn_mp, post.ep_mp)
        &&& thread_caller_callee_wf(post.thrd_mp)
    }) by { container_endpoint_wf_preserved_for_endpoint_owner_eq(pre.ctn_mp, post.ctn_mp, pre.ep_mp, post.ep_mp); thread_caller_callee_wf_preserved_for_call_link_eq(pre.thrd_mp, post.thrd_mp); };
    assert(thread_endpoint_queue_wf(post.thrd_mp, post.ep_mp)) by { seq_skip_one_implies_contains_and_index_shift::<RwLockThreadPtr>(); reveal(endpoint_perms_wf); reveal(LinkedList::wf_value_list); reveal(LinkedList::value_list_unique); reveal(thread_endpoint_queue_wf); };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thrd_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(pre.ctn_mp, post.ctn_mp, pre.thrd_mp, post.thrd_mp, pre.ep_mp, post.ep_mp); };
}

proof fn ipc_cpu_rendezvous_eof_process_management_inv(
    pre: KernelK, post: KernelK, current_thrd_ptr: RwLockThreadPtr, peer_thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr,
    peer_sched_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, source_container: RwLockContainerPtr, target_container: RwLockContainerPtr,
    source_cpu_set: RwLockCpuSetPtr, target_cpu_set: RwLockCpuSetPtr, transfer_cpu_id: CpuId, transferred: bool, peer_result: RetValueType,
    thread_id: LockThreadId,
)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, transfer_cpu_id),
        current_thrd_ptr != peer_thrd_ptr,
        source_container != target_container,
        pre.thrd_mp.spec_index(peer_thrd_ptr).view().owning_container != pre.thrd_mp.spec_index(current_thrd_ptr).view().owning_container,
        index_valid(NUM_CPUS, wake_cpu),
        wake_cpu == pre.thrd_mp.spec_index(peer_thrd_ptr).view().last_cpu,
        source_cpu_set != target_cpu_set,
        pre.ctn_mp.dom().contains(source_container),
        pre.ctn_mp.dom().contains(target_container),
        pre.thrd_mp.dom().contains(current_thrd_ptr),
        pre.thrd_mp.dom().contains(peer_thrd_ptr),
        pre.ep_mp.dom().contains(ep_ptr),
        pre.sched_mp.dom().contains(peer_sched_ptr),
        pre.cpu_set_mp.dom().contains(source_cpu_set),
        pre.cpu_set_mp.dom().contains(target_cpu_set),
        !pre.cpu_set_mp.spec_index(source_cpu_set).being_killed() && !pre.cpu_set_mp.spec_index(target_cpu_set).being_killed(),
        pre.ctn_mp.spec_index(source_container).view_rodata().view().cpu_set == source_cpu_set,
        pre.ctn_mp.spec_index(target_container).view_rodata().view().cpu_set == target_cpu_set,
        pre.ctn_mp.spec_index(pre.thrd_mp.spec_index(peer_thrd_ptr).view().owning_container).view_rodata().view().scheduler == peer_sched_ptr,
        pre.thrd_mp.spec_index(peer_thrd_ptr).view().state.is_endpoint_waiting(),
        pre.thrd_mp.spec_index(peer_thrd_ptr).view().blocking_endpoint_ptr == Some(ep_ptr),
        pre.ep_mp.spec_index(ep_ptr).view().queue.view().len() > 0,
        pre.ep_mp.spec_index(ep_ptr).view().queue.view().spec_index(0) == peer_thrd_ptr,
        transferred ==> {
            &&& pre.cpu_set_mp.spec_index(source_cpu_set).view().owned_cpus.view().contains(transfer_cpu_id)
            &&& pre.cpu_set_mp.spec_index(source_cpu_set).view().owned_cpus.closed_view().contains(transfer_cpu_id)
            &&& !pre.cpu_set_mp.spec_index(target_cpu_set).view().owned_cpus.view().contains(transfer_cpu_id)
            &&& pre.cpu_arr.spec_index(transfer_cpu_id).view().view().view().state is Off
            &&& pre.cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container == source_container
        },
        !pre.sched_mp.spec_index(peer_sched_ptr).shards.spec_index(wake_cpu).view().view().queue.dom().contains(pre.thrd_mp.spec_index(peer_thrd_ptr).view().scheduler_linkedlist_node.addr()),
        ipc_cpu_rendezvous_eof_transition_framing(pre, post, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, source_container, target_container, source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(ipc_cpu_rendezvous_eof_transition_framing);
    ipc_cpu_rendezvous_eof_cpu_wf(pre, post, current_thrd_ptr, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, source_container, target_container, source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id);
    ipc_cpu_rendezvous_eof_endpoint_wf(pre, post, current_thrd_ptr, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, source_container, target_container, source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id);
    assert(post.process_management_inv()) by {
        assert(thread_dangling_chain_end_wf(post.thrd_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thrd_mp, post.thrd_mp); };
        assert({
            &&& container_scheduler_wf(post.ctn_mp, post.sched_mp)
            &&& container_thread_wf(post.ctn_mp, post.thrd_mp)
            &&& process_thread_wf(post.prc_mp, post.thrd_mp)
        }) by { reveal(container_scheduler_wf); reveal(container_thread_wf); reveal(process_thread_wf); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thrd_mp, post.sched_mp)) by {
            seq_push_implies_contains::<RwLockThreadPtr>();
            reveal(scheduler_perms_wf); reveal(LinkedList::wf_map); reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
        };
    };
}

proof fn ipc_cpu_rendezvous_eof_memory_management_inv(
    pre: KernelK, post: KernelK, current_thrd_ptr: RwLockThreadPtr, peer_thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr,
    peer_sched_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, source_container: RwLockContainerPtr, target_container: RwLockContainerPtr,
    source_cpu_set: RwLockCpuSetPtr, target_cpu_set: RwLockCpuSetPtr, transfer_cpu_id: CpuId, transferred: bool, peer_result: RetValueType,
    thread_id: LockThreadId,
)
    requires
        pre.inv(),
        ipc_cpu_rendezvous_eof_transition_framing(pre, post, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, source_container, target_container, source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id),
        post.subsystems_inv(),
    ensures post.memory_management_inv(),
{
    hide(Seq::contains);
    reveal(ipc_cpu_rendezvous_eof_transition_framing);
    assert(post.memory_management_inv()) by {
        assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
        assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
        assert(page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr)) by { reveal(page_object_owner_wf); reveal(container_owned_pages_wf); };
        assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_staged_4k_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_staged_4k_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_staged_2m_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_staged_2m_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_staged_1g_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_staged_1g_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
        assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp)) by {
            container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_4k_mp); reveal(container_thread_wf);
            lemma_thread_effective_quota_4k_fold_sum_eq_forall();
            lemma_thread_pending_4k_folds_eq_forall(post.ctn_mp, pre.thrd_mp, post.thrd_mp);
        };
        assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_2m_mp)) by {
            container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_2m_mp); reveal(container_thread_wf);
            lemma_thread_effective_quota_2m_fold_sum_eq_forall();
            lemma_thread_pending_2m_folds_eq_forall(post.ctn_mp, pre.thrd_mp, post.thrd_mp);
        };
        assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_1g_mp)) by {
            reveal(container_process_allocator_quota_1g_wf); reveal(container_thread_wf);
            lemma_thread_effective_quota_1g_fold_sum_eq_forall();
            lemma_thread_pending_1g_folds_eq_forall(post.ctn_mp, pre.thrd_mp, post.thrd_mp);
        };
    };
}

/// The rendezvous fields of the step and the scheduler-shard push close after the transition.
proof fn ipc_cpu_rendezvous_eof_rendezvous_fields(
    pre: KernelK, post: KernelK, current_thrd_ptr: RwLockThreadPtr, peer_thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr,
    peer_sched_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, source_container: RwLockContainerPtr, target_container: RwLockContainerPtr,
    source_cpu_set: RwLockCpuSetPtr, target_cpu_set: RwLockCpuSetPtr, transfer_cpu_id: CpuId, transferred: bool, peer_result: RetValueType,
    thread_id: LockThreadId, snapshot: KernelK, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, ep_idx: EndpointIdx, waiting_state: ThreadState,
    cpu_transfer: Option<(CpuId, RwLockThreadPtr)>,
)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, transfer_cpu_id),
        current_thrd_ptr != peer_thrd_ptr,
        source_container != target_container,
        pre.thrd_mp.spec_index(peer_thrd_ptr).view().owning_container != pre.thrd_mp.spec_index(current_thrd_ptr).view().owning_container,
        index_valid(NUM_CPUS, wake_cpu),
        wake_cpu == pre.thrd_mp.spec_index(peer_thrd_ptr).view().last_cpu,
        source_cpu_set != target_cpu_set,
        pre.ctn_mp.dom().contains(source_container),
        pre.ctn_mp.dom().contains(target_container),
        pre.thrd_mp.dom().contains(current_thrd_ptr),
        pre.thrd_mp.dom().contains(peer_thrd_ptr),
        pre.ep_mp.dom().contains(ep_ptr),
        pre.sched_mp.dom().contains(peer_sched_ptr),
        pre.cpu_set_mp.dom().contains(source_cpu_set),
        pre.cpu_set_mp.dom().contains(target_cpu_set),
        !pre.cpu_set_mp.spec_index(source_cpu_set).being_killed() && !pre.cpu_set_mp.spec_index(target_cpu_set).being_killed(),
        pre.ctn_mp.spec_index(source_container).view_rodata().view().cpu_set == source_cpu_set,
        pre.ctn_mp.spec_index(target_container).view_rodata().view().cpu_set == target_cpu_set,
        pre.ctn_mp.spec_index(pre.thrd_mp.spec_index(peer_thrd_ptr).view().owning_container).view_rodata().view().scheduler == peer_sched_ptr,
        pre.thrd_mp.spec_index(peer_thrd_ptr).view().state.is_endpoint_waiting(),
        pre.thrd_mp.spec_index(peer_thrd_ptr).view().blocking_endpoint_ptr == Some(ep_ptr),
        pre.ep_mp.spec_index(ep_ptr).view().queue.view().len() > 0,
        pre.ep_mp.spec_index(ep_ptr).view().queue.view().spec_index(0) == peer_thrd_ptr,
        transferred ==> {
            &&& pre.cpu_set_mp.spec_index(source_cpu_set).view().owned_cpus.view().contains(transfer_cpu_id)
            &&& pre.cpu_set_mp.spec_index(source_cpu_set).view().owned_cpus.closed_view().contains(transfer_cpu_id)
            &&& !pre.cpu_set_mp.spec_index(target_cpu_set).view().owned_cpus.view().contains(transfer_cpu_id)
            &&& pre.cpu_arr.spec_index(transfer_cpu_id).view().view().view().state is Off
            &&& pre.cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container == source_container
        },
        !pre.sched_mp.spec_index(peer_sched_ptr).shards.spec_index(wake_cpu).view().view().queue.dom().contains(pre.thrd_mp.spec_index(peer_thrd_ptr).view().scheduler_linkedlist_node.addr()),
        ipc_cpu_rendezvous_eof_transition_framing(pre, post, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, source_container, target_container, source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id),
        post.sched_mp.spec_index(peer_sched_ptr).shards.inv(),
        post.sched_mp.spec_index(peer_sched_ptr).shard(wake_cpu).queue.wf(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&snapshot, &pre),
        kernel_endpoint_nonlock_fields_unchanged(snapshot.ep_mp, pre.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&snapshot, &pre),
        pre.irt.view().owners() == snapshot.irt.view().owners(),
        pre.irt.view().iommu_roots() == snapshot.irt.view().iommu_roots(),
        pre.cpu_tlb.view() == snapshot.cpu_tlb.view(),
        pre.cpu_tlb.structure_caches.view() == snapshot.cpu_tlb.structure_caches.view(),
        pre.iommu_tlb.view() == snapshot.iommu_tlb.view(),
        snapshot.cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        snapshot.thrd_mp.dom().contains(current_thrd_ptr) ==> snapshot.thrd_mp.spec_index(current_thrd_ptr).locking_thread() is None,
        snapshot.ep_mp.dom().contains(ep_ptr) ==> snapshot.ep_mp.spec_index(ep_ptr).locking_thread() is None,
        snapshot.thrd_mp.dom().contains(peer_thrd_ptr) ==> snapshot.thrd_mp.spec_index(peer_thrd_ptr).locking_thread() is None,
        transferred ==> snapshot.cpu_arr.spec_index(transfer_cpu_id).value.locking_thread() is None,
        pre.thrd_mp.spec_index(current_thrd_ptr).view().syscall_progress.view() is None,
        index_valid(NUM_CPUS, cpu_id),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thrd_ptr),
        pre.prc_mp.dom().contains(prc_ptr),
        pre.thrd_mp.spec_index(current_thrd_ptr).being_killed() == false,
        pre.thrd_mp.spec_index(current_thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thrd_mp.spec_index(current_thrd_ptr).view().owning_proc == prc_ptr,
        pre.thrd_mp.spec_index(peer_thrd_ptr).being_killed() == false,
        pre.ctn_mp.dom().contains(pre.thrd_mp.spec_index(current_thrd_ptr).view().owning_container),
        pre.ctn_mp.dom().contains(pre.thrd_mp.spec_index(peer_thrd_ptr).view().owning_container),
        edp_idx_valid(ep_idx),
        pre.thrd_mp.spec_index(current_thrd_ptr).view().endpoint_descriptors.view()[ep_idx as int] == Some(ep_ptr),
        waiting_state is SENDING || waiting_state is RECEIVING,
        (pre.ep_mp.spec_index(ep_ptr).view().queue_state is SEND) != (waiting_state is SENDING),
        (cpu_transfer is Some) == transferred,
        cpu_transfer is Some ==> {
            &&& cpu_transfer.unwrap().0 == transfer_cpu_id
            &&& pre.thrd_mp.dom().contains(cpu_transfer.unwrap().1)
            &&& pre.thrd_mp.spec_index(cpu_transfer.unwrap().1).view().owning_container == target_container
        },
    ensures kernel_ipc_rendezvous_fields(&snapshot, &post, cpu_id, current_thrd_ptr, ep_ptr, ep_idx, waiting_state, peer_thrd_ptr, peer_result, cpu_transfer, None),
{
    reveal(ipc_cpu_rendezvous_eof_transition_framing);
    assert(scheduler_shards_of(post.sched_mp.spec_index(peer_sched_ptr)) =~= scheduler_shards_of(pre.sched_mp.spec_index(peer_sched_ptr)).update(wake_cpu as int, scheduler_shards_of(pre.sched_mp.spec_index(peer_sched_ptr))[wake_cpu as int].push(peer_thrd_ptr))) by {
        reveal(scheduler_shards_of);
    };
    assert(kernel_ipc_rendezvous_fields(&snapshot, &post, cpu_id, current_thrd_ptr, ep_ptr, ep_idx, waiting_state, peer_thrd_ptr, peer_result, cpu_transfer, None)) by {
        running_thread_not_in_endpoint_queue(&pre, ep_ptr, current_thrd_ptr);
        reveal(kernel_ipc_rendezvous_fields); reveal(container_scheduler_wf);
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
        reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
        reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged);
    };
}

pub(super) proof fn ipc_cpu_rendezvous_eof(
    pre: KernelK, post: KernelK, current_thrd_ptr: RwLockThreadPtr, peer_thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr,
    peer_sched_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, source_container: RwLockContainerPtr, target_container: RwLockContainerPtr,
    source_cpu_set: RwLockCpuSetPtr, target_cpu_set: RwLockCpuSetPtr, transfer_cpu_id: CpuId, transferred: bool, peer_result: RetValueType,
    thread_id: LockThreadId, snapshot: KernelK, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, ep_idx: EndpointIdx, waiting_state: ThreadState,
    cpu_transfer: Option<(CpuId, RwLockThreadPtr)>,
)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, transfer_cpu_id),
        current_thrd_ptr != peer_thrd_ptr,
        source_container != target_container,
        pre.thrd_mp.spec_index(peer_thrd_ptr).view().owning_container != pre.thrd_mp.spec_index(current_thrd_ptr).view().owning_container,
        index_valid(NUM_CPUS, wake_cpu),
        wake_cpu == pre.thrd_mp.spec_index(peer_thrd_ptr).view().last_cpu,
        source_cpu_set != target_cpu_set,
        pre.ctn_mp.dom().contains(source_container),
        pre.ctn_mp.dom().contains(target_container),
        pre.thrd_mp.dom().contains(current_thrd_ptr),
        pre.thrd_mp.dom().contains(peer_thrd_ptr),
        pre.ep_mp.dom().contains(ep_ptr),
        pre.sched_mp.dom().contains(peer_sched_ptr),
        pre.cpu_set_mp.dom().contains(source_cpu_set),
        pre.cpu_set_mp.dom().contains(target_cpu_set),
        !pre.cpu_set_mp.spec_index(source_cpu_set).being_killed() && !pre.cpu_set_mp.spec_index(target_cpu_set).being_killed(),
        pre.ctn_mp.spec_index(source_container).view_rodata().view().cpu_set == source_cpu_set,
        pre.ctn_mp.spec_index(target_container).view_rodata().view().cpu_set == target_cpu_set,
        pre.ctn_mp.spec_index(pre.thrd_mp.spec_index(peer_thrd_ptr).view().owning_container).view_rodata().view().scheduler == peer_sched_ptr,
        pre.thrd_mp.spec_index(peer_thrd_ptr).view().state.is_endpoint_waiting(),
        pre.thrd_mp.spec_index(peer_thrd_ptr).view().blocking_endpoint_ptr == Some(ep_ptr),
        pre.ep_mp.spec_index(ep_ptr).view().queue.view().len() > 0,
        pre.ep_mp.spec_index(ep_ptr).view().queue.view().spec_index(0) == peer_thrd_ptr,
        transferred ==> {
            &&& pre.cpu_set_mp.spec_index(source_cpu_set).view().owned_cpus.view().contains(transfer_cpu_id)
            &&& pre.cpu_set_mp.spec_index(source_cpu_set).view().owned_cpus.closed_view().contains(transfer_cpu_id)
            &&& !pre.cpu_set_mp.spec_index(target_cpu_set).view().owned_cpus.view().contains(transfer_cpu_id)
            &&& pre.cpu_arr.spec_index(transfer_cpu_id).view().view().view().state is Off
            &&& pre.cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container == source_container
        },
        !pre.sched_mp.spec_index(peer_sched_ptr).shards.spec_index(wake_cpu).view().view().queue.dom().contains(pre.thrd_mp.spec_index(peer_thrd_ptr).view().scheduler_linkedlist_node.addr()),
        ipc_cpu_rendezvous_eof_transition_framing(pre, post, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, source_container, target_container, source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id),
        post.cpu_arr.inv(),
        post.cpu_set_mp.perms_wf(),
        post.cpu_set_mp.spec_index(source_cpu_set).view().owned_cpus.wf(),
        post.cpu_set_mp.spec_index(target_cpu_set).view().owned_cpus.wf(),
        post.ep_mp.spec_index(ep_ptr).view().queue.wf(),
        post.sched_mp.perms_wf(),
        post.sched_mp.spec_index(peer_sched_ptr).shards.inv(),
        post.sched_mp.spec_index(peer_sched_ptr).shard(wake_cpu).queue.wf(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&snapshot, &pre),
        kernel_endpoint_nonlock_fields_unchanged(snapshot.ep_mp, pre.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&snapshot, &pre),
        pre.irt.view().owners() == snapshot.irt.view().owners(),
        pre.irt.view().iommu_roots() == snapshot.irt.view().iommu_roots(),
        pre.cpu_tlb.view() == snapshot.cpu_tlb.view(),
        pre.cpu_tlb.structure_caches.view() == snapshot.cpu_tlb.structure_caches.view(),
        pre.iommu_tlb.view() == snapshot.iommu_tlb.view(),
        snapshot.cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        snapshot.thrd_mp.dom().contains(current_thrd_ptr) ==> snapshot.thrd_mp.spec_index(current_thrd_ptr).locking_thread() is None,
        snapshot.ep_mp.dom().contains(ep_ptr) ==> snapshot.ep_mp.spec_index(ep_ptr).locking_thread() is None,
        snapshot.thrd_mp.dom().contains(peer_thrd_ptr) ==> snapshot.thrd_mp.spec_index(peer_thrd_ptr).locking_thread() is None,
        transferred ==> snapshot.cpu_arr.spec_index(transfer_cpu_id).value.locking_thread() is None,
        pre.thrd_mp.spec_index(current_thrd_ptr).view().syscall_progress.view() is None,
        index_valid(NUM_CPUS, cpu_id),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thrd_ptr),
        pre.prc_mp.dom().contains(prc_ptr),
        pre.thrd_mp.spec_index(current_thrd_ptr).being_killed() == false,
        pre.thrd_mp.spec_index(current_thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thrd_mp.spec_index(current_thrd_ptr).view().owning_proc == prc_ptr,
        pre.thrd_mp.spec_index(peer_thrd_ptr).being_killed() == false,
        pre.ctn_mp.dom().contains(pre.thrd_mp.spec_index(current_thrd_ptr).view().owning_container),
        pre.ctn_mp.dom().contains(pre.thrd_mp.spec_index(peer_thrd_ptr).view().owning_container),
        edp_idx_valid(ep_idx),
        pre.thrd_mp.spec_index(current_thrd_ptr).view().endpoint_descriptors.view()[ep_idx as int] == Some(ep_ptr),
        waiting_state is SENDING || waiting_state is RECEIVING,
        (pre.ep_mp.spec_index(ep_ptr).view().queue_state is SEND) != (waiting_state is SENDING),
        (cpu_transfer is Some) == transferred,
        cpu_transfer is Some ==> {
            &&& cpu_transfer.unwrap().0 == transfer_cpu_id
            &&& pre.thrd_mp.dom().contains(cpu_transfer.unwrap().1)
            &&& pre.thrd_mp.spec_index(cpu_transfer.unwrap().1).view().owning_container == target_container
        },
    ensures
        post.inv(),
        forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
            pre.ep_mp.dom().contains(p) ==> post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread(),
        forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) && (!transferred || i != transfer_cpu_id) ==> post.cpu_arr.spec_index(i) == pre.cpu_arr.spec_index(i),
        kernel_ipc_rendezvous_fields(&snapshot, &post, cpu_id, current_thrd_ptr, ep_ptr, ep_idx, waiting_state, peer_thrd_ptr, peer_result, cpu_transfer, None),
{
    reveal(ipc_cpu_rendezvous_eof_transition_framing);
    assert(post.subsystems_inv()) by {
        assert({
            &&& thread_perms_wf(post.thrd_mp)
            &&& endpoint_perms_wf(post.ep_mp)
            &&& scheduler_perms_wf(post.sched_mp)
        }) by {
            reveal(thread_perms_wf); reveal(endpoint_perms_wf); reveal(scheduler_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked);
            reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
        };
        reveal(cpu_set_perms_wf); reveal(cpu_array_wf); reveal(cpu_hw_cr3_pcid_wf); reveal(cpu_offline_flags_wf); reveal(cpu_op_wf); reveal(KernelK::default_pagetable_wf);
    };
    ipc_cpu_rendezvous_eof_memory_management_inv(pre, post, current_thrd_ptr, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, source_container, target_container, source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id);
    ipc_cpu_rendezvous_eof_process_management_inv(pre, post, current_thrd_ptr, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, source_container, target_container, source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id);
    assert(post.inv()) by {
        reveal(cpu_dirty_map_process_in_cpu_container); reveal(cpu_dirty_map_covers_nonempty_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_pagetable_pcid_match);
        reveal(cpu_tlb_wf); reveal(structure_cache_wf);
    };
    ipc_cpu_rendezvous_eof_rendezvous_fields(pre, post, current_thrd_ptr, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, source_container, target_container, source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result,
        thread_id, snapshot, cpu_id, prc_ptr, ep_idx, waiting_state, cpu_transfer);
}
}
