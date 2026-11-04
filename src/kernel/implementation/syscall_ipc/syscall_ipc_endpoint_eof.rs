use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_endpoint_spec::{ipc_begin_transit_eof_transition_framing, ipc_copy_endpoint_reference_eof_transition_framing, ipc_finish_transit_eof_transition_framing};

verus! {
/// The receiver's descriptor slot bound to the payload endpoint and the payload endpoint's new owning entry keep the
/// thread-endpoint reference relation.
proof fn ipc_copy_endpoint_reference_eof_thread_endpoint_ref_counter(
    pre: KernelK, post: KernelK, receiver_thrd_ptr: RwLockThreadPtr, target_ep_idx: EndpointIdx, payload_ep_ptr: RwLockEndpointPtr,
)
    requires
        thread_endpoint_ref_counter_wf(pre.thrd_mp, pre.ep_mp),
        ipc_copy_endpoint_reference_eof_transition_framing(pre, post, receiver_thrd_ptr, target_ep_idx, payload_ep_ptr),
        edp_idx_valid(target_ep_idx),
        pre.thrd_mp.dom().contains(receiver_thrd_ptr),
        pre.thrd_mp.spec_index(receiver_thrd_ptr).view().endpoint_descriptors.spec_index(target_ep_idx) is None,
        pre.ep_mp.dom().contains(payload_ep_ptr),
    ensures thread_endpoint_ref_counter_wf(post.thrd_mp, post.ep_mp),
{
    reveal(ipc_copy_endpoint_reference_eof_transition_framing);
    assert(thread_endpoint_ref_counter_wf(post.thrd_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); };
}

/// The thread and endpoint subsystem invariants close after the receiver's descriptor slot is bound to the payload endpoint.
proof fn ipc_copy_endpoint_reference_eof_subsystems(
    pre: KernelK, post: KernelK, receiver_thrd_ptr: RwLockThreadPtr, target_ep_idx: EndpointIdx, payload_ep_ptr: RwLockEndpointPtr,
)
    requires
        pre.inv(),
        edp_idx_valid(target_ep_idx),
        pre.thrd_mp.dom().contains(receiver_thrd_ptr),
        pre.thrd_mp.spec_index(receiver_thrd_ptr).view().endpoint_descriptors.spec_index(target_ep_idx) is None,
        !(pre.thrd_mp.spec_index(receiver_thrd_ptr).view().state is DANGLING),
        pre.ep_mp.dom().contains(payload_ep_ptr),
        ipc_copy_endpoint_reference_eof_transition_framing(pre, post, receiver_thrd_ptr, target_ep_idx, payload_ep_ptr),
        post.thrd_mp.perms_wf(),
        post.ep_mp.perms_wf(),
    ensures post.subsystems_inv(),
{
    reveal(ipc_copy_endpoint_reference_eof_transition_framing);
    thread_endpoint_ref_counter_wf_endpoint_at(pre.thrd_mp, pre.ep_mp, payload_ep_ptr, receiver_thrd_ptr, target_ep_idx);
    assert(thread_perms_wf(post.thrd_mp)) by {
        reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
        reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
    };
    assert(endpoint_perms_wf(post.ep_mp)) by { reveal(endpoint_perms_wf); };
    reveal(KernelK::default_pagetable_wf);
}

/// Closes every kernel invariant after the receiver's descriptor slot is bound to the payload endpoint.
pub(super) proof fn ipc_copy_endpoint_reference_eof(
    pre: KernelK, post: KernelK, receiver_thrd_ptr: RwLockThreadPtr, target_ep_idx: EndpointIdx, payload_ep_ptr: RwLockEndpointPtr,
)
    requires
        pre.inv(),
        edp_idx_valid(target_ep_idx),
        pre.thrd_mp.dom().contains(receiver_thrd_ptr),
        pre.thrd_mp.spec_index(receiver_thrd_ptr).view().endpoint_descriptors.spec_index(target_ep_idx) is None,
        !(pre.thrd_mp.spec_index(receiver_thrd_ptr).view().state is DANGLING),
        pre.ep_mp.dom().contains(payload_ep_ptr),
        {
            let endpoint_owner = pre.ep_mp.spec_index(payload_ep_ptr).view().owning_container;
            &&& pre.ctn_mp.dom().contains(endpoint_owner)
            &&& {
                let receiver_container = pre.thrd_mp.spec_index(receiver_thrd_ptr).view().owning_container;
                ||| endpoint_owner == receiver_container
                ||| pre.ctn_mp.spec_index(endpoint_owner).view_ghost().subtree_set.view().contains(receiver_container)
            }
        },
        ipc_copy_endpoint_reference_eof_transition_framing(pre, post, receiver_thrd_ptr, target_ep_idx, payload_ep_ptr),
        post.thrd_mp.perms_wf(),
        post.ep_mp.perms_wf(),
    ensures post.inv(),
{
    reveal(ipc_copy_endpoint_reference_eof_transition_framing);
    thread_endpoint_ref_counter_wf_endpoint_at(pre.thrd_mp, pre.ep_mp, payload_ep_ptr, receiver_thrd_ptr, target_ep_idx);
    ipc_copy_endpoint_reference_eof_subsystems(pre, post, receiver_thrd_ptr, target_ep_idx, payload_ep_ptr);
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_endpoint_memory_fields(pre, post); };
    assert(post.process_management_inv()) by {
        assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
        assert(thread_caller_callee_wf(post.thrd_mp)) by { thread_caller_callee_wf_preserved_for_call_link_eq(pre.thrd_mp, post.thrd_mp); };
        assert(thread_dangling_chain_end_wf(post.thrd_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thrd_mp, post.thrd_mp); };
        assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { container_endpoint_wf_preserved_for_endpoint_owner_eq(pre.ctn_mp, post.ctn_mp, pre.ep_mp, post.ep_mp); };
        ipc_copy_endpoint_reference_eof_thread_endpoint_ref_counter(pre, post, receiver_thrd_ptr, target_ep_idx, payload_ep_ptr);
        assert(thread_endpoint_queue_wf(post.thrd_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_queue_fields(pre.thrd_mp, post.thrd_mp, pre.ep_mp, post.ep_mp); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thrd_mp, post.ep_mp)) by { reveal(container_thread_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(container_endpoint_wf); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thrd_mp, post.sched_mp)) by { container_thread_scheduler_wf_preserved_for_scheduled_thread_eq(pre.ctn_mp, post.ctn_mp, pre.thrd_mp, post.thrd_mp, post.sched_mp); };
        assert(container_thread_wf(post.ctn_mp, post.thrd_mp)) by { container_thread_wf_preserved_for_container_thread_link_eq(pre.ctn_mp, post.ctn_mp, pre.thrd_mp, post.thrd_mp); };
        assert(process_thread_wf(post.prc_mp, post.thrd_mp)) by { process_thread_wf_preserved_for_process_thread_link_eq(pre.prc_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp); };
        assert(thread_cpu_wf(post.thrd_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_running_thread_eq(pre.thrd_mp, post.thrd_mp, pre.cpu_arr, post.cpu_arr); };
    };
}

/// Closes every kernel invariant after the channel's head waiter is dequeued into transit.
pub(super) proof fn ipc_begin_transit_eof(
    pre: KernelK, post: KernelK, current_thrd_ptr: RwLockThreadPtr, peer_thrd_ptr: RwLockThreadPtr, channel_ep_ptr: RwLockEndpointPtr,
)
    requires
        pre.inv(),
        current_thrd_ptr != peer_thrd_ptr,
        pre.thrd_mp.dom().contains(current_thrd_ptr),
        pre.thrd_mp.dom().contains(peer_thrd_ptr),
        pre.thrd_mp.spec_index(peer_thrd_ptr).view().state is SENDING || pre.thrd_mp.spec_index(peer_thrd_ptr).view().state is RECEIVING,
        pre.thrd_mp.spec_index(peer_thrd_ptr).view().blocking_endpoint_ptr == Some(channel_ep_ptr),
        pre.ep_mp.dom().contains(channel_ep_ptr),
        pre.ep_mp.spec_index(channel_ep_ptr).view().queue.len() != 0,
        pre.ep_mp.spec_index(channel_ep_ptr).view().queue.view().spec_index(0) == peer_thrd_ptr,
        ipc_begin_transit_eof_transition_framing(pre, post, current_thrd_ptr, peer_thrd_ptr, channel_ep_ptr),
        thread_perms_wf(post.thrd_mp),
        endpoint_perms_wf(post.ep_mp),
    ensures post.inv(),
{
    reveal(ipc_begin_transit_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_endpoint_memory_fields(pre, post); };
    assert(post.process_management_inv()) by {
        assert(thread_dangling_chain_end_wf(post.thrd_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thrd_mp, post.thrd_mp); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
        assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { container_endpoint_wf_preserved_for_endpoint_owner_eq(pre.ctn_mp, post.ctn_mp, pre.ep_mp, post.ep_mp); };
        assert(thread_endpoint_ref_counter_wf(post.thrd_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_descriptor_eq(pre.thrd_mp, post.thrd_mp, pre.ep_mp, post.ep_mp); };
        assert(thread_caller_callee_wf(post.thrd_mp)) by { thread_caller_callee_wf_preserved_for_call_link_eq(pre.thrd_mp, post.thrd_mp); };
        assert(container_thread_wf(post.ctn_mp, post.thrd_mp)) by { container_thread_wf_preserved_for_container_thread_link_eq(pre.ctn_mp, post.ctn_mp, pre.thrd_mp, post.thrd_mp); };
        assert(process_thread_wf(post.prc_mp, post.thrd_mp)) by { process_thread_wf_preserved_for_process_thread_link_eq(pre.prc_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp); };
        assert(thread_cpu_wf(post.thrd_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_running_thread_eq(pre.thrd_mp, post.thrd_mp, pre.cpu_arr, post.cpu_arr); };
        assert(thread_endpoint_queue_wf(post.thrd_mp, post.ep_mp)) by { reveal(LinkedList::wf_map); reveal(thread_endpoint_queue_wf); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thrd_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thrd_mp, post.sched_mp)) by { reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); };
    };
}

/// Closes every kernel invariant after the transit peer is scheduled, from the summary and the
/// thread and scheduler representation facts.
pub(super) proof fn ipc_finish_transit_eof(
    pre: KernelK, post: KernelK, current_thrd_ptr: RwLockThreadPtr, peer_thrd_ptr: RwLockThreadPtr, peer_sched_ptr: RwLockSchedulerPtr,
    wake_cpu: CpuId, peer_result: RetValueType,
)
    requires
        pre.inv(),
        current_thrd_ptr != peer_thrd_ptr,
        index_valid(NUM_CPUS, wake_cpu),
        pre.thrd_mp.dom().contains(current_thrd_ptr),
        pre.thrd_mp.dom().contains(peer_thrd_ptr),
        pre.thrd_mp.spec_index(peer_thrd_ptr).view().state is IPC_TRANSIT,
        pre.sched_mp.dom().contains(peer_sched_ptr),
        pre.ctn_mp.dom().contains(pre.thrd_mp.spec_index(peer_thrd_ptr).view().owning_container),
        pre.ctn_mp.spec_index(pre.thrd_mp.spec_index(peer_thrd_ptr).view().owning_container).view_rodata().view().scheduler == peer_sched_ptr,
        pre.sched_mp.spec_index(peer_sched_ptr).owning_container == pre.thrd_mp.spec_index(peer_thrd_ptr).view().owning_container,
        !pre.sched_mp.spec_index(peer_sched_ptr).shard(wake_cpu).queue.view().contains(peer_thrd_ptr),
        ipc_finish_transit_eof_transition_framing(pre, post, current_thrd_ptr, peer_thrd_ptr, peer_sched_ptr, wake_cpu, peer_result),
        thread_perms_wf(post.thrd_mp),
        scheduler_perms_wf(post.sched_mp),
    ensures post.inv(),
{
    reveal(ipc_finish_transit_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_endpoint_memory_fields(pre, post); };
    assert(post.process_management_inv()) by {
        assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
        assert(thread_endpoint_ref_counter_wf(post.thrd_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_descriptor_eq(pre.thrd_mp, post.thrd_mp, pre.ep_mp, post.ep_mp); };
        assert(thread_caller_callee_wf(post.thrd_mp)) by { thread_caller_callee_wf_preserved_for_call_link_eq(pre.thrd_mp, post.thrd_mp); };
        assert(thread_dangling_chain_end_wf(post.thrd_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thrd_mp, post.thrd_mp); };
        assert(thread_endpoint_queue_wf(post.thrd_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_endpoint_waiting_eq(pre.thrd_mp, post.thrd_mp, post.ep_mp); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thrd_mp, post.ep_mp)) by {
            container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(pre.ctn_mp, post.ctn_mp, pre.thrd_mp, post.thrd_mp, pre.ep_mp, post.ep_mp);
        };
        assert({
            &&& container_scheduler_wf(post.ctn_mp, post.sched_mp)
            &&& container_thread_wf(post.ctn_mp, post.thrd_mp)
            &&& process_thread_wf(post.prc_mp, post.thrd_mp)
            &&& thread_cpu_wf(post.thrd_mp, post.cpu_arr)
        }) by { reveal(container_scheduler_wf); reveal(container_thread_wf); reveal(process_thread_wf); reveal(thread_cpu_wf); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thrd_mp, post.sched_mp)) by {
            seq_push_implies_contains::<RwLockThreadPtr>();
            reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); reveal(LinkedList::wf_value_list); reveal(LinkedList::wf_map);
        };
    };
}
} // verus!
