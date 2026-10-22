use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_endpoint_spec::{ipc_begin_endpoint_transfer_eof_transition_framing, ipc_copy_endpoint_reference_eof_transition_framing, ipc_finish_endpoint_transit_eof_transition_framing};

verus! {
/// Closes every kernel invariant after the receiver's descriptor slot is bound to the payload endpoint.
pub(super) proof fn ipc_copy_endpoint_reference_eof(
    pre: KernelK, post: KernelK, receiver_thread_ptr: RwLockThreadPtr, target_endpoint_index: EndpointIdx, payload_endpoint_ptr: RwLockEndpointPtr,
)
    requires
        pre.inv(),
        edp_idx_valid(target_endpoint_index),
        pre.thr_mp.dom().contains(receiver_thread_ptr),
        pre.thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors.spec_index(target_endpoint_index) is None,
        !(pre.thr_mp.spec_index(receiver_thread_ptr).view().state is DANGLING),
        pre.ep_mp.dom().contains(payload_endpoint_ptr),
        {
            let endpoint_owner = pre.ep_mp.spec_index(payload_endpoint_ptr).view().owning_container;
            &&& pre.ctn_mp.dom().contains(endpoint_owner)
            &&& {
                let receiver_container = pre.thr_mp.spec_index(receiver_thread_ptr).view().owning_container;
                ||| endpoint_owner == receiver_container
                ||| pre.ctn_mp.spec_index(endpoint_owner).view_ghost().subtree_set.view().contains(receiver_container)
            }
        },
        ipc_copy_endpoint_reference_eof_transition_framing(pre, post, receiver_thread_ptr, target_endpoint_index, payload_endpoint_ptr),
        post.thr_mp.perms_wf(),
        post.ep_mp.perms_wf(),
    ensures post.inv(),
{
    reveal(ipc_copy_endpoint_reference_eof_transition_framing);
    thread_endpoint_ref_counter_wf_endpoint_at(pre.thr_mp, pre.ep_mp, payload_endpoint_ptr, receiver_thread_ptr, target_endpoint_index);
    assert(post.subsystems_inv()) by {
        assert(thread_perms_wf(post.thr_mp)) by {
            reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
            reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_partner_only_when_wlocked); reveal(thread_peer_implies_ipc_partner);
        };
        assert(endpoint_perms_wf(post.ep_mp)) by { reveal(endpoint_perms_wf); };
        reveal(KernelK::default_pagetable_wf);
    };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_endpoint_memory_fields(pre, post); };
    assert(post.process_management_inv()) by {
        assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
        assert(thread_caller_callee_wf(post.thr_mp)) by { thread_caller_callee_wf_preserved_for_call_link_eq(pre.thr_mp, post.thr_mp); };
        assert(thread_dangling_chain_end_wf(post.thr_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thr_mp, post.thr_mp); };
        assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { container_endpoint_wf_preserved_for_endpoint_owner_eq(pre.ctn_mp, post.ctn_mp, pre.ep_mp, post.ep_mp); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_queue_fields(pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(container_thread_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(container_endpoint_wf); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { container_thread_scheduler_wf_preserved_for_scheduled_thread_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp); };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { container_thread_wf_preserved_for_container_thread_link_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { process_thread_wf_preserved_for_process_thread_link_eq(pre.prc_mp, post.prc_mp, pre.thr_mp, post.thr_mp); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_running_thread_eq(pre.thr_mp, post.thr_mp, pre.cpu_arr, post.cpu_arr); };
    };
}

/// Closes every kernel invariant after the channel's head waiter is dequeued into endpoint transit.
pub(super) proof fn ipc_begin_endpoint_transfer_eof(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, channel_endpoint_ptr: RwLockEndpointPtr,
)
    requires
        pre.inv(),
        current_thread_ptr != peer_thread_ptr,
        pre.thr_mp.dom().contains(current_thread_ptr),
        pre.thr_mp.dom().contains(peer_thread_ptr),
        pre.thr_mp.spec_index(peer_thread_ptr).view().state is SENDING || pre.thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING,
        pre.thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(channel_endpoint_ptr),
        pre.ep_mp.dom().contains(channel_endpoint_ptr),
        pre.ep_mp.spec_index(channel_endpoint_ptr).view().queue.len() != 0,
        pre.ep_mp.spec_index(channel_endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr,
        ipc_begin_endpoint_transfer_eof_transition_framing(pre, post, current_thread_ptr, peer_thread_ptr, channel_endpoint_ptr),
        thread_perms_wf(post.thr_mp),
        endpoint_perms_wf(post.ep_mp),
    ensures post.inv(),
{
    reveal(ipc_begin_endpoint_transfer_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_endpoint_memory_fields(pre, post); };
    assert(post.process_management_inv()) by {
        assert(thread_dangling_chain_end_wf(post.thr_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thr_mp, post.thr_mp); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
        assert({
            &&& container_endpoint_wf(post.ctn_mp, post.ep_mp)
            &&& thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)
            &&& thread_caller_callee_wf(post.thr_mp)
        }) by { reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(thread_caller_callee_wf); };
        assert({
            &&& container_scheduler_wf(post.ctn_mp, post.sched_mp)
            &&& container_thread_wf(post.ctn_mp, post.thr_mp)
            &&& process_thread_wf(post.prc_mp, post.thr_mp)
            &&& thread_cpu_wf(post.thr_mp, post.cpu_arr)
        }) by { reveal(container_scheduler_wf); reveal(container_thread_wf); reveal(process_thread_wf); reveal(thread_cpu_wf); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { reveal(LinkedList::wf_map); reveal(thread_endpoint_queue_wf); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); };
    };
}

/// Closes every kernel invariant after the endpoint-transit peer is scheduled, from the summary and the
/// thread and scheduler representation facts.
pub(super) proof fn ipc_finish_endpoint_transit_eof(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, peer_scheduler_ptr: RwLockSchedulerPtr,
    wake_cpu: CpuId, peer_result: RetValueType,
)
    requires
        pre.inv(),
        current_thread_ptr != peer_thread_ptr,
        index_valid(NUM_CPUS, wake_cpu),
        pre.thr_mp.dom().contains(current_thread_ptr),
        pre.thr_mp.dom().contains(peer_thread_ptr),
        pre.thr_mp.spec_index(peer_thread_ptr).view().state is IPC_ENDPOINT_TRANSIT,
        pre.sched_mp.dom().contains(peer_scheduler_ptr),
        pre.ctn_mp.dom().contains(pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container),
        pre.ctn_mp.spec_index(pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container).view_rodata().view().scheduler == peer_scheduler_ptr,
        pre.sched_mp.spec_index(peer_scheduler_ptr).owning_container == pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container,
        !pre.sched_mp.spec_index(peer_scheduler_ptr).shard(wake_cpu).queue.view().contains(peer_thread_ptr),
        ipc_finish_endpoint_transit_eof_transition_framing(pre, post, current_thread_ptr, peer_thread_ptr, peer_scheduler_ptr, wake_cpu, peer_result),
        thread_perms_wf(post.thr_mp),
        scheduler_perms_wf(post.sched_mp),
    ensures post.inv(),
{
    reveal(ipc_finish_endpoint_transit_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_endpoint_memory_fields(pre, post); };
    assert(post.process_management_inv()) by {
        assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_descriptor_eq(pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
        assert(thread_caller_callee_wf(post.thr_mp)) by { thread_caller_callee_wf_preserved_for_call_link_eq(pre.thr_mp, post.thr_mp); };
        assert(thread_dangling_chain_end_wf(post.thr_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thr_mp, post.thr_mp); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_endpoint_waiting_eq(pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by {
            container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp);
        };
        assert({
            &&& container_scheduler_wf(post.ctn_mp, post.sched_mp)
            &&& container_thread_wf(post.ctn_mp, post.thr_mp)
            &&& process_thread_wf(post.prc_mp, post.thr_mp)
            &&& thread_cpu_wf(post.thr_mp, post.cpu_arr)
        }) by { reveal(container_scheduler_wf); reveal(container_thread_wf); reveal(process_thread_wf); reveal(thread_cpu_wf); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by {
            seq_push_lemma::<RwLockThreadPtr>();
            reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); reveal(LinkedList::wf_value_list); reveal(LinkedList::wf_map);
        };
    };
}
} // verus!
