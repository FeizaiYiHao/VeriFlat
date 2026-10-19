use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_transition_spec::{ipc_block_current_eof_transition_framing, ipc_schedule_waiting_peer_eof_transition_framing};
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_dispatch::running_thread_not_in_endpoint_queue;

verus! {
proof fn ipc_block_current_eof_subsystems(
    pre: KernelK, post: KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, default_cr3: PageTableRoot,
)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        edp_idx_valid(endpoint_index),
        pre.prc_mp.dom().contains(process_ptr),
        pre.thr_mp.dom().contains(current_thread_ptr),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        pre.thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
        pre.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf(),
        pre.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        waiting_state.is_endpoint_waiting(),
        payload.wf(),
        waiting_state is RECEIVING_CALL ==> pre.thr_mp.spec_index(current_thread_ptr).view().caller is None,
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(current_thread_ptr),
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.len() == 0 || match pre.ep_mp.spec_index(endpoint_ptr).view().queue_state {
                EndpointState::SEND => waiting_state.is_endpoint_send_waiting(),
                EndpointState::RECEIVE => waiting_state.is_endpoint_receive_waiting(),
            },
        pre.cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        pre.thr_mp.spec_index(current_thread_ptr).being_killed() == false,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() == pre.ep_mp.spec_index(endpoint_ptr).view().queue.length,
        pre.pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).locking_thread() is Write,
        default_cr3 == pre.dflt_pt.view().cr3,
        ipc_block_current_eof_transition_framing(pre, post, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, default_cr3),
        thread_perms_wf(post.thr_mp),
        endpoint_perms_wf(post.ep_mp),
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        pcid_needflush_wf(post.pcid_needflush),
        cpu_published_wf(post.cpu_published, post.cpu_arr, post.pcid_needflush),
    ensures post.subsystems_inv(),
{
    reveal(ipc_block_current_eof_transition_framing);
    assert(post.subsystems_inv()) by {
        assert({
            &&& cpu_array_wf(post.cpu_arr, post.dflt_pt.view())
            &&& thread_perms_wf(post.thr_mp)
            &&& endpoint_perms_wf(post.ep_mp)
        }) by { reveal(cpu_array_wf); reveal(thread_perms_wf); };
        reveal(KernelK::default_pagetable_wf); reveal(cpu_offline_flags_wf);
    };
}

proof fn ipc_block_current_eof_memory(
    pre: KernelK, post: KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, default_cr3: PageTableRoot,
)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        edp_idx_valid(endpoint_index),
        pre.prc_mp.dom().contains(process_ptr),
        pre.thr_mp.dom().contains(current_thread_ptr),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        pre.thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
        pre.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf(),
        pre.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        waiting_state.is_endpoint_waiting(),
        payload.wf(),
        waiting_state is RECEIVING_CALL ==> pre.thr_mp.spec_index(current_thread_ptr).view().caller is None,
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(current_thread_ptr),
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.len() == 0 || match pre.ep_mp.spec_index(endpoint_ptr).view().queue_state {
                EndpointState::SEND => waiting_state.is_endpoint_send_waiting(),
                EndpointState::RECEIVE => waiting_state.is_endpoint_receive_waiting(),
            },
        pre.cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        pre.thr_mp.spec_index(current_thread_ptr).being_killed() == false,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() == pre.ep_mp.spec_index(endpoint_ptr).view().queue.length,
        pre.pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).locking_thread() is Write,
        default_cr3 == pre.dflt_pt.view().cr3,
        ipc_block_current_eof_transition_framing(pre, post, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, default_cr3),
        thread_perms_wf(post.thr_mp),
        endpoint_perms_wf(post.ep_mp),
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        pcid_needflush_wf(post.pcid_needflush),
        cpu_published_wf(post.cpu_published, post.cpu_arr, post.pcid_needflush),
    ensures post.memory_management_inv(),
{
    reveal(ipc_block_current_eof_transition_framing);
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_endpoint_memory_fields(pre, post); };
}

/// The blocked caller and its idled cpu leave the cpu relations closed.
proof fn ipc_block_current_eof_cpu_wf(
    pre: KernelK, post: KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, default_cr3: PageTableRoot,
)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        edp_idx_valid(endpoint_index),
        pre.prc_mp.dom().contains(process_ptr),
        pre.thr_mp.dom().contains(current_thread_ptr),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        pre.thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
        pre.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf(),
        pre.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        waiting_state.is_endpoint_waiting(),
        payload.wf(),
        waiting_state is RECEIVING_CALL ==> pre.thr_mp.spec_index(current_thread_ptr).view().caller is None,
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(current_thread_ptr),
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.len() == 0 || match pre.ep_mp.spec_index(endpoint_ptr).view().queue_state {
                EndpointState::SEND => waiting_state.is_endpoint_send_waiting(),
                EndpointState::RECEIVE => waiting_state.is_endpoint_receive_waiting(),
            },
        pre.cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        pre.thr_mp.spec_index(current_thread_ptr).being_killed() == false,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() == pre.ep_mp.spec_index(endpoint_ptr).view().queue.length,
        pre.pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).locking_thread() is Write,
        default_cr3 == pre.dflt_pt.view().cr3,
        ipc_block_current_eof_transition_framing(pre, post, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, default_cr3),
        thread_perms_wf(post.thr_mp),
        endpoint_perms_wf(post.ep_mp),
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        pcid_needflush_wf(post.pcid_needflush),
        cpu_published_wf(post.cpu_published, post.cpu_arr, post.pcid_needflush),
        post.subsystems_inv(),
    ensures
        container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr),
        process_cpu_wf(post.prc_mp, post.cpu_arr),
        thread_cpu_wf(post.thr_mp, post.cpu_arr),
{
    reveal(ipc_block_current_eof_transition_framing);
    assert({
        &&& container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)
        &&& process_cpu_wf(post.prc_mp, post.cpu_arr)
        &&& thread_cpu_wf(post.thr_mp, post.cpu_arr)
    }) by { reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf); };
}

proof fn ipc_block_current_eof_process_management_inv(
    pre: KernelK, post: KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, default_cr3: PageTableRoot,
)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        edp_idx_valid(endpoint_index),
        pre.prc_mp.dom().contains(process_ptr),
        pre.thr_mp.dom().contains(current_thread_ptr),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        pre.thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
        pre.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf(),
        pre.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        waiting_state.is_endpoint_waiting(),
        payload.wf(),
        waiting_state is RECEIVING_CALL ==> pre.thr_mp.spec_index(current_thread_ptr).view().caller is None,
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(current_thread_ptr),
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.len() == 0 || match pre.ep_mp.spec_index(endpoint_ptr).view().queue_state {
                EndpointState::SEND => waiting_state.is_endpoint_send_waiting(),
                EndpointState::RECEIVE => waiting_state.is_endpoint_receive_waiting(),
            },
        pre.cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        pre.thr_mp.spec_index(current_thread_ptr).being_killed() == false,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() == pre.ep_mp.spec_index(endpoint_ptr).view().queue.length,
        pre.pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).locking_thread() is Write,
        default_cr3 == pre.dflt_pt.view().cr3,
        ipc_block_current_eof_transition_framing(pre, post, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, default_cr3),
        thread_perms_wf(post.thr_mp),
        endpoint_perms_wf(post.ep_mp),
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        pcid_needflush_wf(post.pcid_needflush),
        cpu_published_wf(post.cpu_published, post.cpu_arr, post.pcid_needflush),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(ipc_block_current_eof_transition_framing);
    ipc_block_current_eof_cpu_wf(pre, post, cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, default_cr3);
    assert(post.process_management_inv()) by {
        assert(thread_dangling_chain_end_wf(post.thr_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thr_mp, post.thr_mp); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); };
        assert({
            &&& container_endpoint_wf(post.ctn_mp, post.ep_mp)
            &&& thread_caller_callee_wf(post.thr_mp)
        }) by { reveal(container_endpoint_wf); reveal(thread_caller_callee_wf); };
        assert({
            &&& container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)
            &&& container_thread_wf(post.ctn_mp, post.thr_mp)
            &&& process_thread_wf(post.prc_mp, post.thr_mp)
        }) by { reveal(container_thread_scheduler_wf); reveal(container_thread_wf); reveal(process_thread_wf); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { seq_push_lemma::<RwLockThreadPtr>(); reveal(thread_endpoint_queue_wf); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(container_thread_endpoint_wf); };
    };
}

/// Closes every kernel invariant after the caller blocks on the endpoint and its cpu idles on the default page table.
pub(super) proof fn ipc_block_current_eof(
    pre: KernelK, post: KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, default_cr3: PageTableRoot,
)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        edp_idx_valid(endpoint_index),
        pre.prc_mp.dom().contains(process_ptr),
        pre.thr_mp.dom().contains(current_thread_ptr),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        pre.thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
        pre.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf(),
        pre.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        waiting_state.is_endpoint_waiting(),
        payload.wf(),
        waiting_state is RECEIVING_CALL ==> pre.thr_mp.spec_index(current_thread_ptr).view().caller is None,
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(current_thread_ptr),
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.len() == 0 || match pre.ep_mp.spec_index(endpoint_ptr).view().queue_state {
                EndpointState::SEND => waiting_state.is_endpoint_send_waiting(),
                EndpointState::RECEIVE => waiting_state.is_endpoint_receive_waiting(),
            },
        pre.cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        pre.thr_mp.spec_index(current_thread_ptr).being_killed() == false,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() == pre.ep_mp.spec_index(endpoint_ptr).view().queue.length,
        pre.pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).locking_thread() is Write,
        default_cr3 == pre.dflt_pt.view().cr3,
        ipc_block_current_eof_transition_framing(pre, post, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, default_cr3),
        thread_perms_wf(post.thr_mp),
        endpoint_perms_wf(post.ep_mp),
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        pcid_needflush_wf(post.pcid_needflush),
        cpu_published_wf(post.cpu_published, post.cpu_arr, post.pcid_needflush),
    ensures post.inv(),
{
    reveal(ipc_block_current_eof_transition_framing);
    ipc_block_current_eof_subsystems(pre, post, cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, default_cr3);
    ipc_block_current_eof_memory(pre, post, cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, default_cr3);
    ipc_block_current_eof_process_management_inv(pre, post, cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, default_cr3);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match);
        reveal(cpu_dirty_map_contains_pagetable_pcid_match);
    };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}

/// The cpu and emptied-thread relations close after the transition.
proof fn ipc_schedule_waiting_peer_eof_cpu_wf(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, peer_result: RetValueType, thread_id: LockThreadId,
)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, wake_cpu),
        pre.thr_mp.dom().contains(peer_thread_ptr),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.sched_mp.dom().contains(peer_scheduler_ptr),
        pre.ctn_mp.dom().contains(pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container),
        pre.ctn_mp.spec_index(pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container).view_rodata().view().scheduler == peer_scheduler_ptr,
        pre.thr_mp.spec_index(peer_thread_ptr).view().state.is_endpoint_waiting(),
        pre.thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() > 0,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr,
        !pre.sched_mp.spec_index(peer_scheduler_ptr).shards.spec_index(wake_cpu).view().view().queue.dom().contains(pre.thr_mp.spec_index(peer_thread_ptr).view().scheduler_linkedlist_node.addr()),
        ipc_schedule_waiting_peer_eof_transition_framing(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, peer_result, thread_id),
        thread_perms_wf(post.thr_mp),
        endpoint_perms_wf(post.ep_mp),
        scheduler_perms_wf(post.sched_mp),
    ensures
        process_emptied_threads_wf(post.prc_mp, post.thr_mp),
        container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr),
        process_cpu_wf(post.prc_mp, post.cpu_arr),
        thread_cpu_wf(post.thr_mp, post.cpu_arr),
{
    reveal(ipc_schedule_waiting_peer_eof_transition_framing);
    assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
    assert({
        &&& container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)
        &&& process_cpu_wf(post.prc_mp, post.cpu_arr)
        &&& thread_cpu_wf(post.thr_mp, post.cpu_arr)
    }) by { reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf); };
}

/// The endpoint queue, descriptor, reference-counter, and call-link relations close after the transition.
proof fn ipc_schedule_waiting_peer_eof_endpoint_wf(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, peer_result: RetValueType, thread_id: LockThreadId,
)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, wake_cpu),
        pre.thr_mp.dom().contains(peer_thread_ptr),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.sched_mp.dom().contains(peer_scheduler_ptr),
        pre.ctn_mp.dom().contains(pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container),
        pre.ctn_mp.spec_index(pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container).view_rodata().view().scheduler == peer_scheduler_ptr,
        pre.thr_mp.spec_index(peer_thread_ptr).view().state.is_endpoint_waiting(),
        pre.thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() > 0,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr,
        !pre.sched_mp.spec_index(peer_scheduler_ptr).shards.spec_index(wake_cpu).view().view().queue.dom().contains(pre.thr_mp.spec_index(peer_thread_ptr).view().scheduler_linkedlist_node.addr()),
        ipc_schedule_waiting_peer_eof_transition_framing(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, peer_result, thread_id),
        thread_perms_wf(post.thr_mp),
        endpoint_perms_wf(post.ep_mp),
        scheduler_perms_wf(post.sched_mp),
    ensures
        thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp),
        container_endpoint_wf(post.ctn_mp, post.ep_mp),
        thread_caller_callee_wf(post.thr_mp),
        thread_endpoint_queue_wf(post.thr_mp, post.ep_mp),
        container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp),
{
    reveal(ipc_schedule_waiting_peer_eof_transition_framing);
    assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_perms_wf); thread_endpoint_ref_counter_wf_preserved_for_descriptor_eq(pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
    assert({
        &&& container_endpoint_wf(post.ctn_mp, post.ep_mp)
        &&& thread_caller_callee_wf(post.thr_mp)
    }) by { container_endpoint_wf_preserved_for_endpoint_owner_eq(pre.ctn_mp, post.ctn_mp, pre.ep_mp, post.ep_mp); thread_caller_callee_wf_preserved_for_call_link_eq(pre.thr_mp, post.thr_mp); };
    assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by {
        seq_skip_lemma::<RwLockThreadPtr>(); reveal(endpoint_perms_wf); reveal(LinkedList::wf_value_list); reveal(LinkedList::value_list_unique); reveal(thread_endpoint_queue_wf);
    };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by {
        reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf); container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp);
    };
}

pub(super) proof fn ipc_schedule_waiting_peer_eof_process(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, peer_result: RetValueType, thread_id: LockThreadId,
)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, wake_cpu),
        pre.thr_mp.dom().contains(peer_thread_ptr),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.sched_mp.dom().contains(peer_scheduler_ptr),
        pre.ctn_mp.dom().contains(pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container),
        pre.ctn_mp.spec_index(pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container).view_rodata().view().scheduler == peer_scheduler_ptr,
        pre.thr_mp.spec_index(peer_thread_ptr).view().state.is_endpoint_waiting(),
        pre.thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() > 0,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr,
        !pre.sched_mp.spec_index(peer_scheduler_ptr).shards.spec_index(wake_cpu).view().view().queue.dom().contains(pre.thr_mp.spec_index(peer_thread_ptr).view().scheduler_linkedlist_node.addr()),
        ipc_schedule_waiting_peer_eof_transition_framing(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, peer_result, thread_id),
        thread_perms_wf(post.thr_mp),
        endpoint_perms_wf(post.ep_mp),
        scheduler_perms_wf(post.sched_mp),
    ensures
        post.process_management_inv(),
{
    reveal(ipc_schedule_waiting_peer_eof_transition_framing);
    ipc_schedule_waiting_peer_eof_cpu_wf(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, peer_result, thread_id);
    ipc_schedule_waiting_peer_eof_endpoint_wf(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, peer_result, thread_id);
    assert(post.process_management_inv()) by {
        assert(thread_dangling_chain_end_wf(post.thr_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thr_mp, post.thr_mp); };
        assert({
            &&& container_scheduler_wf(post.ctn_mp, post.sched_mp)
            &&& container_thread_wf(post.ctn_mp, post.thr_mp)
            &&& process_thread_wf(post.prc_mp, post.thr_mp)
        }) by { reveal(container_scheduler_wf); reveal(container_thread_wf); reveal(process_thread_wf); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by {
            seq_push_lemma::<RwLockThreadPtr>();
            reveal(scheduler_perms_wf); reveal(LinkedList::wf_map); reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
        };
    };
}

pub(super) proof fn ipc_schedule_waiting_peer_eof(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, peer_result: RetValueType, thread_id: LockThreadId,
)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, wake_cpu),
        pre.thr_mp.dom().contains(peer_thread_ptr),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.sched_mp.dom().contains(peer_scheduler_ptr),
        pre.ctn_mp.dom().contains(pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container),
        pre.ctn_mp.spec_index(pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container).view_rodata().view().scheduler == peer_scheduler_ptr,
        pre.thr_mp.spec_index(peer_thread_ptr).view().state.is_endpoint_waiting(),
        pre.thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() > 0,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr,
        !pre.sched_mp.spec_index(peer_scheduler_ptr).shards.spec_index(wake_cpu).view().view().queue.dom().contains(pre.thr_mp.spec_index(peer_thread_ptr).view().scheduler_linkedlist_node.addr()),
        ipc_schedule_waiting_peer_eof_transition_framing(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, peer_result, thread_id),
        thread_perms_wf(post.thr_mp),
        endpoint_perms_wf(post.ep_mp),
        scheduler_perms_wf(post.sched_mp),
    ensures post.inv(),
{
    reveal(ipc_schedule_waiting_peer_eof_transition_framing);
    ipc_schedule_waiting_peer_eof_process(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, peer_result, thread_id);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_endpoint_memory_fields(pre, post); };
}

/// Records the rendezvous step fields between the syscall's snapshot and the scheduled state.
pub(super) proof fn ipc_schedule_waiting_peer_eof_rendezvous_fields(
    snapshot: KernelK, pre: KernelK, post: KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr,
    peer_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, waiting_state: ThreadState,
    peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, peer_result: RetValueType, thread_id: LockThreadId,
)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        pre.prc_mp.dom().contains(process_ptr),
        pre.thr_mp.dom().contains(current_thread_ptr),
        pre.thr_mp.dom().contains(peer_thread_ptr),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.thr_mp.spec_index(current_thread_ptr).being_killed() == false,
        pre.thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
        pre.thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
        pre.thr_mp.spec_index(peer_thread_ptr).being_killed() == false,
        pre.thr_mp.spec_index(peer_thread_ptr).view().state.is_endpoint_waiting(),
        pre.thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.len() != 0,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr,
        edp_idx_valid(endpoint_index),
        pre.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int] == Some(endpoint_ptr),
        waiting_state.is_endpoint_waiting(),
        (pre.ep_mp.spec_index(endpoint_ptr).view().queue_state is SEND) != waiting_state.is_endpoint_send_waiting(),
        wake_cpu == if pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container == pre.thr_mp.spec_index(current_thread_ptr).view().owning_container { cpu_id } else { pre.thr_mp.spec_index(peer_thread_ptr).view().last_cpu },
        pre.ctn_mp.spec_index(pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container).view_rodata().view().scheduler == peer_scheduler_ptr,
        ipc_schedule_waiting_peer_eof_transition_framing(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, peer_result, thread_id),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&snapshot, &pre),
        kernel_endpoint_nonlock_fields_unchanged(snapshot.ep_mp, pre.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&snapshot, &pre),
        pre.irt.view().owners() == snapshot.irt.view().owners(),
        pre.irt.view().iommu_roots() == snapshot.irt.view().iommu_roots(),
        pre.cpu_tlb.view() == snapshot.cpu_tlb.view(),
        pre.iommu_tlb.view() == snapshot.iommu_tlb.view(),
        pre.cpu_set_mp == snapshot.cpu_set_mp,
        snapshot.cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        snapshot.thr_mp.dom().contains(current_thread_ptr) ==> snapshot.thr_mp.spec_index(current_thread_ptr).locking_thread() is None,
        snapshot.ep_mp.dom().contains(endpoint_ptr) ==> snapshot.ep_mp.spec_index(endpoint_ptr).locking_thread() is None,
        snapshot.thr_mp.dom().contains(peer_thread_ptr) ==> snapshot.thr_mp.spec_index(peer_thread_ptr).locking_thread() is None,
    ensures kernel_ipc_rendezvous_fields(&snapshot, &post, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, None, None),
{
    reveal(ipc_schedule_waiting_peer_eof_transition_framing);
    running_thread_not_in_endpoint_queue(&pre, endpoint_ptr, current_thread_ptr);
    container_thread_wf_at(pre.ctn_mp, pre.thr_mp, current_thread_ptr); container_thread_wf_at(pre.ctn_mp, pre.thr_mp, peer_thread_ptr);
    reveal(kernel_ipc_rendezvous_fields); reveal(container_scheduler_wf); reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
    reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
    reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged);
}
} // verus!
