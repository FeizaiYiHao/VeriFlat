use vstd::prelude::*;
use crate::*;

verus! {
/// Writes `payload_endpoint_ptr` into descriptor `target_endpoint_index` of the write-held receiver and records the
/// reference on the write-held endpoint; no other object changes.
#[verifier::opaque]
pub open spec fn ipc_copy_endpoint_reference_eof_transition_framing(
    pre: KernelK, post: KernelK, receiver_thread_ptr: RwLockThreadPtr, target_endpoint_index: EndpointIdx, payload_endpoint_ptr: RwLockEndpointPtr,
) -> bool {
    let thread_before = pre.thr_mp.spec_index(receiver_thread_ptr);
    let thread_after = post.thr_mp.spec_index(receiver_thread_ptr);
    let endpoint_before = pre.ep_mp.spec_index(payload_endpoint_ptr);
    let endpoint_after = post.ep_mp.spec_index(payload_endpoint_ptr);
    &&& post == (KernelK { thr_mp: post.thr_mp, ep_mp: post.ep_mp, ..pre })
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, receiver_thread_ptr)
    &&& post.ep_mp.unchanged_except(&pre.ep_mp, payload_endpoint_ptr)
    &&& thread_after.is_init()
    &&& thread_after.view_rodata() == thread_before.view_rodata()
    &&& thread_after.view_ghost() == thread_before.view_ghost()
    &&& thread_after.locking_thread() == thread_before.locking_thread()
    &&& thread_after.being_killed() == thread_before.being_killed()
    &&& thread_after.killer_info() == thread_before.killer_info()
    &&& thread_after.view() == (Thread { endpoint_descriptors: thread_after.view().endpoint_descriptors, ..thread_before.view() })
    &&& thread_after.view().endpoint_descriptors.wf()
    &&& thread_after.view().endpoint_descriptors.view() =~= thread_before.view().endpoint_descriptors.view().update(target_endpoint_index as int, Some(payload_endpoint_ptr))
    &&& endpoint_after.is_init()
    &&& endpoint_after.view_rodata() == endpoint_before.view_rodata()
    &&& endpoint_after.view_ghost() == endpoint_before.view_ghost()
    &&& endpoint_after.locking_thread() == endpoint_before.locking_thread()
    &&& endpoint_after.being_killed() == endpoint_before.being_killed()
    &&& endpoint_after.killer_info() == endpoint_before.killer_info()
    &&& endpoint_after.view() == (Endpoint { rf_counter: endpoint_after.view().rf_counter, owning_threads: endpoint_after.view().owning_threads, ..endpoint_before.view() })
    &&& endpoint_after.view().rf_counter == endpoint_before.view().rf_counter + 1
    &&& endpoint_after.view().owning_threads.view() =~= endpoint_before.view().owning_threads.view().insert((receiver_thread_ptr, target_endpoint_index))
}

/// Dequeues the head waiter `peer_thread_ptr` of the write-held channel endpoint and moves it into transit with the
/// running thread `current_thread_ptr`; no other object changes.
#[verifier::opaque]
pub open spec fn ipc_begin_transit_eof_transition_framing(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, channel_endpoint_ptr: RwLockEndpointPtr,
) -> bool {
    let peer_before = pre.thr_mp.spec_index(peer_thread_ptr);
    let peer_after = post.thr_mp.spec_index(peer_thread_ptr);
    let channel_before = pre.ep_mp.spec_index(channel_endpoint_ptr);
    let channel_after = post.ep_mp.spec_index(channel_endpoint_ptr);
    let node = peer_before.view().endpoint_linkedlist_node.addr();
    &&& post == (KernelK { thr_mp: post.thr_mp, ep_mp: post.ep_mp, ..pre })
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, peer_thread_ptr)
    &&& post.thr_mp.spec_index(current_thread_ptr) == pre.thr_mp.spec_index(current_thread_ptr)
    &&& peer_after.locking_thread() == peer_before.locking_thread()
    &&& peer_after.being_killed() == peer_before.being_killed()
    &&& peer_after.view_ghost() == peer_before.view_ghost()
    &&& peer_after.view().non_ipc_fields_unchanged(&peer_before.view())
    &&& peer_after.view().caller == peer_before.view().caller
    &&& peer_after.view().callee == peer_before.view().callee
    &&& peer_after.view().syscall_progress == peer_before.view().syscall_progress
    &&& peer_after.view().error_code == peer_before.view().error_code
    &&& peer_after.view().trap_frame == peer_before.view().trap_frame
    &&& peer_after.view().state == (ThreadState::IPC_TRANSIT { partner: current_thread_ptr, wait: if peer_before.view().state is SENDING { IpcWait::Send } else { IpcWait::Receive } })
    &&& peer_after.view().blocking_endpoint_ptr is None
    &&& peer_after.view().blocking_endpoint_index is None
    &&& peer_after.view().endpoint_linkedlist_node.is_init()
    &&& peer_after.view().scheduler_linkedlist_node == peer_before.view().scheduler_linkedlist_node
    &&& peer_after.view().ipc_payload == peer_before.view().ipc_payload
    &&& post.ep_mp.unchanged_except(&pre.ep_mp, channel_endpoint_ptr)
    &&& channel_after.is_init() == channel_before.is_init()
    &&& channel_after.view_rodata() == channel_before.view_rodata()
    &&& channel_after.view_ghost() == channel_before.view_ghost()
    &&& channel_after.locking_thread() == channel_before.locking_thread()
    &&& channel_after.being_killed() == channel_before.being_killed()
    &&& channel_after.view().queue.wf()
    &&& channel_after.view().queue.container_depth == channel_before.view().queue.container_depth
    &&& channel_after.view().queue.lock_minor() == channel_before.view().queue.lock_minor()
    &&& channel_after.view().queue.length as int == channel_before.view().queue.length as int - 1
    &&& channel_after.view().queue.dom() == channel_before.view().queue.dom().remove(node)
    &&& channel_after.view().rf_counter == channel_before.view().rf_counter
    &&& channel_after.view().owning_threads == channel_before.view().owning_threads
    &&& channel_after.view().owning_container == channel_before.view().owning_container
    &&& channel_after.view().queue.view() == channel_before.view().queue.view().skip(1)
    &&& channel_after.view().queue.map() == channel_before.view().queue.map().remove(node)
    &&& channel_after.view().queue_state == channel_before.view().queue_state
    &&& channel_before.view().queue.map().dom().contains(node)
    &&& channel_before.view().queue.map().spec_index(node) == peer_thread_ptr
    &&& !channel_after.view().queue.view().contains(peer_thread_ptr)
    &&& forall|t_ptr: RwLockThreadPtr| #![trigger channel_before.view().queue.view().contains(t_ptr)] #![trigger channel_after.view().queue.view().contains(t_ptr)]
        channel_before.view().queue.view().contains(t_ptr) && t_ptr != peer_thread_ptr ==> channel_after.view().queue.view().contains(t_ptr)
    &&& forall|t_ptr: RwLockThreadPtr| #![trigger channel_before.view().queue.view().contains(t_ptr)] #![trigger channel_after.view().queue.view().contains(t_ptr)]
        channel_after.view().queue.view().contains(t_ptr) ==> channel_before.view().queue.view().contains(t_ptr)
}
/// Schedules the transit peer on `wake_cpu`; no other object changes.
#[verifier::opaque]
pub open spec fn ipc_finish_transit_eof_transition_framing(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, peer_scheduler_ptr: RwLockSchedulerPtr,
    wake_cpu: CpuId, peer_result: RetValueType,
) -> bool {
    let before = pre.thr_mp.spec_index(peer_thread_ptr);
    let after = post.thr_mp.spec_index(peer_thread_ptr);
    let shards_before = pre.sched_mp.spec_index(peer_scheduler_ptr);
    let shards_after = post.sched_mp.spec_index(peer_scheduler_ptr);
    let node = after.view().scheduler_linkedlist_node.addr();
    &&& post == (KernelK { thr_mp: post.thr_mp, sched_mp: post.sched_mp, ..pre })
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, peer_thread_ptr)
    &&& after.locking_thread() == before.locking_thread()
    &&& after.being_killed() == before.being_killed()
    &&& after.view_ghost() == before.view_ghost()
    &&& post.thr_mp.spec_index(current_thread_ptr) == pre.thr_mp.spec_index(current_thread_ptr)
    &&& after.view().non_ipc_fields_unchanged(&before.view())
    &&& after.view().trap_frame == before.view().trap_frame
    &&& after.view().caller == before.view().caller
    &&& after.view().callee == before.view().callee
    &&& after.view().state == (ThreadState::SCHEDULED { cpu_id: wake_cpu })
    &&& after.view().blocking_endpoint_ptr is None
    &&& after.view().blocking_endpoint_index is None
    &&& after.view().endpoint_linkedlist_node.is_init()
    &&& !after.view().scheduler_linkedlist_node.is_init()
    &&& after.view().error_code == Some(peer_result)
    &&& after.view().ipc_payload is Empty
    &&& post.sched_mp.unchanged_except(&pre.sched_mp, peer_scheduler_ptr)
    &&& shards_after.owning_container == shards_before.owning_container
    &&& shards_after.shards.entries_unchanged_except(&shards_before.shards, wake_cpu)
    &&& shards_after.shards.spec_index(wake_cpu).view().locking_thread() == shards_before.shards.spec_index(wake_cpu).view().locking_thread()
    &&& shards_after.shards.spec_index(wake_cpu).view().being_killed() == shards_before.shards.spec_index(wake_cpu).view().being_killed()
    &&& shards_after.shard(wake_cpu).queue.view() == shards_before.shard(wake_cpu).queue.view().push(peer_thread_ptr)
    &&& shards_after.shard(wake_cpu).queue.map() == shards_before.shard(wake_cpu).queue.map().insert(node, peer_thread_ptr)
    &&& shards_after.shard(wake_cpu).queue.dom() == shards_before.shard(wake_cpu).queue.dom().insert(node)
    &&& shards_after.shard(wake_cpu).queue.length == shards_before.shard(wake_cpu).queue.length + 1
    &&& !shards_before.shard(wake_cpu).queue.dom().contains(node)
    &&& !shards_before.shard(wake_cpu).queue.map().dom().contains(node)
    &&& scheduler_shards_of(shards_after) == scheduler_shards_of(shards_before).update(wake_cpu as int, scheduler_shards_of(shards_before)[wake_cpu as int].push(peer_thread_ptr))
}
} // verus!
