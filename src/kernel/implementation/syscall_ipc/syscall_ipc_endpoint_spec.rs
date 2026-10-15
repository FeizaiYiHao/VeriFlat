use vstd::prelude::*;
use crate::*;

verus! {
/// Schedules the endpoint-transit peer on `wake_cpu`; no other object changes.
#[verifier::opaque]
pub open spec fn ipc_finish_endpoint_transit_transition(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, peer_scheduler_ptr: RwLockSchedulerPtr,
    wake_cpu: CpuId, peer_result: RetValueType,
) -> bool {
    let before = pre.thr_mp.spec_index(peer_thread_ptr);
    let after = post.thr_mp.spec_index(peer_thread_ptr);
    let peer_container = before.view().owning_container;
    let shards_before = pre.sched_mp.spec_index(peer_scheduler_ptr);
    let shards_after = post.sched_mp.spec_index(peer_scheduler_ptr);
    let node = after.view().scheduler_linkedlist_node.addr();
    &&& pre.inv()
    &&& current_thread_ptr != peer_thread_ptr
    &&& index_valid(NUM_CPUS, wake_cpu)
    &&& pre.thr_mp.dom().contains(current_thread_ptr)
    &&& pre.thr_mp.dom().contains(peer_thread_ptr)
    &&& before.view().state is IPC_ENDPOINT_TRANSIT
    &&& pre.sched_mp.dom().contains(peer_scheduler_ptr)
    &&& pre.ctn_mp.dom().contains(peer_container)
    &&& pre.ctn_mp.spec_index(peer_container).view_rodata().view().scheduler == peer_scheduler_ptr
    &&& shards_before.owning_container == peer_container
    &&& !shards_before.shard(wake_cpu).queue.view().contains(peer_thread_ptr)
    &&& post == (KernelK { thr_mp: post.thr_mp, sched_mp: post.sched_mp, ..pre })
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, peer_thread_ptr)
    &&& after.locking_thread() == before.locking_thread()
    &&& after.being_killed() == before.being_killed()
    &&& post.thr_mp.spec_index(current_thread_ptr) == pre.thr_mp.spec_index(current_thread_ptr)
    &&& after.view().ipc_framed_fields_equal(&before.view())
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
