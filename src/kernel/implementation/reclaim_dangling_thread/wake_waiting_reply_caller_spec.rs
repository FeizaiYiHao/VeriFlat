use vstd::prelude::*;
use crate::*;

verus! {
/// Schedules the caller `thread_ptr` serves on shard `cpu_id` of the caller's scheduler with `ErrorIpcCalleeExited` and
/// drops the callee's caller link. Shared by exit and kill.
#[verifier::opaque]
pub open spec fn wake_waiting_reply_caller_transition(
    pre: KernelK, post: KernelK, thread_ptr: RwLockThreadPtr, caller_ptr: RwLockThreadPtr, scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId,
) -> bool {
    &&& thread_ptr != caller_ptr
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& pre.thr_mp.dom().contains(thread_ptr)
    &&& pre.thr_mp.dom().contains(caller_ptr)
    &&& pre.sched_mp.dom().contains(scheduler_ptr)
    &&& pre.ctn_mp.spec_index(pre.thr_mp.spec_index(caller_ptr).view().owning_container).view_rodata().view().scheduler == scheduler_ptr
    &&& pre.thr_mp.spec_index(thread_ptr).view().caller == Some(caller_ptr)
    &&& pre.thr_mp.spec_index(caller_ptr).view().state is WAITING_REPLY
    &&& post == (KernelK { thr_mp: post.thr_mp, sched_mp: post.sched_mp, ..pre })
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& forall|key: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(key)] #![trigger post.thr_mp.spec_index(key)]
        #![trigger pre.thr_mp.spec_index(key).view().temp_alloc_cache_2m] #![trigger post.thr_mp.spec_index(key).view().temp_alloc_cache_2m]
        #![trigger pre.thr_mp.spec_index(key).view().temp_alloc_cache_1g] #![trigger post.thr_mp.spec_index(key).view().temp_alloc_cache_1g]
        pre.thr_mp.dom().contains(key) ==> {
            let before = pre.thr_mp.spec_index(key);
            let after = post.thr_mp.spec_index(key);
            &&& after.view().temp_alloc_cache_2m == before.view().temp_alloc_cache_2m
            &&& after.view().temp_alloc_cache_1g == before.view().temp_alloc_cache_1g
            &&& !(key == thread_ptr || key == caller_ptr) ==> after == before
        }
    &&& {
        let before = pre.thr_mp.spec_index(thread_ptr);
        let after = post.thr_mp.spec_index(thread_ptr);
        &&& after.is_init() == before.is_init()
        &&& after.view_rodata() == before.view_rodata()
        &&& after.view_ghost() == before.view_ghost()
        &&& after.being_killed() == before.being_killed()
        &&& after.killer_info() == before.killer_info()
        &&& after.locking_thread() == before.locking_thread()
        &&& after.view() == (Thread { caller: None, ..before.view() })
    }
    &&& {
        let before = pre.thr_mp.spec_index(caller_ptr);
        let after = post.thr_mp.spec_index(caller_ptr);
        &&& after.is_init() == before.is_init()
        &&& after.view_rodata() == before.view_rodata()
        &&& after.view_ghost() == before.view_ghost()
        &&& after.being_killed() == before.being_killed()
        &&& after.killer_info() == before.killer_info()
        &&& after.locking_thread() == before.locking_thread()
        &&& after.view() == (Thread {
            state: ThreadState::SCHEDULED { cpu_id }, callee: None, error_code: Some(RetValueType::ErrorIpcCalleeExited),
            scheduler_linkedlist_node: after.view().scheduler_linkedlist_node, ..before.view()
        })
        &&& after.view().scheduler_linkedlist_node.addr() == before.view().scheduler_linkedlist_node.addr()
        &&& !after.view().scheduler_linkedlist_node.is_init()
    }
    &&& post.sched_mp.dom() == pre.sched_mp.dom()
    &&& forall|key: RwLockSchedulerPtr| #![trigger pre.sched_mp.spec_index(key)] #![trigger post.sched_mp.spec_index(key)]
        pre.sched_mp.dom().contains(key) && key != scheduler_ptr ==> post.sched_mp.spec_index(key) == pre.sched_mp.spec_index(key)
    &&& {
        let before = pre.sched_mp.spec_index(scheduler_ptr);
        let after = post.sched_mp.spec_index(scheduler_ptr);
        let shard_before = before.shards.spec_index(cpu_id).view();
        let shard_after = after.shards.spec_index(cpu_id).view();
        let node_addr = pre.thr_mp.spec_index(caller_ptr).view().scheduler_linkedlist_node.addr();
        &&& after.owning_container == before.owning_container
        &&& after.shards.entries_unchanged_except(&before.shards, cpu_id)
        &&& shard_after.is_init() == shard_before.is_init()
        &&& shard_after.view().queue.view() == shard_before.view().queue.view().push(caller_ptr)
        &&& shard_after.view().queue.length as int == shard_before.view().queue.length as int + 1
        &&& shard_after.view().queue.map() == shard_before.view().queue.map().insert(node_addr, caller_ptr)
        &&& shard_after.view().queue.dom() == shard_before.view().queue.dom().insert(node_addr)
        &&& !shard_before.view().queue.dom().contains(node_addr)
    }
}
} // verus!
