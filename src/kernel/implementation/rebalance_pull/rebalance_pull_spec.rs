use vstd::prelude::*;
use crate::*;
use super::rebalance_pull::RebalanceResult;

verus! {
/// The result of `rebalance_pull` from the state at entry: an Idle cpu whose own shard is empty takes the
/// live head of the lowest-numbered other nonempty shard of its container's scheduler; otherwise nothing moves.
/// The victim's range and nonemptiness restate what `first_nonempty_shard` returns.
pub open spec fn rebalance_pull_syscall_result(pre: KernelU, cpu_id: CpuId) -> RebalanceResult {
    let cpu = pre.cpu_array[cpu_id as int];
    let queues = pre.container_map[cpu.owning_container].scheduler;
    let victim = first_nonempty_shard(queues, 0, cpu_id);
    if cpu.state is Idle && queues[cpu_id as int].len() == 0 && victim is Some && index_valid(NUM_CPUS, victim->Some_0) && queues[victim->Some_0 as int].len() > 0
        && !pre.thread_map[queues[victim->Some_0 as int][0]].killed {
        RebalanceResult::Pulled { thread_ptr: queues[victim->Some_0 as int][0] }
    } else { RebalanceResult::Nothing }
}

/// Moves the head of shard `victim` of `scheduler_ptr` to the tail of the empty shard `cpu_id` and retargets
/// that thread's scheduled state; every other object is unchanged.
#[verifier::opaque]
pub open spec fn rebalance_pull_transition(pre: KernelK, post: KernelK, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr, victim: CpuId, thread_ptr: RwLockThreadPtr) -> bool {
    let before = pre.thr_mp.spec_index(thread_ptr);
    let after = post.thr_mp.spec_index(thread_ptr);
    let scheduler_before = pre.sched_mp.spec_index(scheduler_ptr);
    let scheduler_after = post.sched_mp.spec_index(scheduler_ptr);
    let node = before.view().scheduler_linkedlist_node.addr();
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& index_valid(NUM_CPUS, victim)
    &&& victim != cpu_id
    &&& pre.sched_mp.dom().contains(scheduler_ptr)
    &&& pre.thr_mp.dom().contains(thread_ptr)
    &&& scheduler_before.shard(victim).queue.view().len() > 0
    &&& scheduler_before.shard(victim).queue.view()[0] == thread_ptr
    &&& scheduler_before.shard(cpu_id).queue.view().len() == 0
    &&& before.view().state == (ThreadState::SCHEDULED { cpu_id: victim })
    &&& post == (KernelK { thr_mp: post.thr_mp, sched_mp: post.sched_mp, ..pre })
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr)
    &&& after.is_init() == before.is_init()
    &&& after.view_rodata() == before.view_rodata()
    &&& after.view_ghost() == before.view_ghost()
    &&& after.being_killed() == before.being_killed()
    &&& after.locking_thread() == before.locking_thread()
    &&& after.view() == (Thread { state: ThreadState::SCHEDULED { cpu_id }, ..before.view() })
    &&& post.sched_mp.unchanged_except(&pre.sched_mp, scheduler_ptr)
    &&& scheduler_after.owning_container == scheduler_before.owning_container
    &&& forall|c: CpuId| #![trigger scheduler_after.shards.spec_index(c)]
        index_valid(NUM_CPUS, c) && c != victim && c != cpu_id ==> scheduler_after.shards.spec_index(c) == scheduler_before.shards.spec_index(c)
    &&& forall|c: CpuId| #![trigger scheduler_after.shards.spec_index(c)] index_valid(NUM_CPUS, c) && (c == victim || c == cpu_id) ==> {
        let shard_before = scheduler_before.shards.spec_index(c).view();
        let shard_after = scheduler_after.shards.spec_index(c).view();
        &&& shard_after.is_init() == shard_before.is_init()
        &&& shard_after.view_rodata() == shard_before.view_rodata()
        &&& shard_after.view_ghost() == shard_before.view_ghost()
        &&& shard_after.being_killed() == shard_before.being_killed()
        &&& shard_after.locking_thread() == shard_before.locking_thread()
    }
    &&& scheduler_after.shard(victim).queue.view() == scheduler_before.shard(victim).queue.view().skip(1)
    &&& scheduler_after.shard(victim).queue.map() == scheduler_before.shard(victim).queue.map().remove(node)
    &&& scheduler_after.shard(victim).queue.dom() == scheduler_before.shard(victim).queue.dom().remove(node)
    &&& scheduler_after.shard(cpu_id).queue.view() == scheduler_before.shard(cpu_id).queue.view().push(thread_ptr)
    &&& scheduler_after.shard(cpu_id).queue.map() == scheduler_before.shard(cpu_id).queue.map().insert(node, thread_ptr)
    &&& scheduler_after.shard(cpu_id).queue.dom() == scheduler_before.shard(cpu_id).queue.dom().insert(node)
}

/// User-visible precondition of the pull step on `cpu_id`: the Idle cpu's shard is empty, and the head of
/// the lowest-numbered other nonempty shard is live, unlocked, and queued on that shard.
#[verifier::opaque]
pub open spec fn rebalance_pull_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let queues = old_u.container_map.spec_index(cpu.owning_container).scheduler;
    let victim = first_nonempty_shard(queues, 0, cpu_id)->Some_0;
    let thread = old_u.thread_map.spec_index(queues[victim as int][0]);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& cpu.state is Idle
    &&& old_u.container_map.dom().contains(cpu.owning_container)
    &&& queues[cpu_id as int].len() == 0
    &&& first_nonempty_shard(queues, 0, cpu_id) is Some
    &&& index_valid(NUM_CPUS, victim)
    &&& victim != cpu_id
    &&& queues[victim as int].len() > 0
    &&& old_u.thread_map.dom().contains(queues[victim as int][0])
    &&& thread.lock_state is Unlocked
    &&& !thread.killed
    &&& thread.state == (ThreadState::SCHEDULED { cpu_id: victim })
    &&& thread.owning_container == cpu.owning_container
}

/// User-visible pull step: the head of the lowest-numbered other nonempty shard moves to shard `cpu_id`.
pub open spec fn rebalance_pull_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let queues = old_u.container_map.spec_index(old_u.cpu_array[cpu_id as int].owning_container).scheduler;
    let victim = first_nonempty_shard(queues, 0, cpu_id)->Some_0;
    kernel_u_rebalance_pull_changed(old_u, new_u, cpu_id, victim, queues[victim as int][0])
}

/// Complete trace of one rebalance call, including its unchanged lock modes.
#[verifier::opaque]
pub open spec fn rebalance_pull_syscall_trace(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, pulled: bool) -> bool {
    if pulled {
        &&& trace.len() == 1
        &&& trace[0].old_u == pre
        &&& trace[0].new_u == post
        &&& rebalance_pull_step_pre(pre, cpu_id)
        &&& rebalance_pull_step(pre, post, cpu_id)
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}
}
