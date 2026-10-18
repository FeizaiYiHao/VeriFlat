use vstd::prelude::*;
use crate::*;
use super::rebalance_pull_spec::*;
use super::rebalance_pull::RebalanceResult;
verus! {
/// Each return path's entry-state K facts give its value as the user-view result.
pub(super) proof fn rebalance_pull_result_from_k(krnl: &KernelK, cpu_id: CpuId, ret: RebalanceResult)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let c = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
            let queues = scheduler_shards_of(krnl.sched_mp.spec_index(krnl.ctn_mp.spec_index(c.owning_container).view_rodata().view().scheduler));
            let victim = first_nonempty_shard(queues, 0, cpu_id);
            let head = queues[victim->Some_0 as int][0];
            let ready = c.state is Idle && queues[cpu_id as int].len() == 0 && victim is Some && index_valid(NUM_CPUS, victim->Some_0) && queues[victim->Some_0 as int].len() > 0;
            &&& c.state is Idle ==> krnl.ctn_mp.dom().contains(c.owning_container)
            &&& ready ==> krnl.thr_mp.dom().contains(head)
            &&& (ret is Pulled) == (ready && !krnl.thr_mp.spec_index(head).being_killed())
            &&& ret is Pulled ==> ret->Pulled_thread_ptr == head
        },
    ensures
        rebalance_pull_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
    let queues = scheduler_shards_of(krnl.sched_mp.spec_index(krnl.ctn_mp.spec_index(c.owning_container).view_rodata().view().scheduler));
    let victim = first_nonempty_shard(queues, 0, cpu_id);
    kernel_cpu_projection_at(krnl, cpu_id);
    if krnl.ctn_mp.dom().contains(c.owning_container) { kernel_container_projection_at(krnl, c.owning_container); }
    if victim is Some && index_valid(NUM_CPUS, victim->Some_0) && queues[victim->Some_0 as int].len() > 0 && krnl.thr_mp.dom().contains(queues[victim->Some_0 as int][0]) {
        kernel_thread_projection_at(krnl, queues[victim->Some_0 as int][0]);
    }
}

/// The pull wrapper's user-view facts are exactly the pull step on `pre`/`post`.
pub(super) proof fn rebalance_pull_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, victim: CpuId, thread_ptr: RwLockThreadPtr)
    requires
        kernel_u_rebalance_pull_changed(pre, post, cpu_id, victim, thread_ptr),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let queues = pre.container_map.spec_index(cpu.owning_container).scheduler;
            let thread = pre.thread_map.spec_index(thread_ptr);
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& index_valid(NUM_CPUS, victim)
            &&& victim != cpu_id
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Idle
            &&& pre.container_map.dom().contains(cpu.owning_container)
            &&& queues[cpu_id as int].len() == 0
            &&& first_nonempty_shard(queues, 0, cpu_id) == Some(victim)
            &&& queues[victim as int].len() > 0
            &&& queues[victim as int][0] == thread_ptr
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is Unlocked
            &&& !thread.killed
            &&& thread.state == (ThreadState::SCHEDULED { cpu_id: victim })
            &&& thread.owning_container == cpu.owning_container
        },
    ensures
        rebalance_pull_step_pre(pre, cpu_id),
        rebalance_pull_step(pre, post, cpu_id),
{ reveal(rebalance_pull_step_pre); }

/// The one step pushed since `before` is the complete pulling trace.
pub(super) proof fn rebalance_pull_trace_pull_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        rebalance_pull_step_pre(pre, cpu_id),
        rebalance_pull_step(pre, post, cpu_id),
    ensures
        rebalance_pull_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, true),
{ reveal(rebalance_pull_syscall_trace); }

/// A call that pulls nothing records no step.
pub(super) proof fn rebalance_pull_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId)
    requires
        trace.len() == 0,
    ensures
        rebalance_pull_syscall_trace(trace, pre, pre, cpu_id, false),
{ reveal(rebalance_pull_syscall_trace); }
} // verus!
