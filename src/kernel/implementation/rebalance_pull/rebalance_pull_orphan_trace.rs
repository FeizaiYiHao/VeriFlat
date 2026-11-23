use vstd::prelude::*;
use crate::*;
use super::rebalance_pull_spec::*;
use super::rebalance_pull::RebalanceResult;
verus! {
/// Shard `i` of the scan of the container `ctn_ptr` of cpu `own`: the user view's first orphan shard at or above `i` is `i`
/// itself when `orphan`, the one at or above `i + 1` otherwise, and none past the last shard.
pub(super) proof fn rebalance_orphan_pull_victim_scan_from_k(krnl: &KernelK, ctn_ptr: RwLockContainerPtr, i: usize, own: CpuId, orphan: bool)
    requires
        index_valid(NUM_CPUS, own),
        krnl.cpu_arr.spec_index(own).view().view().view().owning_container == ctn_ptr,
        i < NUM_CPUS ==> orphan == (i != own && !({
            let c = krnl.cpu_arr.spec_index(i).view().view().view();
            c.owning_container == ctn_ptr && !(c.state is Off)
        })),
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            let ctn = u.cpu_array[own as int].owning_container;
            &&& u.cpu_array.len() == NUM_CPUS
            &&& i >= NUM_CPUS ==> first_orphan_shard(u, ctn, i as int, own) is None
            &&& i < NUM_CPUS && orphan ==> first_orphan_shard(u, ctn, i as int, own) == Some(i)
            &&& i < NUM_CPUS && !orphan ==> first_orphan_shard(u, ctn, i as int, own) == first_orphan_shard(u, ctn, i + 1, own)
        }),
{ kernel_cpu_projection_at(krnl, own); if i < NUM_CPUS { kernel_cpu_projection_at(krnl, i); } }

/// Each return path's entry-state K facts give its value as the user-view result.
pub(super) proof fn rebalance_orphan_pull_result_from_k(krnl: &KernelK, cpu_id: CpuId, cursor: CpuId, victim: Option<CpuId>, ret: RebalanceResult)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let c = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
            let ro = krnl.ctn_mp.spec_index(c.owning_container).view_rodata().view();
            let queues = scheduler_shards_of(krnl.sched_mp.spec_index(ro.scheduler));
            let head = queues[victim->Some_0 as int][0];
            let live = !krnl.cpu_arr.spec_index(cpu_id).view().being_killed() && !(c.state is Off) && !krnl.cpu_set_mp.spec_index(ro.cpu_set).being_killed();
            let ready = live && victim is Some && queues[victim->Some_0 as int].len() > 0;
            &&& krnl.ctn_mp.dom().contains(c.owning_container)
            &&& live ==> victim == orphan_victim(kernel_k_to_kernel_u(*krnl), kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].owning_container, cursor, cpu_id)
            &&& ready ==> krnl.thrd_mp.dom().contains(head)
            &&& (ret is Pulled) == (ready && !krnl.thrd_mp.spec_index(head).being_killed())
            &&& ret is Pulled ==> ret->Pulled_thread_ptr == head
        },
    ensures
        orphan_pull_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, cursor) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
    let queues = scheduler_shards_of(krnl.sched_mp.spec_index(krnl.ctn_mp.spec_index(c.owning_container).view_rodata().view().scheduler));
    kernel_cpu_projection_at(krnl, cpu_id); kernel_container_projection_at(krnl, c.owning_container);
    if victim is Some && queues[victim->Some_0 as int].len() > 0 && krnl.thrd_mp.dom().contains(queues[victim->Some_0 as int][0]) {
        kernel_thread_projection_at(krnl, queues[victim->Some_0 as int][0]);
    }
}

/// The orphan pull wrapper's user-view facts, with the scan's victim, are exactly the orphan pull step on `pre`/`post`.
pub(super) proof fn rebalance_orphan_pull_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, cursor: CpuId, victim: CpuId, thrd_ptr: RwLockThreadPtr)
    requires
        kernel_u_orphan_pull_changed(pre, post, cpu_id, victim, thrd_ptr),
        orphan_victim(pre, pre.cpu_array[cpu_id as int].owning_container, cursor, cpu_id) == Some(victim),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let queues = pre.container_map.spec_index(cpu.owning_container).scheduler;
            let thread = pre.thread_map.spec_index(thrd_ptr);
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& index_valid(NUM_CPUS, victim)
            &&& victim != cpu_id
            &&& cpu.lock_state is Unlocked
            &&& !(cpu.state is Off)
            &&& pre.container_map.dom().contains(cpu.owning_container)
            &&& !cpu_serves_container(pre, cpu.owning_container, victim)
            &&& queues[victim as int].len() > 0
            &&& queues[victim as int][0] == thrd_ptr
            &&& pre.thread_map.dom().contains(thrd_ptr)
            &&& thread.lock_state is Unlocked
            &&& !thread.killed
            &&& thread.state == (ThreadState::SCHEDULED { cpu_id: victim })
            &&& thread.owning_container == cpu.owning_container
        },
    ensures
        orphan_pull_step_pre(pre, cpu_id, cursor),
        orphan_pull_step(pre, post, cpu_id, cursor),
{ reveal(orphan_pull_step_pre); }

/// The one step pushed since `before` is the complete pulling trace.
pub(super) proof fn rebalance_orphan_pull_trace_pull_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, cursor: CpuId)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        orphan_pull_step_pre(pre, cpu_id, cursor),
        orphan_pull_step(pre, post, cpu_id, cursor),
    ensures
        orphan_pull_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, cursor, true),
{ reveal(orphan_pull_syscall_trace); }

/// A call that pulls nothing records no step.
pub(super) proof fn rebalance_orphan_pull_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, cursor: CpuId)
    requires
        trace.len() == 0,
    ensures
        orphan_pull_syscall_trace(trace, pre, pre, cpu_id, cursor, false),
{ reveal(orphan_pull_syscall_trace); }
} // verus!
