use vstd::prelude::*;
use crate::*;
use super::rebalance_pull_spec::*;
use super::rebalance_pull::RebalanceResult;
verus! {
/// From index `from` on, the first index other than `own` whose cpu is not an open cpu of the cpu set of the container
/// `ctn_ptr` of cpu `own` is the user view's first orphan shard of that container.
pub(super) proof fn rebalance_orphan_pull_first_orphan_from_k(krnl: &KernelK, ctn_ptr: RwLockContainerPtr, from: int, own: CpuId)
    requires
        index_valid(NUM_CPUS, own),
        krnl.cpu_arr.spec_index(own).view().view().view().owning_container == ctn_ptr,
        krnl.ctn_mp.dom().contains(ctn_ptr),
        container_cpu_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr),
    ensures
        first_cpu_set_orphan(krnl.cpu_set_mp.spec_index(krnl.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).view(), from, own)
            == first_orphan_shard(kernel_k_to_kernel_u(*krnl), kernel_k_to_kernel_u(*krnl).cpu_array[own as int].owning_container, from, own),
    decreases NUM_CPUS - from,
{
    kernel_cpu_projection_at(krnl, own);
    if 0 <= from < NUM_CPUS {
        kernel_cpu_projection_at(krnl, from as CpuId);
        container_cpu_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, ctn_ptr, from as CpuId); container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, from as CpuId);
        rebalance_orphan_pull_first_orphan_from_k(krnl, ctn_ptr, from + 1, own);
    }
}

/// The wrapping scan of the cpu set of the container `ctn_ptr` of cpu `own` from `cursor` picks the user view's orphan
/// victim of that container.
pub(super) proof fn rebalance_orphan_pull_victim_from_k(krnl: &KernelK, ctn_ptr: RwLockContainerPtr, cursor: CpuId, own: CpuId)
    requires
        index_valid(NUM_CPUS, own),
        krnl.cpu_arr.spec_index(own).view().view().view().owning_container == ctn_ptr,
        krnl.ctn_mp.dom().contains(ctn_ptr),
        container_cpu_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr),
    ensures
        cpu_set_orphan_victim(krnl.cpu_set_mp.spec_index(krnl.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).view(), cursor, own)
            == orphan_victim(kernel_k_to_kernel_u(*krnl), kernel_k_to_kernel_u(*krnl).cpu_array[own as int].owning_container, cursor, own),
{ rebalance_orphan_pull_first_orphan_from_k(krnl, ctn_ptr, cursor as int, own); rebalance_orphan_pull_first_orphan_from_k(krnl, ctn_ptr, 0, own); }

/// Each return path's entry-state K facts give its value as the user-view result.
pub(super) proof fn rebalance_orphan_pull_result_from_k(krnl: &KernelK, cpu_id: CpuId, cursor: CpuId, victim: Option<CpuId>, ret: RebalanceResult)
    requires
        index_valid(NUM_CPUS, cpu_id),
        container_cpu_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr),
        {
            let c = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
            let ro = krnl.ctn_mp.spec_index(c.owning_container).view_rodata().view();
            let queues = scheduler_shards_of(krnl.sched_mp.spec_index(ro.scheduler));
            let head = queues[victim->Some_0 as int][0];
            let live = !krnl.cpu_arr.spec_index(cpu_id).view().being_killed() && !(c.state is Off) && !krnl.cpu_set_mp.spec_index(ro.cpu_set).being_killed();
            let ready = live && victim is Some && queues[victim->Some_0 as int].len() > 0;
            &&& krnl.ctn_mp.dom().contains(c.owning_container)
            &&& live ==> victim == cpu_set_orphan_victim(krnl.cpu_set_mp.spec_index(ro.cpu_set).view(), cursor, cpu_id)
            &&& ready ==> krnl.thrd_mp.dom().contains(head)
            &&& (ret is Pulled) == (ready && !krnl.thrd_mp.spec_index(head).being_killed())
            &&& ret is Pulled ==> ret->Pulled_thread_ptr == head
        },
    ensures
        orphan_pull_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, cursor) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
    let queues = scheduler_shards_of(krnl.sched_mp.spec_index(krnl.ctn_mp.spec_index(c.owning_container).view_rodata().view().scheduler));
    kernel_cpu_projection_at(krnl, cpu_id); kernel_container_projection_at(krnl, c.owning_container); rebalance_orphan_pull_victim_from_k(krnl, c.owning_container, cursor, cpu_id);
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
