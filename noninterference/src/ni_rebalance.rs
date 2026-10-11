use vstd::prelude::*;
use crate::*;
use veriflat_syscall_schedule::rebalance_pull::rebalance_pull_spec::*;

verus! {
/// Moving the head of another shard of the container of an Idle cpu of `a` onto that cpu's shard leaves the
/// view of `b` unchanged.
pub proof fn rebalance_pull_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        rebalance_pull_step_pre(old_u, cpu_id),
        rebalance_pull_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kernel_u_rebalance_pull_changed); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `rebalance_pull_step_lr` preserves isolation.
pub proof fn rebalance_pull_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        rebalance_pull_step_pre(old_u, cpu_id),
        rebalance_pull_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kernel_u_rebalance_pull_changed); reveal(kernel_u_cpu_ownership_wf); }

/// The pull result of a cpu of `b` reads only the view of `b`: the cpu, its container's shards, and the head
/// of the victim shard, which that container owns.
pub proof fn rebalance_pull_syscall_result_oc(u1: KernelU, u2: KernelU, cpu_id: CpuId, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u1),
        steps_in_domain(u1, cpu_id, b),
        domain_view(u1, b) =~~= domain_view(u2, b),
    ensures rebalance_pull_syscall_result(u1, cpu_id) == rebalance_pull_syscall_result(u2, cpu_id),
{
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        let cpu = u1.cpu_array[cpu_id as int];
        &&& v1.cpus[cpu_id as int] == Some(cpu)
        &&& v1.containers.dom().contains(cpu.owning_container) && v1.containers[cpu.owning_container] == v2.containers[cpu.owning_container]
    }) by { reveal(kernel_u_cpu_ownership_wf); };
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        let queues = u1.container_map[u1.cpu_array[cpu_id as int].owning_container].scheduler;
        let victim = first_nonempty_shard(queues, 0, cpu_id)->Some_0;
        let head = queues[victim as int][0];
        index_valid(NUM_CPUS, victim) && queues[victim as int].len() > 0
            ==> queues[victim as int].contains(head) && v1.threads.dom().contains(head) && v1.threads[head] == v2.threads[head]
    }) by { reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); };
}
} // verus!
