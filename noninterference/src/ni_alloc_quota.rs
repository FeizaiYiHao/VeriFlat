use vstd::prelude::*;
use crate::*;
use veriflat_syscall_alloc_quota::syscall_alloc_quota::syscall_alloc_quota_spec::*;

verus! {
/// Moving 4K quota from the container of a cpu of `a` to its running process leaves the view of `b`
/// unchanged.
pub proof fn alloc_quota_4k_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, alloc_amount: usize, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        alloc_quota_4k_step_pre(old_u, cpu_id, alloc_amount), alloc_quota_4k_step(old_u, new_u, cpu_id, alloc_amount),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kernel_u_only_process_quota_4k_changed); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `alloc_quota_4k_step_lr` preserves isolation.
pub proof fn alloc_quota_4k_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, alloc_amount: usize, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        alloc_quota_4k_step_pre(old_u, cpu_id, alloc_amount), alloc_quota_4k_step(old_u, new_u, cpu_id, alloc_amount),
    ensures isolated(new_u, a, b),
{ reveal(kernel_u_only_process_quota_4k_changed); }

/// The 4K quota allocation result of a running cpu of `b` reads only the view of `b`.
pub proof fn alloc_quota_4k_syscall_result_oc(u1: KernelU, u2: KernelU, cpu_id: CpuId, alloc_amount: usize, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u1), steps_in_domain(u1, cpu_id, b), u1.cpu_array[cpu_id as int].state is Running,
        domain_view(u1, b) =~~= domain_view(u2, b),
    ensures alloc_quota_4k_syscall_result(u1, cpu_id, alloc_amount) == alloc_quota_4k_syscall_result(u2, cpu_id, alloc_amount),
{
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        let cpu = u1.cpu_array[cpu_id as int];
        &&& v1.cpus[cpu_id as int] == Some(cpu)
        &&& v1.processes.dom().contains(cpu.current_process->Some_0) && v1.processes[cpu.current_process->Some_0] == v2.processes[cpu.current_process->Some_0]
        &&& v1.containers.dom().contains(cpu.owning_container) && v1.containers[cpu.owning_container] == v2.containers[cpu.owning_container]
    }) by { reveal(kernel_u_cpu_ownership_wf); };
}
} // verus!
