use vstd::prelude::*;
use crate::*;
use veriflat_syscall_new_thread::syscall_new_endpoint::syscall_new_endpoint_spec::*;

verus! {
/// Entering endpoint creation on a cpu of `a` locks only the running thread with its process and
/// container, all of `a`, so it leaves the view of `b` unchanged.
pub proof fn new_endpoint_enter_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        new_endpoint_enter_step_pre(old_u, cpu_id, endpoint_index),
        new_endpoint_enter_step(old_u, new_u, cpu_id, endpoint_index),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(new_endpoint_enter_step_pre); reveal(new_endpoint_enter_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `new_endpoint_enter_step_lr` preserves isolation.
pub proof fn new_endpoint_enter_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        new_endpoint_enter_step_pre(old_u, cpu_id, endpoint_index),
        new_endpoint_enter_step(old_u, new_u, cpu_id, endpoint_index),
    ensures isolated(new_u, a, b),
{ reveal(new_endpoint_enter_step_pre); reveal(new_endpoint_enter_step); }

/// Finishing endpoint creation on a cpu of `a` adds a fresh endpoint of `a` held only by the running
/// thread, so it leaves the view of `b` unchanged.
pub proof fn new_endpoint_finish_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        new_endpoint_finish_step_pre(old_u, cpu_id),
        new_endpoint_finish_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(new_endpoint_finish_step_pre); reveal(new_endpoint_finish_step); reveal(kernel_u_new_endpoint_changed); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_endpoint_ownership_wf); }

/// The step of `new_endpoint_finish_step_lr` preserves isolation.
#[verifier::spinoff_prover]
pub proof fn new_endpoint_finish_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        new_endpoint_finish_step_pre(old_u, cpu_id),
        new_endpoint_finish_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(new_endpoint_finish_step_pre); reveal(new_endpoint_finish_step); reveal(kernel_u_new_endpoint_changed); reveal(kernel_u_cpu_ownership_wf);
    assert(forall|p: RwLockProcessPtr| #![trigger new_u.process_map[p]] new_u.process_map.dom().contains(p) && new_u.process_map[p].pagetable is Some
        ==> new_u.process_map[p].pagetable->Some_0.mapping_4k == old_u.process_map[p].pagetable->Some_0.mapping_4k);
}

/// The endpoint creation result of a running cpu of `b` reads only the view of `b`.
pub proof fn new_endpoint_syscall_result_oc(u1: KernelU, u2: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u1),
        steps_in_domain(u1, cpu_id, b),
        u1.cpu_array[cpu_id as int].state is Running,
        domain_view(u1, b) =~~= domain_view(u2, b),
    ensures new_endpoint_syscall_result(u1, cpu_id, endpoint_index) == new_endpoint_syscall_result(u2, cpu_id, endpoint_index),
{
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        let cpu = u1.cpu_array[cpu_id as int];
        &&& v1.cpus[cpu_id as int] == Some(cpu)
        &&& v1.containers.dom().contains(cpu.owning_container) && v1.containers[cpu.owning_container] == v2.containers[cpu.owning_container]
        &&& v1.processes.dom().contains(cpu.current_process->Some_0) && v1.processes[cpu.current_process->Some_0] == v2.processes[cpu.current_process->Some_0]
        &&& v1.threads.dom().contains(cpu.current_thread->Some_0) && v1.threads[cpu.current_thread->Some_0] == v2.threads[cpu.current_thread->Some_0]
    }) by { reveal(kernel_u_cpu_ownership_wf); };
}
} // verus!
