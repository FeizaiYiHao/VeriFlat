use vstd::prelude::*;
use crate::*;
use veriflat_syscall_new_thread::syscall_new_thread::syscall_new_thread_spec::*;

verus! {
/// Entering thread creation on a cpu of `a` locks only objects of `a` and an endpoint its running
/// thread holds, so it leaves the view of `b` unchanged.
pub proof fn new_thread_enter_step_lr(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, regs: Registers, endpoint_index: Option<EndpointIdx>, a: RwLockContainerPtr, b: RwLockContainerPtr,
)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        new_thread_enter_step_pre(old_u, cpu_id, endpoint_index), new_thread_enter_step(old_u, new_u, cpu_id, regs, endpoint_index),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(new_thread_enter_step_pre); reveal(new_thread_enter_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_endpoint_ownership_wf); }

/// The step of `new_thread_enter_step_lr` preserves isolation.
pub proof fn new_thread_enter_step_iso(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, regs: Registers, endpoint_index: Option<EndpointIdx>, a: RwLockContainerPtr, b: RwLockContainerPtr,
)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        new_thread_enter_step_pre(old_u, cpu_id, endpoint_index), new_thread_enter_step(old_u, new_u, cpu_id, regs, endpoint_index),
    ensures isolated(new_u, a, b),
{ reveal(new_thread_enter_step_pre); reveal(new_thread_enter_step); }

/// Finishing thread creation on a cpu of `a` adds a thread of `a` that holds only an endpoint the
/// running thread holds, so it leaves the view of `b` unchanged.
pub proof fn new_thread_finish_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        new_thread_finish_step_pre(old_u, cpu_id), new_thread_finish_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(new_thread_finish_step_pre); reveal(new_thread_finish_step); reveal(kernel_u_new_thread_changed); reveal(kernel_u_cpu_ownership_wf);
    reveal(kernel_u_endpoint_ownership_wf);
}

/// The step of `new_thread_finish_step_lr` preserves isolation.
#[verifier::spinoff_prover]
pub proof fn new_thread_finish_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        new_thread_finish_step_pre(old_u, cpu_id), new_thread_finish_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(new_thread_finish_step_pre); reveal(new_thread_finish_step); reveal(kernel_u_new_thread_changed); reveal(kernel_u_cpu_ownership_wf);
    reveal(kernel_u_endpoint_ownership_wf);
}

/// The thread creation result of a running cpu of `b` reads only the view of `b`.
pub proof fn new_thread_syscall_result_oc(u1: KernelU, u2: KernelU, cpu_id: CpuId, endpoint_index: Option<EndpointIdx>, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u1), steps_in_domain(u1, cpu_id, b), u1.cpu_array[cpu_id as int].state is Running,
        domain_view(u1, b) =~~= domain_view(u2, b),
    ensures new_thread_syscall_result(u1, cpu_id, endpoint_index) == new_thread_syscall_result(u2, cpu_id, endpoint_index),
{
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        let cpu = u1.cpu_array[cpu_id as int];
        &&& v1.cpus[cpu_id as int] == Some(cpu)
        &&& v1.processes.dom().contains(cpu.current_process->Some_0) && v1.processes[cpu.current_process->Some_0] == v2.processes[cpu.current_process->Some_0]
        &&& v1.threads.dom().contains(cpu.current_thread->Some_0) && v1.threads[cpu.current_thread->Some_0] == v2.threads[cpu.current_thread->Some_0]
    }) by { reveal(kernel_u_cpu_ownership_wf); };
}
} // verus!
