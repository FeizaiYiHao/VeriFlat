use vstd::prelude::*;
use crate::*;
use veriflat_syscall_new_process::syscall_new_process::syscall_new_process_spec::*;

verus! {
/// Entering process creation on a cpu of `a` locks only objects of `a` and an endpoint its running
/// thread holds.
pub proof fn new_process_enter_step_lr(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange4K, regs: Registers, endpoint_index: Option<EndpointIdx>, with_iommu: bool,
    a: RwLockContainerPtr, b: RwLockContainerPtr,
)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        new_process_enter_step_pre(old_u, cpu_id, range, endpoint_index, with_iommu), new_process_enter_step(old_u, new_u, cpu_id, range, regs, endpoint_index, with_iommu),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(new_process_enter_step_pre); reveal(new_process_enter_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_endpoint_ownership_wf); }

/// The step of `new_process_enter_step_lr` preserves isolation.
pub proof fn new_process_enter_step_iso(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange4K, regs: Registers, endpoint_index: Option<EndpointIdx>, with_iommu: bool,
    a: RwLockContainerPtr, b: RwLockContainerPtr,
)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        new_process_enter_step_pre(old_u, cpu_id, range, endpoint_index, with_iommu), new_process_enter_step(old_u, new_u, cpu_id, range, regs, endpoint_index, with_iommu),
    ensures isolated(new_u, a, b),
{ reveal(new_process_enter_step_pre); reveal(new_process_enter_step); reveal(kernel_u_cpu_ownership_wf); }

/// Publishing a process on a cpu of `a` adds a child with empty tables to a container of `a` and changes
/// only that container, the running thread, and processes of that container.
pub proof fn new_process_publish_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        new_process_publish_step_pre(old_u, cpu_id), new_process_publish_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    broadcast use vstd::seq_lib::lemma_seq_contains_after_push;
    reveal(new_process_publish_step_pre); reveal(new_process_publish_step);
    reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); reveal(kernel_u_process_ownership_wf);
}

/// The step of `new_process_publish_step_lr` preserves isolation.
pub proof fn new_process_publish_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        new_process_publish_step_pre(old_u, cpu_id), new_process_publish_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(new_process_publish_step_pre); reveal(new_process_publish_step); reveal(kernel_u_cpu_ownership_wf); }

/// Finishing process creation on a cpu of `a` adds a thread to a child process of `a` that holds only an
/// endpoint the running thread holds.
pub proof fn new_process_finish_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        new_process_finish_step_pre(old_u, cpu_id), new_process_finish_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(new_process_finish_step_pre); reveal(new_process_finish_step); reveal(kernel_u_new_thread_changed); reveal(kernel_u_cpu_ownership_wf);
    reveal(kernel_u_endpoint_ownership_wf); reveal(kernel_u_thread_ownership_wf);
}

/// The step of `new_process_finish_step_lr` preserves isolation.
pub proof fn new_process_finish_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        new_process_finish_step_pre(old_u, cpu_id), new_process_finish_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(new_process_finish_step_pre); reveal(new_process_finish_step); reveal(kernel_u_new_thread_changed); reveal(kernel_u_cpu_ownership_wf);
    reveal(kernel_u_endpoint_ownership_wf);
}

/// The process creation result of a running cpu of `b` reads only the view of `b`.
pub proof fn new_process_syscall_result_oc(
    u1: KernelU, u2: KernelU, cpu_id: CpuId, va: VAddr, range: usize, endpoint_index: Option<EndpointIdx>, with_iommu: bool, b: RwLockContainerPtr,
)
    requires
        kernel_u_ownership_wf(u1), steps_in_domain(u1, cpu_id, b), u1.cpu_array[cpu_id as int].state is Running,
        domain_view(u1, b) =~~= domain_view(u2, b),
    ensures new_process_syscall_result(u1, cpu_id, va, range, endpoint_index, with_iommu) == new_process_syscall_result(u2, cpu_id, va, range, endpoint_index, with_iommu),
{
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        let cpu = u1.cpu_array[cpu_id as int];
        let thread = u1.thread_map[cpu.current_thread->Some_0];
        &&& v1.cpus[cpu_id as int] == Some(cpu)
        &&& v1.threads.dom().contains(cpu.current_thread->Some_0) && v1.threads[cpu.current_thread->Some_0] == v2.threads[cpu.current_thread->Some_0]
        &&& v1.processes.dom().contains(thread.owning_proc) && v1.processes[thread.owning_proc] == v2.processes[thread.owning_proc]
        &&& thread.owning_container == cpu.owning_container && v1.containers.dom().contains(thread.owning_container)
        &&& v1.containers[thread.owning_container] == v2.containers[thread.owning_container]
    }) by { reveal(kernel_u_cpu_ownership_wf); };
}
} // verus!
