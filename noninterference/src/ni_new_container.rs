use vstd::prelude::*;
use crate::*;
use veriflat_syscall_new_container::syscall_new_container::syscall_new_container_spec::*;

verus! {
/// Entering container creation on a cpu of `a` locks only objects of `a`.
pub proof fn new_container_enter_step_lr(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange4K, funding: usize, process_quota: usize, transfer_cpu: CpuId, regs: Registers,
    a: RwLockContainerPtr, b: RwLockContainerPtr,
)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        new_container_enter_step_pre(old_u, cpu_id, range, funding, process_quota, transfer_cpu),
        new_container_enter_step(old_u, new_u, cpu_id, range, funding, process_quota, transfer_cpu, regs),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(new_container_enter_step_pre); reveal(new_container_enter_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `new_container_enter_step_lr` preserves isolation.
pub proof fn new_container_enter_step_iso(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange4K, funding: usize, process_quota: usize, transfer_cpu: CpuId, regs: Registers,
    a: RwLockContainerPtr, b: RwLockContainerPtr,
)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        new_container_enter_step_pre(old_u, cpu_id, range, funding, process_quota, transfer_cpu),
        new_container_enter_step(old_u, new_u, cpu_id, range, funding, process_quota, transfer_cpu, regs),
    ensures isolated(new_u, a, b),
{ reveal(new_container_enter_step_pre); reveal(new_container_enter_step); reveal(kernel_u_cpu_ownership_wf); }

/// Publishing a container on a cpu of `a` adds a child of a container of `a`, with a root process with
/// empty tables, to every subtree that contains its parent, none of which is `b` or below it, and moves an
/// Off cpu of the parent into the child.
pub proof fn new_container_publish_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        new_container_publish_step_pre(old_u, cpu_id), new_container_publish_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    broadcast use vstd::seq_lib::lemma_seq_contains_after_push;
    reveal(new_container_publish_step_pre); reveal(new_container_publish_step); reveal(kernel_u_container_root_created);
    reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_container_tree_wf);
}

/// The step of `new_container_publish_step_lr` preserves isolation.
pub proof fn new_container_publish_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        new_container_publish_step_pre(old_u, cpu_id), new_container_publish_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    broadcast use vstd::seq_lib::lemma_seq_contains_after_push;
    reveal(new_container_publish_step_pre); reveal(new_container_publish_step);
    reveal(kernel_u_container_root_created); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf);
    reveal(kernel_u_container_tree_wf); reveal(kernel_u_process_ownership_wf); reveal(kernel_u_endpoint_ownership_wf);
}

/// Finishing container creation on a cpu of `a` adds a thread to the root process of a child of a
/// container of `a`.
pub proof fn new_container_finish_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        new_container_finish_step_pre(old_u, cpu_id), new_container_finish_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(new_container_finish_step_pre); reveal(new_container_finish_step); reveal(kernel_u_new_thread_changed); reveal(kernel_u_cpu_ownership_wf);
    reveal(kernel_u_thread_ownership_wf); reveal(kernel_u_container_tree_wf);
}

/// The step of `new_container_finish_step_lr` preserves isolation.
pub proof fn new_container_finish_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        new_container_finish_step_pre(old_u, cpu_id), new_container_finish_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(new_container_finish_step_pre); reveal(new_container_finish_step); reveal(kernel_u_new_thread_changed); reveal(kernel_u_cpu_ownership_wf);
    reveal(kernel_u_container_tree_wf); reveal(kernel_u_endpoint_ownership_wf);
}

/// The container creation result of a running cpu of `b` reads only the view of `b`: a cpu outside the view
/// is owned by another container, so handing it over fails the same way in both states.
pub proof fn new_container_syscall_result_oc(
    u1: KernelU, u2: KernelU, cpu_id: CpuId, va: VAddr, range: usize, funding_page_count: usize, process_quota_4k: usize, transfer_cpu_id: CpuId,
    b: RwLockContainerPtr,
)
    requires
        kernel_u_ownership_wf(u1), steps_in_domain(u1, cpu_id, b), u1.cpu_array[cpu_id as int].state is Running,
        domain_view(u1, b) =~~= domain_view(u2, b),
    ensures
        new_container_syscall_result(u1, cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id)
            == new_container_syscall_result(u2, cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id),
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
        &&& transfer_cpu_id < NUM_CPUS ==> v1.cpus[transfer_cpu_id as int] == v2.cpus[transfer_cpu_id as int]
    }) by { reveal(kernel_u_cpu_ownership_wf); };
}
} // verus!
