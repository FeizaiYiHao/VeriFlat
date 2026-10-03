use vstd::prelude::*;
use crate::*;
use veriflat_syscall_schedule::syscall_schedule::syscall_schedule_spec::*;

verus! {
/// Switching a cpu of `a` to the head of its container's scheduler leaves the view of `b` unchanged.
pub proof fn schedule_step_lr(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, entry_regs: Registers, flushed_pcid: Option<Pcid>, a: RwLockContainerPtr, b: RwLockContainerPtr,
)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        schedule_step_pre(old_u, cpu_id), schedule_step(old_u, new_u, cpu_id, entry_regs, flushed_pcid),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kernel_u_context_switch_changed); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `schedule_step_lr` preserves isolation.
pub proof fn schedule_step_iso(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, entry_regs: Registers, flushed_pcid: Option<Pcid>, a: RwLockContainerPtr, b: RwLockContainerPtr,
)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        schedule_step_pre(old_u, cpu_id), schedule_step(old_u, new_u, cpu_id, entry_regs, flushed_pcid),
    ensures isolated(new_u, a, b),
{ reveal(kernel_u_context_switch_changed); reveal(kernel_u_cpu_ownership_wf); }

/// The scheduling result of a cpu of `b` reads only the view of `b`: its current process and thread, its
/// container's scheduler, and the scheduler's head, which that container owns.
pub proof fn schedule_syscall_result_oc(u1: KernelU, u2: KernelU, cpu_id: CpuId, b: RwLockContainerPtr)
    requires kernel_u_ownership_wf(u1), kernel_u_cpu_current_pair_wf(u1), steps_in_domain(u1, cpu_id, b), domain_view(u1, b) =~~= domain_view(u2, b),
    ensures schedule_syscall_result(u1, cpu_id) == schedule_syscall_result(u2, cpu_id),
{
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        let cpu = u1.cpu_array[cpu_id as int];
        &&& v1.cpus[cpu_id as int] == Some(cpu)
        &&& v1.containers.dom().contains(cpu.owning_container) && v1.containers[cpu.owning_container] == v2.containers[cpu.owning_container]
        &&& cpu.current_process is Some ==> v1.processes.dom().contains(cpu.current_process->Some_0) && v1.processes[cpu.current_process->Some_0] == v2.processes[cpu.current_process->Some_0]
        &&& cpu.current_process is Some ==> v1.threads.dom().contains(cpu.current_thread->Some_0) && v1.threads[cpu.current_thread->Some_0] == v2.threads[cpu.current_thread->Some_0]
    }) by { reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_cpu_current_pair_wf); };
    assert({
        let queue = u1.container_map[u1.cpu_array[cpu_id as int].owning_container].scheduler;
        queue.len() > 0 ==> queue.contains(queue[0])
    }) by { reveal(kernel_u_cpu_ownership_wf); };
    assert({
        let queue = u1.container_map[u1.cpu_array[cpu_id as int].owning_container].scheduler;
        queue.len() > 0 ==> u1.thread_map.dom().contains(queue[0]) && u1.thread_map[queue[0]].owning_container == u1.cpu_array[cpu_id as int].owning_container
    }) by { reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); };
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        let queue = u1.container_map[u1.cpu_array[cpu_id as int].owning_container].scheduler;
        queue.len() > 0 ==> queue.contains(queue[0]) && v1.threads.dom().contains(queue[0]) && v1.threads[queue[0]] == v2.threads[queue[0]]
    }) by { reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); };
}
} // verus!
