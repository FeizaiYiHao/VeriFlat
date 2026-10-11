use vstd::prelude::*;
use crate::*;
use veriflat_syscall_pci::syscall_pci::syscall_pci_spec::*;

verus! {
/// Attaching a PCI function of the running process of a cpu of `a` changes only that function's attached
/// bit, and no process of `b` owns the function, so the view of `b` is unchanged.
pub proof fn pci_attach_dma_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, bus: usize, device: usize, function: usize, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        pci_attach_dma_step_pre(old_u, cpu_id, bus, device, function),
        pci_attach_dma_step(old_u, new_u, cpu_id, bus, device, function),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kernel_u_pci_attach_changed); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_pci_ownership_wf); }

/// The step of `pci_attach_dma_step_lr` preserves isolation.
pub proof fn pci_attach_dma_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, bus: usize, device: usize, function: usize, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        pci_attach_dma_step_pre(old_u, cpu_id, bus, device, function),
        pci_attach_dma_step(old_u, new_u, cpu_id, bus, device, function),
    ensures isolated(new_u, a, b),
{ reveal(kernel_u_pci_attach_changed); }

/// The attach result of a running cpu of `b` reads only the view of `b`.
pub proof fn pci_attach_dma_syscall_result_oc(u1: KernelU, u2: KernelU, cpu_id: CpuId, bus: usize, device: usize, function: usize, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u1),
        steps_in_domain(u1, cpu_id, b),
        u1.cpu_array[cpu_id as int].state is Running,
        domain_view(u1, b) =~~= domain_view(u2, b),
    ensures pci_attach_dma_syscall_result(u1, cpu_id, bus, device, function) == pci_attach_dma_syscall_result(u2, cpu_id, bus, device, function),
{
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        let cpu = u1.cpu_array[cpu_id as int];
        let p = cpu.current_process->Some_0;
        &&& v1.cpus[cpu_id as int] == Some(cpu)
        &&& v1.processes.dom().contains(p) && v1.processes[p] == v2.processes[p]
        &&& v1.pci_attached[p][(bus, device, function)] == v2.pci_attached[p][(bus, device, function)]
    }) by { reveal(kernel_u_cpu_ownership_wf); };
}
} // verus!
