use vstd::prelude::*;
use crate::*;
use veriflat_syscall_pci::syscall_pci::syscall_pci_spec::*;

verus! {
/// Attaching a PCI function of the running process of a cpu of `a` changes only that function's attached bit and, on
/// first attach, the DID of that process's IOMMU table; no process of `b` owns the function or is that process, so the
/// view of `b` is unchanged.
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
{
    reveal(kernel_u_pci_attach_changed);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

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
        &&& u1.process_map[p].pagetable is Some
        &&& v1.pci_attached.dom().contains(p) && v1.pci_attached[p] == v2.pci_attached[p]
    }) by { reveal(kernel_u_cpu_ownership_wf); };
    let p = u1.cpu_array[cpu_id as int].current_process->Some_0;
    if u1.process_map[p].pagetable->Some_0.pci_functions.dom().contains((bus, device, function)) {
        assert(domain_view(u1, b).pci_attached[p].dom().contains((bus, device, function)));
        assert(u1.iommu_root_table.attached[bus as int][device as int][function as int] == domain_view(u1, b).pci_attached[p][(bus, device, function)]);
        assert(u2.iommu_root_table.attached[bus as int][device as int][function as int] == domain_view(u2, b).pci_attached[p][(bus, device, function)]);
    }
}

/// Claiming an unowned PCI function on a cpu of `a` adds it to the array of the running process, a process of `a`, and makes that
/// process its root-table owner; root-table owners are in no domain view, and no process of `b` holds the unowned function.
pub proof fn pci_claim_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, bus: usize, device: usize, function: usize, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        pci_claim_step_pre(old_u, cpu_id, bus, device, function),
        pci_claim_step(old_u, new_u, cpu_id, bus, device, function),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kernel_u_pci_claim_changed); reveal(kernel_u_cpu_ownership_wf);
    let prc_ptr = old_u.cpu_array[cpu_id as int].current_process->Some_0;
    assert(in_domain(old_u, a, old_u.process_map[prc_ptr].owning_container));
    assert(new_u.process_map.dom() =~= old_u.process_map.dom());
    assert(forall|p: RwLockProcessPtr| #![trigger new_u.process_map[p]] p != prc_ptr ==> new_u.process_map[p] == old_u.process_map[p]);
    assert(new_u.process_map[prc_ptr].owning_container == old_u.process_map[prc_ptr].owning_container);
    assert(domain_view(new_u, b).processes =~= domain_view(old_u, b).processes);
    assert(domain_view(new_u, b).pci_attached =~= domain_view(old_u, b).pci_attached);
}

/// The step of `pci_claim_step_lr` preserves isolation.
pub proof fn pci_claim_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, bus: usize, device: usize, function: usize, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        pci_claim_step_pre(old_u, cpu_id, bus, device, function),
        pci_claim_step(old_u, new_u, cpu_id, bus, device, function),
    ensures isolated(new_u, a, b),
{
    reveal(kernel_u_pci_claim_changed);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// The claim result of a running cpu of `b`, a domain disjoint from some domain `a`, reads only the view of `b`: only the root
/// container's root process passes the root-process check, and the root container has every other container in its subtree, so it
/// lies in no domain disjoint from another.
pub proof fn pci_claim_syscall_result_oc(u1: KernelU, u2: KernelU, cpu_id: CpuId, bus: usize, device: usize, function: usize, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u1),
        domains_disjoint(u1, a, b),
        steps_in_domain(u1, cpu_id, b),
        u1.cpu_array[cpu_id as int].state is Running,
        domain_view(u1, b) =~~= domain_view(u2, b),
    ensures pci_claim_syscall_result(u1, cpu_id, bus, device, function) == pci_claim_syscall_result(u2, cpu_id, bus, device, function),
{
    let cpu = u1.cpu_array[cpu_id as int];
    let p = cpu.current_process->Some_0;
    let c = u1.process_map[p].owning_container;
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        &&& v1.cpus[cpu_id as int] == Some(cpu)
        &&& v1.processes.dom().contains(p) && v1.processes[p] == v2.processes[p]
        &&& v1.containers.dom().contains(c) && v1.containers[c] == v2.containers[c]
    }) by { reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_process_ownership_wf); };
    if u1.container_map[c].parent is None {
        reveal(kernel_u_container_root_wf); reveal(kernel_u_container_tree_wf); reveal(kernel_u_container_depth_wf);
        if c == b {
            assert(u1.container_map[c].subtree_set.contains(a));
        } else {
            assert(u1.container_map[c].subtree_set.contains(b));
            assert(u1.container_map[b].uppertree_seq.contains(c));
            assert(u1.container_map[c].uppertree_seq.contains(b));
        }
    }
}
} // verus!
