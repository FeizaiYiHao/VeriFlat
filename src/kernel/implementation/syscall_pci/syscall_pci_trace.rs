use vstd::prelude::*;
use crate::*;
use super::syscall_pci_spec::*;
verus! {
/// Each return path's entry-state K facts give its value as the user-view result.
pub(super) proof fn pci_attach_dma_result_from_k(krnl: &KernelK, cpu_id: CpuId, bus: usize, device: usize, function: usize, ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        pci_bdf_valid(bus, device, function),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let prc_ptr = cpu.view().view().current_process->Some_0;
            let process = krnl.prc_mp.spec_index(prc_ptr);
            let owns = krnl.pt_mp.spec_index(process.view().pagetable).view().higher.pci.view().dom().contains((bus, device, function));
            let live = !process.being_killed() && owns;
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed() && cpu.view().view().current_process is Some
            &&& !(ret is CpuIdle) ==> krnl.prc_mp.dom().contains(prc_ptr) && !process.view().zombie
            &&& !(ret is CpuIdle || ret is ErrorProcessKilled) ==> krnl.pt_mp.dom().contains(process.view().pagetable)
            &&& ret is ErrorProcessKilled ==> process.being_killed()
            &&& ret is ErrorPciOwnerMismatch ==> !process.being_killed() && !owns
            &&& ret is ErrorPciNoIommuTable ==> live && process.view().iommu_table is None
            &&& ret is ErrorPciAlreadyAttached ==> live && process.view().iommu_table is Some && krnl.irt.view().spec_index_iommu_root(bus, device, function) is Some
            &&& ret is Success ==> live && process.view().iommu_table is Some && krnl.irt.view().spec_index_iommu_root(bus, device, function) is None
            &&& ret is CpuIdle || ret is ErrorProcessKilled || ret is ErrorPciOwnerMismatch || ret is ErrorPciNoIommuTable || ret is ErrorPciAlreadyAttached || ret is Success
        },
    ensures
        pci_attach_dma_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, bus, device, function) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
    kernel_cpu_projection_at(krnl, cpu_id);
    kernel_iommu_root_table_projection_at(krnl, bus, device, function);
    if krnl.prc_mp.dom().contains(c.current_process->Some_0) { kernel_process_projection_at(krnl, c.current_process->Some_0); }
}

/// The attach wrapper's user-view facts are exactly the attach step on `pre`/`post`.
pub(super) proof fn pci_attach_dma_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, bus: usize, device: usize, function: usize)
    requires
        kernel_u_pci_attach_changed(pre, post, cpu_id, bus, device, function),
        pre.cpu_array[cpu_id as int].lock_state is Unlocked,
        pre.cpu_array[cpu_id as int].current_process == Some(prc_ptr),
        pre.process_map[prc_ptr].lock_state is Unlocked,
        pre.process_map[prc_ptr].iommu_table->Some_0.lock_state is Unlocked,
    ensures
        pci_attach_dma_step_pre(pre, cpu_id, bus, device, function),
        pci_attach_dma_step(pre, post, cpu_id, bus, device, function),
{ reveal(pci_attach_dma_step_pre); reveal(kernel_u_pci_attach_changed); }

/// The one step pushed since `before` is the complete successful attach trace.
pub(super) proof fn pci_attach_dma_trace_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, bus: usize, device: usize, function: usize)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        pci_attach_dma_step_pre(pre, cpu_id, bus, device, function),
        pci_attach_dma_step(pre, post, cpu_id, bus, device, function),
    ensures
        pci_attach_dma_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, bus, device, function, RetValueType::Success),
{ reveal(pci_attach_dma_syscall_trace); }

/// A rejected attach records no step.
pub(super) proof fn pci_attach_dma_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, bus: usize, device: usize, function: usize, ret: RetValueType)
    requires
        trace.len() == 0,
        !(ret is Success),
    ensures
        pci_attach_dma_syscall_trace(trace, pre, pre, cpu_id, bus, device, function, ret),
{ reveal(pci_attach_dma_syscall_trace); }

/// Each claim return path's entry-state K facts give its value as the user-view result.
pub(super) proof fn pci_claim_result_from_k(krnl: &KernelK, cpu_id: CpuId, bus: usize, device: usize, function: usize, ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        pci_bdf_valid(bus, device, function),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let prc_ptr = cpu.view().view().current_process->Some_0;
            let process = krnl.prc_mp.spec_index(prc_ptr);
            let ctn_ptr = process.view_rodata().view().owning_container;
            let pci = krnl.pt_mp.spec_index(process.view().pagetable).view().higher.pci;
            let root = process.view_rodata().view().parent is None && krnl.ctn_mp.spec_index(ctn_ptr).view_rodata().view().parent is None;
            let live = !process.being_killed() && root;
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed() && cpu.view().view().current_process is Some
            &&& !(ret is CpuIdle) ==> krnl.prc_mp.dom().contains(prc_ptr) && !process.view().zombie
            &&& !(ret is CpuIdle || ret is ErrorProcessKilled) ==> krnl.pt_mp.dom().contains(process.view().pagetable) && krnl.ctn_mp.dom().contains(ctn_ptr)
            &&& ret is ErrorProcessKilled ==> process.being_killed()
            &&& ret is ErrorPciNotRootProcess ==> !process.being_killed() && !root
            &&& ret is ErrorPciFunctionArrayFull ==> live && pci.view().dom().len() >= PCI_FUNCTIONS_PER_PROCESS
            &&& ret is ErrorPciAlreadyOwned ==> live && pci.view().dom().len() < PCI_FUNCTIONS_PER_PROCESS && krnl.irt.view().spec_index_owner(bus, device, function) is Some
            &&& ret is Success ==> live && pci.view().dom().len() < PCI_FUNCTIONS_PER_PROCESS && krnl.irt.view().spec_index_owner(bus, device, function) is None
            &&& ret is CpuIdle || ret is ErrorProcessKilled || ret is ErrorPciNotRootProcess || ret is ErrorPciFunctionArrayFull || ret is ErrorPciAlreadyOwned || ret is Success
        },
    ensures
        pci_claim_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, bus, device, function) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
    kernel_cpu_projection_at(krnl, cpu_id);
    krnl.irt.view().user_view_eq_owners_and_attached();
    kernel_u_domains_projection(krnl);
    if krnl.prc_mp.dom().contains(c.current_process->Some_0) {
        let process = krnl.prc_mp.spec_index(c.current_process->Some_0);
        kernel_process_projection_at(krnl, c.current_process->Some_0);
        if krnl.ctn_mp.dom().contains(process.view_rodata().view().owning_container) { kernel_container_projection_at(krnl, process.view_rodata().view().owning_container); }
    }
}

/// The claim wrapper's user-view facts are exactly the claim step on `pre`/`post`.
pub(super) proof fn pci_claim_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, bus: usize, device: usize, function: usize)
    requires
        kernel_u_pci_claim_changed(pre, post, cpu_id, bus, device, function),
        pre.cpu_array[cpu_id as int].lock_state is Unlocked,
        pre.cpu_array[cpu_id as int].current_process == Some(prc_ptr),
        pre.process_map[prc_ptr].lock_state is Unlocked,
        pre.process_map[prc_ptr].pagetable->Some_0.lock_state is Unlocked,
    ensures
        pci_claim_step_pre(pre, cpu_id, bus, device, function),
        pci_claim_step(pre, post, cpu_id, bus, device, function),
{ reveal(pci_claim_step_pre); reveal(kernel_u_pci_claim_changed); }

/// The one step pushed since `before` is the complete successful claim trace.
pub(super) proof fn pci_claim_trace_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, bus: usize, device: usize, function: usize)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        pci_claim_step_pre(pre, cpu_id, bus, device, function),
        pci_claim_step(pre, post, cpu_id, bus, device, function),
    ensures
        pci_claim_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, bus, device, function, RetValueType::Success),
{ reveal(pci_claim_syscall_trace); }

/// A rejected claim records no step.
pub(super) proof fn pci_claim_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, bus: usize, device: usize, function: usize, ret: RetValueType)
    requires
        trace.len() == 0,
        !(ret is Success),
    ensures
        pci_claim_syscall_trace(trace, pre, pre, cpu_id, bus, device, function, ret),
{ reveal(pci_claim_syscall_trace); }
} // verus!
