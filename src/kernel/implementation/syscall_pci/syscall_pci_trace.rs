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
            let process_ptr = cpu.view().view().current_process->Some_0;
            let process = krnl.prc_mp.spec_index(process_ptr);
            let owns = process.view_ghost().owned_pci_functions.view().contains((bus, device, function));
            let live = !process.being_killed() && owns;
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed() && cpu.view().view().current_process is Some
            &&& !(ret is CpuIdle) ==> krnl.prc_mp.dom().contains(process_ptr) && !process.view().zombie
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
pub(super) proof fn pci_attach_dma_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, bus: usize, device: usize, function: usize)
    requires
        kernel_u_pci_attach_changed(pre, post, cpu_id, bus, device, function),
        pre.cpu_array[cpu_id as int].lock_state is Unlocked,
        pre.cpu_array[cpu_id as int].current_process == Some(process_ptr),
        pre.process_map[process_ptr].lock_state is Unlocked,
        pre.process_map[process_ptr].iommu_table->Some_0.lock_state is Unlocked,
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
} // verus!
