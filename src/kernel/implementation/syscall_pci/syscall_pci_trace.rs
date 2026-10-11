use vstd::prelude::*;
use crate::*;
use super::syscall_pci_spec::*;
verus! {
/// The attach wrapper's user-view facts are exactly the attach step on `pre`/`post`.
pub(super) proof fn pci_attach_dma_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, bus: usize, device: usize, function: usize)
    requires
        kernel_u_pci_attach_changed(pre, post, cpu_id, bus, device, function),
        pre.cpu_array[cpu_id as int].lock_state is Unlocked,
        pre.cpu_array[cpu_id as int].current_process == Some(process_ptr),
        pre.process_map[process_ptr].lock_state is Unlocked,
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
