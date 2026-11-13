//! Round 5: `pci_attach_dma`, one step from an unlocked cpu that changes only the running process's IOMMU table DID and the
//! root table's attach bit, so it has no inside and is never blocked; its call records at most one step.
use vstd::prelude::*;
use crate::*;
use crate::frame::*;
use crate::pagetable_locks::*;
use veriflat_syscall_pci::syscall_pci::syscall_pci_spec::*;

verus! {
pub open spec fn pci_label(l: StepLabel) -> bool { l is PciAttach }

/// One call with its PCI function.
pub ghost struct PciCall { pub bus: usize, pub device: usize, pub function: usize }

pub open spec fn pci_call_trace_ok(call: PciCall, t: Seq<KernelStep>, c: CpuId) -> bool {
    t.len() == 0 || pci_attach_dma_syscall_trace(t, t[0].old_u, t[0].new_u, c, call.bus, call.device, call.function, RetValueType::Success)
}

pub open spec fn pci_call_bound(call: PciCall) -> nat { 1 }

pub proof fn pci_call_trace_ok_implies_len_bounded(call: PciCall, t: Seq<KernelStep>, c: CpuId)
    requires pci_call_trace_ok(call, t, c),
    ensures t.len() <= pci_call_bound(call),
{ reveal(pci_attach_dma_syscall_trace); }

/// An attach step of `d` keeps every other cpu, every lock, and every pagetable; `d` is unlocked before and after.
pub proof fn pci_step_implies_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), pci_label(l), labeled_step(l, u, u2, d),
    ensures single_step_frame(u, u2, d),
{
    match l {
        StepLabel::PciAttach { bus, device, function } => { reveal(pci_attach_dma_step_pre); reveal(kernel_u_pci_attach_changed); },
        _ => {},
    }
    assert forall|x: CpuId| #![trigger cpu_kept(u, u2, x)] index_valid(NUM_CPUS, x) && x != d implies cpu_kept(u, u2, x) by {};
}
} // verus!
