//! Round 6: the environment and trap events: entering, leaving, and diverting the trap path, user register changes,
//! syscall return values, and hardware TLB and context-cache fills. None is a syscall step: a trap step needs its cpu in
//! user mode or on its trap path, so a cpu inside a syscall, which runs inside its kernel step, takes only fills, and a
//! fill changes only the TLBs.
use vstd::prelude::*;
use crate::*;
use crate::frame::*;
use crate::pagetable_locks::*;

verus! {
pub open spec fn env_label(l: StepLabel) -> bool {
    ||| l is TrapEnter || l is TrapReturn || l is TrapDivert || l is RegsChanged || l is TrapReturnValuesWritten
    ||| l is CpuTlbFilled || l is IommuTlbFilled || l is IommuContextCacheFilled
}

/// Only the TLBs change.
pub open spec fn tlbs_only_changed(u: KernelU, u2: KernelU) -> bool { u2 == (KernelU { cpu_tlb: u2.cpu_tlb, iommu_tlb: u2.iommu_tlb, ..u }) }

/// A write-locked cpu runs inside its kernel step.
pub open spec fn locked_cpus_in_step(u: KernelU) -> bool {
    forall|x: CpuId| #![trigger u.cpu_array[x as int]] index_valid(NUM_CPUS, x) && !cpu_outside(u, x) ==> u.cpu_array[x as int].op is InStep
}

/// An environment step of `d` from outside every syscall is a one-step frame; from inside, it is a fill, which changes only
/// the TLBs.
pub proof fn env_step_implies_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), locked_cpus_in_step(u), env_label(l), labeled_step(l, u, u2, d),
    ensures
        cpu_outside(u, d) ==> single_step_frame(u, u2, d),
        !cpu_outside(u, d) ==> tlbs_only_changed(u, u2),
        others_kept(u, u2, d),
{
    reveal(kernel_u_cpu_ownership_wf);
    let ud = u.cpu_array[d as int];
    match l {
        StepLabel::TrapEnter => { reveal(kernel_u_trap_enter_step_pre); reveal(kernel_u_trap_enter_step); },
        StepLabel::TrapReturn => { reveal(kernel_u_trap_return_step_pre); reveal(kernel_u_trap_return_step); },
        StepLabel::TrapDivert => { reveal(kernel_u_trap_divert_step_pre); reveal(kernel_u_trap_divert_step); },
        StepLabel::RegsChanged { regs } => { reveal(kernel_u_regs_changed_step_pre); reveal(kernel_u_regs_changed_step); },
        StepLabel::TrapReturnValuesWritten { rax, rdx, rsi } => {
            reveal(kernel_u_trap_return_values_written_step_pre); reveal(kernel_u_trap_return_values_written_step);
        },
        StepLabel::CpuTlbFilled { cpu_id, pcid, added } => { reveal(kernel_u_cpu_tlb_filled_step); },
        StepLabel::IommuTlbFilled { did, added } => { reveal(kernel_u_iommu_tlb_filled_step); },
        StepLabel::IommuContextCacheFilled => { reveal(kernel_u_iommu_context_cache_filled_step); },
        _ => {},
    }
    if !cpu_outside(u, d) { assert(u.cpu_array[d as int] == ud); }
    assert forall|x: CpuId| #![trigger cpu_kept(u, u2, x)] index_valid(NUM_CPUS, x) && x != d implies cpu_kept(u, u2, x) by {
        let ux = u.cpu_array[x as int];
        if ux.current_thread is Some && ux.current_thread == ud.current_thread { assert(u.thread_map[ux.current_thread->Some_0].state == (ThreadState::RUNNING { cpu_id: x })); }
    };
}
} // verus!
