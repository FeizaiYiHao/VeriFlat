use vstd::prelude::*;
use crate::*;

verus! {
/// A cpu of `a` entering its trap path from user mode changes only that cpu, which `a` owns.
pub proof fn trap_enter_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kernel_u_trap_enter_step_pre(old_u, cpu_id),
        kernel_u_trap_enter_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kernel_u_trap_enter_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `trap_enter_step_lr` preserves isolation.
pub proof fn trap_enter_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kernel_u_trap_enter_step_pre(old_u, cpu_id),
        kernel_u_trap_enter_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(kernel_u_trap_enter_step);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// A cpu of `a` returning from its trap path to user mode changes only that cpu, which `a` owns.
pub proof fn trap_return_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kernel_u_trap_return_step_pre(old_u, cpu_id),
        kernel_u_trap_return_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kernel_u_trap_return_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `trap_return_step_lr` preserves isolation.
pub proof fn trap_return_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kernel_u_trap_return_step_pre(old_u, cpu_id),
        kernel_u_trap_return_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(kernel_u_trap_return_step);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// A marked cpu of `a` diverting from its trap path to its idle loop changes only that cpu, which `a` owns.
pub proof fn trap_divert_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kernel_u_trap_divert_step_pre(old_u, cpu_id),
        kernel_u_trap_divert_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kernel_u_trap_divert_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `trap_divert_step_lr` preserves isolation.
pub proof fn trap_divert_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kernel_u_trap_divert_step_pre(old_u, cpu_id),
        kernel_u_trap_divert_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(kernel_u_trap_divert_step);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// User code on a cpu of `a` changing the registers of its running thread, which `a` owns, leaves the view of `b` unchanged.
pub proof fn regs_changed_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, regs: Registers, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kernel_u_regs_changed_step_pre(old_u, cpu_id),
        kernel_u_regs_changed_step(old_u, new_u, cpu_id, regs),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kernel_u_regs_changed_step_pre); reveal(kernel_u_regs_changed_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `regs_changed_step_lr` preserves isolation.
pub proof fn regs_changed_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, regs: Registers, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kernel_u_regs_changed_step_pre(old_u, cpu_id),
        kernel_u_regs_changed_step(old_u, new_u, cpu_id, regs),
    ensures isolated(new_u, a, b),
{
    reveal(kernel_u_regs_changed_step_pre); reveal(kernel_u_regs_changed_step);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// Writing the syscall return values into the registers of the thread a cpu of `a` runs, which `a` owns, leaves the view of `b` unchanged.
pub proof fn trap_return_values_written_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, rax: u64, rdx: u64, rsi: u64, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kernel_u_trap_return_values_written_step_pre(old_u, cpu_id),
        kernel_u_trap_return_values_written_step(old_u, new_u, cpu_id, rax, rdx, rsi),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kernel_u_trap_return_values_written_step_pre); reveal(kernel_u_trap_return_values_written_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `trap_return_values_written_step_lr` preserves isolation.
pub proof fn trap_return_values_written_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, rax: u64, rdx: u64, rsi: u64, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kernel_u_trap_return_values_written_step_pre(old_u, cpu_id),
        kernel_u_trap_return_values_written_step(old_u, new_u, cpu_id, rax, rdx, rsi),
    ensures isolated(new_u, a, b),
{
    reveal(kernel_u_trap_return_values_written_step_pre); reveal(kernel_u_trap_return_values_written_step);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}
} // verus!
