use vstd::prelude::*;
use crate::*;
use veriflat_map_4k::*;
use veriflat_syscall_unmap_4k::syscall_unmap_4k::syscall_unmap_4k_spec::*;

verus! {
/// Entering unmap on a cpu of `a` locks only objects of `a`.
pub proof fn unmap_4k_enter_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange4K, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_4k_enter_step_pre(old_u, cpu_id, range),
        unmap_4k_enter_step(old_u, new_u, cpu_id, range),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(unmap_4k_enter_step_pre); reveal(unmap_4k_enter_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `unmap_4k_enter_step_lr` preserves isolation.
pub proof fn unmap_4k_enter_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange4K, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_4k_enter_step_pre(old_u, cpu_id, range),
        unmap_4k_enter_step(old_u, new_u, cpu_id, range),
    ensures isolated(new_u, a, b),
{
    reveal(unmap_4k_enter_step_pre); reveal(unmap_4k_enter_step); reveal(kernel_u_cpu_ownership_wf);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// An unmap leaf on a cpu of `a` removes the next recorded mapping of a process of `a`.
pub proof fn unmap_4k_leaf_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_4k_leaf_step_pre(old_u, cpu_id),
        unmap_4k_leaf_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(unmap_4k_leaf_step_pre); reveal(unmap_4k_leaf_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// The step of `unmap_4k_leaf_step_lr` preserves isolation.
pub proof fn unmap_4k_leaf_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_4k_leaf_step_pre(old_u, cpu_id),
        unmap_4k_leaf_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(unmap_4k_leaf_step_pre); reveal(unmap_4k_leaf_step); reveal(kernel_u_cpu_ownership_wf);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b); memory_view_entries_kept_or_outside_other_view_implies_memory_iso(old_u, new_u, a, b);
}


/// An unmap TLB flush on a cpu of `a` read-locks the cpu set of a container of `a` and changes only cpu TLBs, which no
/// domain view contains.
pub proof fn unmap_4k_tlb_flush_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_4k_flush_step_pre(old_u, cpu_id),
        unmap_4k_tlb_flush_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_tlb_flush_step); reveal(kernel_u_cpu_tlb_cleared); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `unmap_4k_tlb_flush_step_lr` preserves isolation.
pub proof fn unmap_4k_tlb_flush_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_4k_flush_step_pre(old_u, cpu_id),
        unmap_4k_tlb_flush_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_tlb_flush_step); reveal(kernel_u_cpu_tlb_cleared);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// Recording the unmap flush on a cpu of `a` changes only its running thread and the cpu-set lock mode of its container.
pub proof fn unmap_4k_flushed_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_4k_flush_step_pre(old_u, cpu_id),
        unmap_4k_flushed_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_flushed_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `unmap_4k_flushed_step_lr` preserves isolation.
pub proof fn unmap_4k_flushed_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_4k_flush_step_pre(old_u, cpu_id),
        unmap_4k_flushed_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_flushed_step);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// An unmap quota refund on a cpu of `a` raises the quota of a container of `a` or of an ancestor of
/// `a`, neither of which lies in `b`.
pub proof fn unmap_4k_refund_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_4k_refund_step_pre(old_u, cpu_id),
        kernel_u_container_quota_4k_increased(old_u, new_u, old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].owning_container),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(unmap_4k_refund_step_pre); reveal(kernel_u_container_quota_4k_increased); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_container_tree_wf); }

/// The step of `unmap_4k_refund_step_lr` preserves isolation.
pub proof fn unmap_4k_refund_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_4k_refund_step_pre(old_u, cpu_id),
        kernel_u_container_quota_4k_increased(old_u, new_u, old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].owning_container),
    ensures isolated(new_u, a, b),
{
    reveal(unmap_4k_refund_step_pre); reveal(kernel_u_container_quota_4k_increased); reveal(kernel_u_cpu_ownership_wf);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// Exiting unmap on a cpu of `a` unlocks only objects of `a`.
pub proof fn unmap_4k_exit_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_4k_refund_step_pre(old_u, cpu_id),
        unmap_4k_exit_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(unmap_4k_refund_step_pre); reveal(unmap_4k_exit_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// The step of `unmap_4k_exit_step_lr` preserves isolation.
pub proof fn unmap_4k_exit_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        unmap_4k_refund_step_pre(old_u, cpu_id),
        unmap_4k_exit_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(unmap_4k_refund_step_pre); reveal(unmap_4k_exit_step); reveal(kernel_u_cpu_ownership_wf);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// The 4K unmap result of a running cpu of `b` reads only the view of `b`.
pub proof fn unmap_4k_syscall_result_oc(u1: KernelU, u2: KernelU, cpu_id: CpuId, va: VAddr, range: usize, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u1),
        steps_in_domain(u1, cpu_id, b),
        u1.cpu_array[cpu_id as int].state is Running,
        domain_view(u1, b) =~~= domain_view(u2, b),
    ensures unmap_4k_syscall_result(u1, cpu_id, va, range) == unmap_4k_syscall_result(u2, cpu_id, va, range),
{
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        let cpu = u1.cpu_array[cpu_id as int];
        let thread = u1.thread_map[cpu.current_thread->Some_0];
        &&& v1.cpus[cpu_id as int] == Some(cpu)
        &&& v1.threads.dom().contains(cpu.current_thread->Some_0) && v1.threads[cpu.current_thread->Some_0] == v2.threads[cpu.current_thread->Some_0]
        &&& v1.processes.dom().contains(thread.owning_proc) && v1.processes[thread.owning_proc] == v2.processes[thread.owning_proc]
    }) by { reveal(kernel_u_cpu_ownership_wf); };
}
} // verus!
