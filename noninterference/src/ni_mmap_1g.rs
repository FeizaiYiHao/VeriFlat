use vstd::prelude::*;
use crate::*;
use veriflat_map_4k::*;
use veriflat_map_4k::map_4k::mmap_1g_install_directory::*;
use veriflat_syscall_mmap_1g::syscall_mmap_1g::syscall_mmap_1g_spec::*;

verus! {
/// Entering 1G mmap on a cpu of `a` locks only objects of `a`.
pub proof fn mmap_1g_enter_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange1G, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_1g_enter_step_pre(old_u, cpu_id, range),
        mmap_1g_enter_step(old_u, new_u, cpu_id, range),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(mmap_1g_enter_step_pre); reveal(mmap_1g_enter_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `mmap_1g_enter_step_lr` preserves isolation.
pub proof fn mmap_1g_enter_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange1G, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_1g_enter_step_pre(old_u, cpu_id, range),
        mmap_1g_enter_step(old_u, new_u, cpu_id, range),
    ensures isolated(new_u, a, b),
{
    reveal(mmap_1g_enter_step_pre); reveal(mmap_1g_enter_step); reveal(kernel_u_cpu_ownership_wf);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// Hiding L3 entries of a 1G mmap on a cpu of `a` changes only window locks of a pagetable of `a` and its running thread's progress.
pub proof fn mmap_1g_hide_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_1g_hide_step_pre(old_u, cpu_id),
        mmap_1g_hide_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(mmap_1g_hide_step_pre); reveal(mmap_1g_hide_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// The step of `mmap_1g_hide_step_lr` preserves isolation.
pub proof fn mmap_1g_hide_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_1g_hide_step_pre(old_u, cpu_id),
        mmap_1g_hide_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(mmap_1g_hide_step_pre); reveal(mmap_1g_hide_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// A 1G mmap TLB flush on a cpu of `a` read-locks the cpu set of a container of `a` and changes only cpu TLBs, which no
/// domain view contains.
pub proof fn mmap_1g_flush_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_1g_flush_step_pre(old_u, cpu_id),
        unmap_4k_tlb_flush_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(mmap_1g_flush_step_pre); reveal(unmap_4k_tlb_flush_step); reveal(kernel_u_cpu_tlb_cleared); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `mmap_1g_flush_step_lr` preserves isolation.
pub proof fn mmap_1g_flush_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_1g_flush_step_pre(old_u, cpu_id),
        unmap_4k_tlb_flush_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(mmap_1g_flush_step_pre); reveal(unmap_4k_tlb_flush_step); reveal(kernel_u_cpu_tlb_cleared);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// Recording the 1G mmap flush on a cpu of `a` changes only its running thread's progress and the cpu-set readers of its container.
pub proof fn mmap_1g_flushed_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_1g_flush_step_pre(old_u, cpu_id),
        mmap_1g_flushed_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(mmap_1g_flush_step_pre); reveal(mmap_1g_flushed_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `mmap_1g_flushed_step_lr` preserves isolation.
pub proof fn mmap_1g_flushed_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_1g_flush_step_pre(old_u, cpu_id),
        mmap_1g_flushed_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(mmap_1g_flush_step_pre); reveal(mmap_1g_flushed_step);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// Reclaiming a table page of a 1G mmap on a cpu of `a` raises the 4K quota of a container of `a` or of an ancestor of `a`,
/// neither of which lies in `b`.
pub proof fn mmap_1g_reclaim_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_1g_reclaim_step_pre(old_u, cpu_id),
        kernel_u_container_quota_4k_increased(old_u, new_u, old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].owning_container),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(mmap_1g_reclaim_step_pre); reveal(kernel_u_container_quota_4k_increased); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_container_tree_wf); }

/// The step of `mmap_1g_reclaim_step_lr` preserves isolation.
pub proof fn mmap_1g_reclaim_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_1g_reclaim_step_pre(old_u, cpu_id),
        kernel_u_container_quota_4k_increased(old_u, new_u, old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].owning_container),
    ensures isolated(new_u, a, b),
{
    reveal(mmap_1g_reclaim_step_pre); reveal(kernel_u_container_quota_4k_increased); reveal(kernel_u_cpu_ownership_wf);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// A 1G mmap directory step on a cpu of `a` changes only its running thread.
pub proof fn mmap_1g_directory_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_1g_directory_step_pre(old_u, cpu_id),
        mmap_1g_directory_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(mmap_1g_directory_step_pre); reveal(mmap_1g_directory_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `mmap_1g_directory_step_lr` preserves isolation.
pub proof fn mmap_1g_directory_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_1g_directory_step_pre(old_u, cpu_id),
        mmap_1g_directory_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(mmap_1g_directory_step_pre); reveal(mmap_1g_directory_step);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// A 1G mmap leaf on a cpu of `a` maps a 1G frame that no mapping reaches, into a process of `a`.
pub proof fn mmap_1g_leaf_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_1g_leaf_step_pre(old_u, cpu_id),
        mmap_1g_leaf_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(mmap_1g_leaf_step_pre); reveal(mmap_1g_leaf_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// The step of `mmap_1g_leaf_step_lr` preserves isolation.
pub proof fn mmap_1g_leaf_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_1g_leaf_step_pre(old_u, cpu_id),
        mmap_1g_leaf_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    let entry = new_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0.mapping_1g.spec_index(progress->Mmap1g_range.view()[progress->Mmap1g_mapped as int]);
    reveal(mmap_1g_leaf_step_pre); reveal(mmap_1g_leaf_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf);
    assert(forall|p: RwLockProcessPtr, v: VAddr| #![trigger old_u.process_map[p].pagetable->Some_0.mapping_4k[v]]
        old_u.process_map.dom().contains(p) && old_u.process_map[p].pagetable is Some && old_u.process_map[p].pagetable->Some_0.mapping_4k.dom().contains(v)
            ==> !in_1g_frame(entry.addr, old_u.process_map[p].pagetable->Some_0.mapping_4k[v].addr)) by { reveal(in_1g_frame); };
    assert(forall|p: RwLockProcessPtr, v: VAddr| #![trigger old_u.process_map[p].iommu_table->Some_0.mapping_4k[v]]
        old_u.process_map.dom().contains(p) && old_u.process_map[p].iommu_table is Some && old_u.process_map[p].iommu_table->Some_0.mapping_4k.dom().contains(v)
            ==> !in_1g_frame(entry.addr, old_u.process_map[p].iommu_table->Some_0.mapping_4k[v].addr)) by { reveal(in_1g_frame); };
    assert(forall|p: RwLockProcessPtr, v: VAddr| #![trigger old_u.process_map[p].pagetable->Some_0.mapping_2m[v]]
        old_u.process_map.dom().contains(p) && old_u.process_map[p].pagetable is Some && old_u.process_map[p].pagetable->Some_0.mapping_2m.dom().contains(v)
            ==> !in_1g_frame(entry.addr, old_u.process_map[p].pagetable->Some_0.mapping_2m[v].addr)) by { reveal(in_1g_frame); };
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b); memory_view_entries_kept_or_outside_other_view_implies_memory_iso(old_u, new_u, a, b);
}

/// Exiting 1G mmap on a cpu of `a` unlocks only objects of `a`.
pub proof fn mmap_1g_exit_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_1g_exit_step_pre(old_u, cpu_id),
        mmap_1g_exit_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(mmap_1g_exit_step_pre); reveal(mmap_1g_exit_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// The step of `mmap_1g_exit_step_lr` preserves isolation.
pub proof fn mmap_1g_exit_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_1g_exit_step_pre(old_u, cpu_id),
        mmap_1g_exit_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(mmap_1g_exit_step_pre); reveal(mmap_1g_exit_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf);
    process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, a); process_mappings_unchanged_implies_memory_view_unchanged(old_u, new_u, b);
    memory_view_unchanged_implies_memory_iso_preserved(old_u, new_u, a, b);
}

/// The 1G mmap result of a running cpu of `b` reads only the view of `b`.
pub proof fn mmap_1g_syscall_result_oc(u1: KernelU, u2: KernelU, cpu_id: CpuId, va: VAddr, range: usize, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u1),
        steps_in_domain(u1, cpu_id, b),
        u1.cpu_array[cpu_id as int].state is Running,
        domain_view(u1, b) =~~= domain_view(u2, b),
    ensures mmap_1g_syscall_result(u1, cpu_id, va, range) == mmap_1g_syscall_result(u2, cpu_id, va, range),
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
