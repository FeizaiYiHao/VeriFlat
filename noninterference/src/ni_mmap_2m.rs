use vstd::prelude::*;
use crate::*;
use veriflat_map_4k::*;
use veriflat_syscall_mmap_2m::syscall_mmap_2m::syscall_mmap_2m_spec::*;

verus! {
/// Entering 2M mmap on a cpu of `a` locks only objects of `a`.
pub proof fn mmap_2m_enter_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange2M, phase: Mmap2mPhase, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_2m_enter_step_pre(old_u, cpu_id, range, phase),
        mmap_2m_enter_step(old_u, new_u, cpu_id, range, phase),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(mmap_2m_enter_step_pre); reveal(mmap_2m_enter_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `mmap_2m_enter_step_lr` preserves isolation.
pub proof fn mmap_2m_enter_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange2M, phase: Mmap2mPhase, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_2m_enter_step_pre(old_u, cpu_id, range, phase),
        mmap_2m_enter_step(old_u, new_u, cpu_id, range, phase),
    ensures isolated(new_u, a, b),
{
    reveal(mmap_2m_enter_step_pre); reveal(mmap_2m_enter_step);
    assert(new_u.process_map.dom() =~= old_u.process_map.dom());
    assert(forall|p: RwLockProcessPtr| #![trigger new_u.process_map[p]] old_u.process_map.dom().contains(p) ==> {
        &&& new_u.process_map[p].owning_container == old_u.process_map[p].owning_container
        &&& new_u.process_map[p].iommu_table == old_u.process_map[p].iommu_table
        &&& (new_u.process_map[p].pagetable is Some) == (old_u.process_map[p].pagetable is Some)
        &&& new_u.process_map[p].pagetable->Some_0.mapping_4k == old_u.process_map[p].pagetable->Some_0.mapping_4k
        &&& new_u.process_map[p].pagetable->Some_0.mapping_2m == old_u.process_map[p].pagetable->Some_0.mapping_2m
        &&& new_u.process_map[p].pagetable->Some_0.mapping_1g == old_u.process_map[p].pagetable->Some_0.mapping_1g
    });
}

/// Holding the cpu and thread for a 2M mmap on a cpu of `a` locks only objects of `a`.
pub proof fn mmap_2m_hold_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange2M, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_2m_hold_step_pre(old_u, cpu_id, range),
        mmap_2m_hold_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(mmap_2m_hold_step_pre); reveal(mmap_2m_hold_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// The step of `mmap_2m_hold_step_lr` preserves isolation.
pub proof fn mmap_2m_hold_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange2M, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_2m_hold_step_pre(old_u, cpu_id, range),
        mmap_2m_hold_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(mmap_2m_hold_step_pre); reveal(mmap_2m_hold_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// Releasing the cpu and thread of a rejected 2M mmap on a cpu of `a` unlocks only objects of `a`.
pub proof fn mmap_2m_release_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_2m_release_step_pre(old_u, cpu_id),
        mmap_2m_release_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(mmap_2m_release_step_pre); reveal(mmap_2m_release_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// The step of `mmap_2m_release_step_lr` preserves isolation.
pub proof fn mmap_2m_release_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_2m_release_step_pre(old_u, cpu_id),
        mmap_2m_release_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(mmap_2m_release_step_pre); reveal(mmap_2m_release_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// A 2M mmap directory step on a cpu of `a` changes only its running thread and that thread's process.
pub proof fn mmap_2m_directory_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_2m_directory_step_pre(old_u, cpu_id),
        mmap_2m_directory_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(mmap_2m_directory_step_pre); reveal(mmap_2m_directory_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `mmap_2m_directory_step_lr` preserves isolation.
pub proof fn mmap_2m_directory_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_2m_directory_step_pre(old_u, cpu_id),
        mmap_2m_directory_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(mmap_2m_directory_step_pre); reveal(mmap_2m_directory_step);
    assert(forall|p: RwLockProcessPtr| #![trigger new_u.process_map[p]] old_u.process_map.dom().contains(p) ==> {
        &&& new_u.process_map[p].owning_container == old_u.process_map[p].owning_container
        &&& new_u.process_map[p].iommu_table == old_u.process_map[p].iommu_table
        &&& (new_u.process_map[p].pagetable is Some) == (old_u.process_map[p].pagetable is Some)
        &&& new_u.process_map[p].pagetable->Some_0.mapping_4k == old_u.process_map[p].pagetable->Some_0.mapping_4k
        &&& new_u.process_map[p].pagetable->Some_0.mapping_2m == old_u.process_map[p].pagetable->Some_0.mapping_2m
        &&& new_u.process_map[p].pagetable->Some_0.mapping_1g == old_u.process_map[p].pagetable->Some_0.mapping_1g
    });
}

/// Downgrading the pagetable lock of a 2M mmap on a cpu of `a` changes only its running thread and that thread's process.
pub proof fn mmap_2m_downgrade_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_2m_downgrade_step_pre(old_u, cpu_id),
        mmap_2m_downgrade_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(mmap_2m_downgrade_step_pre); reveal(mmap_2m_downgrade_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// The step of `mmap_2m_downgrade_step_lr` preserves isolation.
pub proof fn mmap_2m_downgrade_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_2m_downgrade_step_pre(old_u, cpu_id),
        mmap_2m_downgrade_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(mmap_2m_downgrade_step_pre); reveal(mmap_2m_downgrade_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// A 2M mmap TLB flush on a cpu of `a` read-locks the cpu set of a container of `a` and changes only cpu TLBs, which no
/// domain view contains.
pub proof fn mmap_2m_flush_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_2m_flush_step_pre(old_u, cpu_id),
        unmap_4k_tlb_flush_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(mmap_2m_flush_step_pre); reveal(unmap_4k_tlb_flush_step); reveal(kernel_u_cpu_tlb_cleared); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `mmap_2m_flush_step_lr` preserves isolation.
pub proof fn mmap_2m_flush_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_2m_flush_step_pre(old_u, cpu_id),
        unmap_4k_tlb_flush_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(mmap_2m_flush_step_pre); reveal(unmap_4k_tlb_flush_step); reveal(kernel_u_cpu_tlb_cleared); }

/// Recording the 2M mmap flush on a cpu of `a` changes only the cpu-set lock mode of its container.
pub proof fn mmap_2m_flushed_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_2m_flushed_step_pre(old_u, cpu_id),
        mmap_2m_flushed_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(mmap_2m_flushed_step_pre); reveal(mmap_2m_flushed_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `mmap_2m_flushed_step_lr` preserves isolation.
pub proof fn mmap_2m_flushed_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_2m_flushed_step_pre(old_u, cpu_id),
        mmap_2m_flushed_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(mmap_2m_flushed_step_pre); reveal(mmap_2m_flushed_step); }

/// Reclaiming a hidden L1 table of a 2M mmap on a cpu of `a` raises the 4K quota of a container of `a` or of an ancestor
/// of `a`, neither of which lies in `b`.
pub proof fn mmap_2m_l1_reclaim_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_2m_l1_reclaim_step_pre(old_u, cpu_id),
        kernel_u_container_quota_4k_increased(old_u, new_u, old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].owning_container),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(mmap_2m_l1_reclaim_step_pre); reveal(kernel_u_container_quota_4k_increased); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_container_tree_wf); }

/// The step of `mmap_2m_l1_reclaim_step_lr` preserves isolation.
pub proof fn mmap_2m_l1_reclaim_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_2m_l1_reclaim_step_pre(old_u, cpu_id),
        kernel_u_container_quota_4k_increased(old_u, new_u, old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].owning_container),
    ensures isolated(new_u, a, b),
{ reveal(mmap_2m_l1_reclaim_step_pre); reveal(kernel_u_container_quota_4k_increased); reveal(kernel_u_cpu_ownership_wf); }

/// A 2M mmap leaf on a cpu of `a` maps a 2M frame that no mapping reaches, into a process of `a`.
pub proof fn mmap_2m_leaf_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_2m_leaf_step_pre(old_u, cpu_id),
        mmap_2m_leaf_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(mmap_2m_leaf_step_pre); reveal(mmap_2m_leaf_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// The step of `mmap_2m_leaf_step_lr` preserves isolation.
pub proof fn mmap_2m_leaf_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_2m_leaf_step_pre(old_u, cpu_id),
        mmap_2m_leaf_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    let entry = new_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0.mapping_2m.spec_index(progress->Mmap2m_range.view()[progress->Mmap2m_mapped as int]);
    reveal(mmap_2m_leaf_step_pre); reveal(mmap_2m_leaf_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf);
    assert(forall|p: RwLockProcessPtr, v: VAddr| #![trigger old_u.process_map[p].pagetable->Some_0.mapping_4k[v]]
        old_u.process_map.dom().contains(p) && old_u.process_map[p].pagetable is Some && old_u.process_map[p].pagetable->Some_0.mapping_4k.dom().contains(v)
            ==> !in_2m_frame(entry.addr, old_u.process_map[p].pagetable->Some_0.mapping_4k[v].addr)) by { reveal(in_2m_frame); };
    assert(forall|p: RwLockProcessPtr, v: VAddr| #![trigger old_u.process_map[p].iommu_table->Some_0.mapping_4k[v]]
        old_u.process_map.dom().contains(p) && old_u.process_map[p].iommu_table is Some && old_u.process_map[p].iommu_table->Some_0.mapping_4k.dom().contains(v)
            ==> !in_2m_frame(entry.addr, old_u.process_map[p].iommu_table->Some_0.mapping_4k[v].addr)) by { reveal(in_2m_frame); };
}

/// Exiting 2M mmap on a cpu of `a` unlocks only objects of `a`.
pub proof fn mmap_2m_exit_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_2m_exit_step_pre(old_u, cpu_id),
        mmap_2m_exit_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(mmap_2m_exit_step_pre); reveal(mmap_2m_exit_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// The step of `mmap_2m_exit_step_lr` preserves isolation.
pub proof fn mmap_2m_exit_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        mmap_2m_exit_step_pre(old_u, cpu_id),
        mmap_2m_exit_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(mmap_2m_exit_step_pre); reveal(mmap_2m_exit_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// The 2M mmap result of a running cpu of `b` reads only the view of `b`.
pub proof fn mmap_2m_syscall_result_oc(u1: KernelU, u2: KernelU, cpu_id: CpuId, va: VAddr, range: usize, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u1),
        steps_in_domain(u1, cpu_id, b),
        u1.cpu_array[cpu_id as int].state is Running,
        domain_view(u1, b) =~~= domain_view(u2, b),
    ensures mmap_2m_syscall_result(u1, cpu_id, va, range) == mmap_2m_syscall_result(u2, cpu_id, va, range),
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
