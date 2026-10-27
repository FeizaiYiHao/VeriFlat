use vstd::prelude::*;
use crate::*;
use veriflat_syscall_iommu_unmap_4k::syscall_iommu_unmap_4k::syscall_iommu_unmap_4k_spec::*;

verus! {
/// Entering IOMMU unmap on a cpu of `a` locks only objects of `a`.
pub proof fn iommu_unmap_4k_enter_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, iova_range: VaRange4K, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        iommu_unmap_4k_enter_step_pre(old_u, cpu_id, iova_range),
        iommu_unmap_4k_enter_step(old_u, new_u, cpu_id, iova_range),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(iommu_unmap_4k_enter_step_pre); reveal(iommu_unmap_4k_enter_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `iommu_unmap_4k_enter_step_lr` preserves isolation.
pub proof fn iommu_unmap_4k_enter_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, iova_range: VaRange4K, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        iommu_unmap_4k_enter_step_pre(old_u, cpu_id, iova_range),
        iommu_unmap_4k_enter_step(old_u, new_u, cpu_id, iova_range),
    ensures isolated(new_u, a, b),
{ reveal(iommu_unmap_4k_enter_step_pre); reveal(iommu_unmap_4k_enter_step); reveal(kernel_u_cpu_ownership_wf); }

/// An IOMMU unmap leaf on a cpu of `a` removes one IOMMU mapping of a process of `a`.
pub proof fn iommu_unmap_4k_leaf_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        iommu_unmap_4k_leaf_step_pre(old_u, cpu_id),
        iommu_unmap_4k_leaf_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(iommu_unmap_4k_leaf_step_pre); reveal(iommu_unmap_4k_leaf_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// The step of `iommu_unmap_4k_leaf_step_lr` preserves isolation.
pub proof fn iommu_unmap_4k_leaf_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        iommu_unmap_4k_leaf_step_pre(old_u, cpu_id),
        iommu_unmap_4k_leaf_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(iommu_unmap_4k_leaf_step_pre); reveal(iommu_unmap_4k_leaf_step); reveal(kernel_u_cpu_ownership_wf); }

/// An IOTLB flush on a cpu of `a` empties only the IOTLB domain of its process's IOMMU table, if it has a DID, and
/// records the flush on its running thread; no domain view contains the IOTLB.
pub proof fn iommu_unmap_4k_flush_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        iommu_unmap_4k_flush_step_pre(old_u, cpu_id),
        iommu_unmap_4k_flush_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(iommu_unmap_4k_flush_step_pre); reveal(iommu_unmap_4k_flush_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `iommu_unmap_4k_flush_step_lr` preserves isolation, which does not read the IOTLB.
pub proof fn iommu_unmap_4k_flush_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        iommu_unmap_4k_flush_step_pre(old_u, cpu_id),
        iommu_unmap_4k_flush_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(iommu_unmap_4k_flush_step_pre); reveal(iommu_unmap_4k_flush_step); }

/// An IOMMU unmap quota refund on a cpu of `a` raises the quota of a container of `a` or of an ancestor of `a`,
/// neither of which lies in `b`.
pub proof fn iommu_unmap_4k_refund_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        iommu_unmap_4k_refund_step_pre(old_u, cpu_id),
        kernel_u_container_quota_4k_increased(old_u, new_u, old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].owning_container),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(iommu_unmap_4k_refund_step_pre); reveal(kernel_u_container_quota_4k_increased); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_container_tree_wf); }

/// The step of `iommu_unmap_4k_refund_step_lr` preserves isolation.
pub proof fn iommu_unmap_4k_refund_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        iommu_unmap_4k_refund_step_pre(old_u, cpu_id),
        kernel_u_container_quota_4k_increased(old_u, new_u, old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].owning_container),
    ensures isolated(new_u, a, b),
{ reveal(iommu_unmap_4k_refund_step_pre); reveal(kernel_u_container_quota_4k_increased); reveal(kernel_u_cpu_ownership_wf); }

/// Exiting IOMMU unmap on a cpu of `a` unlocks only objects of `a`.
pub proof fn iommu_unmap_4k_exit_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        iommu_unmap_4k_exit_step_pre(old_u, cpu_id),
        iommu_unmap_4k_exit_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(iommu_unmap_4k_exit_step_pre); reveal(iommu_unmap_4k_exit_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// The step of `iommu_unmap_4k_exit_step_lr` preserves isolation.
pub proof fn iommu_unmap_4k_exit_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        iommu_unmap_4k_exit_step_pre(old_u, cpu_id),
        iommu_unmap_4k_exit_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(iommu_unmap_4k_exit_step_pre); reveal(iommu_unmap_4k_exit_step); reveal(kernel_u_cpu_ownership_wf); }

/// The 4K IOMMU unmap result of a running cpu of `b` reads only the view of `b`.
pub proof fn iommu_unmap_4k_syscall_result_oc(u1: KernelU, u2: KernelU, cpu_id: CpuId, iova: VAddr, range: usize, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u1),
        steps_in_domain(u1, cpu_id, b),
        u1.cpu_array[cpu_id as int].state is Running,
        domain_view(u1, b) =~~= domain_view(u2, b),
    ensures iommu_unmap_4k_syscall_result(u1, cpu_id, iova, range) == iommu_unmap_4k_syscall_result(u2, cpu_id, iova, range),
{
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        let cpu = u1.cpu_array[cpu_id as int];
        let thread = u1.thread_map[cpu.current_thread->Some_0];
        &&& v1.cpus[cpu_id as int] == Some(cpu)
        &&& v1.threads.dom().contains(cpu.current_thread->Some_0) && v1.threads[cpu.current_thread->Some_0] == v2.threads[cpu.current_thread->Some_0]
        &&& v1.processes.dom().contains(thread.owning_proc) && v1.processes[thread.owning_proc] == v2.processes[thread.owning_proc]
        &&& thread.owning_container == cpu.owning_container && v1.containers.dom().contains(thread.owning_container)
        &&& v1.containers[thread.owning_container] == v2.containers[thread.owning_container]
    }) by { reveal(kernel_u_cpu_ownership_wf); };
}
} // verus!
