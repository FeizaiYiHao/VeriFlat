use vstd::prelude::*;
use crate::*;

verus! {
/// Under the kernel invariant, what CPU `cpu_id` may cache under `pcid` in K it may also cache in the user projection.
pub proof fn kernel_cpu_tlb_within_may_cache_projection(krnl: &KernelK, cpu_id: CpuId, pcid: Pcid, tlb: SingleTLB)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        cpu_tlb_within_may_cache(*krnl, cpu_id, pcid, tlb),
    ensures
        cpu_tlb_within_may_cache_u(kernel_k_user_projection(*krnl), cpu_id, pcid, tlb),
        cpu_tlb_within_may_cache_u(kernel_k_to_kernel_u(*krnl), cpu_id, pcid, tlb),
{
    let cpu = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
    kernel_cpu_user_projection_at(krnl, cpu_id);
    if pcid != KERNEL_DEFAULT_PCID && cpu.current_pcid == pcid && cpu.current_pagetable is Some {
        cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_id); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id);
        process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, cpu.current_process->Some_0); kernel_process_user_projection_at(krnl, cpu.current_process->Some_0);
    }
    assert(kernel_k_to_kernel_u(*krnl) == kernel_k_user_projection(*krnl)) by { reveal(kernel_k_to_kernel_u); };
}

/// Under the kernel invariant, what the IOTLB may cache for domain `did` in K it may also cache in the user projection; a
/// zombie anchor owner's emptied IOMMU table backs no translation.
pub proof fn kernel_iommu_tlb_within_may_cache_projection(krnl: &KernelK, did: VtdDomainId, tlb: SingleTLB)
    requires
        krnl.inv(),
        vtd_domain_id_valid(did),
        iommu_tlb_within_may_cache(*krnl, did, tlb),
    ensures
        iommu_tlb_within_may_cache_u(kernel_k_user_projection(*krnl), did, tlb),
        iommu_tlb_within_may_cache_u(kernel_k_to_kernel_u(*krnl), did, tlb),
{
    let anchor = pci_bdf_of_did(did);
    let root_table = krnl.irt.view();
    kernel_u_user_domains_projection(krnl); root_table.user_view_unfold();
    if root_table.spec_index_iommu_did(anchor.0, anchor.1, anchor.2) == Some(did) {
        let owner = root_table.spec_index_owner(anchor.0, anchor.1, anchor.2);
        let it = krnl.prc_mp.spec_index(owner).view().iommu_table->Some_0;
        assert({
            &&& krnl.prc_mp.dom().contains(owner)
            &&& root_table.spec_index_iommu_root(anchor.0, anchor.1, anchor.2) is Some
            &&& krnl.prc_mp.spec_index(owner).view().iommu_table is Some
            &&& krnl.it_mp.dom().contains(it)
            &&& krnl.it_mp.spec_index(it).view().did == Some(did)
        }) by { reveal(iommu_root_table_process_wf); root_table.context_wf_at(anchor.0, anchor.1, anchor.2); };
        process_perms_wf_at(krnl.prc_mp, owner); kernel_process_user_projection_at(krnl, owner);
        process_emptied_tables_wf_at(krnl.prc_mp, krnl.pt_mp, krnl.pt_lower.view(), krnl.it_mp, owner); pagetable_no_huge_leaf_wf_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.it_mp, it);
        if krnl.prc_mp.spec_index(owner).view().zombie {
            assert(tlb.tlb_4k().dom() =~= Set::<VAddr>::empty() && tlb.tlb_2m().dom() =~= Set::<VAddr>::empty() && tlb.tlb_1g().dom() =~= Set::<VAddr>::empty());
        }
    }
    assert(kernel_k_to_kernel_u(*krnl) == kernel_k_user_projection(*krnl)) by { reveal(kernel_k_to_kernel_u); };
}

/// A CPU TLB fill under the kernel invariant is the matching user TLB fill in the projection.
pub proof fn kernel_k_cpu_tlb_filled_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, pcid: Pcid, added: SingleTLB)
    requires
        pre.inv(),
        kernel_k_cpu_tlb_filled(*pre, *post, cpu_id, pcid, added),
    ensures
        kernel_u_cpu_tlb_filled_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id, pcid, added),
{
    reveal(kernel_u_cpu_tlb_filled_step); reveal(kernel_k_to_kernel_u);
    kernel_cpu_tlb_within_may_cache_projection(pre, cpu_id, pcid, added);
}

/// An IOTLB fill under the kernel invariant is the matching user IOTLB fill in the projection.
pub proof fn kernel_k_iommu_tlb_filled_implies_u_step(pre: &KernelK, post: &KernelK, did: VtdDomainId, added: SingleTLB)
    requires
        pre.inv(),
        kernel_k_iommu_tlb_filled(*pre, *post, did, added),
    ensures
        kernel_u_iommu_tlb_filled_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), did, added),
{
    reveal(kernel_u_iommu_tlb_filled_step); reveal(kernel_k_to_kernel_u);
    kernel_iommu_tlb_within_may_cache_projection(pre, did, added);
}

/// A context-cache fill changes neither projection.
pub proof fn kernel_k_iommu_context_cache_filled_implies_u_step(pre: &KernelK, post: &KernelK, bdf: PciBdf, entry: (PageTableRoot, VtdDomainId))
    requires kernel_k_iommu_context_cache_filled(*pre, *post, bdf, entry),
    ensures
        kernel_u_iommu_context_cache_filled_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post)),
{
    reveal(kernel_u_iommu_context_cache_filled_step); reveal(kernel_k_to_kernel_u);
}

/// A trap entry under the kernel invariant is the user trap entry.
pub proof fn kernel_k_trap_enter_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId)
    requires
        pre.inv(),
        kernel_k_trap_enter(*pre, *post, cpu_id),
    ensures
        kernel_u_trap_enter_step_pre(kernel_k_to_kernel_u(*pre), cpu_id),
        kernel_u_trap_enter_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id),
{
    let pre_u = kernel_k_to_kernel_u(*pre);
    reveal(kernel_u_trap_enter_step_pre); reveal(kernel_u_trap_enter_step); reveal(kernel_k_to_kernel_u);
    cpu_op_wf_at(pre.cpu_op.view().view(), pre.cpu_arr, cpu_id);
    assert(kernel_k_to_kernel_u(*post).cpu_array =~= pre_u.cpu_array.update(cpu_id as int, CpuU { op: CpuOpState::Trap, ..pre_u.cpu_array[cpu_id as int] }));
}

/// A trap return under the kernel invariant is the user trap return.
pub proof fn kernel_k_trap_return_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId)
    requires
        pre.inv(),
        kernel_k_trap_return(*pre, *post, cpu_id),
    ensures
        kernel_u_trap_return_step_pre(kernel_k_to_kernel_u(*pre), cpu_id),
        kernel_u_trap_return_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id),
{
    let pre_u = kernel_k_to_kernel_u(*pre);
    reveal(kernel_u_trap_return_step_pre); reveal(kernel_u_trap_return_step); reveal(kernel_k_to_kernel_u);
    cpu_op_wf_at(pre.cpu_op.view().view(), pre.cpu_arr, cpu_id);
    assert(kernel_k_to_kernel_u(*post).cpu_array =~= pre_u.cpu_array.update(cpu_id as int, CpuU { op: CpuOpState::User, ..pre_u.cpu_array[cpu_id as int] }));
}

/// A trap divert under the kernel invariant is the user trap divert.
pub proof fn kernel_k_trap_divert_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId)
    requires
        pre.inv(),
        kernel_k_trap_divert(*pre, *post, cpu_id),
    ensures
        kernel_u_trap_divert_step_pre(kernel_k_to_kernel_u(*pre), cpu_id),
        kernel_u_trap_divert_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id),
{
    let pre_u = kernel_k_to_kernel_u(*pre);
    reveal(kernel_u_trap_divert_step_pre); reveal(kernel_u_trap_divert_step); reveal(kernel_k_to_kernel_u);
    cpu_op_wf_at(pre.cpu_op.view().view(), pre.cpu_arr, cpu_id);
    assert(kernel_k_to_kernel_u(*post).cpu_array =~= pre_u.cpu_array.update(cpu_id as int, CpuU { op: CpuOpState::Idle, ..pre_u.cpu_array[cpu_id as int] }));
}
}
