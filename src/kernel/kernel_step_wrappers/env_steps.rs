use vstd::prelude::*;
use crate::*;

verus! {
/// Under the kernel invariant, what CPU `cpu_id` may cache under `pcid` in K it may also cache in the user projection.
pub proof fn kernel_cpu_tlb_within_may_cache_projection(krnl: &KernelK, cpu_id: CpuId, pcid: Pcid, tlb: SingleTLB, cache: PagingStructureCache)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        cpu_tlb_within_may_cache(*krnl, cpu_id, pcid, tlb, cache),
    ensures
        cpu_tlb_within_may_cache_u(kernel_k_user_projection(*krnl), cpu_id, pcid, tlb),
        cpu_tlb_within_may_cache_u(kernel_k_to_kernel_u(*krnl), cpu_id, pcid, tlb),
{
    let cpu = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
    kernel_cpu_user_projection_at(krnl, cpu_id);
    if pcid != KERNEL_DEFAULT_PCID && cpu.current_pcid == pcid && cpu.current_pagetable is Some {
        cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_id); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id);
        process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, cpu.current_process->Some_0); kernel_process_user_projection_at(krnl, cpu.current_process->Some_0);
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), cpu.current_pagetable->Some_0); reveal(WholePageTable::wf_mapping_4k); reveal(WholePageTable::wf_mapping_2m);
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, WholePageTable::spec_resolve_mapping_4k_l1_some_implies_spec_held_4k_l1_eq, WholePageTable::spec_resolve_mapping_2m_l2_some_implies_spec_held_2m_l2_eq;
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
    kernel_u_user_domains_projection(krnl); root_table.user_view_eq_owners_and_attached();
    if root_table.spec_index_iommu_did(anchor.0, anchor.1, anchor.2) == Some(did) {
        let owner = root_table.spec_index_owner(anchor.0, anchor.1, anchor.2);
        let it = krnl.prc_mp.spec_index(owner).view().iommu_table->Some_0;
        assert({
            &&& krnl.prc_mp.dom().contains(owner)
            &&& root_table.spec_index_iommu_root(anchor.0, anchor.1, anchor.2) is Some
            &&& krnl.prc_mp.spec_index(owner).view().iommu_table is Some
            &&& krnl.it_mp.dom().contains(it)
            &&& krnl.it_mp.spec_index(it).view().did == Some(did)
        }) by { reveal(iommu_root_table_process_wf); root_table.wf_context_entry_at(anchor.0, anchor.1, anchor.2); };
        process_perms_wf_at(krnl.prc_mp, owner); kernel_process_user_projection_at(krnl, owner);
        process_emptied_tables_wf_at(krnl.prc_mp, krnl.pt_mp, krnl.pt_lower.view(), krnl.it_mp, krnl.pg_arr, owner); iommu_table_no_huge_leaf_wf_at(krnl.it_mp, it);
        if krnl.prc_mp.spec_index(owner).view().zombie {
            assert(tlb.tlb_4k().dom() =~= Set::<VAddr>::empty() && tlb.tlb_2m().dom() =~= Set::<VAddr>::empty() && tlb.tlb_1g().dom() =~= Set::<VAddr>::empty());
        }
    }
    assert(kernel_k_to_kernel_u(*krnl) == kernel_k_user_projection(*krnl)) by { reveal(kernel_k_to_kernel_u); };
}
}
