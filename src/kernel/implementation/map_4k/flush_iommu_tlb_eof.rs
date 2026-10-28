use vstd::prelude::*;
use crate::*;

verus! {
/// Invalidating the IOTLB domain of IOMMU table `iommu_table`, which then holds at most what the unit may cache, or nothing
/// when it has no DID, keeps the context cache; every other kernel field is unchanged.
pub(super) proof fn flush_iommu_tlb_for_table_eof(pre: KernelK, post: KernelK, iommu_table: RwLockPageTableRoot)
    requires
        pre.inv(),
        pre.it_mp.dom().contains(iommu_table),
        post == (KernelK { iommu_tlb: post.iommu_tlb, ..pre }),
        post.iommu_tlb.inv(),
        post.iommu_tlb.context_cache() == pre.iommu_tlb.context_cache(),
        pre.it_mp.spec_index(iommu_table).view().did matches Some(did) ==> iommu_tlb_within_may_cache(pre, did, post.iommu_tlb.spec_index(did)),
        pre.it_mp.spec_index(iommu_table).view().did matches Some(did)
            ==> forall|x: VtdDomainId| #![trigger post.iommu_tlb.spec_index(x)] x != did ==> post.iommu_tlb.spec_index(x) == pre.iommu_tlb.spec_index(x),
        pre.it_mp.spec_index(iommu_table).view().did is None ==> post.iommu_tlb == pre.iommu_tlb,
    ensures
        post.inv(),
        iommu_table_tlb_entries_present(post.iommu_tlb, post.irt.view(), post.it_mp, iommu_table),
{
    reveal(iommu_tlb_wf_spec);
    if let Some(did) = pre.it_mp.spec_index(iommu_table).view().did {
        let owner = pre.it_mp.spec_index(iommu_table).view().proc_ptr;
        assert(pre.prc_mp.dom().contains(owner) && pre.prc_mp.spec_index(owner).view().iommu_table == Some(iommu_table)) by { reveal(process_iommu_table_match); };
        iommu_root_table_process_wf_table_at(pre.irt.view(), pre.prc_mp, pre.it_mp, iommu_table);
        assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    }
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(iommu_table_tlb_entries_present(post.iommu_tlb, post.irt.view(), post.it_mp, iommu_table)) by { reveal(iommu_table_tlb_entries_present); };
}
}
