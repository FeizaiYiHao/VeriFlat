use vstd::prelude::*;
use crate::*;

verus! {
/// A global IOTLB flush empties every domain and keeps the context cache; every other kernel field is unchanged.
pub(super) proof fn flush_iommu_tlb_for_table_eof(pre: KernelK, post: KernelK, iommu_table: RwLockPageTableRoot)
    requires
        pre.inv(),
        post == (KernelK { iommu_tlb: post.iommu_tlb, ..pre }),
        post.iommu_tlb.inv(),
        forall|did: VtdDomainId| #![trigger post.iommu_tlb.spec_index(did)] vtd_domain_id_valid(did) ==> post.iommu_tlb.spec_index(did).is_empty(),
        post.iommu_tlb.context_cache() == pre.iommu_tlb.context_cache(),
    ensures
        post.inv(),
        iommu_table_tlb_entries_present(post.iommu_tlb, post.irt.view(), post.it_mp, iommu_table),
{
    reveal(iommu_tlb_wf_spec);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(iommu_table_tlb_entries_present(post.iommu_tlb, post.irt.view(), post.it_mp, iommu_table)) by { reveal(iommu_table_tlb_entries_present); };
}
}
