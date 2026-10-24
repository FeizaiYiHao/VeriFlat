use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::flush_iommu_tlb_eof::flush_iommu_tlb_for_table_eof;

verus! {
/// Flushes every IOTLB domain, so each domain attached to the write-held IOMMU table `iommu_table` caches only present
/// leaves again. The flush changes the user-visible IOTLB, so it runs inside a released kernel-view section.
pub fn flush_iommu_tlb_for_table(krnl: &mut KernelK, iommu_table: RwLockPageTableRoot, Tracked(lctx): Tracked<&LocalContext>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), lctx),
        lctx.kernel_view_locking_state() is Release,
        old(krnl).it_mp.dom().contains(iommu_table),
        typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), iommu_table, TypedLockMode::Write),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), lctx),
        *final(krnl) == (KernelK { iommu_tlb: final(krnl).iommu_tlb, ..*old(krnl) }),
        final(krnl).iommu_tlb.view().dom() == old(krnl).iommu_tlb.view().dom(),
        forall|did: VtdDomainId| #![trigger final(krnl).iommu_tlb.spec_index(did)] vtd_domain_id_valid(did) ==> final(krnl).iommu_tlb.spec_index(did).is_empty(),
        final(krnl).iommu_tlb.context_cache() == old(krnl).iommu_tlb.context_cache(),
        iommu_table_tlb_entries_present(final(krnl).iommu_tlb, final(krnl).irt.view(), final(krnl).it_mp, iommu_table),
{
    krnl.iommu_tlb.flush_all_iotlb();
    proof { flush_iommu_tlb_for_table_eof(*old(krnl), *krnl, iommu_table); }
}
}
