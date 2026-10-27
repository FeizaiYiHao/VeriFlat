use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::flush_iommu_tlb_eof::flush_iommu_tlb_for_table_eof;

verus! {
/// Invalidates the IOTLB domain of the write-held IOMMU table `iommu_table`, if it has one, so that domain caches only
/// present leaves again; a table without a DID touches no hardware. The context cache is untouched. The invalidation
/// changes the user-visible IOTLB, so it runs inside a released kernel-view section.
pub fn flush_iommu_tlb_for_table(krnl: &mut KernelK, iommu_table: RwLockPageTableRoot, Tracked(lctx): Tracked<&LocalContext>, iommu_table_perm: Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), lctx),
        lctx.kernel_view_locking_state() is Release,
        old(krnl).it_mp.dom().contains(iommu_table),
        typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), iommu_table, TypedLockMode::Write),
        iommu_table_perm.view().state() is WriteLock,
        iommu_table_perm.view().thread_id() == lctx.thread_id(),
        iommu_table_perm.view().lock_id() == old(krnl).it_mp.spec_index(iommu_table).locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), lctx),
        *final(krnl) == (KernelK { iommu_tlb: final(krnl).iommu_tlb, ..*old(krnl) }),
        final(krnl).iommu_tlb.context_cache() == old(krnl).iommu_tlb.context_cache(),
        old(krnl).it_mp.spec_index(iommu_table).view().did matches Some(did)
            ==> final(krnl).iommu_tlb.view() == old(krnl).iommu_tlb.view().insert(did, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
        old(krnl).it_mp.spec_index(iommu_table).view().did is None ==> final(krnl).iommu_tlb == old(krnl).iommu_tlb,
        iommu_table_tlb_entries_present(final(krnl).iommu_tlb, final(krnl).irt.view(), final(krnl).it_mp, iommu_table),
{
    assert(krnl.it_mp.perms_wf() && krnl.it_mp.spec_index(iommu_table).is_init() && krnl.it_mp.spec_index(iommu_table).view().inv()) by {
        iommu_table_perms_wf_map(krnl.it_mp); iommu_table_perms_wf_at(krnl.it_mp, iommu_table);
    };
    let did = krnl.it_mp.borrow_typed(iommu_table, Ghost(lctx.iommu_table_lock_map()), Tracked(lctx), iommu_table_perm).did;
    if let Some(d) = did { krnl.iommu_tlb.invalidate_iotlb_domain(d, Tracked(lctx)); }
    proof { flush_iommu_tlb_for_table_eof(*old(krnl), *krnl, iommu_table); }
}
}
