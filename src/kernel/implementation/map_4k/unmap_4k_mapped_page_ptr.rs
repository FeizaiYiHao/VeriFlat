use vstd::prelude::*;
use crate::*;

verus! {
/// Reads the page that the 4K leaf of `indices` maps in a write-locked IOMMU table and the L1 page holding that leaf.
pub(super) fn unmap_iommu_4k_mapped_page_ptr(
    krnl: &KernelK, iommu_table: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index), Tracked(lctx): Tracked<&LocalContext>, iommu_table_perm: Tracked<&LockPerm>,
) -> (ret: (PagePtr, PageMapPtr))
    requires
        typed_lock_maps_aligned(krnl, lctx),
        krnl.it_mp.perms_wf(),
        krnl.it_mp.dom().contains(iommu_table),
        krnl.it_mp.spec_index(iommu_table).inv(),
        krnl.it_mp.spec_index(iommu_table).view().inv(),
        krnl.it_mp.spec_index(iommu_table).view().kernel_l4_end == 0,
        typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), iommu_table, TypedLockMode::Write),
        iommu_table_perm.view().state() is WriteLock,
        iommu_table_perm.view().thread_id() == lctx.thread_id(),
        iommu_table_perm.view().lock_id() == krnl.it_mp.spec_index(iommu_table).locking_thread()->Write_lock_id,
        pei_valid(indices.0) && pei_valid(indices.1) && pei_valid(indices.2) && pei_valid(indices.3),
        krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va(indices)),
    ensures
        ret.0 == krnl.it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(spec_index2va(indices)).addr,
        krnl.it_mp.spec_index(iommu_table).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        krnl.it_mp.spec_index(iommu_table).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == ret.1,
{
    let it = krnl.it_mp.borrow_typed(iommu_table, Ghost(lctx.iommu_table_lock_map()), Tracked(lctx), iommu_table_perm);
    assert(it.spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some) by { reveal(PageTable::wf_mapping_4k); };
    let l4 = it.get_entry_l4(indices.0).unwrap();
    let l3 = it.get_entry_l3(indices.0, indices.1, &l4).unwrap();
    let l2 = it.get_entry_l2(indices.0, indices.1, indices.2, &l3).unwrap();
    (it.get_entry_l1(indices.0, indices.1, indices.2, indices.3, &l2).unwrap().addr, l2.addr)
}
}
