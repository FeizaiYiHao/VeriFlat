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

/// Reads the page that the 4K leaf `va` maps in the read- or write-locked page table `pagetable`.
pub(super) fn unmap_4k_mapped_page_ptr(
    krnl: &KernelK, pagetable: RwLockPageTableRoot, va: VAddr, indices: (L4Index, L3Index, L2Index, L1Index), Tracked(lctx): Tracked<&LocalContext>, pagetable_perm: Tracked<&LockPerm>,
) -> (pg_ptr: PagePtr)
    requires
        krnl.inv(),
        typed_lock_maps_aligned(krnl, lctx),
        krnl.pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        indices == spec_va2index(va),
        krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= indices.0,
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        pagetable_perm.view().thread_id() == lctx.thread_id(),
        pagetable_perm.view().state() is WriteLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock ==> pagetable_perm.view().lock_id() == krnl.pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        pagetable_perm.view().state() is ReadLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Read),
        pagetable_perm.view().state() is ReadLock ==> krnl.pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), pagetable_perm.view().lock_id()),
    ensures
        pg_ptr == whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(va).addr,
        page_ptr_valid(pg_ptr),
{
    proof {
        spec_va_4k_index_roundtrip_at(va, indices.0, indices.1, indices.2, indices.3);
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).wf_mapping_4k_at(indices.0, indices.1, indices.2, indices.3);
    }
    let pt = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(lctx), pagetable_perm);
    let tracked lower = krnl.pt_lower.borrow().tracked_borrow(pagetable);
    let l4 = pt.get_entry_l4(indices.0).unwrap();
    let l3 = pt.get_entry_l3(indices.0, indices.1, &l4).unwrap();
    let l2 = pt.get_entry_l2(Tracked(lower), indices.0, indices.1, indices.2, &l3).unwrap();
    pt.get_entry_l1(Tracked(lower), indices.0, indices.1, indices.2, indices.3, &l3, &l2).unwrap().addr
}

/// Reads the L2 and L1 pages on the path to the 4K leaf `va` of the read- or write-locked page table `pagetable`.
pub(super) fn unmap_4k_leaf_table_ptrs(
    krnl: &KernelK, pagetable: RwLockPageTableRoot, va: VAddr, indices: (L4Index, L3Index, L2Index, L1Index), Tracked(lctx): Tracked<&LocalContext>, pagetable_perm: Tracked<&LockPerm>,
) -> (ret: (PageMapPtr, PageMapPtr))
    requires
        krnl.inv(),
        typed_lock_maps_aligned(krnl, lctx),
        krnl.pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        indices == spec_va2index(va),
        krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= indices.0,
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        pagetable_perm.view().thread_id() == lctx.thread_id(),
        pagetable_perm.view().state() is WriteLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock ==> pagetable_perm.view().lock_id() == krnl.pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        pagetable_perm.view().state() is ReadLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Read),
        pagetable_perm.view().state() is ReadLock ==> krnl.pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), pagetable_perm.view().lock_id()),
    ensures
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == ret.0,
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == ret.1,
{
    proof {
        spec_va_4k_index_roundtrip_at(va, indices.0, indices.1, indices.2, indices.3);
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).wf_mapping_4k_at(indices.0, indices.1, indices.2, indices.3);
    }
    let pt = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(lctx), pagetable_perm);
    let tracked lower = krnl.pt_lower.borrow().tracked_borrow(pagetable);
    let l4 = pt.get_entry_l4(indices.0).unwrap();
    let l3 = pt.get_entry_l3(indices.0, indices.1, &l4).unwrap();
    let l2 = pt.get_entry_l2(Tracked(lower), indices.0, indices.1, indices.2, &l3).unwrap();
    (l3.addr, l2.addr)
}
}
