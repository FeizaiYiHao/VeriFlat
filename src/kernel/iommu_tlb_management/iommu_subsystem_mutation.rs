use vstd::prelude::*;
use crate::*;

verus! {
/// Detaches one B/D/F under the held root-table lock, hands its slot to `owner`, and flushes its IOTLB domain.
pub fn iommu_root_table_reassign_detached(
    irt: &mut IommuRootTableLock, iommu_tlb: &mut IommuTLB, bus: usize, device: usize, function: usize, owner: RwLockProcessPtr,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(irt_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(irt).inv(),
        old(iommu_tlb).inv(),
        pci_bdf_valid(bus, device, function),
        iommu_root_table_typed_lock_map_aligned(*old(irt), lctx.iommu_root_table_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.iommu_root_table_lock_map(), old(irt).view().table_base(), TypedLockMode::Write),
        irt_lock_perm.state() is WriteLock,
        irt_lock_perm.thread_id() == lctx.thread_id(),
        irt_lock_perm.lock_id() == old(irt).locking_thread()->Write_lock_id,
    ensures
        final(irt).inv(),
        iommu_root_table_typed_lock_map_aligned(*final(irt), lctx.iommu_root_table_lock_map(), lctx.thread_id()),
        final(irt).locking_thread() == old(irt).locking_thread(),
        final(irt).view().table_base() == old(irt).view().table_base(),
        final(irt).view().owners() == seq3_update(old(irt).view().owners(), bus as int, device as int, function as int, owner),
        final(irt).view().iommu_roots() == seq3_update(old(irt).view().iommu_roots(), bus as int, device as int, function as int, None),
        forall|b: usize, d: usize, f: usize| #![trigger final(irt).view().spec_index_owner(b, d, f)] #![trigger final(irt).view().spec_index_iommu_root(b, d, f)] pci_bdf_valid(b, d, f) ==> {
            &&& final(irt).view().spec_index_owner(b, d, f) == if (b, d, f) == (bus, device, function) { owner } else { old(irt).view().spec_index_owner(b, d, f) }
            &&& final(irt).view().spec_index_iommu_root(b, d, f) == if (b, d, f) == (bus, device, function) { None } else { old(irt).view().spec_index_iommu_root(b, d, f) }
        },
        final(iommu_tlb).inv(),
        final(iommu_tlb).view() == old(iommu_tlb).view().insert(pci_bdf_did(bus, device, function), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
{
    assert(irt.wlocked_by(lctx)) by { reveal(iommu_root_table_typed_lock_map_aligned); };
    let table = irt.borrow_mut(Tracked(lctx), Tracked(irt_lock_perm));
    table.detach(bus, device, function);
    table.set_owner(bus, device, function, owner);
    let did = IommuRootTable::pci_bdf_slot(bus, device, function);
    iommu_tlb.invalidate_domain(did, Tracked(lctx));
    proof { assert(iommu_root_table_typed_lock_map_aligned(*irt, lctx.iommu_root_table_lock_map(), lctx.thread_id())) by { reveal(iommu_root_table_typed_lock_map_aligned); }; }
}

/// Points one B/D/F's context entry at `root` under the held root-table lock; owners are untouched.
pub fn iommu_root_table_attach(
    irt: &mut IommuRootTableLock, bus: usize, device: usize, function: usize, root: PageTableRoot, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(irt_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(irt).inv(),
        pci_bdf_valid(bus, device, function),
        page_ptr_valid(root),
        iommu_root_table_typed_lock_map_aligned(*old(irt), lctx.iommu_root_table_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.iommu_root_table_lock_map(), old(irt).view().table_base(), TypedLockMode::Write),
        irt_lock_perm.state() is WriteLock,
        irt_lock_perm.thread_id() == lctx.thread_id(),
        irt_lock_perm.lock_id() == old(irt).locking_thread()->Write_lock_id,
    ensures
        final(irt).inv(),
        iommu_root_table_typed_lock_map_aligned(*final(irt), lctx.iommu_root_table_lock_map(), lctx.thread_id()),
        final(irt).locking_thread() == old(irt).locking_thread(),
        final(irt).view().table_base() == old(irt).view().table_base(),
        final(irt).view().owners() == old(irt).view().owners(),
        final(irt).view().iommu_roots() == seq3_update(old(irt).view().iommu_roots(), bus as int, device as int, function as int, Some(root)),
        forall|b: usize, d: usize, f: usize| #![trigger final(irt).view().spec_index_owner(b, d, f)] #![trigger final(irt).view().spec_index_iommu_root(b, d, f)] pci_bdf_valid(b, d, f) ==> {
            &&& final(irt).view().spec_index_owner(b, d, f) == old(irt).view().spec_index_owner(b, d, f)
            &&& final(irt).view().spec_index_iommu_root(b, d, f) == if (b, d, f) == (bus, device, function) { Some(root) } else { old(irt).view().spec_index_iommu_root(b, d, f) }
        },
{
    assert(irt.wlocked_by(lctx)) by { reveal(iommu_root_table_typed_lock_map_aligned); };
    let table = irt.borrow_mut(Tracked(lctx), Tracked(irt_lock_perm));
    table.attach(bus, device, function, root);
    proof { assert(iommu_root_table_typed_lock_map_aligned(*irt, lctx.iommu_root_table_lock_map(), lctx.thread_id())) by { reveal(iommu_root_table_typed_lock_map_aligned); }; }
}
}
