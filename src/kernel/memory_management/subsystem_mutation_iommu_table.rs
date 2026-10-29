use vstd::prelude::*;
use crate::*;
use super::subsystem_mutation_eof::*;
use vstd::simple_pptr::PointsTo;

verus! {
/// IOMMU-table mirrors of the 4K unmap helpers `pagetable_map_clear_4k_present`, `pagetable_map_unmap_4k_kernel`,
/// `page_array_remove_4k_mapping_without_free`, and `page_array_remove_last_4k_mapping_to_cache`: the table is an
/// `IommuTableLockedMap` entry held under `iommu_table_lock_map`, and the page's reverse map is `iommu_mappings`. IOMMU
/// pages are never MMIO.
pub fn iommu_table_map_clear_4k_present(iommu_table_map: &mut IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index), target_l1_ptr: PageMapPtr, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(iommu_table_lock_perm): Tracked<&LockPerm>)
    requires
        iommu_table_perms_wf(*old(iommu_table_map)),
        old(iommu_table_map).dom().contains(iommu_table_ptr),
        old(iommu_table_map).typed_lock_map_aligned(old(lctx).iommu_table_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        iommu_table_lock_perm.state() is WriteLock,
        iommu_table_lock_perm.thread_id() == old(lctx).thread_id(),
        iommu_table_lock_perm.lock_id() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_l4_end <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        old(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        old(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_4k().dom().contains(spec_index2va(indices)),
    ensures
        iommu_table_perms_wf(*final(iommu_table_map)),
        final(iommu_table_map).perms_wf(),
        final(iommu_table_map).unchanged_except(old(iommu_table_map), iommu_table_ptr),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(iommu_table_map).typed_lock_map_aligned(final(lctx).iommu_table_lock_map(), final(lctx).thread_id()),
        final(iommu_table_map).lock_id_by_key(iommu_table_ptr) == old(iommu_table_map).lock_id_by_key(iommu_table_ptr),
        final(iommu_table_map).spec_index(iommu_table_ptr).locking_thread() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread(),
        final(iommu_table_map).spec_index(iommu_table_ptr).being_killed() == old(iommu_table_map).spec_index(iommu_table_ptr).being_killed(),
        final(iommu_table_map).spec_index(iommu_table_ptr).wlocked_by(final(lctx)),
        final(iommu_table_map).spec_index(iommu_table_ptr).inv(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_l4_end == old(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_l4_end,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().page_closure() == old(iommu_table_map).spec_index(iommu_table_ptr).view().page_closure(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_4k() == old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_4k().insert(spec_index2va(indices),
            MapEntry { present: false, ..old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_4k().spec_index(spec_index2va(indices)) }),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_2m() == old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_2m(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_1g() == old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_1g(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_entries == old(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_entries,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().cr3 == old(iommu_table_map).spec_index(iommu_table_ptr).view().cr3,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().pcid == old(iommu_table_map).spec_index(iommu_table_ptr).view().pcid,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().did == old(iommu_table_map).spec_index(iommu_table_ptr).view().did,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr == old(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr,
{
    assert(iommu_table_map.perms_wf() && iommu_table_map.spec_index(iommu_table_ptr).inv()) by { iommu_table_perms_wf_map(*iommu_table_map); iommu_table_perms_wf_at(*iommu_table_map, iommu_table_ptr); };
    let iommu_table = iommu_table_map.borrow_mut_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_table_lock_perm));
    iommu_table.unmap_4k_page_user_view(indices.0, indices.1, indices.2, indices.3, target_l1_ptr, Tracked(&mut *lctx));
    proof {
        assert(iommu_table_map_clear_4k_present_eof_transition_framing(*old(iommu_table_map), *iommu_table_map, iommu_table_ptr)) by { reveal(iommu_table_map_clear_4k_present_eof_transition_framing); };
        iommu_table_map_clear_4k_present_eof(*old(iommu_table_map), *iommu_table_map, iommu_table_ptr);
    }
}

/// Sets the VT-d domain ID of the write-held IOMMU table `iommu_table_ptr`; its mappings, topology, owner, and lock state are untouched.
pub fn iommu_table_map_set_did(
    iommu_table_map: &mut IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot, did: Option<VtdDomainId>, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(iommu_table_lock_perm): Tracked<&LockPerm>,
)
    requires
        iommu_table_perms_wf(*old(iommu_table_map)),
        old(iommu_table_map).dom().contains(iommu_table_ptr),
        old(iommu_table_map).typed_lock_map_aligned(lctx.iommu_table_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        iommu_table_lock_perm.state() is WriteLock,
        iommu_table_lock_perm.thread_id() == lctx.thread_id(),
        iommu_table_lock_perm.lock_id() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
        did matches Some(d) ==> vtd_domain_id_valid(d),
    ensures
        iommu_table_perms_wf(*final(iommu_table_map)),
        final(iommu_table_map).unchanged_except(old(iommu_table_map), iommu_table_ptr),
        final(iommu_table_map).typed_lock_map_aligned(lctx.iommu_table_lock_map(), lctx.thread_id()),
        final(iommu_table_map).lock_id_by_key(iommu_table_ptr) == old(iommu_table_map).lock_id_by_key(iommu_table_ptr),
        final(iommu_table_map).spec_index(iommu_table_ptr).locking_thread() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread(),
        final(iommu_table_map).spec_index(iommu_table_ptr).being_killed() == old(iommu_table_map).spec_index(iommu_table_ptr).being_killed(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view() == (PageTable { did, ..old(iommu_table_map).spec_index(iommu_table_ptr).view() }),
{
    assert(iommu_table_map.perms_wf() && iommu_table_map.spec_index(iommu_table_ptr).inv()) by { iommu_table_perms_wf_map(*iommu_table_map); iommu_table_perms_wf_at(*iommu_table_map, iommu_table_ptr); };
    let iommu_table = iommu_table_map.borrow_mut_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(lctx), Tracked(iommu_table_lock_perm));
    iommu_table.did = did;
    proof {
        assert(iommu_table_map_set_did_eof_transition_framing(*old(iommu_table_map), *iommu_table_map, iommu_table_ptr, did)) by {
            reveal(iommu_table_map_set_did_eof_transition_framing);
        };
        iommu_table_map_set_did_eof(*old(iommu_table_map), *iommu_table_map, iommu_table_ptr, did);
    }
}

pub fn iommu_table_map_unmap_4k_kernel(iommu_table_map: &mut IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index), target_l1_ptr: PageMapPtr, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(iommu_table_lock_perm): Tracked<&LockPerm>)
    requires
        iommu_table_perms_wf(*old(iommu_table_map)),
        old(iommu_table_map).dom().contains(iommu_table_ptr),
        old(iommu_table_map).typed_lock_map_aligned(old(lctx).iommu_table_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        iommu_table_lock_perm.state() is WriteLock,
        iommu_table_lock_perm.thread_id() == old(lctx).thread_id(),
        iommu_table_lock_perm.lock_id() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_l4_end <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        old(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        old(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_4k().dom().contains(spec_index2va(indices)),
        !old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_4k().spec_index(spec_index2va(indices)).present || old(iommu_table_map).spec_index(iommu_table_ptr).view().did is None,
    ensures
        iommu_table_perms_wf(*final(iommu_table_map)),
        final(iommu_table_map).perms_wf(),
        final(iommu_table_map).unchanged_except(old(iommu_table_map), iommu_table_ptr),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(iommu_table_map).typed_lock_map_aligned(final(lctx).iommu_table_lock_map(), final(lctx).thread_id()),
        final(iommu_table_map).lock_id_by_key(iommu_table_ptr) == old(iommu_table_map).lock_id_by_key(iommu_table_ptr),
        final(iommu_table_map).spec_index(iommu_table_ptr).locking_thread() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread(),
        final(iommu_table_map).spec_index(iommu_table_ptr).being_killed() == old(iommu_table_map).spec_index(iommu_table_ptr).being_killed(),
        final(iommu_table_map).spec_index(iommu_table_ptr).wlocked_by(final(lctx)),
        final(iommu_table_map).spec_index(iommu_table_ptr).inv(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_l4_end == old(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_l4_end,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().page_closure() == old(iommu_table_map).spec_index(iommu_table_ptr).view().page_closure(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_4k() == old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_4k().remove(spec_index2va(indices)),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_2m() == old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_2m(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_1g() == old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_1g(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_entries == old(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_entries,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().cr3 == old(iommu_table_map).spec_index(iommu_table_ptr).view().cr3,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().pcid == old(iommu_table_map).spec_index(iommu_table_ptr).view().pcid,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().did == old(iommu_table_map).spec_index(iommu_table_ptr).view().did,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr == old(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr,
{
    assert(iommu_table_map.perms_wf() && iommu_table_map.spec_index(iommu_table_ptr).inv()) by { iommu_table_perms_wf_map(*iommu_table_map); iommu_table_perms_wf_at(*iommu_table_map, iommu_table_ptr); };
    let iommu_table = iommu_table_map.borrow_mut_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_table_lock_perm));
    iommu_table.unmap_4k_page_kernel(indices.0, indices.1, indices.2, indices.3, target_l1_ptr, Tracked(&mut *lctx));
    proof {
        assert(iommu_table_map_unmap_4k_kernel_eof_transition_framing(*old(iommu_table_map), *iommu_table_map, iommu_table_ptr)) by { reveal(iommu_table_map_unmap_4k_kernel_eof_transition_framing); };
        iommu_table_map_unmap_4k_kernel_eof(*old(iommu_table_map), *iommu_table_map, iommu_table_ptr);
    }
}

/// IOMMU mirror of `pagetable_map_insert_4k_wlocked`: install the present 4K leaf `target_entry` at `indices` of the write-held
/// IOMMU table `iommu_table_ptr`, whose L1 page `target_l1_ptr` is already linked.
pub fn iommu_table_map_insert_4k(
    iommu_table_map: &mut IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index), target_l1_ptr: PageMapPtr, target_entry: &MapEntry,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(iommu_table_lock_perm): Tracked<&LockPerm>,
)
    requires
        iommu_table_perms_wf(*old(iommu_table_map)),
        old(iommu_table_map).dom().contains(iommu_table_ptr),
        old(iommu_table_map).typed_lock_map_aligned(old(lctx).iommu_table_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        iommu_table_lock_perm.state() is WriteLock,
        iommu_table_lock_perm.thread_id() == old(lctx).thread_id(),
        iommu_table_lock_perm.lock_id() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_l4_end <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        page_table_key_4k_valid::<IOMMU_TYPE>(spec_index2va(indices)),
        old(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        old(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        old(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_4k_l1(indices.0, indices.1, indices.2, indices.3) is None
            || !old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_4k().dom().contains(spec_index2va(indices)),
        page_ptr_valid(target_entry.addr),
        target_entry.present,
    ensures
        iommu_table_perms_wf(*final(iommu_table_map)),
        final(iommu_table_map).perms_wf(),
        final(iommu_table_map).unchanged_except(old(iommu_table_map), iommu_table_ptr),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(iommu_table_map).typed_lock_map_aligned(final(lctx).iommu_table_lock_map(), final(lctx).thread_id()),
        final(iommu_table_map).lock_id_by_key(iommu_table_ptr) == old(iommu_table_map).lock_id_by_key(iommu_table_ptr),
        final(iommu_table_map).spec_index(iommu_table_ptr).locking_thread() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread(),
        final(iommu_table_map).spec_index(iommu_table_ptr).being_killed() == old(iommu_table_map).spec_index(iommu_table_ptr).being_killed(),
        final(iommu_table_map).spec_index(iommu_table_ptr).wlocked_by(final(lctx)),
        final(iommu_table_map).spec_index(iommu_table_ptr).inv(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_l4_end == old(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_l4_end,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().page_closure() == old(iommu_table_map).spec_index(iommu_table_ptr).view().page_closure(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_4k() == old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_4k().insert(spec_index2va(indices), *target_entry),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_2m() == old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_2m(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_1g() == old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_1g(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_entries == old(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_entries,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().cr3 == old(iommu_table_map).spec_index(iommu_table_ptr).view().cr3,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().pcid == old(iommu_table_map).spec_index(iommu_table_ptr).view().pcid,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().did == old(iommu_table_map).spec_index(iommu_table_ptr).view().did,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr == old(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger final(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
            old(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> final(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(l4i, l3i, l2i) == old(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(l4i, l3i, l2i),
{
    assert(iommu_table_map.perms_wf() && iommu_table_map.spec_index(iommu_table_ptr).inv()) by { iommu_table_perms_wf_map(*iommu_table_map); iommu_table_perms_wf_at(*iommu_table_map, iommu_table_ptr); };
    let iommu_table = iommu_table_map.borrow_mut_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_table_lock_perm));
    iommu_table.map_4k_page(indices.0, indices.1, indices.2, indices.3, target_l1_ptr, target_entry, Tracked(&mut *lctx));
    proof {
        assert(iommu_table_map_insert_4k_eof_transition_framing(*old(iommu_table_map), *iommu_table_map, iommu_table_ptr)) by { reveal(iommu_table_map_insert_4k_eof_transition_framing); };
        iommu_table_map_insert_4k_eof(*old(iommu_table_map), *iommu_table_map, iommu_table_ptr);
    }
}

/// IOMMU mirror of `pagetable_map_create_entry_l4`: link the empty L3 page `page_map_ptr` at L4 index `indices.0` of the write-held
/// IOMMU table `iommu_table_ptr`; every mapping stays.
pub fn iommu_table_map_create_entry_l4(
    iommu_table_map: &mut IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index), page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(iommu_table_lock_perm): Tracked<&LockPerm>,
)
    requires
        iommu_table_perms_wf(*old(iommu_table_map)),
        old(iommu_table_map).dom().contains(iommu_table_ptr),
        old(iommu_table_map).typed_lock_map_aligned(old(lctx).iommu_table_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        iommu_table_lock_perm.state() is WriteLock,
        iommu_table_lock_perm.thread_id() == old(lctx).thread_id(),
        iommu_table_lock_perm.lock_id() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_l4_end <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        old(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l4(indices.0) is None,
        page_ptr_valid(page_map_ptr),
        !old(iommu_table_map).spec_index(iommu_table_ptr).view().page_closure().contains(page_map_ptr),
        page_map_perm.addr() == page_map_ptr,
        page_map_perm.is_init(),
        page_map_perm.value().wf(),
        forall|i: usize| #![trigger page_map_perm.value().spec_index(i)] pei_valid(i) ==> page_map_perm.value().spec_index(i).is_empty(),
    ensures
        iommu_table_perms_wf(*final(iommu_table_map)),
        final(iommu_table_map).perms_wf(),
        final(iommu_table_map).unchanged_except(old(iommu_table_map), iommu_table_ptr),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(iommu_table_map).typed_lock_map_aligned(final(lctx).iommu_table_lock_map(), final(lctx).thread_id()),
        final(iommu_table_map).lock_id_by_key(iommu_table_ptr) == old(iommu_table_map).lock_id_by_key(iommu_table_ptr),
        final(iommu_table_map).spec_index(iommu_table_ptr).locking_thread() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread(),
        final(iommu_table_map).spec_index(iommu_table_ptr).being_killed() == old(iommu_table_map).spec_index(iommu_table_ptr).being_killed(),
        final(iommu_table_map).spec_index(iommu_table_ptr).inv(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_l4_end == old(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_l4_end,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().page_closure() == old(iommu_table_map).spec_index(iommu_table_ptr).view().page_closure().insert(page_map_ptr),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_4k() == old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_4k(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_2m() == old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_2m(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_1g() == old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_1g(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_entries == old(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_entries,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().cr3 == old(iommu_table_map).spec_index(iommu_table_ptr).view().cr3,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().pcid == old(iommu_table_map).spec_index(iommu_table_ptr).view().pcid,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().did == old(iommu_table_map).spec_index(iommu_table_ptr).view().did,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr == old(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l4(indices.0) is Some,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l4(indices.0)->0.addr == page_map_ptr,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) is None,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_1g_l3(indices.0, indices.1) is None,
{
    assert(iommu_table_map.perms_wf() && iommu_table_map.spec_index(iommu_table_ptr).inv()) by { iommu_table_perms_wf_map(*iommu_table_map); iommu_table_perms_wf_at(*iommu_table_map, iommu_table_ptr); };
    let iommu_table = iommu_table_map.borrow_mut_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_table_lock_perm));
    iommu_table.create_entry_l4(indices.0, indices.1, page_map_ptr, Tracked(page_map_perm), Tracked(&mut *lctx));
    proof {
        assert(iommu_table_map_create_entry_l4_eof_transition_framing(*old(iommu_table_map), *iommu_table_map, iommu_table_ptr)) by { reveal(iommu_table_map_create_entry_l4_eof_transition_framing); };
        iommu_table_map_create_entry_l4_eof(*old(iommu_table_map), *iommu_table_map, iommu_table_ptr);
    }
}

/// IOMMU mirror of `pagetable_map_create_entry_l3`: link the empty L2 page `page_map_ptr` at `indices` below the L3 page
/// `target_l3_ptr` of the write-held IOMMU table `iommu_table_ptr`; every mapping stays.
pub fn iommu_table_map_create_entry_l3(
    iommu_table_map: &mut IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index), target_l3_ptr: PageMapPtr, page_map_ptr: PageMapPtr,
    Tracked(page_map_perm): Tracked<PointsTo<PageMap>>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(iommu_table_lock_perm): Tracked<&LockPerm>,
)
    requires
        iommu_table_perms_wf(*old(iommu_table_map)),
        old(iommu_table_map).dom().contains(iommu_table_ptr),
        old(iommu_table_map).typed_lock_map_aligned(old(lctx).iommu_table_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        iommu_table_lock_perm.state() is WriteLock,
        iommu_table_lock_perm.thread_id() == old(lctx).thread_id(),
        iommu_table_lock_perm.lock_id() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_l4_end <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        old(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l4(indices.0) is Some,
        old(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l4(indices.0)->0.addr == target_l3_ptr,
        old(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) is None,
        old(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_1g_l3(indices.0, indices.1) is None,
        page_ptr_valid(page_map_ptr),
        !old(iommu_table_map).spec_index(iommu_table_ptr).view().page_closure().contains(page_map_ptr),
        page_map_perm.addr() == page_map_ptr,
        page_map_perm.is_init(),
        page_map_perm.value().wf(),
        forall|i: usize| #![trigger page_map_perm.value().spec_index(i)] pei_valid(i) ==> page_map_perm.value().spec_index(i).is_empty(),
    ensures
        iommu_table_perms_wf(*final(iommu_table_map)),
        final(iommu_table_map).perms_wf(),
        final(iommu_table_map).unchanged_except(old(iommu_table_map), iommu_table_ptr),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(iommu_table_map).typed_lock_map_aligned(final(lctx).iommu_table_lock_map(), final(lctx).thread_id()),
        final(iommu_table_map).lock_id_by_key(iommu_table_ptr) == old(iommu_table_map).lock_id_by_key(iommu_table_ptr),
        final(iommu_table_map).spec_index(iommu_table_ptr).locking_thread() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread(),
        final(iommu_table_map).spec_index(iommu_table_ptr).being_killed() == old(iommu_table_map).spec_index(iommu_table_ptr).being_killed(),
        final(iommu_table_map).spec_index(iommu_table_ptr).inv(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_l4_end == old(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_l4_end,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().page_closure() == old(iommu_table_map).spec_index(iommu_table_ptr).view().page_closure().insert(page_map_ptr),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_4k() == old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_4k(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_2m() == old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_2m(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_1g() == old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_1g(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_entries == old(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_entries,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().cr3 == old(iommu_table_map).spec_index(iommu_table_ptr).view().cr3,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().pcid == old(iommu_table_map).spec_index(iommu_table_ptr).view().pcid,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().did == old(iommu_table_map).spec_index(iommu_table_ptr).view().did,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr == old(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l4(indices.0) == old(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l4(indices.0),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == page_map_ptr,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None,
{
    assert(iommu_table_map.perms_wf() && iommu_table_map.spec_index(iommu_table_ptr).inv()) by { iommu_table_perms_wf_map(*iommu_table_map); iommu_table_perms_wf_at(*iommu_table_map, iommu_table_ptr); };
    let iommu_table = iommu_table_map.borrow_mut_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_table_lock_perm));
    iommu_table.create_entry_l3(indices.0, indices.1, indices.2, target_l3_ptr, page_map_ptr, Tracked(page_map_perm), Tracked(&mut *lctx));
    proof {
        assert(iommu_table_map_create_entry_l3_eof_transition_framing(*old(iommu_table_map), *iommu_table_map, iommu_table_ptr)) by { reveal(iommu_table_map_create_entry_l3_eof_transition_framing); };
        iommu_table_map_create_entry_l3_eof(*old(iommu_table_map), *iommu_table_map, iommu_table_ptr);
    }
}

/// IOMMU mirror of `pagetable_map_create_entry_l2_wlocked`: link the empty L1 page `page_map_ptr` at `indices` below the L2 page
/// `target_l2_ptr` of the write-held IOMMU table `iommu_table_ptr`; every mapping stays.
pub fn iommu_table_map_create_entry_l2(
    iommu_table_map: &mut IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index), target_l2_ptr: PageMapPtr, page_map_ptr: PageMapPtr,
    Tracked(page_map_perm): Tracked<PointsTo<PageMap>>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(iommu_table_lock_perm): Tracked<&LockPerm>,
)
    requires
        iommu_table_perms_wf(*old(iommu_table_map)),
        old(iommu_table_map).dom().contains(iommu_table_ptr),
        old(iommu_table_map).typed_lock_map_aligned(old(lctx).iommu_table_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        iommu_table_lock_perm.state() is WriteLock,
        iommu_table_lock_perm.thread_id() == old(lctx).thread_id(),
        iommu_table_lock_perm.lock_id() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_l4_end <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        old(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        old(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        old(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None,
        old(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None,
        page_ptr_valid(page_map_ptr),
        !old(iommu_table_map).spec_index(iommu_table_ptr).view().page_closure().contains(page_map_ptr),
        page_map_perm.addr() == page_map_ptr,
        page_map_perm.is_init(),
        page_map_perm.value().wf(),
        forall|i: usize| #![trigger page_map_perm.value().spec_index(i)] pei_valid(i) ==> page_map_perm.value().spec_index(i).is_empty(),
    ensures
        iommu_table_perms_wf(*final(iommu_table_map)),
        final(iommu_table_map).perms_wf(),
        final(iommu_table_map).unchanged_except(old(iommu_table_map), iommu_table_ptr),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(iommu_table_map).typed_lock_map_aligned(final(lctx).iommu_table_lock_map(), final(lctx).thread_id()),
        final(iommu_table_map).lock_id_by_key(iommu_table_ptr) == old(iommu_table_map).lock_id_by_key(iommu_table_ptr),
        final(iommu_table_map).spec_index(iommu_table_ptr).locking_thread() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread(),
        final(iommu_table_map).spec_index(iommu_table_ptr).being_killed() == old(iommu_table_map).spec_index(iommu_table_ptr).being_killed(),
        final(iommu_table_map).spec_index(iommu_table_ptr).inv(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_l4_end == old(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_l4_end,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().page_closure() == old(iommu_table_map).spec_index(iommu_table_ptr).view().page_closure().insert(page_map_ptr),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_4k() == old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_4k(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_2m() == old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_2m(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_1g() == old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_1g(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_entries == old(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_entries,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().cr3 == old(iommu_table_map).spec_index(iommu_table_ptr).view().cr3,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().pcid == old(iommu_table_map).spec_index(iommu_table_ptr).view().pcid,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().did == old(iommu_table_map).spec_index(iommu_table_ptr).view().did,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr == old(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l4(indices.0) == old(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l4(indices.0),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) == old(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == page_map_ptr,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None,
{
    assert(iommu_table_map.perms_wf() && iommu_table_map.spec_index(iommu_table_ptr).inv()) by { iommu_table_perms_wf_map(*iommu_table_map); iommu_table_perms_wf_at(*iommu_table_map, iommu_table_ptr); };
    let iommu_table = iommu_table_map.borrow_mut_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_table_lock_perm));
    iommu_table.create_entry_l2(indices.0, indices.1, indices.2, target_l2_ptr, page_map_ptr, Tracked(page_map_perm), Tracked(&mut *lctx));
    proof {
        assert(iommu_table_map_create_entry_l2_eof_transition_framing(*old(iommu_table_map), *iommu_table_map, iommu_table_ptr)) by { reveal(iommu_table_map_create_entry_l2_eof_transition_framing); };
        iommu_table_map_create_entry_l2_eof(*old(iommu_table_map), *iommu_table_map, iommu_table_ptr);
    }
}

/// Unlink the table page that `scan` names from the write-held IOMMU table `iommu_table_ptr` and return its memory; every mapping stays.
pub fn iommu_table_map_remove_table_page(
    iommu_table_map: &mut IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot, scan: StructureScan, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(iommu_table_lock_perm): Tracked<&LockPerm>,
) -> (ret: Tracked<vstd::simple_pptr::PointsTo<PageMap>>)
    requires
        iommu_table_perms_wf(*old(iommu_table_map)),
        old(iommu_table_map).dom().contains(iommu_table_ptr),
        old(iommu_table_map).typed_lock_map_aligned(old(lctx).iommu_table_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        iommu_table_lock_perm.state() is WriteLock,
        iommu_table_lock_perm.thread_id() == old(lctx).thread_id(),
        iommu_table_lock_perm.lock_id() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(iommu_table_map).spec_index(iommu_table_ptr).view().spec_structure_scan_wf(scan),
        scan.spec_table_page() is Some,
    ensures
        iommu_table_perms_wf(*final(iommu_table_map)),
        final(iommu_table_map).perms_wf(),
        final(iommu_table_map).unchanged_except(old(iommu_table_map), iommu_table_ptr),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(iommu_table_map).typed_lock_map_aligned(final(lctx).iommu_table_lock_map(), final(lctx).thread_id()),
        final(iommu_table_map).lock_id_by_key(iommu_table_ptr) == old(iommu_table_map).lock_id_by_key(iommu_table_ptr),
        final(iommu_table_map).spec_index(iommu_table_ptr).locking_thread() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread(),
        final(iommu_table_map).spec_index(iommu_table_ptr).being_killed() == old(iommu_table_map).spec_index(iommu_table_ptr).being_killed(),
        final(iommu_table_map).spec_index(iommu_table_ptr).inv(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_l4_end == old(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_l4_end,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().page_closure() == old(iommu_table_map).spec_index(iommu_table_ptr).view().page_closure().remove(scan.spec_table_page()->Some_0),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_4k() == old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_4k(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_2m() == old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_2m(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_1g() == old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_1g(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_entries == old(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_entries,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().cr3 == old(iommu_table_map).spec_index(iommu_table_ptr).view().cr3,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().pcid == old(iommu_table_map).spec_index(iommu_table_ptr).view().pcid,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().did == old(iommu_table_map).spec_index(iommu_table_ptr).view().did,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr == old(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr,
        ret.view().is_init(),
        ret.view().addr() == scan.spec_table_page()->Some_0,
{
    assert(iommu_table_map.perms_wf() && iommu_table_map.spec_index(iommu_table_ptr).inv()) by { iommu_table_perms_wf_map(*iommu_table_map); iommu_table_perms_wf_at(*iommu_table_map, iommu_table_ptr); };
    let iommu_table = iommu_table_map.borrow_mut_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_table_lock_perm));
    let ret = iommu_table.remove_structure_page(scan, Tracked(&mut *lctx));
    proof {
        assert(iommu_table_map_remove_table_page_eof_transition_framing(*old(iommu_table_map), *iommu_table_map, iommu_table_ptr)) by { reveal(iommu_table_map_remove_table_page_eof_transition_framing); };
        iommu_table_map_remove_table_page_eof(*old(iommu_table_map), *iommu_table_map, iommu_table_ptr);
    }
    ret
}
}
