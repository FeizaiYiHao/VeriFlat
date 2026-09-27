use vstd::prelude::*;
use crate::*;

verus! {
pub fn page_array_retype_owned_4k(
    page_array: &mut PageLockedArray, page_index: PageIndex, new_state: PageState,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>,
) -> (ret: Tracked<PagePerm4k>)
    requires
        page_array_wf(*old(page_array)),
        index_valid(NUM_PAGES, page_index),
        old(page_array).typed_lock_map_aligned(old(lctx).page_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_index, TypedLockMode::Write),
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == old(lctx).thread_id(),
        page_lock_perm.lock_id() == old(page_array).spec_index(page_index).view().locking_thread()->Write_lock_id,
        old(page_array).spec_index(page_index).view().view().state is Owned4k,
        new_state is Allocated4k || new_state is IOMMUTable,
        old(lctx).kernel_view_locking_state() is Release,
    ensures
        page_array_wf(*final(page_array)),
        final(page_array).inv(),
        final(page_array).spec_index(page_index).view().inv(),
        final(page_array).entries_unchanged_except(old(page_array), page_index),
        final(page_array).typed_lock_map_aligned(final(lctx).page_lock_map(), final(lctx).thread_id()),
        final(page_array).spec_index(page_index).view().locking_thread() == old(page_array).spec_index(page_index).view().locking_thread(),
        final(page_array).spec_index(page_index).view().being_killed() == old(page_array).spec_index(page_index).view().being_killed(),
        final(page_array).spec_index(page_index).view().view() == (Page {
            state: new_state,
            perm_4k: final(page_array).spec_index(page_index).view().view().perm_4k,
            ..old(page_array).spec_index(page_index).view().view()
        }),
        final(page_array).spec_index(page_index).view().view_rodata()
            == old(page_array).spec_index(page_index).view().view_rodata(),
        final(page_array).spec_index(page_index).view().view_ghost()
            == old(page_array).spec_index(page_index).view().view_ghost(),
        final(page_array).spec_index(page_index).view().view().state == new_state,
        final(page_array).spec_index(page_index).view().view().perm_4k.view().is_none(),
        final(page_array).spec_index(page_index).view().view().addr == old(page_array).spec_index(page_index).view().view().addr,
        final(page_array).spec_index(page_index).view().view().is_io_page == old(page_array).spec_index(page_index).view().view().is_io_page,
        final(page_array).spec_index(page_index).view().view().ref_count == old(page_array).spec_index(page_index).view().view().ref_count,
        final(page_array).spec_index(page_index).view().view().owning_container == old(page_array).spec_index(page_index).view().view().owning_container,
        final(page_array).spec_index(page_index).view().view().mappings() == old(page_array).spec_index(page_index).view().view().mappings(),
        final(page_array).spec_index(page_index).view().view().free_list_node_storage
            == old(page_array).spec_index(page_index).view().view().free_list_node_storage,
        final(page_array).spec_index(page_index).view().view().free_list == old(page_array).spec_index(page_index).view().view().free_list,
        final(page_array).spec_index(page_index).view().view().perm_2m.view() == old(page_array).spec_index(page_index).view().view().perm_2m.view(),
        final(page_array).spec_index(page_index).view().view().perm_1g.view() == old(page_array).spec_index(page_index).view().view().perm_1g.view(),
        ret.view().is_init(),
        ret.view().addr() == final(page_array).spec_index(page_index).view().view().addr,
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_index), TypedHeldLock {
            lock_id: final(page_array).lock_id_by_index(page_index), mode: TypedLockMode::Write,
        }),
        final(lctx).page_lock_map() == old(lctx).page_lock_map().insert(page_index, TypedHeldLock {
            lock_id: final(page_array).lock_id_by_index(page_index), mode: TypedLockMode::Write,
        }),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
{
    assert(page_array.inv() && page_array.spec_index(page_index).view().is_init()
        && page_array.spec_index(page_index).view().view().inv()) by { page_array_wf_at(*page_array, page_index); };
    let ghost old_lock_id = page_array.lock_id_by_index(page_index);
    let page = page_array.borrow_mut_typed(
        page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(page_lock_perm),
    );
    let ret = retype_owned_4k_to_kernel_object(page, new_state);
    proof {
        lctx.update_lock_id(KernelObjId::Page(page_index), old_lock_id, page_array.lock_id_by_index(page_index));
        assert(page_array_wf(*page_array)) by { reveal(page_array_wf); };
        assert(page_array.typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    }
    ret
}

pub fn page_array_add_4k_mapping(
    page_array: &mut PageLockedArray, page_index: PageIndex, pagetable_ptr: RwLockPageTableRoot, va: VAddr,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>,
)
    requires
        page_array_wf(*old(page_array)),
        hugepage_2m_wf(*old(page_array)),
        hugepage_1g_wf(*old(page_array)),
        index_valid(NUM_PAGES, page_index),
        old(page_array).typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.page_lock_map(), page_index, TypedLockMode::Write),
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == lctx.thread_id(),
        page_lock_perm.lock_id() == old(page_array).spec_index(page_index).view().locking_thread()->Write_lock_id,
        old(page_array).spec_index(page_index).view().view().state is Mapped4k,
        va_4k_valid(va),
        !old(page_array).spec_index(page_index).view().view().mappings().contains((pagetable_ptr, va)),
        old(page_array).spec_index(page_index).view().view().ref_count < usize::MAX,
    ensures
        page_array_wf(*final(page_array)),
        hugepage_2m_wf(*final(page_array)),
        hugepage_1g_wf(*final(page_array)),
        final(page_array).entries_unchanged_except(old(page_array), page_index),
        final(page_array).typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id()),
        final(page_array).spec_index(page_index).view().locking_thread() == old(page_array).spec_index(page_index).view().locking_thread(),
        final(page_array).spec_index(page_index).view().being_killed() == old(page_array).spec_index(page_index).view().being_killed(),
        final(page_array).spec_index(page_index).view().view().mappings()
            == old(page_array).spec_index(page_index).view().view().mappings().insert((pagetable_ptr, va)),
        final(page_array).spec_index(page_index).view().view().ref_count
            == old(page_array).spec_index(page_index).view().view().ref_count + 1,
        final(page_array).spec_index(page_index).view().view().addr == old(page_array).spec_index(page_index).view().view().addr,
        final(page_array).spec_index(page_index).view().view().state == old(page_array).spec_index(page_index).view().view().state,
        final(page_array).spec_index(page_index).view().view().is_io_page == old(page_array).spec_index(page_index).view().view().is_io_page,
        final(page_array).spec_index(page_index).view().view().owning_container == old(page_array).spec_index(page_index).view().view().owning_container,
        final(page_array).spec_index(page_index).view().view().free_list_node_storage
            == old(page_array).spec_index(page_index).view().view().free_list_node_storage,
        final(page_array).spec_index(page_index).view().view().free_list == old(page_array).spec_index(page_index).view().view().free_list,
        final(page_array).spec_index(page_index).view().view().perm_4k.view() == old(page_array).spec_index(page_index).view().view().perm_4k.view(),
        final(page_array).spec_index(page_index).view().view().perm_2m.view() == old(page_array).spec_index(page_index).view().view().perm_2m.view(),
        final(page_array).spec_index(page_index).view().view().perm_1g.view() == old(page_array).spec_index(page_index).view().view().perm_1g.view(),
{
    assert(page_array.inv() && page_array.spec_index(page_index).view().inv()) by { page_array_wf_at(*page_array, page_index); };
    let page = page_array.borrow_mut_typed(
        page_index, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(page_lock_perm),
    );
    add_4k_mapping(page, pagetable_ptr, va);
    proof {
        assert(page_array_wf(*page_array)) by { reveal(page_array_wf); };
        assert(hugepage_2m_wf(*page_array)) by { hugepage_2m_wf_preserved_for_page_state_eq(*old(page_array), *page_array); };
        assert(hugepage_1g_wf(*page_array)) by { hugepage_1g_wf_preserved_for_page_state_eq(*old(page_array), *page_array); };
        assert(page_array.typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    }
}

pub fn pagetable_map_insert_4k(
    pagetable_map: &mut PageTableLockedMap, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index, L1Index), target_l1_ptr: PageMapPtr, target_entry: &MapEntry,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        old(pagetable_map).dom().contains(pagetable_ptr),
        old(pagetable_map).typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        page_table_key_4k_valid::<PT_TYPE>(spec_index2va(indices)),
        old(pagetable_map).spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        old(pagetable_map).spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        old(pagetable_map).spec_index(pagetable_ptr).view().spec_resolve_mapping_4k_l1(indices.0, indices.1, indices.2, indices.3) is None
            || !old(pagetable_map).spec_index(pagetable_ptr).view().mapping_4k().dom().contains(spec_index2va(indices)),
        page_ptr_valid(target_entry.addr),
        target_entry.present,
    ensures
        pagetable_perms_wf(*final(pagetable_map)),
        final(pagetable_map).unchanged_except(old(pagetable_map), pagetable_ptr),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(pagetable_map).typed_lock_map_aligned(final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        final(pagetable_map).lock_id_by_key(pagetable_ptr) == old(pagetable_map).lock_id_by_key(pagetable_ptr),
        final(pagetable_map).spec_index(pagetable_ptr).locking_thread() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread(),
        final(pagetable_map).spec_index(pagetable_ptr).wlocked() == old(pagetable_map).spec_index(pagetable_ptr).wlocked(),
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end,
        final(pagetable_map).spec_index(pagetable_ptr).view().page_closure() == old(pagetable_map).spec_index(pagetable_ptr).view().page_closure(),
        final(pagetable_map).spec_index(pagetable_ptr).view().mapping_4k()
            == old(pagetable_map).spec_index(pagetable_ptr).view().mapping_4k().insert(spec_index2va(indices), *target_entry),
        final(pagetable_map).spec_index(pagetable_ptr).view().mapping_2m() =~= old(pagetable_map).spec_index(pagetable_ptr).view().mapping_2m(),
        final(pagetable_map).spec_index(pagetable_ptr).view().mapping_1g() =~= old(pagetable_map).spec_index(pagetable_ptr).view().mapping_1g(),
        final(pagetable_map).spec_index(pagetable_ptr).view().spec_resolve_mapping_l4(indices.0)
            == old(pagetable_map).spec_index(pagetable_ptr).view().spec_resolve_mapping_l4(indices.0),
        final(pagetable_map).spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1)
            == old(pagetable_map).spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger final(pagetable_map).spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
            final(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i)
                && pei_valid(l3i) && pei_valid(l2i)
            ==> final(pagetable_map).spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(l4i, l3i, l2i)
                == old(pagetable_map).spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(l4i, l3i, l2i),
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries =~= old(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries,
        final(pagetable_map).spec_index(pagetable_ptr).view().pcid == old(pagetable_map).spec_index(pagetable_ptr).view().pcid,
        final(pagetable_map).spec_index(pagetable_ptr).view().cr3 =~= old(pagetable_map).spec_index(pagetable_ptr).view().cr3,
        final(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr =~= old(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr,
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).inv()) by { pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_mut_typed(
        pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm),
    );
    pagetable.map_4k_page(
        indices.0, indices.1, indices.2, indices.3, target_l1_ptr, target_entry, Tracked(&mut *lctx),
    );
    proof {
        assert(pagetable_perms_wf(*pagetable_map)) by { reveal(pagetable_perms_wf); };
        assert(pagetable_map.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn pagetable_map_clear_4k_present(
    pagetable_map: &mut PageTableLockedMap, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index, L1Index), target_l1_ptr: PageMapPtr,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        old(pagetable_map).dom().contains(pagetable_ptr),
        old(pagetable_map).typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        old(pagetable_map).spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        old(pagetable_map).spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        old(pagetable_map).spec_index(pagetable_ptr).view().mapping_4k().dom().contains(spec_index2va(indices)),
    ensures
        pagetable_perms_wf(*final(pagetable_map)),
        final(pagetable_map).perms_wf(),
        final(pagetable_map).unchanged_except(old(pagetable_map), pagetable_ptr),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(pagetable_map).typed_lock_map_aligned(final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        final(pagetable_map).lock_id_by_key(pagetable_ptr) == old(pagetable_map).lock_id_by_key(pagetable_ptr),
        final(pagetable_map).spec_index(pagetable_ptr).locking_thread() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread(),
        final(pagetable_map).spec_index(pagetable_ptr).being_killed() == old(pagetable_map).spec_index(pagetable_ptr).being_killed(),
        final(pagetable_map).spec_index(pagetable_ptr).wlocked_by(final(lctx)),
        final(pagetable_map).spec_index(pagetable_ptr).inv(),
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end,
        final(pagetable_map).spec_index(pagetable_ptr).view().page_closure() == old(pagetable_map).spec_index(pagetable_ptr).view().page_closure(),
        final(pagetable_map).spec_index(pagetable_ptr).view().mapping_4k() == old(pagetable_map).spec_index(pagetable_ptr).view().mapping_4k().insert(spec_index2va(indices), MapEntry { present: false, ..old(pagetable_map).spec_index(pagetable_ptr).view().mapping_4k().spec_index(spec_index2va(indices)) }),
        final(pagetable_map).spec_index(pagetable_ptr).view().mapping_2m() == old(pagetable_map).spec_index(pagetable_ptr).view().mapping_2m(),
        final(pagetable_map).spec_index(pagetable_ptr).view().mapping_1g() == old(pagetable_map).spec_index(pagetable_ptr).view().mapping_1g(),
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries,
        final(pagetable_map).spec_index(pagetable_ptr).view().cr3 == old(pagetable_map).spec_index(pagetable_ptr).view().cr3,
        final(pagetable_map).spec_index(pagetable_ptr).view().pcid == old(pagetable_map).spec_index(pagetable_ptr).view().pcid,
        final(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr == old(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr,
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).inv()) by { pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_mut_typed(
        pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm),
    );
    pagetable.unmap_4k_page_user_view(indices.0, indices.1, indices.2, indices.3, target_l1_ptr, Tracked(&mut *lctx));
    proof {
        assert(pagetable_perms_wf(*pagetable_map)) by { reveal(pagetable_perms_wf); };
        assert(pagetable_map.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn pagetable_map_unmap_4k_kernel(
    pagetable_map: &mut PageTableLockedMap, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index, L1Index), target_l1_ptr: PageMapPtr,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        old(pagetable_map).dom().contains(pagetable_ptr),
        old(pagetable_map).typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        old(pagetable_map).spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        old(pagetable_map).spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        old(pagetable_map).spec_index(pagetable_ptr).view().mapping_4k().dom().contains(spec_index2va(indices)),
        !old(pagetable_map).spec_index(pagetable_ptr).view().mapping_4k().spec_index(spec_index2va(indices)).present,
    ensures
        pagetable_perms_wf(*final(pagetable_map)),
        final(pagetable_map).perms_wf(),
        final(pagetable_map).unchanged_except(old(pagetable_map), pagetable_ptr),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(pagetable_map).typed_lock_map_aligned(final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        final(pagetable_map).lock_id_by_key(pagetable_ptr) == old(pagetable_map).lock_id_by_key(pagetable_ptr),
        final(pagetable_map).spec_index(pagetable_ptr).locking_thread() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread(),
        final(pagetable_map).spec_index(pagetable_ptr).being_killed() == old(pagetable_map).spec_index(pagetable_ptr).being_killed(),
        final(pagetable_map).spec_index(pagetable_ptr).wlocked_by(final(lctx)),
        final(pagetable_map).spec_index(pagetable_ptr).inv(),
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end,
        final(pagetable_map).spec_index(pagetable_ptr).view().page_closure() == old(pagetable_map).spec_index(pagetable_ptr).view().page_closure(),
        final(pagetable_map).spec_index(pagetable_ptr).view().mapping_4k() == old(pagetable_map).spec_index(pagetable_ptr).view().mapping_4k().remove(spec_index2va(indices)),
        final(pagetable_map).spec_index(pagetable_ptr).view().mapping_2m() == old(pagetable_map).spec_index(pagetable_ptr).view().mapping_2m(),
        final(pagetable_map).spec_index(pagetable_ptr).view().mapping_1g() == old(pagetable_map).spec_index(pagetable_ptr).view().mapping_1g(),
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries,
        final(pagetable_map).spec_index(pagetable_ptr).view().cr3 == old(pagetable_map).spec_index(pagetable_ptr).view().cr3,
        final(pagetable_map).spec_index(pagetable_ptr).view().pcid == old(pagetable_map).spec_index(pagetable_ptr).view().pcid,
        final(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr == old(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr,
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).inv()) by { pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_mut_typed(
        pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm),
    );
    pagetable.unmap_4k_page_kernel(indices.0, indices.1, indices.2, indices.3, target_l1_ptr, Tracked(&mut *lctx));
    proof {
        assert(pagetable_perms_wf(*pagetable_map)) by { reveal(pagetable_perms_wf); };
        assert(pagetable_map.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
}

pub fn page_array_remove_4k_mapping_without_free(
    page_array: &mut PageLockedArray, page_index: PageIndex, pagetable_ptr: RwLockPageTableRoot, va: VAddr,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>,
)
    requires
        page_array_wf(*old(page_array)),
        index_valid(NUM_PAGES, page_index),
        old(page_array).typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.page_lock_map(), page_index, TypedLockMode::Write),
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == lctx.thread_id(),
        page_lock_perm.lock_id() == old(page_array).spec_index(page_index).view().locking_thread()->Write_lock_id,
        old(page_array).spec_index(page_index).view().view().state is Mapped4k,
        old(page_array).spec_index(page_index).view().view().mappings().contains((pagetable_ptr, va)),
        old(page_array).spec_index(page_index).view().view().ref_count > 1 || old(page_array).spec_index(page_index).view().view().is_io_page,
    ensures
        page_array_wf(*final(page_array)),
        final(page_array).inv(),
        final(page_array).entries_unchanged_except(old(page_array), page_index),
        lctx.page_lock_map().index(page_index).lock_id == old(page_array).lock_id_by_index(page_index),
        final(page_array).typed_lock_map_aligned(lctx.page_lock_map().insert(page_index, TypedHeldLock { lock_id: final(page_array).lock_id_by_index(page_index), mode: TypedLockMode::Write }), lctx.thread_id()),
        final(page_array).spec_index(page_index).view().is_init(),
        final(page_array).spec_index(page_index).view().inv(),
        final(page_array).spec_index(page_index).view().wlocked_by(lctx),
        final(page_array).spec_index(page_index).view().locking_thread() == old(page_array).spec_index(page_index).view().locking_thread(),
        final(page_array).spec_index(page_index).view().being_killed() == old(page_array).spec_index(page_index).view().being_killed(),
        final(page_array).spec_index(page_index).view().view_rodata() == old(page_array).spec_index(page_index).view().view_rodata(),
        final(page_array).spec_index(page_index).view().view_ghost() == old(page_array).spec_index(page_index).view().view_ghost(),
        final(page_array).spec_index(page_index).view().view().mappings() == old(page_array).spec_index(page_index).view().view().mappings().remove((pagetable_ptr, va)),
        final(page_array).spec_index(page_index).view().view().ref_count == old(page_array).spec_index(page_index).view().view().ref_count - 1,
        final(page_array).spec_index(page_index).view().view().state == if old(page_array).spec_index(page_index).view().view().ref_count > 1 { PageState::Mapped4k } else { PageState::Unavailable },
        forall|i: PageIndex| #![trigger old(page_array).spec_index(i).view().view().state] #![trigger final(page_array).spec_index(i).view().view().state] index_valid(NUM_PAGES, i) && i != page_index ==> final(page_array).spec_index(i).view().view().state == old(page_array).spec_index(i).view().view().state,
        old(page_array).spec_index(page_index).view().view().ref_count > 1 ==> final(page_array).spec_index(page_index).view().view() == (Page { mappings: final(page_array).spec_index(page_index).view().view().mappings, ref_count: final(page_array).spec_index(page_index).view().view().ref_count, ..old(page_array).spec_index(page_index).view().view() }),
        old(page_array).spec_index(page_index).view().view().ref_count == 1 ==> final(page_array).spec_index(page_index).view().view() == (Page { state: PageState::Unavailable, mappings: final(page_array).spec_index(page_index).view().view().mappings, ref_count: 0, perm_4k: final(page_array).spec_index(page_index).view().view().perm_4k, ..old(page_array).spec_index(page_index).view().view() }) && final(page_array).spec_index(page_index).view().view().perm_4k.view() is None,
{
    assert(page_array.inv() && page_array.spec_index(page_index).view().is_init() && page_array.spec_index(page_index).view().view().inv()) by { page_array_wf_at(*page_array, page_index); };
    let page = page_array.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(page_lock_perm));
    if page.ref_count > 1 { remove_shared_4k_mapping(page, pagetable_ptr, va); }
    else { remove_last_4k_io_mapping(page, pagetable_ptr, va); }
    proof { assert(page_array_wf(*page_array)) by { reveal(page_array_wf); }; }
}

pub fn page_array_remove_last_4k_mapping_to_cache(
    page_array: &mut PageLockedArray, page_index: PageIndex, pagetable_ptr: RwLockPageTableRoot, va: VAddr,
    allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>,
) -> (ret: (usize, Tracked<vstd::simple_pptr::PointsTo<Node<PagePtr>>>))
    requires
        page_array_wf(*old(page_array)),
        index_valid(NUM_PAGES, page_index),
        old(page_array).typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.page_lock_map(), page_index, TypedLockMode::Write),
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == lctx.thread_id(),
        page_lock_perm.lock_id() == old(page_array).spec_index(page_index).view().locking_thread()->Write_lock_id,
        old(page_array).spec_index(page_index).view().view().state is Mapped4k,
        !old(page_array).spec_index(page_index).view().view().is_io_page,
        old(page_array).spec_index(page_index).view().view().mappings().contains((pagetable_ptr, va)),
        old(page_array).spec_index(page_index).view().view().ref_count == 1,
        index_valid(NUM_CPUS, cpu_id),
    ensures
        page_array_wf(*final(page_array)),
        final(page_array).inv(),
        final(page_array).entries_unchanged_except(old(page_array), page_index),
        lctx.page_lock_map().index(page_index).lock_id == old(page_array).lock_id_by_index(page_index),
        final(page_array).typed_lock_map_aligned(lctx.page_lock_map().insert(page_index, TypedHeldLock { lock_id: final(page_array).lock_id_by_index(page_index), mode: TypedLockMode::Write }), lctx.thread_id()),
        final(page_array).spec_index(page_index).view().is_init(),
        final(page_array).spec_index(page_index).view().inv(),
        final(page_array).spec_index(page_index).view().wlocked_by(lctx),
        final(page_array).spec_index(page_index).view().locking_thread() == old(page_array).spec_index(page_index).view().locking_thread(),
        final(page_array).spec_index(page_index).view().being_killed() == old(page_array).spec_index(page_index).view().being_killed(),
        final(page_array).spec_index(page_index).view().view_rodata() == old(page_array).spec_index(page_index).view().view_rodata(),
        final(page_array).spec_index(page_index).view().view_ghost() == old(page_array).spec_index(page_index).view().view_ghost(),
        final(page_array).spec_index(page_index).view().view() == (Page {
            state: PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } },
            mappings: Ghost(old(page_array).spec_index(page_index).view().view().mappings().remove((pagetable_ptr, va))),
            ref_count: 0,
            free_list_node_storage: final(page_array).spec_index(page_index).view().view().free_list_node_storage,
            ..old(page_array).spec_index(page_index).view().view()
        }),
        final(page_array).spec_index(page_index).view().view().mappings() == Set::<(RwLockPageTableRoot, VAddr)>::empty(),
        final(page_array).spec_index(page_index).view().view().free_list_node_storage.addr() == old(page_array).spec_index(page_index).view().view().free_list_node_storage.addr(),
        ret.0 == old(page_array).spec_index(page_index).view().view().free_list_node_storage.addr(),
        ret.1.view().is_init(),
        ret.1.view().addr() == ret.0,
        ret.1.view().value().view() == old(page_array).spec_index(page_index).view().view().addr,
{
    assert(page_array.inv() && page_array.spec_index(page_index).view().is_init() && page_array.spec_index(page_index).view().view().inv()) by { page_array_wf_at(*page_array, page_index); };
    let page = page_array.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(page_lock_perm));
    let ret = remove_last_4k_mapping_to_cache(page, pagetable_ptr, va, allocator_ptr, cpu_id);
    proof { assert(page_array_wf(*page_array)) by { reveal(page_array_wf); }; }
    ret
}

pub fn page_array_move_free_4k_to_global_list(
    page_array: &mut PageLockedArray, page_index: PageIndex, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>,
)
    requires
        page_array_wf(*old(page_array)),
        index_valid(NUM_PAGES, page_index),
        old(page_array).typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.page_lock_map(), page_index, TypedLockMode::Write),
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == lctx.thread_id(),
        page_lock_perm.lock_id() == old(page_array).spec_index(page_index).view().locking_thread()->Write_lock_id,
        old(page_array).spec_index(page_index).view().view().state == (PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } }),
    ensures
        page_array_wf(*final(page_array)),
        final(page_array).inv(),
        final(page_array).entries_unchanged_except(old(page_array), page_index),
        final(page_array).typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id()),
        final(page_array).lock_id_by_index(page_index) == old(page_array).lock_id_by_index(page_index),
        final(page_array).spec_index(page_index).view().is_init(),
        final(page_array).spec_index(page_index).view().inv(),
        final(page_array).spec_index(page_index).view().wlocked_by(lctx),
        final(page_array).spec_index(page_index).view().locking_thread() == old(page_array).spec_index(page_index).view().locking_thread(),
        final(page_array).spec_index(page_index).view().being_killed() == old(page_array).spec_index(page_index).view().being_killed(),
        final(page_array).spec_index(page_index).view().view_rodata() == old(page_array).spec_index(page_index).view().view_rodata(),
        final(page_array).spec_index(page_index).view().view_ghost() == old(page_array).spec_index(page_index).view().view_ghost(),
        final(page_array).spec_index(page_index).view().view() == (Page { state: PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::GlobalList }, ..old(page_array).spec_index(page_index).view().view() }),
{
    assert(page_array.inv() && page_array.spec_index(page_index).view().is_init() && page_array.spec_index(page_index).view().view().inv()) by { page_array_wf_at(*page_array, page_index); };
    let page = page_array.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(page_lock_perm));
    page.state = PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::GlobalList };
    proof {
        assert(page_array_wf(*page_array)) by { reveal(page_array_wf); };
        assert(page_array.typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    }
}

pub fn page_array_retype_owned_4k_for_container(
    pages: &mut PageLockedArray, child_container_ptr: RwLockContainerPtr, page_ptr: PagePtr, page_state: Allocated4KPageState,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>,
) -> (ret: Tracked<PagePerm4k>)
    requires
        page_array_wf(*old(pages)),
        old(pages).typed_lock_map_aligned(old(lctx).page_lock_map(), old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Release,
        page_ptr_valid(page_ptr),
        old(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().state is Owned4k,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == old(lctx).thread_id(),
        page_lock_perm.lock_id() == old(pages).spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(pages).inv(),
        page_array_wf(*final(pages)),
        final(pages).typed_lock_map_aligned(final(lctx).page_lock_map(), final(lctx).thread_id()),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(page_ptr)), TypedHeldLock {
            lock_id: final(pages).lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write,
        }),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom(),
        final(pages).entries_unchanged_except(old(pages), page_ptr2page_index(page_ptr)),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().mappings()]
            #![trigger old(pages).spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().mappings() == old(pages).spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().free_list]
            index_valid(NUM_PAGES, index) && index != page_ptr2page_index(page_ptr)
                ==> final(pages).spec_index(index).view().view().free_list == old(pages).spec_index(index).view().view().free_list,
        forall|index: PageIndex|
            #![trigger final(lctx).page_lock_map().get(index)]
            #![trigger final(lctx).page_lock_map().dom().contains(index)]
            #![trigger old(lctx).page_lock_map().get(index)]
            index != page_ptr2page_index(page_ptr) ==> final(lctx).page_lock_map().get(index) == old(lctx).page_lock_map().get(index),
        final(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Allocated4k { state: page_state }),
        final(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == child_container_ptr,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_lock_perm.lock_id() == final(pages).spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        ret.view().is_init(),
        ret.view().addr() == page_ptr,
{
    let page_index = page_ptr2page_index(page_ptr);
    let ghost old_page_lock_id = pages.lock_id_by_index(page_index);
    assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(pages.inv() && pages.spec_index(page_index).view().is_init()
        && pages.spec_index(page_index).view().view().inv()) by { page_array_wf_at(*pages, page_index); };
    let page = pages.borrow_mut_typed(
        page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(page_lock_perm),
    );
    let Tracked(page_perm) = retype_owned_4k_to_kernel_object(page, PageState::Allocated4k { state: page_state });
    page.owning_container = child_container_ptr;
    proof {
        lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, pages.lock_id_by_index(page_index));
        assert(pages.spec_index(page_index).view().inv()) by { reveal(RwLock::inv); };
        assert(pages.spec_index(page_index).view().view().addr == page_index2page_ptr(page_index)) by { page_ptr_roundtrip(); reveal(page_array_wf); };
        assert(page_array_wf(*pages)) by { reveal(page_array_wf); };
        assert(pages.typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    }
    Tracked(page_perm)
}

pub fn page_array_retype_owned_2m_for_container(
    pages: &mut PageLockedArray, child_container_ptr: RwLockContainerPtr, page_ptr: PagePtr, page_state: Allocated2MPageState,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>,
) -> (ret: Tracked<PagePerm2m>)
    requires
        page_array_wf(*old(pages)),
        old(pages).typed_lock_map_aligned(old(lctx).page_lock_map(), old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Release,
        page_ptr_2m_valid(page_ptr),
        old(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().state is Owned2m,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == old(lctx).thread_id(),
        page_lock_perm.lock_id() == old(pages).spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(pages).inv(),
        page_array_wf(*final(pages)),
        final(pages).typed_lock_map_aligned(final(lctx).page_lock_map(), final(lctx).thread_id()),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(page_ptr)), TypedHeldLock {
            lock_id: final(pages).lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write,
        }),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom(),
        final(pages).entries_unchanged_except(old(pages), page_ptr2page_index(page_ptr)),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().mappings()]
            #![trigger old(pages).spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().mappings() == old(pages).spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().free_list]
            index_valid(NUM_PAGES, index) && index != page_ptr2page_index(page_ptr)
                ==> final(pages).spec_index(index).view().view().free_list == old(pages).spec_index(index).view().view().free_list,
        forall|index: PageIndex|
            #![trigger final(lctx).page_lock_map().get(index)]
            #![trigger final(lctx).page_lock_map().dom().contains(index)]
            #![trigger old(lctx).page_lock_map().get(index)]
            index != page_ptr2page_index(page_ptr) ==> final(lctx).page_lock_map().get(index) == old(lctx).page_lock_map().get(index),
        final(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Allocated2m { state: page_state }),
        final(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == child_container_ptr,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_lock_perm.lock_id() == final(pages).spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        ret.view().is_init(),
        ret.view().addr() == page_ptr,
{
    let page_index = page_ptr2page_index(page_ptr);
    let ghost old_page_lock_id = pages.lock_id_by_index(page_index);
    assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(pages.inv() && pages.spec_index(page_index).view().is_init()
        && pages.spec_index(page_index).view().view().inv()
        && pages.spec_index(page_index).view().view().addr == page_index2page_ptr(page_index)) by { page_array_wf_at(*pages, page_index); };
    let page = pages.borrow_mut_typed(
        page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(page_lock_perm),
    );
    let Tracked(page_perm) = take_perm_2m(page);
    page.state = PageState::Allocated2m { state: page_state };
    page.owning_container = child_container_ptr;
    proof {
        lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, pages.lock_id_by_index(page_index));
        assert(page_perm.addr() == page_ptr) by { page_ptr_roundtrip(); };
        assert(page_array_wf(*pages)) by { reveal(page_array_wf); };
    }
    Tracked(page_perm)
}
pub fn page_allocator_map_insert_new(
    allocator_map: &mut PageAllocatorUnLockedMap, allocator_page: PagePtr, allocator_value: PageAllocator,
    Ghost(quota_lock_map): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>,
    Ghost(cache_lock_map): Ghost<Map<(RwLockPageAllocatorPtr, CpuId), TypedHeldLock>>,
    Ghost(global_pool_lock_map): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(page_perm): Tracked<PagePerm4k>,
)
    requires
        old(allocator_map).perms_wf(),
        !old(allocator_map).dom().contains(allocator_page),
        old(allocator_map).typed_quota_lock_map_aligned(quota_lock_map, lctx.thread_id()),
        old(allocator_map).typed_cache_lock_map_aligned(cache_lock_map, lctx.thread_id()),
        old(allocator_map).typed_global_pool_lock_map_aligned(global_pool_lock_map, lctx.thread_id()),
        allocator_value.inv(),
        !allocator_value.quota.locked(),
        !allocator_value.global_pool.locked(),
        forall|cpu_id: CpuId|
            #![trigger allocator_value.cpu_caches.spec_index(cpu_id).view().locked()]
            #![trigger allocator_value.cpu_caches.spec_index(cpu_id).view().locked_by_thread(lctx.thread_id())]
            #![trigger allocator_value.cpu_caches.spec_index(cpu_id).view().rlocked_by_thread(lctx.thread_id())]
            #![trigger allocator_value.cpu_caches.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())]
            index_valid(NUM_CPUS, cpu_id) ==> !allocator_value.cpu_caches.spec_index(cpu_id).view().locked(),
        page_perm.is_init(),
        page_perm.addr() == allocator_page,
    ensures
        final(allocator_map).perms_wf(),
        allocator_perms_wf(*old(allocator_map)) ==> allocator_perms_wf(*final(allocator_map)),
        final(allocator_map).dom() =~= old(allocator_map).dom().insert(allocator_page),
        final(allocator_map).spec_index(allocator_page) == allocator_value,
        forall|ptr: RwLockPageAllocatorPtr|
            #![trigger final(allocator_map).spec_index(ptr)]
            old(allocator_map).dom().contains(ptr) ==> final(allocator_map).spec_index(ptr) == old(allocator_map).spec_index(ptr),
        final(allocator_map).typed_quota_lock_map_aligned(quota_lock_map, lctx.thread_id()),
        final(allocator_map).typed_cache_lock_map_aligned(cache_lock_map, lctx.thread_id()),
        final(allocator_map).typed_global_pool_lock_map_aligned(global_pool_lock_map, lctx.thread_id()),
{
    allocator_map.retype_page_to_allocator_and_insert(allocator_page, allocator_value, Tracked(page_perm));
    proof {
        assert(allocator_perms_wf(*old(allocator_map)) ==> allocator_perms_wf(*allocator_map)) by { reveal(allocator_perms_wf); };
        assert(allocator_map.typed_quota_lock_map_aligned(quota_lock_map, lctx.thread_id())) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); };
        assert(allocator_map.typed_cache_lock_map_aligned(cache_lock_map, lctx.thread_id())) by { reveal(UnLockedMap::typed_cache_lock_map_aligned); };
        assert(allocator_map.typed_global_pool_lock_map_aligned(global_pool_lock_map, lctx.thread_id())) by { reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
    }
}
}
