use vstd::prelude::*;
use crate::*;
use vstd::simple_pptr::PointsTo;

verus! {
pub fn page_array_retype_owned_4k(
    page_array: &mut PageLockedArray, page_index: PageIndex, new_state: PageState, Ghost(page_locks): Ghost<Map<PageIndex, TypedHeldLock>>, Tracked(lctx): Tracked<&LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>,
) -> (ret: Tracked<PagePerm4k>)
    requires
        page_array_wf(*old(page_array)),
        index_valid(NUM_PAGES, page_index),
        old(page_array).typed_lock_map_aligned(page_locks, lctx.thread_id()),
        typed_lock_map_contains_mode(page_locks, page_index, TypedLockMode::Write),
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == lctx.thread_id(),
        page_lock_perm.lock_id() == old(page_array).spec_index(page_index).view().locking_thread()->Write_lock_id,
        old(page_array).spec_index(page_index).view().view().state is Owned4k,
        new_state is Allocated4k,
    ensures
        page_array_wf(*final(page_array)),
        final(page_array).inv(),
        final(page_array).spec_index(page_index).view().inv(),
        final(page_array).entries_unchanged_except(old(page_array), page_index),
        final(page_array).typed_lock_map_aligned(page_locks.insert(page_index, TypedHeldLock { lock_id: final(page_array).lock_id_by_index(page_index), mode: TypedLockMode::Write }), lctx.thread_id()),
        final(page_array).spec_index(page_index).view().locking_thread() == old(page_array).spec_index(page_index).view().locking_thread(),
        final(page_array).spec_index(page_index).view().being_killed() == old(page_array).spec_index(page_index).view().being_killed(),
        final(page_array).spec_index(page_index).view().view() == (Page { state: new_state, perm_4k: final(page_array).spec_index(page_index).view().view().perm_4k, ..old(page_array).spec_index(page_index).view().view() }),
        final(page_array).spec_index(page_index).view().view_rodata() == old(page_array).spec_index(page_index).view().view_rodata(),
        final(page_array).spec_index(page_index).view().view_ghost() == old(page_array).spec_index(page_index).view().view_ghost(),
        final(page_array).spec_index(page_index).view().view().state == new_state,
        final(page_array).spec_index(page_index).view().view().perm_4k.view().is_none(),
        final(page_array).spec_index(page_index).view().view().addr == old(page_array).spec_index(page_index).view().view().addr,
        final(page_array).spec_index(page_index).view().view().is_io_page == old(page_array).spec_index(page_index).view().view().is_io_page,
        final(page_array).spec_index(page_index).view().view().ref_count == old(page_array).spec_index(page_index).view().view().ref_count,
        final(page_array).spec_index(page_index).view().view().owning_container == old(page_array).spec_index(page_index).view().view().owning_container,
        final(page_array).spec_index(page_index).view().view().mappings() == old(page_array).spec_index(page_index).view().view().mappings(),
        final(page_array).spec_index(page_index).view().view().iommu_mappings() == old(page_array).spec_index(page_index).view().view().iommu_mappings(),
        final(page_array).spec_index(page_index).view().view().free_list_node_storage == old(page_array).spec_index(page_index).view().view().free_list_node_storage,
        final(page_array).spec_index(page_index).view().view().free_list == old(page_array).spec_index(page_index).view().view().free_list,
        final(page_array).spec_index(page_index).view().view().perm_2m.view() == old(page_array).spec_index(page_index).view().view().perm_2m.view(),
        final(page_array).spec_index(page_index).view().view().perm_1g.view() == old(page_array).spec_index(page_index).view().view().perm_1g.view(),
        ret.view().is_init(),
        ret.view().addr() == final(page_array).spec_index(page_index).view().view().addr,
{
    assert(page_array.inv() && page_array.spec_index(page_index).view().is_init() && page_array.spec_index(page_index).view().view().inv()) by { page_array_wf_map(*page_array); page_array_wf_at(*page_array, page_index); };
    let page = page_array.borrow_mut_typed(page_index, Ghost(page_locks), Tracked(lctx), Tracked(page_lock_perm));
    let ret = retype_owned_4k_to_kernel_object(page, new_state);
    proof { assert(page_array_wf(*page_array)) by { reveal(page_array_wf); }; }
    ret
}

pub fn page_array_add_4k_mapping(page_array: &mut PageLockedArray, page_index: PageIndex, pagetable_ptr: RwLockPageTableRoot, va: VAddr, Tracked(lctx): Tracked<&LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>)
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
        final(page_array).spec_index(page_index).view().view().mappings() == old(page_array).spec_index(page_index).view().view().mappings().insert((pagetable_ptr, va)),
        final(page_array).spec_index(page_index).view().view().iommu_mappings() == old(page_array).spec_index(page_index).view().view().iommu_mappings(),
        final(page_array).spec_index(page_index).view().view().ref_count == old(page_array).spec_index(page_index).view().view().ref_count + 1,
        final(page_array).spec_index(page_index).view().view().addr == old(page_array).spec_index(page_index).view().view().addr,
        final(page_array).spec_index(page_index).view().view().state == old(page_array).spec_index(page_index).view().view().state,
        final(page_array).spec_index(page_index).view().view().is_io_page == old(page_array).spec_index(page_index).view().view().is_io_page,
        final(page_array).spec_index(page_index).view().view().owning_container == old(page_array).spec_index(page_index).view().view().owning_container,
        final(page_array).spec_index(page_index).view().view().free_list_node_storage == old(page_array).spec_index(page_index).view().view().free_list_node_storage,
        final(page_array).spec_index(page_index).view().view().free_list == old(page_array).spec_index(page_index).view().view().free_list,
        final(page_array).spec_index(page_index).view().view().perm_4k.view() == old(page_array).spec_index(page_index).view().view().perm_4k.view(),
        final(page_array).spec_index(page_index).view().view().perm_2m.view() == old(page_array).spec_index(page_index).view().view().perm_2m.view(),
        final(page_array).spec_index(page_index).view().view().perm_1g.view() == old(page_array).spec_index(page_index).view().view().perm_1g.view(),
{
    assert(page_array.inv() && page_array.spec_index(page_index).view().inv()) by { page_array_wf_map(*page_array); page_array_wf_at(*page_array, page_index); };
    let page = page_array.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(page_lock_perm));
    add_4k_mapping(page, pagetable_ptr, va);
    proof {
        assert(page_array_wf(*page_array)) by { reveal(page_array_wf); };
        assert(hugepage_2m_wf(*page_array)) by { hugepage_2m_wf_preserved_for_page_state_eq(*old(page_array), *page_array); };
        assert(hugepage_1g_wf(*page_array)) by { hugepage_1g_wf_preserved_for_page_state_eq(*old(page_array), *page_array); };
    }
}

/// IOMMU mirror of `page_array_add_4k_mapping`: record `(iommu_table_ptr, iova)` in the page's `iommu_mappings`.
pub fn page_array_add_4k_iommu_mapping(page_array: &mut PageLockedArray, page_index: PageIndex, iommu_table_ptr: RwLockPageTableRoot, iova: VAddr, Tracked(lctx): Tracked<&LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>)
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
        iova_4k_valid(iova),
        !old(page_array).spec_index(page_index).view().view().iommu_mappings().contains((iommu_table_ptr, iova)),
        old(page_array).spec_index(page_index).view().view().ref_count < usize::MAX,
    ensures
        page_array_wf(*final(page_array)),
        hugepage_2m_wf(*final(page_array)),
        hugepage_1g_wf(*final(page_array)),
        final(page_array).entries_unchanged_except(old(page_array), page_index),
        final(page_array).typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id()),
        final(page_array).spec_index(page_index).view().locking_thread() == old(page_array).spec_index(page_index).view().locking_thread(),
        final(page_array).spec_index(page_index).view().being_killed() == old(page_array).spec_index(page_index).view().being_killed(),
        final(page_array).spec_index(page_index).view().view().iommu_mappings() == old(page_array).spec_index(page_index).view().view().iommu_mappings().insert((iommu_table_ptr, iova)),
        final(page_array).spec_index(page_index).view().view().mappings() == old(page_array).spec_index(page_index).view().view().mappings(),
        final(page_array).spec_index(page_index).view().view().ref_count == old(page_array).spec_index(page_index).view().view().ref_count + 1,
        final(page_array).spec_index(page_index).view().view().addr == old(page_array).spec_index(page_index).view().view().addr,
        final(page_array).spec_index(page_index).view().view().state == old(page_array).spec_index(page_index).view().view().state,
        final(page_array).spec_index(page_index).view().view().is_io_page == old(page_array).spec_index(page_index).view().view().is_io_page,
        final(page_array).spec_index(page_index).view().view().owning_container == old(page_array).spec_index(page_index).view().view().owning_container,
        final(page_array).spec_index(page_index).view().view().free_list_node_storage == old(page_array).spec_index(page_index).view().view().free_list_node_storage,
        final(page_array).spec_index(page_index).view().view().free_list == old(page_array).spec_index(page_index).view().view().free_list,
        final(page_array).spec_index(page_index).view().view().perm_4k.view() == old(page_array).spec_index(page_index).view().view().perm_4k.view(),
        final(page_array).spec_index(page_index).view().view().perm_2m.view() == old(page_array).spec_index(page_index).view().view().perm_2m.view(),
        final(page_array).spec_index(page_index).view().view().perm_1g.view() == old(page_array).spec_index(page_index).view().view().perm_1g.view(),
{
    assert(page_array.inv() && page_array.spec_index(page_index).view().inv()) by { page_array_wf_map(*page_array); page_array_wf_at(*page_array, page_index); };
    let page = page_array.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(page_lock_perm));
    add_4k_iommu_mapping(page, iommu_table_ptr, iova);
    proof {
        assert(page_array_wf(*page_array)) by { reveal(page_array_wf); };
        assert(hugepage_2m_wf(*page_array)) by { hugepage_2m_wf_preserved_for_page_state_eq(*old(page_array), *page_array); };
        assert(hugepage_1g_wf(*page_array)) by { hugepage_1g_wf_preserved_for_page_state_eq(*old(page_array), *page_array); };
    }
}

/// Install the present 4K leaf `target_entry` in the 2M window of `indices` of page table `pagetable_ptr`: this thread holds
/// the table's big read lock and that window lock; only the window half `pt_lower[pagetable_ptr]` changes.
pub fn pagetable_map_insert_4k(
    pagetable_map: &PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index, L1Index), target_l1_ptr: PageMapPtr, target_entry: &MapEntry,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*pagetable_map),
        pagetable_lower_wf(*pagetable_map, *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *old(pt_lower)),
        pagetable_map.dom().contains(pagetable_ptr),
        pagetable_map.typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_map.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        page_table_key_4k_valid::<PT_TYPE>(spec_index2va(indices)),
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_4k_l1(indices.0, indices.1, indices.2, indices.3) is None
            || !pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().dom().contains(spec_index2va(indices)),
        page_ptr_valid(target_entry.addr),
        target_entry.present,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*pagetable_map, *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *final(pt_lower)),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).page_closure() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).page_closure(),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_4k() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().insert(spec_index2va(indices), *target_entry),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_2m() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_2m(),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_lock == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_lock,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
            pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.map_4k_page(Tracked(lower), indices.0, indices.1, indices.2, indices.3, target_l1_ptr, target_entry, Tracked(&mut *lctx));
    proof {
        let post_c = PageTableC { higher: *pagetable, lower: *lower };
        assert(pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        let va = spec_index2va(indices);
        assert(pagetable_map.spec_index(pagetable_ptr).locking_thread() is Read) by { pagetable_map.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); };
        assert(pagetable_map_insert_4k_eof_transition_framing(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, va, *target_entry)) by {
            reveal(pagetable_map_insert_4k_eof_transition_framing);
        };
        pagetable_map_insert_4k_eof(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, va, *target_entry, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id());
    }
}

/// Install the present 4K leaf `target_entry` in the 2M window of `indices` of page table `pagetable_ptr`: this thread holds
/// the table's big write lock and that window lock; only the window half `pt_lower[pagetable_ptr]` changes, and the lock's
/// ghost slot keeps a copy of it.
pub fn pagetable_map_insert_4k_wlocked(
    pagetable_map: &mut PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index, L1Index), target_l1_ptr: PageMapPtr, target_entry: &MapEntry,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        pagetable_lower_wf(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*old(pagetable_map), *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*old(pagetable_map), *old(pt_lower)),
        old(pagetable_map).dom().contains(pagetable_ptr),
        old(pagetable_map).typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        page_table_key_4k_valid::<PT_TYPE>(spec_index2va(indices)),
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_4k_l1(indices.0, indices.1, indices.2, indices.3) is None
            || !pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().dom().contains(spec_index2va(indices)),
        page_ptr_valid(target_entry.addr),
        target_entry.present,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        pagetable_perms_wf(*final(pagetable_map)),
        final(pagetable_map).unchanged_except(old(pagetable_map), pagetable_ptr),
        final(pagetable_map).typed_lock_map_aligned(final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        final(pagetable_map).lock_id_by_key(pagetable_ptr) == old(pagetable_map).lock_id_by_key(pagetable_ptr),
        final(pagetable_map).spec_index(pagetable_ptr).locking_thread() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread(),
        final(pagetable_map).spec_index(pagetable_ptr).being_killed() == old(pagetable_map).spec_index(pagetable_ptr).being_killed(),
        final(pagetable_map).spec_index(pagetable_ptr).view() == old(pagetable_map).spec_index(pagetable_ptr).view(),
        final(pagetable_map).spec_index(pagetable_ptr).view_ghost() == final(pt_lower).spec_index(pagetable_ptr),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*final(pagetable_map), *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().insert(spec_index2va(indices), *target_entry),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_lock == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_lock,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
            old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.map_4k_page(Tracked(lower), indices.0, indices.1, indices.2, indices.3, target_l1_ptr, target_entry, Tracked(&mut *lctx));
    proof {
        let post_c = PageTableC { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        let va = spec_index2va(indices);
        assert(pagetable_map_insert_4k_wlocked_eof_transition_framing(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, va, *target_entry)) by {
            reveal(pagetable_map_insert_4k_wlocked_eof_transition_framing);
        };
        pagetable_map_insert_4k_wlocked_eof(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, va, *target_entry, lctx.pagetable_window_lock_map(),
            lctx.pagetable_lock_map(), lctx.thread_id());
    }
}

/// Link the empty L1 page `page_map_ptr` into the 2M window of `indices` of page table `pagetable_ptr` at L2 page `target_l2_ptr`:
/// this thread holds the table's big read lock and that window lock; only the window half `pt_lower[pagetable_ptr]` changes.
pub fn pagetable_map_create_entry_l2(
    pagetable_map: &PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index, L1Index), target_l2_ptr: PageMapPtr, page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*pagetable_map),
        pagetable_lower_wf(*pagetable_map, *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *old(pt_lower)),
        pagetable_map.dom().contains(pagetable_ptr),
        pagetable_map.typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_map.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None,
        page_ptr_valid(page_map_ptr),
        !pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).page_closure().contains(page_map_ptr),
        page_map_perm.addr() == page_map_ptr,
        page_map_perm.is_init(),
        page_map_perm.value().wf(),
        forall|i: usize|
            #![trigger page_map_perm.value().spec_index(i).is_empty()]
            #![trigger page_map_perm.value().spec_index(i).perm.present]
            #![trigger page_map_perm.value().spec_index(i).perm.ps]
            #![trigger page_map_perm.value().spec_index(i).perm.kernel_present]
            pei_valid(i) ==> page_map_perm.value().spec_index(i).is_empty(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*pagetable_map, *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *final(pt_lower)),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).page_closure() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).page_closure().insert(page_map_ptr),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_4k() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k(),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_2m() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_2m(),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_lock == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_lock,
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == page_map_ptr,
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
            pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                ==> pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.create_entry_l2(Tracked(lower), indices.0, indices.1, indices.2, target_l2_ptr, page_map_ptr, Tracked(page_map_perm), Tracked(&mut *lctx));
    proof {
        let post_c = PageTableC { higher: *pagetable, lower: *lower };
        assert(pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(pagetable_map.spec_index(pagetable_ptr).locking_thread() is Read) by { pagetable_map.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); };
        assert(pagetable_map_create_entry_l2_eof_transition_framing(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr)) by {
            reveal(pagetable_map_create_entry_l2_eof_transition_framing);
        };
        pagetable_map_create_entry_l2_eof(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id());
    }
}

/// Link the empty L1 page `page_map_ptr` into the 2M window of `indices` of page table `pagetable_ptr` at L2 page `target_l2_ptr`:
/// this thread holds the table's big write lock and that window lock; only the window half `pt_lower[pagetable_ptr]` changes, and
/// the lock's ghost slot keeps a copy of it.
pub fn pagetable_map_create_entry_l2_wlocked(
    pagetable_map: &mut PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index, L1Index), target_l2_ptr: PageMapPtr, page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        pagetable_lower_wf(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*old(pagetable_map), *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*old(pagetable_map), *old(pt_lower)),
        old(pagetable_map).dom().contains(pagetable_ptr),
        old(pagetable_map).typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None,
        page_ptr_valid(page_map_ptr),
        !pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure().contains(page_map_ptr),
        page_map_perm.addr() == page_map_ptr,
        page_map_perm.is_init(),
        page_map_perm.value().wf(),
        forall|i: usize|
            #![trigger page_map_perm.value().spec_index(i).is_empty()]
            #![trigger page_map_perm.value().spec_index(i).perm.present]
            #![trigger page_map_perm.value().spec_index(i).perm.ps]
            #![trigger page_map_perm.value().spec_index(i).perm.kernel_present]
            pei_valid(i) ==> page_map_perm.value().spec_index(i).is_empty(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        pagetable_perms_wf(*final(pagetable_map)),
        final(pagetable_map).unchanged_except(old(pagetable_map), pagetable_ptr),
        final(pagetable_map).typed_lock_map_aligned(final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        final(pagetable_map).lock_id_by_key(pagetable_ptr) == old(pagetable_map).lock_id_by_key(pagetable_ptr),
        final(pagetable_map).spec_index(pagetable_ptr).locking_thread() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread(),
        final(pagetable_map).spec_index(pagetable_ptr).being_killed() == old(pagetable_map).spec_index(pagetable_ptr).being_killed(),
        final(pagetable_map).spec_index(pagetable_ptr).view() == old(pagetable_map).spec_index(pagetable_ptr).view(),
        final(pagetable_map).spec_index(pagetable_ptr).view_ghost() == final(pt_lower).spec_index(pagetable_ptr),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*final(pagetable_map), *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure().insert(page_map_ptr),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_lock == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_lock,
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == page_map_ptr,
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
            pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.create_entry_l2(Tracked(lower), indices.0, indices.1, indices.2, target_l2_ptr, page_map_ptr, Tracked(page_map_perm), Tracked(&mut *lctx));
    proof {
        let post_c = PageTableC { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(pagetable_map_create_entry_l2_wlocked_eof_transition_framing(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr)) by {
            reveal(pagetable_map_create_entry_l2_wlocked_eof_transition_framing);
        };
        pagetable_map_create_entry_l2_wlocked_eof(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(),
            lctx.thread_id());
    }
}

/// Link the empty L3 page `page_map_ptr` into root entry `indices.0` of page table `pagetable_ptr`: this thread holds the table's
/// big write lock; only the big-lock payload changes, so the window half and its ghost-slot copy stay.
pub fn pagetable_map_create_entry_l4(
    pagetable_map: &mut PageTableLockedMap, Tracked(pt_lower): Tracked<&PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index, L1Index), page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        pagetable_lower_wf(*old(pagetable_map), *pt_lower),
        pagetable_window_holders_hold_pagetable(*old(pagetable_map), *pt_lower),
        pagetable_hidden_leaves_only_when_locked(*old(pagetable_map), *pt_lower),
        pagetable_window_stale_cpus_only_when_locked(*old(pagetable_map), *pt_lower),
        pagetable_window_typed_lock_map_aligned(*old(pagetable_map), *pt_lower, old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*old(pagetable_map), *pt_lower),
        old(pagetable_map).dom().contains(pagetable_ptr),
        old(pagetable_map).typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        pagetable_c(*old(pagetable_map), *pt_lower, pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pagetable_c(*old(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l4(indices.0) is None,
        page_ptr_valid(page_map_ptr),
        !pagetable_c(*old(pagetable_map), *pt_lower, pagetable_ptr).page_closure().contains(page_map_ptr),
        page_map_perm.addr() == page_map_ptr,
        page_map_perm.is_init(),
        page_map_perm.value().wf(),
        forall|i: usize| #![trigger page_map_perm.value().spec_index(i)] pei_valid(i) ==> page_map_perm.value().spec_index(i).is_empty(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        pagetable_perms_wf(*final(pagetable_map)),
        final(pagetable_map).unchanged_except(old(pagetable_map), pagetable_ptr),
        final(pagetable_map).typed_lock_map_aligned(final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        final(pagetable_map).lock_id_by_key(pagetable_ptr) == old(pagetable_map).lock_id_by_key(pagetable_ptr),
        final(pagetable_map).spec_index(pagetable_ptr).locking_thread() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread(),
        final(pagetable_map).spec_index(pagetable_ptr).being_killed() == old(pagetable_map).spec_index(pagetable_ptr).being_killed(),
        final(pagetable_map).spec_index(pagetable_ptr).view_ghost() == old(pagetable_map).spec_index(pagetable_ptr).view_ghost(),
        pagetable_lower_wf(*final(pagetable_map), *pt_lower),
        pagetable_window_holders_hold_pagetable(*final(pagetable_map), *pt_lower),
        pagetable_hidden_leaves_only_when_locked(*final(pagetable_map), *pt_lower),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *pt_lower),
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *pt_lower, final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *pt_lower),
        pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).page_closure() == pagetable_c(*old(pagetable_map), *pt_lower, pagetable_ptr).page_closure().insert(page_map_ptr),
        pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).mapping_4k() == pagetable_c(*old(pagetable_map), *pt_lower, pagetable_ptr).mapping_4k(),
        pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).mapping_2m() == pagetable_c(*old(pagetable_map), *pt_lower, pagetable_ptr).mapping_2m(),
        pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).mapping_1g() == pagetable_c(*old(pagetable_map), *pt_lower, pagetable_ptr).mapping_1g(),
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end,
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries,
        final(pagetable_map).spec_index(pagetable_ptr).view().cr3 == old(pagetable_map).spec_index(pagetable_ptr).view().cr3,
        final(pagetable_map).spec_index(pagetable_ptr).view().pcid == old(pagetable_map).spec_index(pagetable_ptr).view().pcid,
        final(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr == old(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr,
        pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l4(indices.0) is Some,
        pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l4(indices.0)->0.addr == page_map_ptr,
        pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is None,
        pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_1g_l3(indices.0, indices.1) is None,
        forall|l4i: L4Index, l3i: L3Index| #![trigger pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i)]
            old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i)
                ==> pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i) == pagetable_c(*old(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
            pagetable_c(*old(pagetable_map), *pt_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pagetable_c(*old(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                ==> pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(*old(pagetable_map), *pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_mut_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow(pagetable_ptr);
    pagetable.create_entry_l4(Tracked(lower), indices.0, indices.1, page_map_ptr, Tracked(page_map_perm), Tracked(&mut *lctx));
    proof {
        let post_c = PageTableC { higher: *pagetable, lower: *lower };
        assert(pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        assert(pagetable_map_create_entry_l4_eof_transition_framing(*old(pagetable_map), *pagetable_map, *pt_lower, pagetable_ptr)) by {
            reveal(pagetable_map_create_entry_l4_eof_transition_framing);
        };
        pagetable_map_create_entry_l4_eof(*old(pagetable_map), *pagetable_map, *pt_lower, pagetable_ptr, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id());
    }
}

/// Link the empty L2 page `page_map_ptr` into L3 entry `indices.1` of `target_l3_ptr` in page table `pagetable_ptr`: this thread
/// holds the table's big write lock; windows `lo..=hi` of the new page start held by this thread and their lock perms are returned,
/// the other new windows start unlocked, and the lock's ghost slot keeps a copy of the new window half.
pub fn pagetable_map_create_entry_l3(
    pagetable_map: &mut PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index, L1Index), target_l3_ptr: PageMapPtr, page_map_ptr: PageMapPtr, Tracked(page_perm): Tracked<PagePerm4k>, lo: L2Index, hi: L2Index,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
) -> (ret: Tracked<Map<L2Index, LockPerm>>)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        pagetable_lower_wf(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*old(pagetable_map), *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*old(pagetable_map), *old(pt_lower)),
        old(pagetable_map).dom().contains(pagetable_ptr),
        old(pagetable_map).typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        KERNEL_MEM_END_L4INDEX <= indices.0,
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(lo) && pei_valid(hi) && lo <= hi,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(indices.0) is Some,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(indices.0)->0.addr == target_l3_ptr,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is None,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_1g_l3(indices.0, indices.1) is None,
        page_ptr_valid(page_map_ptr),
        !pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure().contains(page_map_ptr),
        page_perm.addr() == page_map_ptr,
        page_perm.is_init(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        nonwindow_typed_lock_maps_unchanged(old(lctx), final(lctx)),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (old(lctx).pagetable_window_lock_map().dom().contains((p, w))
                || (p == pagetable_ptr && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi)),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w))
                && !(p == pagetable_ptr && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi)
                ==> final(lctx).pagetable_window_lock_map().index((p, w)) == old(lctx).pagetable_window_lock_map().index((p, w)),
        forall|w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((pagetable_ptr, w))]
            w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi
                ==> final(lctx).pagetable_window_lock_map().index((pagetable_ptr, w)) == (TypedHeldLock { lock_id: window_lock_id_at(pagetable_ptr, w), mode: TypedLockMode::Write }),
        pagetable_perms_wf(*final(pagetable_map)),
        final(pagetable_map).unchanged_except(old(pagetable_map), pagetable_ptr),
        final(pagetable_map).typed_lock_map_aligned(final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        final(pagetable_map).lock_id_by_key(pagetable_ptr) == old(pagetable_map).lock_id_by_key(pagetable_ptr),
        final(pagetable_map).spec_index(pagetable_ptr).locking_thread() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread(),
        final(pagetable_map).spec_index(pagetable_ptr).being_killed() == old(pagetable_map).spec_index(pagetable_ptr).being_killed(),
        final(pagetable_map).spec_index(pagetable_ptr).view_ghost() == final(pt_lower).spec_index(pagetable_ptr),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*final(pagetable_map), *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure().insert(page_map_ptr),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_1g() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_1g(),
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end,
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries,
        final(pagetable_map).spec_index(pagetable_ptr).view().cr3 == old(pagetable_map).spec_index(pagetable_ptr).view().cr3,
        final(pagetable_map).spec_index(pagetable_ptr).view().pcid == old(pagetable_map).spec_index(pagetable_ptr).view().pcid,
        final(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr == old(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr,
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(indices.0) == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(indices.0),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == page_map_ptr,
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_1g_l3(indices.0, indices.1) is None,
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None,
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
            pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_lock
            == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_lock.insert(page_map_ptr, pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_lock_of(page_map_ptr)),
        forall|i: L2Index|
            #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_lock_of(page_map_ptr).lock_state(i)]
            pei_valid(i) && !(lo <= i <= hi) ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_lock_of(page_map_ptr).lock_state(i) is None,
        forall|i: L2Index| #![trigger ret.view().dom().contains(i)] ret.view().dom().contains(i) == (lo <= i <= hi),
        forall|i: L2Index| #![trigger ret.view().index(i)] lo <= i <= hi ==> {
            &&& pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_lock_of(page_map_ptr).lock_perm_match(i, &ret.view().index(i))
            &&& ret.view().index(i).state() is WriteLock
            &&& ret.view().index(i).ordering_lock_id() == window_lock_id(pagetable_ptr, indices.0, indices.1, i)
            &&& ret.view().index(i).thread_id() == final(lctx).thread_id()
        },
        forall|l4i: L4Index, l3i: L3Index| #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i)]
            old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && !(l4i == indices.0 && l3i == indices.1)
                ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i) == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)
                    == (pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)
                        || (l4i == indices.0 && l3i == indices.1 && lo <= l2i <= hi && thread_id == final(lctx).thread_id())),
        forall|l4i: L4Index, l3i: L3Index|
            #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_lock_of(pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_l2_page(l4i, l3i))]
            old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_exists(l4i, l3i)
                ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_lock_of(pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_l2_page(l4i, l3i))
                    == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_lock_of(pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_l2_page(l4i, l3i)),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_mut_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    let ret = pagetable.create_entry_l3(Tracked(lower), indices.0, indices.1, indices.2, target_l3_ptr, page_map_ptr, Tracked(page_perm), lo, hi, Ghost(pagetable_ptr),
        Tracked(&mut *lctx));
    proof {
        let post_c = PageTableC { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(pagetable_map_create_entry_l3_eof_transition_framing(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, indices.0, indices.1, lo, hi,
            lctx.thread_id())) by {
            reveal(pagetable_map_create_entry_l3_eof_transition_framing);
        };
        pagetable_map_create_entry_l3_eof(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, old(lctx).pagetable_window_lock_map(),
            lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id(), indices.0, indices.1, lo, hi);
    }
    ret
}

/// Clear the user present bit of the 4K leaf at `indices` of page table `pagetable_ptr`: this thread holds the table's big
/// write lock, which a table with hidden leaves needs, and the 2M window lock of `indices`; the lock's ghost slot keeps a
/// copy of the new window half.
pub fn pagetable_map_clear_4k_present(
    pagetable_map: &mut PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index, L1Index), target_l1_ptr: PageMapPtr, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        pagetable_lower_wf(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*old(pagetable_map), *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*old(pagetable_map), *old(pt_lower)),
        old(pagetable_map).dom().contains(pagetable_ptr),
        old(pagetable_map).typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().dom().contains(spec_index2va(indices)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        pagetable_perms_wf(*final(pagetable_map)),
        final(pagetable_map).unchanged_except(old(pagetable_map), pagetable_ptr),
        final(pagetable_map).typed_lock_map_aligned(final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        final(pagetable_map).lock_id_by_key(pagetable_ptr) == old(pagetable_map).lock_id_by_key(pagetable_ptr),
        final(pagetable_map).spec_index(pagetable_ptr).locking_thread() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread(),
        final(pagetable_map).spec_index(pagetable_ptr).being_killed() == old(pagetable_map).spec_index(pagetable_ptr).being_killed(),
        final(pagetable_map).spec_index(pagetable_ptr).view() == old(pagetable_map).spec_index(pagetable_ptr).view(),
        final(pagetable_map).spec_index(pagetable_ptr).view_ghost() == final(pt_lower).spec_index(pagetable_ptr),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*final(pagetable_map), *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().insert(spec_index2va(indices),
            MapEntry { present: false, ..pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().spec_index(spec_index2va(indices)) }),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_lock == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_lock,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.unmap_4k_page_user_view(Tracked(lower), indices.0, indices.1, indices.2, indices.3, target_l1_ptr, Tracked(&mut *lctx));
    proof {
        let post_c = PageTableC { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        let va = spec_index2va(indices);
        assert(pagetable_map_clear_4k_present_eof_transition_framing(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, va)) by {
            reveal(pagetable_map_clear_4k_present_eof_transition_framing);
        };
        pagetable_map_clear_4k_present_eof(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, va, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id());
    }
}

/// Remove the hidden 4K leaf at `indices` of page table `pagetable_ptr` after its stale TLB entries are flushed: this thread
/// holds the table's big write lock and the 2M window lock of `indices`; the lock's ghost slot keeps a copy of the new
/// window half.
pub fn pagetable_map_unmap_4k_kernel(
    pagetable_map: &mut PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index, L1Index), target_l1_ptr: PageMapPtr, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        pagetable_lower_wf(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*old(pagetable_map), *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*old(pagetable_map), *old(pt_lower)),
        old(pagetable_map).dom().contains(pagetable_ptr),
        old(pagetable_map).typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().dom().contains(spec_index2va(indices)),
        !pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().spec_index(spec_index2va(indices)).present,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        pagetable_perms_wf(*final(pagetable_map)),
        final(pagetable_map).unchanged_except(old(pagetable_map), pagetable_ptr),
        final(pagetable_map).typed_lock_map_aligned(final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        final(pagetable_map).lock_id_by_key(pagetable_ptr) == old(pagetable_map).lock_id_by_key(pagetable_ptr),
        final(pagetable_map).spec_index(pagetable_ptr).locking_thread() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread(),
        final(pagetable_map).spec_index(pagetable_ptr).being_killed() == old(pagetable_map).spec_index(pagetable_ptr).being_killed(),
        final(pagetable_map).spec_index(pagetable_ptr).view() == old(pagetable_map).spec_index(pagetable_ptr).view(),
        final(pagetable_map).spec_index(pagetable_ptr).view_ghost() == final(pt_lower).spec_index(pagetable_ptr),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*final(pagetable_map), *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().remove(spec_index2va(indices)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_lock == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_lock,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.unmap_4k_page_kernel(Tracked(lower), indices.0, indices.1, indices.2, indices.3, target_l1_ptr, Tracked(&mut *lctx));
    proof {
        let post_c = PageTableC { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        let va = spec_index2va(indices);
        assert(pagetable_map_unmap_4k_kernel_eof_transition_framing(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, va)) by {
            reveal(pagetable_map_unmap_4k_kernel_eof_transition_framing);
        };
        pagetable_map_unmap_4k_kernel_eof(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, va, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id());
    }
}

/// Clear the user present bit of the 4K leaf at `indices` of page table `pagetable_ptr`: this thread holds the table's big
/// read lock and the 2M window lock of `indices`; only the window half `pt_lower[pagetable_ptr]` changes.
pub fn pagetable_map_clear_4k_present_rlocked(
    pagetable_map: &PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index, L1Index), target_l1_ptr: PageMapPtr, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*pagetable_map),
        pagetable_lower_wf(*pagetable_map, *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *old(pt_lower)),
        pagetable_map.dom().contains(pagetable_ptr),
        pagetable_map.typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_map.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().dom().contains(spec_index2va(indices)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*pagetable_map, *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *final(pt_lower)),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).page_closure() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).page_closure(),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_4k() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().insert(spec_index2va(indices),
            MapEntry { present: false, ..pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().spec_index(spec_index2va(indices)) }),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_2m() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_2m(),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_lock == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_lock,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.unmap_4k_page_user_view(Tracked(lower), indices.0, indices.1, indices.2, indices.3, target_l1_ptr, Tracked(&mut *lctx));
    proof {
        let post_c = PageTableC { higher: *pagetable, lower: *lower };
        assert(pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(pagetable_map.spec_index(pagetable_ptr).locking_thread() is Read) by { pagetable_map.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); };
        assert(pagetable_map_clear_4k_present_rlocked_eof_transition_framing(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, spec_index2va(indices))) by {
            reveal(pagetable_map_clear_4k_present_rlocked_eof_transition_framing);
        };
        pagetable_map_clear_4k_present_rlocked_eof(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, indices, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id());
    }
}

/// Remove the hidden 4K leaf at `indices` of page table `pagetable_ptr` after its stale TLB entries are flushed: this thread
/// holds the table's big read lock and the 2M window lock of `indices`; only the window half `pt_lower[pagetable_ptr]` changes.
pub fn pagetable_map_unmap_4k_kernel_rlocked(
    pagetable_map: &PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index, L1Index), target_l1_ptr: PageMapPtr, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*pagetable_map),
        pagetable_lower_wf(*pagetable_map, *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *old(pt_lower)),
        pagetable_map.dom().contains(pagetable_ptr),
        pagetable_map.typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_map.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().dom().contains(spec_index2va(indices)),
        !pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().spec_index(spec_index2va(indices)).present,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*pagetable_map, *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *final(pt_lower)),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).page_closure() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).page_closure(),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_4k() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().remove(spec_index2va(indices)),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_2m() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_2m(),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_lock == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_lock,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.unmap_4k_page_kernel(Tracked(lower), indices.0, indices.1, indices.2, indices.3, target_l1_ptr, Tracked(&mut *lctx));
    proof {
        let post_c = PageTableC { higher: *pagetable, lower: *lower };
        assert(pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(pagetable_map.spec_index(pagetable_ptr).locking_thread() is Read) by { pagetable_map.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); };
        assert(pagetable_map_unmap_4k_kernel_rlocked_eof_transition_framing(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, spec_index2va(indices))) by {
            reveal(pagetable_map_unmap_4k_kernel_rlocked_eof_transition_framing);
        };
        pagetable_map_unmap_4k_kernel_rlocked_eof(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, spec_index2va(indices), lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(),
            lctx.thread_id());
    }
}

pub fn page_array_remove_4k_mapping_without_free(page_array: &mut PageLockedArray, page_index: PageIndex, pagetable_ptr: RwLockPageTableRoot, va: VAddr, Tracked(lctx): Tracked<&LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>)
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
        final(page_array).spec_index(page_index).view().view().iommu_mappings() == old(page_array).spec_index(page_index).view().view().iommu_mappings(),
        final(page_array).spec_index(page_index).view().view().ref_count == old(page_array).spec_index(page_index).view().view().ref_count - 1,
        final(page_array).spec_index(page_index).view().view().state == if old(page_array).spec_index(page_index).view().view().ref_count > 1 { PageState::Mapped4k } else { PageState::Unavailable },
        forall|i: PageIndex| #![trigger old(page_array).spec_index(i).view().view().state] #![trigger final(page_array).spec_index(i).view().view().state]
            index_valid(NUM_PAGES, i) && i != page_index ==> final(page_array).spec_index(i).view().view().state == old(page_array).spec_index(i).view().view().state,
        old(page_array).spec_index(page_index).view().view().ref_count > 1
            ==> final(page_array).spec_index(page_index).view().view() == (Page { mappings: final(page_array).spec_index(page_index).view().view().mappings,
                ref_count: final(page_array).spec_index(page_index).view().view().ref_count, ..old(page_array).spec_index(page_index).view().view() }),
        old(page_array).spec_index(page_index).view().view().ref_count == 1
            ==> final(page_array).spec_index(page_index).view().view() == (Page { state: PageState::Unavailable, mappings: final(page_array).spec_index(page_index).view().view().mappings, ref_count: 0,
                perm_4k: final(page_array).spec_index(page_index).view().view().perm_4k, ..old(page_array).spec_index(page_index).view().view() })
            && final(page_array).spec_index(page_index).view().view().perm_4k.view() is None,
{
    assert(page_array.inv() && page_array.spec_index(page_index).view().is_init() && page_array.spec_index(page_index).view().view().inv()) by { page_array_wf_map(*page_array); page_array_wf_at(*page_array, page_index); };
    let page = page_array.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(page_lock_perm));
    if page.ref_count > 1 { remove_shared_4k_mapping(page, pagetable_ptr, va); }
    else { remove_last_4k_io_mapping(page, pagetable_ptr, va); }
    proof { assert(page_array_wf(*page_array)) by { reveal(page_array_wf); }; }
}

pub fn page_array_remove_last_4k_mapping_to_cache(
    page_array: &mut PageLockedArray, page_index: PageIndex, pagetable_ptr: RwLockPageTableRoot, va: VAddr,
    allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, Tracked(lctx): Tracked<&LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>,
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
        final(page_array).spec_index(page_index).view().view() == (Page { state: PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } },
            mappings: Ghost(old(page_array).spec_index(page_index).view().view().mappings().remove((pagetable_ptr, va))), ref_count: 0,
            free_list_node_storage: final(page_array).spec_index(page_index).view().view().free_list_node_storage, ..old(page_array).spec_index(page_index).view().view() }),
        final(page_array).spec_index(page_index).view().view().mappings() == Set::<(RwLockPageTableRoot, VAddr)>::empty(),
        final(page_array).spec_index(page_index).view().view().free_list_node_storage.addr() == old(page_array).spec_index(page_index).view().view().free_list_node_storage.addr(),
        ret.0 == old(page_array).spec_index(page_index).view().view().free_list_node_storage.addr(),
        ret.1.view().is_init(),
        ret.1.view().addr() == ret.0,
        ret.1.view().value().view() == old(page_array).spec_index(page_index).view().view().addr,
{
    assert(page_array.inv() && page_array.spec_index(page_index).view().is_init() && page_array.spec_index(page_index).view().view().inv()) by { page_array_wf_map(*page_array); page_array_wf_at(*page_array, page_index); };
    let page = page_array.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(page_lock_perm));
    let ret = remove_last_4k_mapping_to_cache(page, pagetable_ptr, va, allocator_ptr, cpu_id);
    proof { assert(page_array_wf(*page_array)) by { reveal(page_array_wf); }; }
    ret
}

/// IOMMU-table mirrors of the four 4K unmap helpers above: the table is an `IommuTableLockedMap` entry held under
/// `iommu_table_lock_map`, and the page's reverse map is `iommu_mappings`. IOMMU pages are never MMIO.
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
        final(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr == old(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr,
{
    assert(iommu_table_map.perms_wf() && iommu_table_map.spec_index(iommu_table_ptr).inv()) by { iommu_table_perms_wf_map(*iommu_table_map); iommu_table_perms_wf_at(*iommu_table_map, iommu_table_ptr); };
    let iommu_table = iommu_table_map.borrow_mut_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_table_lock_perm));
    iommu_table.unmap_4k_page_user_view(indices.0, indices.1, indices.2, indices.3, target_l1_ptr, Tracked(&mut *lctx));
    proof { assert(iommu_table_perms_wf(*iommu_table_map)) by { reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); }; }
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
        !old(iommu_table_map).spec_index(iommu_table_ptr).view().mapping_4k().spec_index(spec_index2va(indices)).present,
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
        final(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr == old(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr,
{
    assert(iommu_table_map.perms_wf() && iommu_table_map.spec_index(iommu_table_ptr).inv()) by { iommu_table_perms_wf_map(*iommu_table_map); iommu_table_perms_wf_at(*iommu_table_map, iommu_table_ptr); };
    let iommu_table = iommu_table_map.borrow_mut_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_table_lock_perm));
    iommu_table.unmap_4k_page_kernel(indices.0, indices.1, indices.2, indices.3, target_l1_ptr, Tracked(&mut *lctx));
    proof { assert(iommu_table_perms_wf(*iommu_table_map)) by { reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); }; }
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
        final(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr == old(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger final(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
            old(iommu_table_map).spec_index(iommu_table_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> final(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(l4i, l3i, l2i) == old(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(l4i, l3i, l2i),
{
    assert(iommu_table_map.perms_wf() && iommu_table_map.spec_index(iommu_table_ptr).inv()) by { iommu_table_perms_wf_map(*iommu_table_map); iommu_table_perms_wf_at(*iommu_table_map, iommu_table_ptr); };
    let iommu_table = iommu_table_map.borrow_mut_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_table_lock_perm));
    iommu_table.map_4k_page(indices.0, indices.1, indices.2, indices.3, target_l1_ptr, target_entry, Tracked(&mut *lctx));
    proof { assert(iommu_table_perms_wf(*iommu_table_map)) by { reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); }; }
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
        final(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr == old(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l4(indices.0) is Some,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l4(indices.0)->0.addr == page_map_ptr,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) is None,
        final(iommu_table_map).spec_index(iommu_table_ptr).view().spec_resolve_mapping_1g_l3(indices.0, indices.1) is None,
{
    assert(iommu_table_map.perms_wf() && iommu_table_map.spec_index(iommu_table_ptr).inv()) by { iommu_table_perms_wf_map(*iommu_table_map); iommu_table_perms_wf_at(*iommu_table_map, iommu_table_ptr); };
    let iommu_table = iommu_table_map.borrow_mut_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_table_lock_perm));
    iommu_table.create_entry_l4(indices.0, indices.1, page_map_ptr, Tracked(page_map_perm), Tracked(&mut *lctx));
    proof { assert(iommu_table_perms_wf(*iommu_table_map)) by { reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); }; }
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
    proof { assert(iommu_table_perms_wf(*iommu_table_map)) by { reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); }; }
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
    proof { assert(iommu_table_perms_wf(*iommu_table_map)) by { reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); }; }
}

/// Unlink the table page that `scan` names from the write-held page table `pagetable_ptr` and return its memory; every mapping stays.
/// Lock preconditions per branch mirror `remove_structure_page`: an L1 page needs its 2M window lock, an L2 page needs all
/// 512 of its windows unlocked.
pub fn pagetable_map_remove_table_page(
    pagetable_map: &mut PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot, scan: StructureScan,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
) -> (ret: Tracked<PagePerm4k>)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        pagetable_lower_wf(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*old(pagetable_map), *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*old(pagetable_map), *old(pt_lower)),
        old(pagetable_map).dom().contains(pagetable_ptr),
        old(pagetable_map).typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_structure_scan_wf(scan),
        scan.spec_table_page() is Some,
        scan is L1 ==> pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(scan->L1_l4i, scan->L1_l3i, scan->L1_l2i, old(lctx).thread_id()),
        scan is L2 ==> old(lctx).pagetable_window_lock_map().dom().is_empty(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        pagetable_perms_wf(*final(pagetable_map)),
        final(pagetable_map).unchanged_except(old(pagetable_map), pagetable_ptr),
        final(pagetable_map).typed_lock_map_aligned(final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        final(pagetable_map).lock_id_by_key(pagetable_ptr) == old(pagetable_map).lock_id_by_key(pagetable_ptr),
        final(pagetable_map).spec_index(pagetable_ptr).locking_thread() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread(),
        final(pagetable_map).spec_index(pagetable_ptr).being_killed() == old(pagetable_map).spec_index(pagetable_ptr).being_killed(),
        final(pagetable_map).spec_index(pagetable_ptr).view_ghost() == final(pt_lower).spec_index(pagetable_ptr),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*final(pagetable_map), *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        scan is L2 ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus.filter_keys(|k: (PageMapPtr, L2Index)| k.0 != scan->L2_l2_p),
        !(scan is L2) ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure().remove(scan.spec_table_page()->Some_0),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_1g() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_1g(),
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end,
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries,
        final(pagetable_map).spec_index(pagetable_ptr).view().cr3 == old(pagetable_map).spec_index(pagetable_ptr).view().cr3,
        final(pagetable_map).spec_index(pagetable_ptr).view().pcid == old(pagetable_map).spec_index(pagetable_ptr).view().pcid,
        final(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr == old(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr,
        scan is L1 ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_lock == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_lock,
        scan is L1 ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).higher == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).higher,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        ret.view().is_init(),
        ret.view().addr() == scan.spec_table_page()->Some_0,
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    proof {
        if scan is L2 {
            assert(pagetable_map.spec_index(pagetable_ptr).wlocked_by_thread(lctx.thread_id())) by {
                pagetable_map.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
            };
            pagetable_l2_windows_unlocked_when_wlocker_holds_no_windows(*pagetable_map, *pt_lower, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr,
                scan->L2_l4i, scan->L2_l3i, scan->L2_l2_p);
        }
    }
    let pagetable = pagetable_map.borrow_mut_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    let ret = pagetable.remove_structure_page(Tracked(lower), scan, Tracked(&mut *lctx));
    proof {
        let post_c = PageTableC { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(pagetable_map_remove_table_page_eof_transition_framing(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr)) by {
            reveal(pagetable_map_remove_table_page_eof_transition_framing);
        };
        pagetable_map_remove_table_page_eof(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(),
            lctx.thread_id());
    }
    ret
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
        final(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr == old(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr,
        ret.view().is_init(),
        ret.view().addr() == scan.spec_table_page()->Some_0,
{
    assert(iommu_table_map.perms_wf() && iommu_table_map.spec_index(iommu_table_ptr).inv()) by { iommu_table_perms_wf_map(*iommu_table_map); iommu_table_perms_wf_at(*iommu_table_map, iommu_table_ptr); };
    let iommu_table = iommu_table_map.borrow_mut_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_table_lock_perm));
    let ret = iommu_table.remove_structure_page(scan, Tracked(&mut *lctx));
    proof { assert(iommu_table_perms_wf(*iommu_table_map)) by { reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); }; }
    ret
}

pub fn page_array_remove_4k_iommu_mapping_without_free(page_array: &mut PageLockedArray, page_index: PageIndex, iommu_table_ptr: RwLockPageTableRoot, iova: VAddr, Tracked(lctx): Tracked<&LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>)
    requires
        page_array_wf(*old(page_array)),
        index_valid(NUM_PAGES, page_index),
        old(page_array).typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.page_lock_map(), page_index, TypedLockMode::Write),
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == lctx.thread_id(),
        page_lock_perm.lock_id() == old(page_array).spec_index(page_index).view().locking_thread()->Write_lock_id,
        old(page_array).spec_index(page_index).view().view().state is Mapped4k,
        old(page_array).spec_index(page_index).view().view().iommu_mappings().contains((iommu_table_ptr, iova)),
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
        final(page_array).spec_index(page_index).view().view().iommu_mappings() == old(page_array).spec_index(page_index).view().view().iommu_mappings().remove((iommu_table_ptr, iova)),
        final(page_array).spec_index(page_index).view().view().mappings() == old(page_array).spec_index(page_index).view().view().mappings(),
        final(page_array).spec_index(page_index).view().view().owning_container == old(page_array).spec_index(page_index).view().view().owning_container,
        final(page_array).spec_index(page_index).view().view().ref_count == old(page_array).spec_index(page_index).view().view().ref_count - 1,
        final(page_array).spec_index(page_index).view().view().state == if old(page_array).spec_index(page_index).view().view().ref_count > 1 { PageState::Mapped4k } else { PageState::Unavailable },
        forall|i: PageIndex| #![trigger old(page_array).spec_index(i).view().view().state] #![trigger final(page_array).spec_index(i).view().view().state]
            index_valid(NUM_PAGES, i) && i != page_index ==> final(page_array).spec_index(i).view().view().state == old(page_array).spec_index(i).view().view().state,
        old(page_array).spec_index(page_index).view().view().ref_count > 1
            ==> final(page_array).spec_index(page_index).view().view() == (Page { iommu_mappings: final(page_array).spec_index(page_index).view().view().iommu_mappings,
                ref_count: final(page_array).spec_index(page_index).view().view().ref_count, ..old(page_array).spec_index(page_index).view().view() }),
        old(page_array).spec_index(page_index).view().view().ref_count == 1
            ==> final(page_array).spec_index(page_index).view().view() == (Page { state: PageState::Unavailable, iommu_mappings: final(page_array).spec_index(page_index).view().view().iommu_mappings,
                ref_count: 0, perm_4k: final(page_array).spec_index(page_index).view().view().perm_4k, ..old(page_array).spec_index(page_index).view().view() })
            && final(page_array).spec_index(page_index).view().view().perm_4k.view() is None,
{
    assert(page_array.inv() && page_array.spec_index(page_index).view().is_init() && page_array.spec_index(page_index).view().view().inv()) by { page_array_wf_map(*page_array); page_array_wf_at(*page_array, page_index); };
    let page = page_array.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(page_lock_perm));
    if page.ref_count > 1 { remove_shared_4k_iommu_mapping(page, iommu_table_ptr, iova); }
    else { remove_last_4k_iommu_io_mapping(page, iommu_table_ptr, iova); }
    proof { assert(page_array_wf(*page_array)) by { reveal(page_array_wf); }; }
}

pub fn page_array_remove_last_4k_iommu_mapping_to_cache(
    page_array: &mut PageLockedArray, page_index: PageIndex, iommu_table_ptr: RwLockPageTableRoot, iova: VAddr,
    allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, Tracked(lctx): Tracked<&LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>,
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
        old(page_array).spec_index(page_index).view().view().iommu_mappings().contains((iommu_table_ptr, iova)),
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
        final(page_array).spec_index(page_index).view().view() == (Page { state: PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } },
            iommu_mappings: Ghost(old(page_array).spec_index(page_index).view().view().iommu_mappings().remove((iommu_table_ptr, iova))), ref_count: 0,
            free_list_node_storage: final(page_array).spec_index(page_index).view().view().free_list_node_storage, ..old(page_array).spec_index(page_index).view().view() }),
        final(page_array).spec_index(page_index).view().view().iommu_mappings() == Set::<(RwLockPageTableRoot, VAddr)>::empty(),
        final(page_array).spec_index(page_index).view().view().mappings() == Set::<(RwLockPageTableRoot, VAddr)>::empty(),
        final(page_array).spec_index(page_index).view().view().free_list_node_storage.addr() == old(page_array).spec_index(page_index).view().view().free_list_node_storage.addr(),
        ret.0 == old(page_array).spec_index(page_index).view().view().free_list_node_storage.addr(),
        ret.1.view().is_init(),
        ret.1.view().addr() == ret.0,
        ret.1.view().value().view() == old(page_array).spec_index(page_index).view().view().addr,
{
    assert(page_array.inv() && page_array.spec_index(page_index).view().is_init() && page_array.spec_index(page_index).view().view().inv()) by { page_array_wf_map(*page_array); page_array_wf_at(*page_array, page_index); };
    let page = page_array.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(page_lock_perm));
    let ret = remove_last_4k_iommu_mapping_to_cache(page, iommu_table_ptr, iova, allocator_ptr, cpu_id);
    proof { assert(page_array_wf(*page_array)) by { reveal(page_array_wf); }; }
    ret
}

pub fn page_array_retire_kernel_object_4k_to_cache(
    page_array: &mut PageLockedArray, page_index: PageIndex, Tracked(perm): Tracked<PagePerm4k>, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
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
        old(page_array).spec_index(page_index).view().view().state is Allocated4k,
        perm.is_init(),
        perm.addr() == page_index2page_ptr(page_index),
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
        final(page_array).spec_index(page_index).view().view() == (Page { state: PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } },
            free_list_node_storage: final(page_array).spec_index(page_index).view().view().free_list_node_storage, perm_4k: final(page_array).spec_index(page_index).view().view().perm_4k,
            ..old(page_array).spec_index(page_index).view().view() }),
        final(page_array).spec_index(page_index).view().view().perm_4k.view() == Some(perm),
        final(page_array).spec_index(page_index).view().view().free_list_node_storage.addr() == old(page_array).spec_index(page_index).view().view().free_list_node_storage.addr(),
        ret.0 == old(page_array).spec_index(page_index).view().view().free_list_node_storage.addr(),
        ret.1.view().is_init(),
        ret.1.view().addr() == ret.0,
        ret.1.view().value().view() == old(page_array).spec_index(page_index).view().view().addr,
{
    assert(page_array.inv() && page_array.spec_index(page_index).view().is_init() && page_array.spec_index(page_index).view().view().inv()
        && page_array.spec_index(page_index).view().view().addr == page_index2page_ptr(page_index)) by { page_array_wf_map(*page_array); page_array_wf_at(*page_array, page_index); };
    let page = page_array.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(page_lock_perm));
    let ret = convert_kernel_object_4k_to_free_cache(page, Tracked(perm), allocator_ptr, cpu_id);
    proof { assert(page_array_wf(*page_array)) by { reveal(page_array_wf); }; }
    ret
}

/// Return the memory of the retired 2M kernel object at `page_index` to the global pool of `allocator_ptr`, owned by
/// `owning_container`; the write-held head page changes its lock id with its state.
pub fn page_array_retire_kernel_object_2m_to_global(
    page_array: &mut PageLockedArray, page_index: PageIndex, Tracked(perm): Tracked<PagePerm2m>, allocator_ptr: RwLockPageAllocatorPtr, owning_container: RwLockContainerPtr,
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
        old(page_array).spec_index(page_index).view().view().state is Allocated2m,
        perm.is_init(),
        perm.addr() == page_index2page_ptr(page_index),
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
        final(page_array).spec_index(page_index).view().view() == (Page { state: PageState::Free2m { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::GlobalList },
            owning_container, free_list_node_storage: final(page_array).spec_index(page_index).view().view().free_list_node_storage,
            perm_2m: final(page_array).spec_index(page_index).view().view().perm_2m, ..old(page_array).spec_index(page_index).view().view() }),
        final(page_array).spec_index(page_index).view().view().perm_2m.view() == Some(perm),
        final(page_array).spec_index(page_index).view().view().free_list_node_storage.addr() == old(page_array).spec_index(page_index).view().view().free_list_node_storage.addr(),
        ret.0 == old(page_array).spec_index(page_index).view().view().free_list_node_storage.addr(),
        ret.1.view().is_init(),
        ret.1.view().addr() == ret.0,
        ret.1.view().value().view() == old(page_array).spec_index(page_index).view().view().addr,
{
    assert(page_array.inv() && page_array.spec_index(page_index).view().is_init() && page_array.spec_index(page_index).view().view().inv()
        && page_array.spec_index(page_index).view().view().addr == page_index2page_ptr(page_index)) by { page_array_wf_map(*page_array); page_array_wf_at(*page_array, page_index); };
    let page = page_array.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(page_lock_perm));
    let ret = convert_kernel_object_2m_to_free_global(page, Tracked(perm), allocator_ptr, owning_container);
    proof { assert(page_array_wf(*page_array)) by { reveal(page_array_wf); }; }
    ret
}

/// Return the memory of the retired 4K kernel object at `page_index` to the global pool of `allocator_ptr`, owned by
/// `owning_container`; the write-held page changes its lock id with its state.
pub fn page_array_retire_kernel_object_4k_to_global(
    page_array: &mut PageLockedArray, page_index: PageIndex, Tracked(perm): Tracked<PagePerm4k>, allocator_ptr: RwLockPageAllocatorPtr, owning_container: RwLockContainerPtr,
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
        old(page_array).spec_index(page_index).view().view().state is Allocated4k,
        perm.is_init(),
        perm.addr() == page_index2page_ptr(page_index),
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
        final(page_array).spec_index(page_index).view().view() == (Page { state: PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::GlobalList },
            owning_container, free_list_node_storage: final(page_array).spec_index(page_index).view().view().free_list_node_storage,
            perm_4k: final(page_array).spec_index(page_index).view().view().perm_4k, ..old(page_array).spec_index(page_index).view().view() }),
        final(page_array).spec_index(page_index).view().view().perm_4k.view() == Some(perm),
        final(page_array).spec_index(page_index).view().view().free_list_node_storage.addr() == old(page_array).spec_index(page_index).view().view().free_list_node_storage.addr(),
        ret.0 == old(page_array).spec_index(page_index).view().view().free_list_node_storage.addr(),
        ret.1.view().is_init(),
        ret.1.view().addr() == ret.0,
        ret.1.view().value().view() == old(page_array).spec_index(page_index).view().view().addr,
{
    assert(page_array.inv() && page_array.spec_index(page_index).view().is_init() && page_array.spec_index(page_index).view().view().inv()
        && page_array.spec_index(page_index).view().view().addr == page_index2page_ptr(page_index)) by { page_array_wf_map(*page_array); page_array_wf_at(*page_array, page_index); };
    let page = page_array.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(page_lock_perm));
    let ret = convert_kernel_object_4k_to_free_global(page, Tracked(perm), allocator_ptr, owning_container);
    proof { assert(page_array_wf(*page_array)) by { reveal(page_array_wf); }; }
    ret
}

pub fn page_array_move_free_4k_to_global_list(page_array: &mut PageLockedArray, page_index: PageIndex, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, Tracked(lctx): Tracked<&LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>)
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
    assert(page_array.inv() && page_array.spec_index(page_index).view().is_init() && page_array.spec_index(page_index).view().view().inv()) by { page_array_wf_map(*page_array); page_array_wf_at(*page_array, page_index); };
    let page = page_array.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(page_lock_perm));
    page.state = PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::GlobalList };
    proof { assert(page_array.spec_index(page_index).view().view().inv()) by { reveal(Page::mappings_va_valid); }; assert(page_array_wf(*page_array)) by { reveal(page_array_wf); }; }
}

pub fn page_array_move_free_4k_to_cpu_cache(page_array: &mut PageLockedArray, page_index: PageIndex, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, Tracked(lctx): Tracked<&LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>)
    requires
        page_array_wf(*old(page_array)),
        index_valid(NUM_PAGES, page_index),
        index_valid(NUM_CPUS, cpu_id),
        old(page_array).typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.page_lock_map(), page_index, TypedLockMode::Write),
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == lctx.thread_id(),
        page_lock_perm.lock_id() == old(page_array).spec_index(page_index).view().locking_thread()->Write_lock_id,
        old(page_array).spec_index(page_index).view().view().state == (PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::GlobalList }),
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
        final(page_array).spec_index(page_index).view().view() == (Page { state: PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } }, ..old(page_array).spec_index(page_index).view().view() }),
{
    assert(page_array.inv() && page_array.spec_index(page_index).view().is_init() && page_array.spec_index(page_index).view().view().inv()) by { page_array_wf_map(*page_array); page_array_wf_at(*page_array, page_index); };
    let page = page_array.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(page_lock_perm));
    page.state = PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } };
    proof { assert(page_array.spec_index(page_index).view().view().inv()) by { reveal(Page::mappings_va_valid); }; assert(page_array_wf(*page_array)) by { reveal(page_array_wf); }; }
}

pub fn page_array_retype_owned_4k_for_container(pages: &mut PageLockedArray, child_container_ptr: RwLockContainerPtr, page_ptr: PagePtr, page_state: Allocated4KPageState,
    Ghost(page_locks): Ghost<Map<PageIndex, TypedHeldLock>>, Tracked(lctx): Tracked<&LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>) -> (ret: Tracked<PagePerm4k>)
    requires
        page_array_wf(*old(pages)),
        page_ptr_valid(page_ptr),
        old(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().state is Owned4k,
        old(pages).typed_lock_map_aligned(page_locks, lctx.thread_id()),
        typed_lock_map_contains_mode(page_locks, page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == lctx.thread_id(),
        page_lock_perm.lock_id() == old(pages).spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
    ensures
        final(pages).inv(),
        page_array_wf(*final(pages)),
        final(pages).entries_unchanged_except(old(pages), page_ptr2page_index(page_ptr)),
        final(pages).typed_lock_map_aligned(page_locks.insert(page_ptr2page_index(page_ptr), TypedHeldLock { lock_id: final(pages).lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write }), lctx.thread_id()),
        final(pages).spec_index(page_ptr2page_index(page_ptr)).view().locking_thread() == old(pages).spec_index(page_ptr2page_index(page_ptr)).view().locking_thread(),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().mappings()]
            #![trigger old(pages).spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().mappings() == old(pages).spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().iommu_mappings()]
            #![trigger old(pages).spec_index(index).view().view().iommu_mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().iommu_mappings() == old(pages).spec_index(index).view().view().iommu_mappings(),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().free_list]
            index_valid(NUM_PAGES, index) && index != page_ptr2page_index(page_ptr) ==> final(pages).spec_index(index).view().view().free_list == old(pages).spec_index(index).view().view().free_list,
        final(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Allocated4k { state: page_state }),
        final(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == child_container_ptr,
        page_lock_perm.lock_id() == final(pages).spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        ret.view().is_init(),
        ret.view().addr() == page_ptr,
{
    let page_index = page_ptr2page_index(page_ptr);
    assert(pages.inv() && pages.spec_index(page_index).view().is_init() && pages.spec_index(page_index).view().view().inv()
        && pages.spec_index(page_index).view().view().addr == page_index2page_ptr(page_index)) by { page_array_wf_map(*pages); page_array_wf_at(*pages, page_index); };
    let page = pages.borrow_mut_typed(page_index, Ghost(page_locks), Tracked(lctx), Tracked(page_lock_perm));
    let Tracked(page_perm) = retype_owned_4k_to_kernel_object(page, PageState::Allocated4k { state: page_state });
    page.owning_container = child_container_ptr;
    proof {
        assert(pages.spec_index(page_index).view().inv()) by { reveal(Page::mappings_va_valid); };
        assert(pages.spec_index(page_index).view().view().addr == page_index2page_ptr(page_index)) by { reveal(page_array_wf); };
        assert(page_array_wf(*pages)) by { reveal(page_array_wf); };
    }
    Tracked(page_perm)
}

pub fn page_array_retype_owned_2m_for_container(pages: &mut PageLockedArray, child_container_ptr: RwLockContainerPtr, page_ptr: PagePtr, page_state: Allocated2MPageState,
    Ghost(page_locks): Ghost<Map<PageIndex, TypedHeldLock>>, Tracked(lctx): Tracked<&LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>) -> (ret: Tracked<PagePerm2m>)
    requires
        page_array_wf(*old(pages)),
        page_ptr_2m_valid(page_ptr),
        old(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().state is Owned2m,
        old(pages).typed_lock_map_aligned(page_locks, lctx.thread_id()),
        typed_lock_map_contains_mode(page_locks, page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == lctx.thread_id(),
        page_lock_perm.lock_id() == old(pages).spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
    ensures
        final(pages).inv(),
        page_array_wf(*final(pages)),
        final(pages).entries_unchanged_except(old(pages), page_ptr2page_index(page_ptr)),
        final(pages).typed_lock_map_aligned(page_locks.insert(page_ptr2page_index(page_ptr), TypedHeldLock { lock_id: final(pages).lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write }), lctx.thread_id()),
        final(pages).spec_index(page_ptr2page_index(page_ptr)).view().locking_thread() == old(pages).spec_index(page_ptr2page_index(page_ptr)).view().locking_thread(),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().mappings()]
            #![trigger old(pages).spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().mappings() == old(pages).spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().iommu_mappings()]
            #![trigger old(pages).spec_index(index).view().view().iommu_mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().iommu_mappings() == old(pages).spec_index(index).view().view().iommu_mappings(),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().free_list]
            index_valid(NUM_PAGES, index) && index != page_ptr2page_index(page_ptr) ==> final(pages).spec_index(index).view().view().free_list == old(pages).spec_index(index).view().view().free_list,
        final(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Allocated2m { state: page_state }),
        final(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == child_container_ptr,
        page_lock_perm.lock_id() == final(pages).spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        ret.view().is_init(),
        ret.view().addr() == page_ptr,
{
    let page_index = page_ptr2page_index(page_ptr);
    assert(pages.inv() && pages.spec_index(page_index).view().is_init() && pages.spec_index(page_index).view().view().inv()
        && pages.spec_index(page_index).view().view().addr == page_index2page_ptr(page_index)) by { page_array_wf_map(*pages); page_array_wf_at(*pages, page_index); };
    let page = pages.borrow_mut_typed(page_index, Ghost(page_locks), Tracked(lctx), Tracked(page_lock_perm));
    let Tracked(page_perm) = take_perm_2m(page);
    page.state = PageState::Allocated2m { state: page_state };
    page.owning_container = child_container_ptr;
    proof { assert(page_array_wf(*pages)) by { reveal(page_array_wf); reveal(Page::mappings_va_valid); }; }
    Tracked(page_perm)
}

pub fn page_allocator_map_insert_new<const SIZE: usize>(
    allocator_map: &mut PageAllocatorUnLockedMap<SIZE>, allocator_page: PagePtr, allocator_value: PageAllocator<SIZE>,
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
        lctx.kernel_view_locking_state() is Acquire,
    ensures
        final(allocator_map).perms_wf(),
        allocator_perms_wf(*old(allocator_map)) ==> allocator_perms_wf(*final(allocator_map)),
        final(allocator_map).dom() =~= old(allocator_map).dom().insert(allocator_page),
        final(allocator_map).spec_index(allocator_page) == allocator_value,
        forall|ptr: RwLockPageAllocatorPtr| #![trigger final(allocator_map).spec_index(ptr)] old(allocator_map).dom().contains(ptr) ==> final(allocator_map).spec_index(ptr) == old(allocator_map).spec_index(ptr),
        final(allocator_map).typed_quota_lock_map_aligned(quota_lock_map, lctx.thread_id()),
        final(allocator_map).typed_cache_lock_map_aligned(cache_lock_map, lctx.thread_id()),
        final(allocator_map).typed_global_pool_lock_map_aligned(global_pool_lock_map, lctx.thread_id()),
{
    allocator_map.retype_page_to_allocator_and_insert(allocator_page, allocator_value, Tracked(page_perm), Tracked(lctx));
    proof {
        assert(allocator_perms_wf(*old(allocator_map)) ==> allocator_perms_wf(*allocator_map)) by { reveal(allocator_perms_wf); };
        assert(allocator_map.typed_quota_lock_map_aligned(quota_lock_map, lctx.thread_id())) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); };
        assert(allocator_map.typed_cache_lock_map_aligned(cache_lock_map, lctx.thread_id())) by { reveal(UnLockedMap::typed_cache_lock_map_aligned); };
        assert(allocator_map.typed_global_pool_lock_map_aligned(global_pool_lock_map, lctx.thread_id())) by { reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
    }
}
}
