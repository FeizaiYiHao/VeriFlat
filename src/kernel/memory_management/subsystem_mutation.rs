use vstd::prelude::*;
use crate::*;
use super::subsystem_mutation_eof::*;

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
    proof {
        assert(page_array_retype_owned_4k_eof_transition_framing(*old(page_array), *page_array, page_index)) by { reveal(page_array_retype_owned_4k_eof_transition_framing); };
        page_array_retype_owned_4k_eof(*old(page_array), *page_array, page_index);
    }
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
        assert(page_array_add_4k_mapping_eof_transition_framing(*old(page_array), *page_array, page_index)) by { reveal(page_array_add_4k_mapping_eof_transition_framing); };
        page_array_add_4k_mapping_eof(*old(page_array), *page_array, page_index);
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
        assert(page_array_add_4k_iommu_mapping_eof_transition_framing(*old(page_array), *page_array, page_index)) by { reveal(page_array_add_4k_iommu_mapping_eof_transition_framing); };
        page_array_add_4k_iommu_mapping_eof(*old(page_array), *page_array, page_index);
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
    proof {
        assert(page_array_remove_4k_mapping_without_free_eof_transition_framing(*old(page_array), *page_array, page_index)) by { reveal(page_array_remove_4k_mapping_without_free_eof_transition_framing); };
        page_array_remove_4k_mapping_without_free_eof(*old(page_array), *page_array, page_index);
    }
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
    proof {
        assert(page_array_remove_last_4k_mapping_to_cache_eof_transition_framing(*old(page_array), *page_array, page_index)) by { reveal(page_array_remove_last_4k_mapping_to_cache_eof_transition_framing); };
        page_array_remove_last_4k_mapping_to_cache_eof(*old(page_array), *page_array, page_index);
    }
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
    proof {
        assert(page_array_remove_4k_iommu_mapping_without_free_eof_transition_framing(*old(page_array), *page_array, page_index)) by { reveal(page_array_remove_4k_iommu_mapping_without_free_eof_transition_framing); };
        page_array_remove_4k_iommu_mapping_without_free_eof(*old(page_array), *page_array, page_index);
    }
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
    proof {
        assert(page_array_remove_last_4k_iommu_mapping_to_cache_eof_transition_framing(*old(page_array), *page_array, page_index)) by { reveal(page_array_remove_last_4k_iommu_mapping_to_cache_eof_transition_framing); };
        page_array_remove_last_4k_iommu_mapping_to_cache_eof(*old(page_array), *page_array, page_index);
    }
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
    proof {
        assert(page_array_retire_kernel_object_4k_to_cache_eof_transition_framing(*old(page_array), *page_array, page_index)) by { reveal(page_array_retire_kernel_object_4k_to_cache_eof_transition_framing); };
        page_array_retire_kernel_object_4k_to_cache_eof(*old(page_array), *page_array, page_index);
    }
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
    proof {
        assert(page_array_retire_kernel_object_2m_to_global_eof_transition_framing(*old(page_array), *page_array, page_index)) by { reveal(page_array_retire_kernel_object_2m_to_global_eof_transition_framing); };
        page_array_retire_kernel_object_2m_to_global_eof(*old(page_array), *page_array, page_index);
    }
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
    proof {
        assert(page_array_retire_kernel_object_4k_to_global_eof_transition_framing(*old(page_array), *page_array, page_index)) by { reveal(page_array_retire_kernel_object_4k_to_global_eof_transition_framing); };
        page_array_retire_kernel_object_4k_to_global_eof(*old(page_array), *page_array, page_index);
    }
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
    proof {
        assert(page_array.spec_index(page_index).view().view().inv()) by { reveal(Page::mappings_va_valid); };
        assert(page_array_move_free_4k_to_global_list_eof_transition_framing(*old(page_array), *page_array, page_index)) by { reveal(page_array_move_free_4k_to_global_list_eof_transition_framing); };
        page_array_move_free_4k_to_global_list_eof(*old(page_array), *page_array, page_index);
    }
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
    proof {
        assert(page_array.spec_index(page_index).view().view().inv()) by { reveal(Page::mappings_va_valid); };
        assert(page_array_move_free_4k_to_cpu_cache_eof_transition_framing(*old(page_array), *page_array, page_index)) by { reveal(page_array_move_free_4k_to_cpu_cache_eof_transition_framing); };
        page_array_move_free_4k_to_cpu_cache_eof(*old(page_array), *page_array, page_index);
    }
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
        assert(page_array_retype_owned_4k_for_container_eof_transition_framing(*old(pages), *pages, page_index)) by { reveal(page_array_retype_owned_4k_for_container_eof_transition_framing); reveal(Page::mappings_va_valid); };
        page_array_retype_owned_4k_for_container_eof(*old(pages), *pages, page_index);
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
    proof {
        assert(page_array_retype_owned_2m_for_container_eof_transition_framing(*old(pages), *pages, page_index)) by { reveal(page_array_retype_owned_2m_for_container_eof_transition_framing); reveal(Page::mappings_va_valid); };
        page_array_retype_owned_2m_for_container_eof(*old(pages), *pages, page_index);
    }
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
        assert(page_allocator_map_insert_new_eof_transition_framing(*old(allocator_map), *allocator_map, allocator_page, allocator_value)) by { reveal(page_allocator_map_insert_new_eof_transition_framing); };
        page_allocator_map_insert_new_eof(*old(allocator_map), *allocator_map, allocator_page, allocator_value);
        assert(allocator_map.typed_quota_lock_map_aligned(quota_lock_map, lctx.thread_id())) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); };
        assert(allocator_map.typed_cache_lock_map_aligned(cache_lock_map, lctx.thread_id())) by { reveal(UnLockedMap::typed_cache_lock_map_aligned); };
        assert(allocator_map.typed_global_pool_lock_map_aligned(global_pool_lock_map, lctx.thread_id())) by { reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
    }
}
}
