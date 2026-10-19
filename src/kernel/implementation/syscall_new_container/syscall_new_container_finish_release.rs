use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_new_container_finish_eof::{release_backing_page_lock_group_eof, release_backing_page_lock_group_eof_transition_framing};
use super::*;
use super::syscall_new_container_tail_unlock::wunlock_new_container_2m_page_tails;

verus! {
/// The staged backing-page indices in release order, with the distinctness facts their release needs.
pub(super) fn staged_container_backing_page_indices(
    pages_4k: &ArrayVec<PagePtr, 9>, container_page: PagePtr, pcid_allocator_page: PagePtr,
) -> (ret: ((PageIndex, PageIndex, PageIndex, PageIndex, PageIndex), (PageIndex, PageIndex, PageIndex, PageIndex, PageIndex)))
    requires
        pages_4k.wf(),
        pages_4k.len() == 9,
        pages_4k.view().no_duplicates(),
        page_ptr_valid(pages_4k.view().spec_index(0)),
        page_ptr_valid(pages_4k.view().spec_index(1)),
        page_ptr_valid(pages_4k.view().spec_index(2)),
        page_ptr_valid(pages_4k.view().spec_index(3)),
        page_ptr_valid(pages_4k.view().spec_index(4)),
        page_ptr_valid(pages_4k.view().spec_index(5)),
        page_ptr_valid(pages_4k.view().spec_index(6)),
        page_ptr_valid(pages_4k.view().spec_index(7)),
        page_ptr_valid(pages_4k.view().spec_index(8)),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        container_page != pcid_allocator_page,
        pages_4k.view().to_set().disjoint(page_2m_all_ptrs(page_ptr2page_index(container_page))),
        pages_4k.view().to_set().disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        page_2m_all_ptrs(page_ptr2page_index(container_page)).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
    ensures
        ret.0 == (page_ptr2page_index(pages_4k.view().spec_index(0)), page_ptr2page_index(pages_4k.view().spec_index(1)), page_ptr2page_index(pages_4k.view().spec_index(2)), page_ptr2page_index(pages_4k.view().spec_index(3)), page_ptr2page_index(pages_4k.view().spec_index(8))),
        ret.1 == (page_ptr2page_index(pages_4k.view().spec_index(4)), page_ptr2page_index(pages_4k.view().spec_index(5)), page_ptr2page_index(pages_4k.view().spec_index(6)), page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page)),
        seq![ret.0.0, ret.0.1, ret.0.2, ret.0.3, ret.0.4].no_duplicates(),
        seq![ret.1.0, ret.1.1, ret.1.2, ret.1.3, ret.1.4].no_duplicates(),
        set![ret.0.0, ret.0.1, ret.0.2, ret.0.3, ret.0.4].disjoint(set![ret.1.0, ret.1.1, ret.1.2, ret.1.3, ret.1.4]),
        !set![ret.0.0, ret.0.1, ret.0.2, ret.0.3, ret.0.4].contains(page_ptr2page_index(pages_4k.view().spec_index(7))),
        !set![ret.1.0, ret.1.1, ret.1.2, ret.1.3, ret.1.4].contains(page_ptr2page_index(pages_4k.view().spec_index(7))),
{
    let first = (
        page_ptr2page_index(*pages_4k.get(0)), page_ptr2page_index(*pages_4k.get(1)), page_ptr2page_index(*pages_4k.get(2)), page_ptr2page_index(*pages_4k.get(3)),
        page_ptr2page_index(*pages_4k.get(8)),
    );
    let second = (
        page_ptr2page_index(*pages_4k.get(4)), page_ptr2page_index(*pages_4k.get(5)), page_ptr2page_index(*pages_4k.get(6)), page_ptr2page_index(container_page),
        page_ptr2page_index(pcid_allocator_page),
    );
    assert({
        &&& seq![first.0, first.1, first.2, first.3, first.4].no_duplicates()
        &&& seq![second.0, second.1, second.2, second.3, second.4].no_duplicates()
        &&& set![first.0, first.1, first.2, first.3, first.4].disjoint(set![second.0, second.1, second.2, second.3, second.4])
        &&& !set![first.0, first.1, first.2, first.3, first.4].contains(page_ptr2page_index(pages_4k.view().spec_index(7)))
        &&& !set![second.0, second.1, second.2, second.3, second.4].contains(page_ptr2page_index(pages_4k.view().spec_index(7)))
    }) by { page_ptr_roundtrip(); page_2m_all_ptrs_contains_head(second.3); page_2m_all_ptrs_contains_head(second.4); };
    (first, second)
}

/// Releases the two 2M tail ranges and exposes, for the staged backing pages, the lock-map and page facts the backing-page release needs.
pub(super) fn finish_staged_container_unlock_tails(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, pages_4k: &ArrayVec<PagePtr, 9>, container_page: PagePtr, pcid_allocator_page: PagePtr,
    Ghost(first): Ghost<(PageIndex, PageIndex, PageIndex, PageIndex, PageIndex)>, Ghost(second): Ghost<(PageIndex, PageIndex, PageIndex, PageIndex, PageIndex)>,
    Tracked(container_tail_lock_perms): Tracked<Map<PageIndex, LockPerm>>, Tracked(pcid_allocator_tail_lock_perms): Tracked<Map<PageIndex, LockPerm>>,
)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        pages_4k.len() == 9,
        page_ptr_valid(pages_4k.view().spec_index(0)),
        page_ptr_valid(pages_4k.view().spec_index(1)),
        page_ptr_valid(pages_4k.view().spec_index(2)),
        page_ptr_valid(pages_4k.view().spec_index(3)),
        page_ptr_valid(pages_4k.view().spec_index(4)),
        page_ptr_valid(pages_4k.view().spec_index(5)),
        page_ptr_valid(pages_4k.view().spec_index(6)),
        page_ptr_valid(pages_4k.view().spec_index(7)),
        page_ptr_valid(pages_4k.view().spec_index(8)),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        container_page != pcid_allocator_page,
        page_2m_tail_indices(page_ptr2page_index(container_page)).disjoint(set![
            page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page), page_ptr2page_index(pages_4k.view().spec_index(0)),
            page_ptr2page_index(pages_4k.view().spec_index(1)), page_ptr2page_index(pages_4k.view().spec_index(2)),
            page_ptr2page_index(pages_4k.view().spec_index(3)), page_ptr2page_index(pages_4k.view().spec_index(4)),
            page_ptr2page_index(pages_4k.view().spec_index(5)), page_ptr2page_index(pages_4k.view().spec_index(6)),
            page_ptr2page_index(pages_4k.view().spec_index(7)), page_ptr2page_index(pages_4k.view().spec_index(8)),
        ]),
        page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).disjoint(set![
            page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page), page_ptr2page_index(pages_4k.view().spec_index(0)),
            page_ptr2page_index(pages_4k.view().spec_index(1)), page_ptr2page_index(pages_4k.view().spec_index(2)),
            page_ptr2page_index(pages_4k.view().spec_index(3)), page_ptr2page_index(pages_4k.view().spec_index(4)),
            page_ptr2page_index(pages_4k.view().spec_index(5)), page_ptr2page_index(pages_4k.view().spec_index(6)),
            page_ptr2page_index(pages_4k.view().spec_index(7)), page_ptr2page_index(pages_4k.view().spec_index(8)),
        ]),
        old(lctx).page_lock_map().dom().difference(page_2m_tail_indices(page_ptr2page_index(container_page)).union(page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page))).union(set![
            page_ptr2page_index(pages_4k.view().spec_index(0)), page_ptr2page_index(pages_4k.view().spec_index(1)),
            page_ptr2page_index(pages_4k.view().spec_index(2)), page_ptr2page_index(pages_4k.view().spec_index(3)),
            page_ptr2page_index(pages_4k.view().spec_index(8)), page_ptr2page_index(pages_4k.view().spec_index(4)),
            page_ptr2page_index(pages_4k.view().spec_index(5)), page_ptr2page_index(pages_4k.view().spec_index(6)),
            page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page),
        ])) =~= set![page_ptr2page_index(pages_4k.view().spec_index(7))],
        owned_2m_tail_lock_perms_wf(container_tail_lock_perms, old(krnl).pg_arr, old(lctx), page_ptr2page_index(container_page)),
        owned_2m_tail_lock_perms_wf(pcid_allocator_tail_lock_perms, old(krnl).pg_arr, old(lctx), page_ptr2page_index(pcid_allocator_page)),
        first == (page_ptr2page_index(pages_4k.view().spec_index(0)), page_ptr2page_index(pages_4k.view().spec_index(1)), page_ptr2page_index(pages_4k.view().spec_index(2)), page_ptr2page_index(pages_4k.view().spec_index(3)), page_ptr2page_index(pages_4k.view().spec_index(8))),
        second == (page_ptr2page_index(pages_4k.view().spec_index(4)), page_ptr2page_index(pages_4k.view().spec_index(5)), page_ptr2page_index(pages_4k.view().spec_index(6)), page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page)),
        !set![first.0, first.1, first.2, first.3, first.4].contains(page_ptr2page_index(pages_4k.view().spec_index(7))),
        !set![second.0, second.1, second.2, second.3, second.4].contains(page_ptr2page_index(pages_4k.view().spec_index(7))),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), first.0, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), first.1, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), first.2, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), first.3, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), first.4, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), second.0, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), second.1, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), second.2, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), second.3, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), second.4, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(7)), TypedLockMode::Write),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, ..*old(krnl) }),
        page_invariant_fields_unchanged(old(krnl).pg_arr, final(krnl).pg_arr),
        final(lctx).page_lock_map().dom().difference(set![first.0, first.1, first.2, first.3, first.4]).difference(set![second.0, second.1, second.2, second.3, second.4]) =~= set![page_ptr2page_index(pages_4k.view().spec_index(7))],
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), first.0, TypedLockMode::Write),
        final(krnl).pg_arr.spec_index(first.0) == old(krnl).pg_arr.spec_index(first.0),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), first.1, TypedLockMode::Write),
        final(krnl).pg_arr.spec_index(first.1) == old(krnl).pg_arr.spec_index(first.1),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), first.2, TypedLockMode::Write),
        final(krnl).pg_arr.spec_index(first.2) == old(krnl).pg_arr.spec_index(first.2),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), first.3, TypedLockMode::Write),
        final(krnl).pg_arr.spec_index(first.3) == old(krnl).pg_arr.spec_index(first.3),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), first.4, TypedLockMode::Write),
        final(krnl).pg_arr.spec_index(first.4) == old(krnl).pg_arr.spec_index(first.4),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), second.0, TypedLockMode::Write),
        final(krnl).pg_arr.spec_index(second.0) == old(krnl).pg_arr.spec_index(second.0),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), second.1, TypedLockMode::Write),
        final(krnl).pg_arr.spec_index(second.1) == old(krnl).pg_arr.spec_index(second.1),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), second.2, TypedLockMode::Write),
        final(krnl).pg_arr.spec_index(second.2) == old(krnl).pg_arr.spec_index(second.2),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), second.3, TypedLockMode::Write),
        final(krnl).pg_arr.spec_index(second.3) == old(krnl).pg_arr.spec_index(second.3),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), second.4, TypedLockMode::Write),
        final(krnl).pg_arr.spec_index(second.4) == old(krnl).pg_arr.spec_index(second.4),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(7)), TypedLockMode::Write),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(7))) == old(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(7))),
{
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
    wunlock_new_container_2m_page_tails(krnl, Tracked(&mut *lctx), container_head, pcid_allocator_head, Tracked(container_tail_lock_perms), Tracked(pcid_allocator_tail_lock_perms));
}

pub(super) fn release_backing_page_lock_group(
    pages: &mut PageLockedArray, Tracked(lctx): Tracked<&mut LocalContext>, indices: (PageIndex, PageIndex, PageIndex, PageIndex, PageIndex),
    Tracked(perm0): Tracked<LockPerm>, Tracked(perm1): Tracked<LockPerm>, Tracked(perm2): Tracked<LockPerm>, Tracked(perm3): Tracked<LockPerm>, Tracked(perm4): Tracked<LockPerm>,
)
    requires
        page_array_wf(*old(pages)),
        old(pages).typed_lock_map_aligned(old(lctx).page_lock_map(), old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Release,
        seq![indices.0, indices.1, indices.2, indices.3, indices.4].no_duplicates(),
        index_valid(NUM_PAGES, indices.0),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), indices.0, TypedLockMode::Write),
        perm0.state() is WriteLock,
        perm0.thread_id() == old(lctx).thread_id(),
        perm0.lock_id() == old(pages).spec_index(indices.0).view().locking_thread()->Write_lock_id,
        index_valid(NUM_PAGES, indices.1),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), indices.1, TypedLockMode::Write),
        perm1.state() is WriteLock,
        perm1.thread_id() == old(lctx).thread_id(),
        perm1.lock_id() == old(pages).spec_index(indices.1).view().locking_thread()->Write_lock_id,
        index_valid(NUM_PAGES, indices.2),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), indices.2, TypedLockMode::Write),
        perm2.state() is WriteLock,
        perm2.thread_id() == old(lctx).thread_id(),
        perm2.lock_id() == old(pages).spec_index(indices.2).view().locking_thread()->Write_lock_id,
        index_valid(NUM_PAGES, indices.3),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), indices.3, TypedLockMode::Write),
        perm3.state() is WriteLock,
        perm3.thread_id() == old(lctx).thread_id(),
        perm3.lock_id() == old(pages).spec_index(indices.3).view().locking_thread()->Write_lock_id,
        index_valid(NUM_PAGES, indices.4),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), indices.4, TypedLockMode::Write),
        perm4.state() is WriteLock,
        perm4.thread_id() == old(lctx).thread_id(),
        perm4.lock_id() == old(pages).spec_index(indices.4).view().locking_thread()->Write_lock_id,
    ensures
        page_array_wf(*final(pages)),
        page_invariant_fields_unchanged(*old(pages), *final(pages)),
        final(pages).typed_lock_map_aligned(final(lctx).page_lock_map(), final(lctx).thread_id()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).page_lock_map() == old(lctx).page_lock_map().remove_keys(set![indices.0, indices.1, indices.2, indices.3, indices.4]),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        forall|index: PageIndex| #![trigger final(pages).spec_index(index)] index_valid(NUM_PAGES, index) && !set![indices.0, indices.1, indices.2, indices.3, indices.4].contains(index)
            ==> final(pages).spec_index(index) == old(pages).spec_index(index),
{
    proof { page_array_wf_map(*pages); }
    assert({
        &&& pages.spec_index(indices.0).view().wlocked_by(&*lctx)
        &&& lctx.lock_entry_contains(pages.lock_id_by_index(indices.0), KernelObjId::Page(indices.0))
        &&& pages.spec_index(indices.1).view().wlocked_by(&*lctx)
        &&& lctx.lock_entry_contains(pages.lock_id_by_index(indices.1), KernelObjId::Page(indices.1))
        &&& pages.spec_index(indices.2).view().wlocked_by(&*lctx)
        &&& lctx.lock_entry_contains(pages.lock_id_by_index(indices.2), KernelObjId::Page(indices.2))
        &&& pages.spec_index(indices.3).view().wlocked_by(&*lctx)
        &&& lctx.lock_entry_contains(pages.lock_id_by_index(indices.3), KernelObjId::Page(indices.3))
        &&& pages.spec_index(indices.4).view().wlocked_by(&*lctx)
        &&& lctx.lock_entry_contains(pages.lock_id_by_index(indices.4), KernelObjId::Page(indices.4))
    }) by { reveal(LockedArray::typed_lock_map_aligned); };
    pages.wunlock(indices.0, Tracked(&mut *lctx), Tracked(perm0), Ghost(KernelObjId::Page(indices.0)));
    pages.wunlock(indices.1, Tracked(&mut *lctx), Tracked(perm1), Ghost(KernelObjId::Page(indices.1)));
    pages.wunlock(indices.2, Tracked(&mut *lctx), Tracked(perm2), Ghost(KernelObjId::Page(indices.2)));
    pages.wunlock(indices.3, Tracked(&mut *lctx), Tracked(perm3), Ghost(KernelObjId::Page(indices.3)));
    pages.wunlock(indices.4, Tracked(&mut *lctx), Tracked(perm4), Ghost(KernelObjId::Page(indices.4)));
    proof {
        assert(release_backing_page_lock_group_eof_transition_framing(*old(pages), *pages, indices)) by { reveal(release_backing_page_lock_group_eof_transition_framing); };
        release_backing_page_lock_group_eof(*old(pages), *pages, indices);
    }
    assert(pages.typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
}
}
