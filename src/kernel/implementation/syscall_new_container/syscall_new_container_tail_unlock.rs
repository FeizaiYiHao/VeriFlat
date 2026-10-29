use vstd::prelude::*;
use crate::*;

verus! {
/// Releases the tail locks of the two staged 2M pages and reports one combined page-array frame.
pub(super) fn wunlock_new_container_2m_page_tails(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, left: PageIndex, right: PageIndex,
    Tracked(left_perms): Tracked<Map<PageIndex, LockPerm>>, Tracked(right_perms): Tracked<Map<PageIndex, LockPerm>>,
)
    requires
        old(krnl).inv(),
        page_index_2m_valid(left),
        page_index_2m_valid(right),
        left != right,
        owned_2m_tail_lock_perms_wf(left_perms, old(krnl).pg_arr, old(lctx), left),
        owned_2m_tail_lock_perms_wf(right_perms, old(krnl).pg_arr, old(lctx), right),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).page_lock_map() == old(lctx).page_lock_map().remove_keys(page_2m_tail_indices(left)).remove_keys(page_2m_tail_indices(right)),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom().difference(page_2m_tail_indices(left)).difference(page_2m_tail_indices(right)),
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
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, ..*old(krnl) }),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index)]
            #![trigger old(krnl).pg_arr.spec_index(index)]
            index_valid(NUM_PAGES, index) && !page_2m_tail_indices(left).contains(index) && !page_2m_tail_indices(right).contains(index) ==> final(krnl).pg_arr.spec_index(index) == old(krnl).pg_arr.spec_index(index),
        forall|index: PageIndex| #![trigger final(krnl).pg_arr.spec_index(index).view().view()] index_valid(NUM_PAGES, index) ==> final(krnl).pg_arr.spec_index(index).view().view() == old(krnl).pg_arr.spec_index(index).view().view(),
{
    wunlock_owned_2m_page_tails(krnl, left, Tracked(&mut *lctx), Tracked(left_perms));
    wunlock_owned_2m_page_tails(krnl, right, Tracked(&mut *lctx), Tracked(right_perms));
}
} // verus!
