use vstd::prelude::*;

use crate::*;

use super::{Create4kEntryPages, mmap_4k_bundle_locks_match};

verus! {

impl KernelK {
    /// Release every page-slot lock carried by one completed 4K-entry bundle.
    /// All non-page objects and all non-page LocalContext lock maps are framed;
    /// the page lock map loses exactly the bundle roles.
    pub(crate) fn wunlock_mmap_4k_bundle_pages(
        &mut self,
        pages: Create4kEntryPages,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(page_lock_perms): Tracked<Map<PagePtr, LockPerm>>,
    )
        requires
            old(self).inv(),
            old(lctx).wf(),
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            old(lctx).kernel_view_locking_state() is Release,
            old(lctx).user_view_locking_state() is Release,
            pages.roles_distinct(),
            old(self).create_4k_entry_page_locks_held(
                pages,
                old(lctx),
                &page_lock_perms,
            ),
            mmap_4k_bundle_locks_match(
                pages,
                old(lctx),
                &page_lock_perms,
            ),
            match pages {
                Create4kEntryPages::DataOnly { data_page } =>
                    page_lock_perms.dom()
                        =~= Set::empty().insert(data_page),
                Create4kEntryPages::L1AndData { l1_page, data_page } =>
                    page_lock_perms.dom()
                        =~= Set::empty().insert(l1_page).insert(data_page),
                Create4kEntryPages::L2L1AndData {
                    l2_page,
                    l1_page,
                    data_page,
                } => page_lock_perms.dom()
                    =~= Set::empty().insert(l2_page).insert(l1_page)
                        .insert(data_page),
                Create4kEntryPages::L3L2L1AndData {
                    l3_page,
                    l2_page,
                    l1_page,
                    data_page,
                } => page_lock_perms.dom()
                    =~= Set::empty().insert(l3_page).insert(l2_page)
                        .insert(l1_page).insert(data_page),
            },
        ensures
            final(self).inv(),
            final(lctx).wf(),
            final(self).locked_objects_match_lctx(final(lctx)),
            lock_id_aligned(final(self), final(lctx)),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).user_view_locking_state() is Release,
            final(self).pagetable_map == old(self).pagetable_map,
            final(self).iommu_table_map == old(self).iommu_table_map,
            final(self).iommu_root_table == old(self).iommu_root_table,
            final(self).cpu_array == old(self).cpu_array,
            final(self).cpu_tlb == old(self).cpu_tlb,
            final(self).iommu_tlb == old(self).iommu_tlb,
            final(self).root_container == old(self).root_container,
            final(self).container_map == old(self).container_map,
            final(self).scheduler_map == old(self).scheduler_map,
            final(self).pcid_allocator_map == old(self).pcid_allocator_map,
            final(self).process_map == old(self).process_map,
            final(self).thread_map == old(self).thread_map,
            final(self).endpoint_map == old(self).endpoint_map,
            final(self).allocator_4k_map == old(self).allocator_4k_map,
            final(self).allocator_2m_map == old(self).allocator_2m_map,
            final(self).allocator_1g_map == old(self).allocator_1g_map,
            final(self).default_pagetable == old(self).default_pagetable,
            final(lctx).container_lock_map() =~= old(lctx).container_lock_map(),
            final(lctx).process_lock_map() =~= old(lctx).process_lock_map(),
            final(lctx).thread_lock_map() =~= old(lctx).thread_lock_map(),
            final(lctx).endpoint_lock_map() =~= old(lctx).endpoint_lock_map(),
            final(lctx).scheduler_lock_map() =~= old(lctx).scheduler_lock_map(),
            final(lctx).pcid_allocator_lock_map()
                =~= old(lctx).pcid_allocator_lock_map(),
            final(lctx).pagetable_lock_map() =~= old(lctx).pagetable_lock_map(),
            final(lctx).iommu_table_lock_map()
                =~= old(lctx).iommu_table_lock_map(),
            final(lctx).cpu_lock_map() =~= old(lctx).cpu_lock_map(),
            final(lctx).allocator_4k_lock_map()
                =~= old(lctx).allocator_4k_lock_map(),
            final(lctx).allocator_2m_lock_map()
                =~= old(lctx).allocator_2m_lock_map(),
            final(lctx).allocator_1g_lock_map()
                =~= old(lctx).allocator_1g_lock_map(),
            match pages {
                Create4kEntryPages::DataOnly { data_page } =>
                    final(lctx).page_lock_map()
                        =~= old(lctx).page_lock_map().remove(
                            page_ptr2page_index(data_page),
                        ),
                Create4kEntryPages::L1AndData { l1_page, data_page } =>
                    final(lctx).page_lock_map()
                        =~= old(lctx).page_lock_map()
                            .remove(page_ptr2page_index(l1_page))
                            .remove(page_ptr2page_index(data_page)),
                Create4kEntryPages::L2L1AndData {
                    l2_page,
                    l1_page,
                    data_page,
                } => final(lctx).page_lock_map()
                    =~= old(lctx).page_lock_map()
                        .remove(page_ptr2page_index(l2_page))
                        .remove(page_ptr2page_index(l1_page))
                        .remove(page_ptr2page_index(data_page)),
                Create4kEntryPages::L3L2L1AndData {
                    l3_page,
                    l2_page,
                    l1_page,
                    data_page,
                } => final(lctx).page_lock_map()
                    =~= old(lctx).page_lock_map()
                        .remove(page_ptr2page_index(l3_page))
                        .remove(page_ptr2page_index(l2_page))
                        .remove(page_ptr2page_index(l1_page))
                        .remove(page_ptr2page_index(data_page)),
            },
            final(lctx).page_lock_map().dom() =~= match pages {
                Create4kEntryPages::DataOnly { data_page } =>
                    old(lctx).page_lock_map().dom().remove(
                        page_ptr2page_index(data_page),
                    ),
                Create4kEntryPages::L1AndData { l1_page, data_page } =>
                    old(lctx).page_lock_map().dom()
                        .remove(page_ptr2page_index(l1_page))
                        .remove(page_ptr2page_index(data_page)),
                Create4kEntryPages::L2L1AndData {
                    l2_page, l1_page, data_page,
                } => old(lctx).page_lock_map().dom()
                    .remove(page_ptr2page_index(l2_page))
                    .remove(page_ptr2page_index(l1_page))
                    .remove(page_ptr2page_index(data_page)),
                Create4kEntryPages::L3L2L1AndData {
                    l3_page, l2_page, l1_page, data_page,
                } => old(lctx).page_lock_map().dom()
                    .remove(page_ptr2page_index(l3_page))
                    .remove(page_ptr2page_index(l2_page))
                    .remove(page_ptr2page_index(l1_page))
                    .remove(page_ptr2page_index(data_page)),
            },
            final(lctx).page_lock_map().dom()
                =~= Set::<PageIndex>::empty(),
    {
        let tracked mut perms = page_lock_perms;
        match pages {
            Create4kEntryPages::DataOnly { data_page } => {
                assert(page_index_wf(page_ptr2page_index(data_page))) by { page_ptr_lemma1(); };
                let tracked data_page_perm = perms.tracked_remove(data_page);
                self.wunlock_page(
                    page_ptr2page_index(data_page),
                    Tracked(&mut *lctx),
                    Tracked(data_page_perm),
                );
            },
            Create4kEntryPages::L1AndData { l1_page, data_page } => {
                assert(
                    page_index_wf(page_ptr2page_index(l1_page))
                    && page_index_wf(page_ptr2page_index(data_page))
                    && page_ptr2page_index(l1_page)
                        != page_ptr2page_index(data_page)
                ) by { page_ptr_lemma1(); };
                let tracked l1_page_perm = perms.tracked_remove(l1_page);
                self.wunlock_page(
                    page_ptr2page_index(l1_page),
                    Tracked(&mut *lctx),
                    Tracked(l1_page_perm),
                );
                let tracked data_page_perm = perms.tracked_remove(data_page);
                self.wunlock_page(
                    page_ptr2page_index(data_page),
                    Tracked(&mut *lctx),
                    Tracked(data_page_perm),
                );
            },
            Create4kEntryPages::L2L1AndData {
                l2_page,
                l1_page,
                data_page,
            } => {
                assert(
                    page_index_wf(page_ptr2page_index(l2_page))
                    && page_index_wf(page_ptr2page_index(l1_page))
                    && page_index_wf(page_ptr2page_index(data_page))
                    && page_ptr2page_index(l2_page)
                        != page_ptr2page_index(l1_page)
                    && page_ptr2page_index(l2_page)
                        != page_ptr2page_index(data_page)
                    && page_ptr2page_index(l1_page)
                        != page_ptr2page_index(data_page)
                ) by { page_ptr_lemma1(); };
                let tracked l2_page_perm = perms.tracked_remove(l2_page);
                self.wunlock_page(
                    page_ptr2page_index(l2_page),
                    Tracked(&mut *lctx),
                    Tracked(l2_page_perm),
                );
                let tracked l1_page_perm = perms.tracked_remove(l1_page);
                self.wunlock_page(
                    page_ptr2page_index(l1_page),
                    Tracked(&mut *lctx),
                    Tracked(l1_page_perm),
                );
                let tracked data_page_perm = perms.tracked_remove(data_page);
                self.wunlock_page(
                    page_ptr2page_index(data_page),
                    Tracked(&mut *lctx),
                    Tracked(data_page_perm),
                );
            },
            Create4kEntryPages::L3L2L1AndData {
                l3_page,
                l2_page,
                l1_page,
                data_page,
            } => {
                assert(
                    page_index_wf(page_ptr2page_index(l3_page))
                    && page_index_wf(page_ptr2page_index(l2_page))
                    && page_index_wf(page_ptr2page_index(l1_page))
                    && page_index_wf(page_ptr2page_index(data_page))
                    && page_ptr2page_index(l3_page)
                        != page_ptr2page_index(l2_page)
                    && page_ptr2page_index(l3_page)
                        != page_ptr2page_index(l1_page)
                    && page_ptr2page_index(l3_page)
                        != page_ptr2page_index(data_page)
                    && page_ptr2page_index(l2_page)
                        != page_ptr2page_index(l1_page)
                    && page_ptr2page_index(l2_page)
                        != page_ptr2page_index(data_page)
                    && page_ptr2page_index(l1_page)
                        != page_ptr2page_index(data_page)
                ) by { page_ptr_lemma1(); };
                let tracked l3_page_perm = perms.tracked_remove(l3_page);
                self.wunlock_page(
                    page_ptr2page_index(l3_page),
                    Tracked(&mut *lctx),
                    Tracked(l3_page_perm),
                );
                let tracked l2_page_perm = perms.tracked_remove(l2_page);
                self.wunlock_page(
                    page_ptr2page_index(l2_page),
                    Tracked(&mut *lctx),
                    Tracked(l2_page_perm),
                );
                let tracked l1_page_perm = perms.tracked_remove(l1_page);
                self.wunlock_page(
                    page_ptr2page_index(l1_page),
                    Tracked(&mut *lctx),
                    Tracked(l1_page_perm),
                );
                let tracked data_page_perm = perms.tracked_remove(data_page);
                self.wunlock_page(
                    page_ptr2page_index(data_page),
                    Tracked(&mut *lctx),
                    Tracked(data_page_perm),
                );
            },
        }
    }
}

} // verus!
