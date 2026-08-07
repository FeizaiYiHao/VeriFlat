use vstd::prelude::*;

use super::{mmap_4k_bundle_locks_match, mmap_4k_lock_domains_framed};

verus! {

use crate::*;
use super::Create4kEntryPages;
use super::create_entry_install::MissingPageTableLevel;

impl KernelK {
    pub open spec fn create_4k_entry_page_lock_held(
        &self,
        page_ptr: PagePtr,
        lctx: &LocalContext,
        page_lock_perms: &Map<PagePtr, LockPerm>,
    ) -> bool {
        let page_index = page_ptr2page_index(page_ptr);
        &&& page_ptr_valid(page_ptr)
        &&& self.page_array.spec_index(page_index).view().wlocked_by(lctx)
        &&& page_lock_perms.dom().contains(page_ptr)
        &&& page_lock_perms.spec_index(page_ptr).state() is WriteLock
        &&& page_lock_perms.spec_index(page_ptr).thread_id() == lctx.thread_id()
        &&& page_lock_perms.spec_index(page_ptr).lock_id()
            == self.page_array.spec_index(page_index).view().locking_thread()->Write_lock_id
    }

    /// One physical page is ready to be consumed by `create_4k_entry`.
    /// The page remains owned by `thread_ptr`, staged in that thread, and its
    /// write-lock permission is available in the caller-owned permission map.
    pub open spec fn create_4k_entry_page_ready(
        &self,
        page_ptr: PagePtr,
        thread_ptr: RwLockThreadPtr,
        lctx: &LocalContext,
        page_lock_perms: &Map<PagePtr, LockPerm>,
    ) -> bool {
        let page_index = page_ptr2page_index(page_ptr);
        &&& self.thread_map.dom().contains(thread_ptr)
        &&& self.create_4k_entry_page_lock_held(
            page_ptr, lctx, page_lock_perms,
        )
        &&& self.page_array.spec_index(page_index).view().view().state
            == (PageState::Owned4k { thread_ptr })
        &&& self.page_array.spec_index(page_index).view().view().owning_container
            == self.thread_map.spec_index(thread_ptr).view().owning_container
        &&& self.thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
            .contains(page_ptr)
    }

    pub open spec fn create_4k_entry_page_locks_held(
        &self,
        pages: Create4kEntryPages,
        lctx: &LocalContext,
        page_lock_perms: &Map<PagePtr, LockPerm>,
    ) -> bool {
        match pages {
            Create4kEntryPages::DataOnly { data_page } =>
                self.create_4k_entry_page_lock_held(
                    data_page, lctx, page_lock_perms,
                ),
            Create4kEntryPages::L1AndData { l1_page, data_page } => {
                &&& self.create_4k_entry_page_lock_held(
                    l1_page, lctx, page_lock_perms,
                )
                &&& self.create_4k_entry_page_lock_held(
                    data_page, lctx, page_lock_perms,
                )
            },
            Create4kEntryPages::L2L1AndData { l2_page, l1_page, data_page } => {
                &&& self.create_4k_entry_page_lock_held(
                    l2_page, lctx, page_lock_perms,
                )
                &&& self.create_4k_entry_page_lock_held(
                    l1_page, lctx, page_lock_perms,
                )
                &&& self.create_4k_entry_page_lock_held(
                    data_page, lctx, page_lock_perms,
                )
            },
            Create4kEntryPages::L3L2L1AndData {
                l3_page,
                l2_page,
                l1_page,
                data_page,
            } => {
                &&& self.create_4k_entry_page_lock_held(
                    l3_page, lctx, page_lock_perms,
                )
                &&& self.create_4k_entry_page_lock_held(
                    l2_page, lctx, page_lock_perms,
                )
                &&& self.create_4k_entry_page_lock_held(
                    l1_page, lctx, page_lock_perms,
                )
                &&& self.create_4k_entry_page_lock_held(
                    data_page, lctx, page_lock_perms,
                )
            },
        }
    }

    pub open spec fn create_4k_entry_pages_ready(
        &self,
        pages: Create4kEntryPages,
        thread_ptr: RwLockThreadPtr,
        lctx: &LocalContext,
        page_lock_perms: &Map<PagePtr, LockPerm>,
    ) -> bool {
        &&& pages.roles_distinct()
        &&& match pages {
            Create4kEntryPages::DataOnly { data_page } =>
                self.create_4k_entry_page_ready(
                    data_page, thread_ptr, lctx, page_lock_perms,
                ),
            Create4kEntryPages::L1AndData { l1_page, data_page } => {
                &&& self.create_4k_entry_page_ready(
                    l1_page, thread_ptr, lctx, page_lock_perms,
                )
                &&& self.create_4k_entry_page_ready(
                    data_page, thread_ptr, lctx, page_lock_perms,
                )
            },
            Create4kEntryPages::L2L1AndData { l2_page, l1_page, data_page } => {
                &&& self.create_4k_entry_page_ready(
                    l2_page, thread_ptr, lctx, page_lock_perms,
                )
                &&& self.create_4k_entry_page_ready(
                    l1_page, thread_ptr, lctx, page_lock_perms,
                )
                &&& self.create_4k_entry_page_ready(
                    data_page, thread_ptr, lctx, page_lock_perms,
                )
            },
            Create4kEntryPages::L3L2L1AndData {
                l3_page,
                l2_page,
                l1_page,
                data_page,
            } => {
                &&& self.create_4k_entry_page_ready(
                    l3_page, thread_ptr, lctx, page_lock_perms,
                )
                &&& self.create_4k_entry_page_ready(
                    l2_page, thread_ptr, lctx, page_lock_perms,
                )
                &&& self.create_4k_entry_page_ready(
                    l1_page, thread_ptr, lctx, page_lock_perms,
                )
                &&& self.create_4k_entry_page_ready(
                    data_page, thread_ptr, lctx, page_lock_perms,
                )
            },
        }
    }

    /// The exact bundle shape mirrors the first absent page-table level.
    pub open spec fn create_4k_entry_path_matches(
        &self,
        pages: Create4kEntryPages,
        pagetable_ptr: RwLockPageTableRoot,
        va: VAddr,
    ) -> bool {
        let pagetable = self.pagetable_map.spec_index(pagetable_ptr).view();
        let indices = spec_va2index(va);
        &&& self.pagetable_map.dom().contains(pagetable_ptr)
        &&& va_4k_valid(va)
        &&& pagetable.kernel_l4_end <= indices.0 < 512
        &&& indices.1 < 512
        &&& indices.2 < 512
        &&& indices.3 < 512
        &&& !pagetable.mapping_4k().dom().contains(va)
        &&& pagetable.spec_resolve_mapping_1g_l3(indices.0, indices.1) is None
        &&& pagetable.spec_resolve_mapping_2m_l2(
            indices.0, indices.1, indices.2,
        ) is None
        &&& pagetable.spec_resolve_mapping_4k_l1(
            indices.0, indices.1, indices.2, indices.3,
        ) is None
        &&& match pages {
            Create4kEntryPages::DataOnly { .. } =>
                pagetable.spec_resolve_mapping_l2(
                    indices.0, indices.1, indices.2,
                ) is Some,
            Create4kEntryPages::L1AndData { .. } => {
                &&& pagetable.spec_resolve_mapping_l3(indices.0, indices.1) is Some
                &&& pagetable.spec_resolve_mapping_l2(
                    indices.0, indices.1, indices.2,
                ) is None
            },
            Create4kEntryPages::L2L1AndData { .. } => {
                &&& pagetable.spec_resolve_mapping_l4(indices.0) is Some
                &&& pagetable.spec_resolve_mapping_l3(indices.0, indices.1) is None
            },
            Create4kEntryPages::L3L2L1AndData { .. } =>
                pagetable.spec_resolve_mapping_l4(indices.0) is None,
        }
    }

    pub open spec fn create_4k_entry_structure_page_installed(
        &self,
        old_page_array: PageLockedArray,
        page_ptr: PagePtr,
        pagetable_ptr: RwLockPageTableRoot,
    ) -> bool {
        let page_index = page_ptr2page_index(page_ptr);
        &&& self.page_array.spec_index(page_index).view().view().state
            == (PageState::Allocated4k {
                state: Allocated4KPageState::PageTable {
                    pagetable_root: pagetable_ptr,
                },
            })
        &&& self.page_array.spec_index(page_index).view().view().perm_4k.view().is_none()
        &&& self.page_array.spec_index(page_index).view().view().ref_count
            == old_page_array.spec_index(page_index).view().view().ref_count
        &&& self.page_array.spec_index(page_index).view().view().mappings()
            == old_page_array.spec_index(page_index).view().view().mappings()
        &&& self.page_array.spec_index(page_index).view().view().owning_container
            == old_page_array.spec_index(page_index).view().view().owning_container
        &&& self.page_array.spec_index(page_index).view().view().is_io_page
            == old_page_array.spec_index(page_index).view().view().is_io_page
        &&& self.page_array.spec_index(page_index).view().view().free_list_node_storage
            == old_page_array.spec_index(page_index).view().view().free_list_node_storage
        &&& self.page_array.spec_index(page_index).view().view().free_list
            == old_page_array.spec_index(page_index).view().view().free_list
    }

    pub open spec fn create_4k_entry_structure_pages_installed(
        &self,
        old_page_array: PageLockedArray,
        pages: Create4kEntryPages,
        pagetable_ptr: RwLockPageTableRoot,
    ) -> bool {
        match pages {
            Create4kEntryPages::DataOnly { .. } => true,
            Create4kEntryPages::L1AndData { l1_page, .. } =>
                self.create_4k_entry_structure_page_installed(
                    old_page_array, l1_page, pagetable_ptr,
                ),
            Create4kEntryPages::L2L1AndData { l2_page, l1_page, .. } => {
                &&& self.create_4k_entry_structure_page_installed(
                    old_page_array, l2_page, pagetable_ptr,
                )
                &&& self.create_4k_entry_structure_page_installed(
                    old_page_array, l1_page, pagetable_ptr,
                )
            },
            Create4kEntryPages::L3L2L1AndData { l3_page, l2_page, l1_page, .. } => {
                &&& self.create_4k_entry_structure_page_installed(
                    old_page_array, l3_page, pagetable_ptr,
                )
                &&& self.create_4k_entry_structure_page_installed(
                    old_page_array, l2_page, pagetable_ptr,
                )
                &&& self.create_4k_entry_structure_page_installed(
                    old_page_array, l1_page, pagetable_ptr,
                )
            },
        }
    }

    pub open spec fn create_4k_entry_page_array_framed(
        &self,
        old_page_array: PageLockedArray,
        pages: Create4kEntryPages,
    ) -> bool {
        match pages {
            Create4kEntryPages::DataOnly { data_page } =>
                self.page_array.unchanged_except(
                    &old_page_array,
                    page_ptr2page_index(data_page),
                ),
            Create4kEntryPages::L1AndData { l1_page, data_page } =>
                forall|page_index: PageIndex|
                    #![trigger self.page_array.spec_index(page_index)]
                    #![trigger old_page_array.spec_index(page_index)]
                    page_index_wf(page_index)
                    && page_index != page_ptr2page_index(l1_page)
                    && page_index != page_ptr2page_index(data_page)
                    ==> self.page_array.spec_index(page_index)
                        == old_page_array.spec_index(page_index),
            Create4kEntryPages::L2L1AndData { l2_page, l1_page, data_page } =>
                forall|page_index: PageIndex|
                    #![trigger self.page_array.spec_index(page_index)]
                    #![trigger old_page_array.spec_index(page_index)]
                    page_index_wf(page_index)
                    && page_index != page_ptr2page_index(l2_page)
                    && page_index != page_ptr2page_index(l1_page)
                    && page_index != page_ptr2page_index(data_page)
                    ==> self.page_array.spec_index(page_index)
                        == old_page_array.spec_index(page_index),
            Create4kEntryPages::L3L2L1AndData { l3_page, l2_page, l1_page, data_page } =>
                forall|page_index: PageIndex|
                    #![trigger self.page_array.spec_index(page_index)]
                    #![trigger old_page_array.spec_index(page_index)]
                    page_index_wf(page_index)
                    && page_index != page_ptr2page_index(l3_page)
                    && page_index != page_ptr2page_index(l2_page)
                    && page_index != page_ptr2page_index(l1_page)
                    && page_index != page_ptr2page_index(data_page)
                    ==> self.page_array.spec_index(page_index)
                        == old_page_array.spec_index(page_index),
        }
    }

    /// Create every missing directory entry on one fresh 4K walk and then map
    /// the final data page. `pages` contains exactly the pages required by the
    /// current path shape, so this operation never leaves an unused staged page
    /// that would need rollback.
    ///
    /// Every parent table is fully initialized before its parent entry is
    /// published. The data-page leaf is the final executable publication. The
    /// caller keeps all object locks and closes the surrounding user-view step
    /// after releasing the user-visible PageTable lock.
    pub fn create_4k_entry(
        &mut self,
        pages: Create4kEntryPages,
        thread_ptr: RwLockThreadPtr,
        pagetable_ptr: RwLockPageTableRoot,
        va: VAddr,
        write: bool,
        execute_disable: bool,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(page_lock_perms): Tracked<&Map<PagePtr, LockPerm>>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
        Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    )
        requires
            old(self).inv(),
            old(lctx).wf(),
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            old(lctx).kernel_view_locking_state() is Release,
            old(lctx).user_view_locking_state() is Release,
            va_4k_valid(va),
            old(self).thread_map.dom().contains(thread_ptr),
            old(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            old(self).pagetable_map.dom().contains(pagetable_ptr),
            old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                <= spec_va2index(va).0,
            spec_va2index(va).0 < 512,
            spec_va2index(va).1 < 512,
            spec_va2index(va).2 < 512,
            old(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                == pagetable_ptr,
            old(self).thread_map.spec_index(thread_ptr).view().quota_4k
                >= pages.count(),
            old(self).create_4k_entry_pages_ready(
                pages,
                thread_ptr,
                old(lctx),
                page_lock_perms,
            ),
            mmap_4k_bundle_locks_match(pages, old(lctx), page_lock_perms),
            old(self).create_4k_entry_path_matches(pages, pagetable_ptr, va),
            old(self).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id()
                == old(self).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(self).pagetable_map.spec_index(pagetable_ptr).wlocked_by(old(lctx)),
            pagetable_lock_perm.state() is WriteLock,
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            pagetable_lock_perm.lock_id()
                == old(self).pagetable_map.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        ensures
            final(self).inv(),
            final(lctx).wf(),
            final(self).locked_objects_match_lctx(final(lctx)),
            lock_id_aligned(final(self), final(lctx)),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).user_view_locking_state() is Release,
            final(lctx).thread_id() == old(lctx).thread_id(),
            mmap_4k_lock_domains_framed(final(lctx), old(lctx)),
            final(lctx).page_lock_map().dom()
                =~= pages.page_index_set(),
            mmap_4k_bundle_locks_match(pages, final(lctx), page_lock_perms),
            final(self).create_4k_entry_page_locks_held(
                pages,
                final(lctx),
                page_lock_perms,
            ),
            final(self).thread_map.spec_index(thread_ptr).wlocked_by(final(lctx)),
            final(self).pagetable_map.spec_index(pagetable_ptr).wlocked_by(final(lctx)),
            thread_lock_perm.lock_id()
                == final(self).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            pagetable_lock_perm.lock_id()
                == final(self).pagetable_map.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            final(self).create_4k_entry_structure_pages_installed(
                old(self).page_array,
                pages,
                pagetable_ptr,
            ),
            match pages {
                Create4kEntryPages::DataOnly { .. } => true,
                Create4kEntryPages::L1AndData { l1_page, .. } => {
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                            spec_va2index(va).2,
                        ) is Some
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                            spec_va2index(va).2,
                        )->0.addr == l1_page
                },
                Create4kEntryPages::L2L1AndData { l2_page, l1_page, .. } => {
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                        ) is Some
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                        )->0.addr == l2_page
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                            spec_va2index(va).2,
                        ) is Some
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                            spec_va2index(va).2,
                        )->0.addr == l1_page
                },
                Create4kEntryPages::L3L2L1AndData {
                    l3_page,
                    l2_page,
                    l1_page,
                    ..
                } => {
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l4(spec_va2index(va).0) is Some
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l4(spec_va2index(va).0)->0.addr == l3_page
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                        ) is Some
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                        )->0.addr == l2_page
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                            spec_va2index(va).2,
                        ) is Some
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                            spec_va2index(va).2,
                        )->0.addr == l1_page
                },
            },
            final(self).create_4k_entry_page_array_framed(old(self).page_array, pages),
            final(self).page_array.spec_index(
                page_ptr2page_index(pages.data_page()),
            ).view().view().state == PageState::Mapped4k,
            final(self).page_array.spec_index(
                page_ptr2page_index(pages.data_page()),
            ).view().view().mappings() == Set::empty().insert((pagetable_ptr, va)),
            final(self).page_array.spec_index(
                page_ptr2page_index(pages.data_page()),
            ).view().view().ref_count == 1,
            final(self).page_array.spec_index(
                page_ptr2page_index(pages.data_page()),
            ).view().view().owning_container
                == old(self).page_array.spec_index(
                    page_ptr2page_index(pages.data_page()),
                ).view().view().owning_container,
            final(self).page_array.spec_index(
                page_ptr2page_index(pages.data_page()),
            ).view().view().is_io_page
                == old(self).page_array.spec_index(
                    page_ptr2page_index(pages.data_page()),
                ).view().view().is_io_page,
            final(self).page_array.spec_index(
                page_ptr2page_index(pages.data_page()),
            ).view().view().free_list_node_storage
                == old(self).page_array.spec_index(
                    page_ptr2page_index(pages.data_page()),
                ).view().view().free_list_node_storage,
            final(self).page_array.spec_index(
                page_ptr2page_index(pages.data_page()),
            ).view().view().free_list
                == old(self).page_array.spec_index(
                    page_ptr2page_index(pages.data_page()),
                ).view().view().free_list,
            final(self).page_array.spec_index(
                page_ptr2page_index(pages.data_page()),
            ).view().view().perm_4k.view()
                is None,
            final(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
                == pages.remove_pages(
                    old(self).thread_map.spec_index(thread_ptr).view()
                        .temp_alloc_cache_4k.view(),
                ),
            ({
                let old_thread = old(self).thread_map.spec_index(thread_ptr).view();
                &&& old_thread.temp_alloc_cache_4k.view() =~= pages.page_set()
                &&& old_thread.temp_alloc_cache_2m.view().len() == 0
                &&& old_thread.temp_alloc_cache_1g.view().len() == 0
            }) ==> final(self).thread_map.spec_index(thread_ptr).view()
                .temp_alloc_clean(),
            final(self).thread_map.spec_index(thread_ptr).view().quota_4k
                == old(self).thread_map.spec_index(thread_ptr).view().quota_4k
                    - pages.count(),
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m,
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            final(self).thread_map.spec_index(thread_ptr).view().quota_2m
                == old(self).thread_map.spec_index(thread_ptr).view().quota_2m,
            final(self).thread_map.spec_index(thread_ptr).view().quota_1g
                == old(self).thread_map.spec_index(thread_ptr).view().quota_1g,
            final(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_4k
                == old(self).thread_map.spec_index(thread_ptr).view()
                    .direct_free_quota_pending_4k,
            final(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_2m
                == old(self).thread_map.spec_index(thread_ptr).view()
                    .direct_free_quota_pending_2m,
            final(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_1g
                == old(self).thread_map.spec_index(thread_ptr).view()
                    .direct_free_quota_pending_1g,
            final(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_4k
                == old(self).thread_map.spec_index(thread_ptr).view()
                    .indirect_free_quota_pending_4k,
            final(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_2m
                == old(self).thread_map.spec_index(thread_ptr).view()
                    .indirect_free_quota_pending_2m,
            final(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_1g
                == old(self).thread_map.spec_index(thread_ptr).view()
                    .indirect_free_quota_pending_1g,
            final(self).thread_map.spec_index(thread_ptr).view().state
                == old(self).thread_map.spec_index(thread_ptr).view().state,
            final(self).thread_map.spec_index(thread_ptr).view().owning_container
                == old(self).thread_map.spec_index(thread_ptr).view().owning_container,
            final(self).thread_map.spec_index(thread_ptr).view().owning_proc
                == old(self).thread_map.spec_index(thread_ptr).view().owning_proc,
            final(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                == old(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr,
            thread_process_management_fields_unchanged(
                old(self).thread_map,
                final(self).thread_map,
            ),
            final(self).thread_map.spec_index(thread_ptr).view().blocking_endpoint_index
                == old(self).thread_map.spec_index(thread_ptr).view().blocking_endpoint_index,
            final(self).thread_map.spec_index(thread_ptr).view().ipc_payload
                == old(self).thread_map.spec_index(thread_ptr).view().ipc_payload,
            final(self).thread_map.spec_index(thread_ptr).view().error_code
                == old(self).thread_map.spec_index(thread_ptr).view().error_code,
            final(self).thread_map.spec_index(thread_ptr).view().trap_frame
                == old(self).thread_map.spec_index(thread_ptr).view().trap_frame,
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
                    .insert(
                        va,
                        MapEntry {
                            addr: pages.data_page(),
                            present: true,
                            write,
                            execute_disable,
                        },
                    ),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().page_closure()
                == pages.add_structure_pages(
                    old(self).pagetable_map.spec_index(pagetable_ptr).view().page_closure(),
                ),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_entries
                =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_entries,
            final(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end,
            final(self).pagetable_map.spec_index(pagetable_ptr).view().pcid
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().pcid,
            final(self).pagetable_map.spec_index(pagetable_ptr).view().cr3
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().cr3,
            final(self).pagetable_map.spec_index(pagetable_ptr).view().proc_ptr
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().proc_ptr,
            final(self).pagetable_map.unchanged_except(
                &old(self).pagetable_map,
                pagetable_ptr,
            ),
            final(self).thread_map.unchanged_except(&old(self).thread_map, thread_ptr),
            final(self).iommu_table_map == old(self).iommu_table_map,
            final(self).iommu_root_table == old(self).iommu_root_table,
            final(self).cpu_array == old(self).cpu_array,
            final(self).container_map == old(self).container_map,
            final(self).scheduler_map == old(self).scheduler_map,
            final(self).pcid_allocator_map == old(self).pcid_allocator_map,
            final(self).process_map == old(self).process_map,
            final(self).endpoint_map == old(self).endpoint_map,
            final(self).allocator_4k_map == old(self).allocator_4k_map,
            final(self).allocator_2m_map == old(self).allocator_2m_map,
            final(self).allocator_1g_map == old(self).allocator_1g_map,
            final(self).cpu_tlb == old(self).cpu_tlb,
            final(self).iommu_tlb == old(self).iommu_tlb,
            final(self).root_container == old(self).root_container,
            final(self).default_pagetable == old(self).default_pagetable,
    {
        match pages {
            Create4kEntryPages::DataOnly { data_page } => {
                let tracked data_page_lock_perm = page_lock_perms.tracked_borrow(data_page);
                self.map_owned_4k_page(
                    data_page,
                    thread_ptr,
                    pagetable_ptr,
                    va,
                    write,
                    execute_disable,
                    Tracked(&mut *lctx),
                    Tracked(data_page_lock_perm),
                    Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm),
                );
            },
            Create4kEntryPages::L1AndData { l1_page, data_page } => {
                let tracked l1_page_lock_perm = page_lock_perms.tracked_borrow(l1_page);
                self.install_staged_4k_page_table_page(
                    MissingPageTableLevel::L2,
                    l1_page,
                    thread_ptr,
                    pagetable_ptr,
                    va,
                    Tracked(&mut *lctx),
                    Tracked(l1_page_lock_perm),
                    Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm),
                );
                let tracked data_page_lock_perm = page_lock_perms.tracked_borrow(data_page);
                self.map_owned_4k_page(
                    data_page,
                    thread_ptr,
                    pagetable_ptr,
                    va,
                    write,
                    execute_disable,
                    Tracked(&mut *lctx),
                    Tracked(data_page_lock_perm),
                    Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm),
                );
            },
            Create4kEntryPages::L2L1AndData { l2_page, l1_page, data_page } => {
                let tracked l2_page_lock_perm = page_lock_perms.tracked_borrow(l2_page);
                self.install_staged_4k_page_table_page(
                    MissingPageTableLevel::L3,
                    l2_page,
                    thread_ptr,
                    pagetable_ptr,
                    va,
                    Tracked(&mut *lctx),
                    Tracked(l2_page_lock_perm),
                    Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm),
                );
                let tracked l1_page_lock_perm = page_lock_perms.tracked_borrow(l1_page);
                self.install_staged_4k_page_table_page(
                    MissingPageTableLevel::L2,
                    l1_page,
                    thread_ptr,
                    pagetable_ptr,
                    va,
                    Tracked(&mut *lctx),
                    Tracked(l1_page_lock_perm),
                    Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm),
                );
                let tracked data_page_lock_perm = page_lock_perms.tracked_borrow(data_page);
                self.map_owned_4k_page(
                    data_page,
                    thread_ptr,
                    pagetable_ptr,
                    va,
                    write,
                    execute_disable,
                    Tracked(&mut *lctx),
                    Tracked(data_page_lock_perm),
                    Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm),
                );
            },
            Create4kEntryPages::L3L2L1AndData {
                l3_page,
                l2_page,
                l1_page,
                data_page,
            } => {
                let tracked l3_page_lock_perm = page_lock_perms.tracked_borrow(l3_page);
                self.install_staged_4k_page_table_page(
                    MissingPageTableLevel::L4,
                    l3_page,
                    thread_ptr,
                    pagetable_ptr,
                    va,
                    Tracked(&mut *lctx),
                    Tracked(l3_page_lock_perm),
                    Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm),
                );
                let tracked l2_page_lock_perm = page_lock_perms.tracked_borrow(l2_page);
                self.install_staged_4k_page_table_page(
                    MissingPageTableLevel::L3,
                    l2_page,
                    thread_ptr,
                    pagetable_ptr,
                    va,
                    Tracked(&mut *lctx),
                    Tracked(l2_page_lock_perm),
                    Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm),
                );
                let tracked l1_page_lock_perm = page_lock_perms.tracked_borrow(l1_page);
                self.install_staged_4k_page_table_page(
                    MissingPageTableLevel::L2,
                    l1_page,
                    thread_ptr,
                    pagetable_ptr,
                    va,
                    Tracked(&mut *lctx),
                    Tracked(l1_page_lock_perm),
                    Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm),
                );
                let tracked data_page_lock_perm = page_lock_perms.tracked_borrow(data_page);
                self.map_owned_4k_page(
                    data_page,
                    thread_ptr,
                    pagetable_ptr,
                    va,
                    write,
                    execute_disable,
                    Tracked(&mut *lctx),
                    Tracked(data_page_lock_perm),
                    Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm),
                );
            },
        }
    }
}

}
