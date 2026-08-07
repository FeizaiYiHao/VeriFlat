use vstd::prelude::*;
use vstd::set::lemma_set_remove_len;

use super::mmap_4k_lock_domains_framed;

verus! {

use crate::*;

/// The first absent directory entry on a 4K walk.  Each variant installs
/// exactly one already-initialized child table: L4 installs an L3 table, L3
/// installs an L2 table, and L2 installs the L1 table that will hold the leaf.
#[derive(Clone, Copy)]
pub(super) enum MissingPageTableLevel {
    L4,
    L3,
    L2,
}

impl KernelK {
    /// Consume one staged 4K page and publish it as exactly one page-table
    /// structure page.  The parent pointer is intentionally recovered from the
    /// locked PageTable here rather than accepted from the caller: the semantic
    /// missing level determines both the parent and the PageTable operation.
    ///
    /// Hidden Page/Thread state is made consistent before the single published
    /// parent-entry store.  The caller has already opened a user-view step and
    /// therefore supplies both LocalContext phases in Release.
    pub(super) fn install_staged_4k_page_table_page(
        &mut self,
        level: MissingPageTableLevel,
        page_ptr: PagePtr,
        thread_ptr: RwLockThreadPtr,
        pagetable_ptr: RwLockPageTableRoot,
        va: VAddr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        page_lock_perm: Tracked<&LockPerm>,
        thread_lock_perm: Tracked<&LockPerm>,
        pagetable_lock_perm: Tracked<&LockPerm>,
    )
        requires
            old(self).inv(),
            old(lctx).wf(),
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            old(lctx).kernel_view_locking_state() is Release,
            old(lctx).user_view_locking_state() is Release,
            page_ptr_valid(page_ptr),
            va_4k_valid(va),
            old(self).thread_map.dom().contains(thread_ptr),
            old(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            old(self).pagetable_map.dom().contains(pagetable_ptr),
            old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                <= spec_va2index(va).0,
            spec_va2index(va).0 < 512,
            spec_va2index(va).1 < 512,
            spec_va2index(va).2 < 512,
            old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                == (PageState::Owned4k { thread_ptr }),
            old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container
                == old(self).thread_map.spec_index(thread_ptr).view().owning_container,
            old(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                == pagetable_ptr,
            old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
                .contains(page_ptr),
            old(self).thread_map.spec_index(thread_ptr).view().quota_4k >= 1,
            match level {
                MissingPageTableLevel::L4 =>
                    old(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l4(spec_va2index(va).0) is None,
                MissingPageTableLevel::L3 => {
                    &&& old(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l4(spec_va2index(va).0) is Some
                    &&& old(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                        ) is None
                    &&& old(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_1g_l3(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                        ) is None
                },
                MissingPageTableLevel::L2 => {
                    &&& old(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                        ) is Some
                    &&& old(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                            spec_va2index(va).2,
                        ) is None
                    &&& old(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_2m_l2(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                            spec_va2index(va).2,
                        ) is None
                },
            },
            old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view()
                .wlocked_by(old(lctx)),
            page_lock_perm.view().state() is WriteLock,
            page_lock_perm.view().thread_id() == old(lctx).thread_id(),
            page_lock_perm.view().lock_id()
                == old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view()
                    .locking_thread()->Write_lock_id,
            old(self).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
            thread_lock_perm.view().state() is WriteLock,
            thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            thread_lock_perm.view().lock_id()
                == old(self).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(self).pagetable_map.spec_index(pagetable_ptr).wlocked_by(old(lctx)),
            pagetable_lock_perm.view().state() is WriteLock,
            pagetable_lock_perm.view().thread_id() == old(lctx).thread_id(),
            pagetable_lock_perm.view().lock_id()
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
            final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view()
                .wlocked_by(final(lctx)),
            final(self).thread_map.spec_index(thread_ptr).wlocked_by(final(lctx)),
            final(self).pagetable_map.spec_index(pagetable_ptr).wlocked_by(final(lctx)),
            page_lock_perm.view().lock_id()
                == final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view()
                    .locking_thread()->Write_lock_id,
            thread_lock_perm.view().lock_id()
                == final(self).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            pagetable_lock_perm.view().lock_id()
                == final(self).pagetable_map.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                == (PageState::Allocated4k {
                    state: Allocated4KPageState::PageTable {
                        pagetable_root: pagetable_ptr,
                    },
                }),
            final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
                .perm_4k.view().is_none(),
            final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count
                == old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
                    .ref_count,
            final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().mappings()
                == old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
                    .mappings(),
            final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
                .owning_container
                == old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
                    .owning_container,
            final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().is_io_page
                == old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
                    .is_io_page,
            final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
                .free_list_node_storage
                == old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
                    .free_list_node_storage,
            final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().free_list
                == old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
                    .free_list,
            final(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
                    .remove(page_ptr),
            final(self).thread_map.spec_index(thread_ptr).view().quota_4k
                == old(self).thread_map.spec_index(thread_ptr).view().quota_4k - 1,
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m.view()
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m.view(),
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g.view()
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g.view(),
            final(self).thread_map.spec_index(thread_ptr).view().quota_2m
                == old(self).thread_map.spec_index(thread_ptr).view().quota_2m,
            final(self).thread_map.spec_index(thread_ptr).view().quota_1g
                == old(self).thread_map.spec_index(thread_ptr).view().quota_1g,
            final(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view()
                == old(self).thread_map.spec_index(thread_ptr).view()
                    .direct_free_quota_pending_4k.view(),
            final(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_2m.view()
                == old(self).thread_map.spec_index(thread_ptr).view()
                    .direct_free_quota_pending_2m.view(),
            final(self).thread_map.spec_index(thread_ptr).view().direct_free_quota_pending_1g.view()
                == old(self).thread_map.spec_index(thread_ptr).view()
                    .direct_free_quota_pending_1g.view(),
            final(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view()
                == old(self).thread_map.spec_index(thread_ptr).view()
                    .indirect_free_quota_pending_4k.view(),
            final(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_2m.view()
                == old(self).thread_map.spec_index(thread_ptr).view()
                    .indirect_free_quota_pending_2m.view(),
            final(self).thread_map.spec_index(thread_ptr).view().indirect_free_quota_pending_1g.view()
                == old(self).thread_map.spec_index(thread_ptr).view()
                    .indirect_free_quota_pending_1g.view(),
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
            final(self).pagetable_map.spec_index(pagetable_ptr).view().page_closure()
                =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().page_closure()
                    .insert(page_ptr),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
                =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
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
            match level {
                MissingPageTableLevel::L4 => {
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l4(spec_va2index(va).0) is Some
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l4(spec_va2index(va).0)->0.addr == page_ptr
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                        ) is None
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_1g_l3(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                        ) is None
                },
                MissingPageTableLevel::L3 => {
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l4(spec_va2index(va).0)
                        == old(self).pagetable_map.spec_index(pagetable_ptr).view()
                            .spec_resolve_mapping_l4(spec_va2index(va).0)
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                        ) is Some
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                        )->0.addr == page_ptr
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_1g_l3(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                        ) is None
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                            spec_va2index(va).2,
                        ) is None
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_2m_l2(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                            spec_va2index(va).2,
                        ) is None
                },
                MissingPageTableLevel::L2 => {
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l4(spec_va2index(va).0)
                        == old(self).pagetable_map.spec_index(pagetable_ptr).view()
                            .spec_resolve_mapping_l4(spec_va2index(va).0)
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                        )
                        == old(self).pagetable_map.spec_index(pagetable_ptr).view()
                            .spec_resolve_mapping_l3(
                                spec_va2index(va).0,
                                spec_va2index(va).1,
                            )
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
                        )->0.addr == page_ptr
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_2m_l2(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                            spec_va2index(va).2,
                        ) is None
                },
            },
            final(self).pagetable_map.unchanged_except(&old(self).pagetable_map, pagetable_ptr),
            final(self).page_array.unchanged_except(
                &old(self).page_array,
                page_ptr2page_index(page_ptr),
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
        let page_index = page_ptr2page_index(page_ptr);
        let indices = va2index(va);
        assert(
            self.pagetable_map.perms_wf()
            && self.pagetable_map.spec_index(pagetable_ptr).inv()
            && page_index_wf(page_index)
            && self.page_array.inv()
            && self.page_array.spec_index(page_index).view().is_init()
            && self.page_array.spec_index(page_index).view().inv()
            && self.page_array.spec_index(page_index).view().view().inv()
            && self.page_array.spec_index(page_index).view().view().addr == page_ptr
            && self.thread_map.perms_wf()
            && self.thread_map.spec_index(thread_ptr).inv()
        ) by {
            reveal(pagetable_perms_wf);
            reveal(page_array_wf);
            reveal(thread_perms_wf);
            page_ptr_lemma1();
        };
        assert(!self.pagetable_map.spec_index(pagetable_ptr).view().page_closure().contains(page_ptr)) by { reveal(pagetable_pages_wf); };

        let parent_page_map_ptr;
        {
            let pagetable = self.pagetable_map.borrow(
                pagetable_ptr,
                pagetable_lock_perm,
            );
            parent_page_map_ptr = match level {
                MissingPageTableLevel::L4 => pagetable.cr3,
                MissingPageTableLevel::L3 =>
                    pagetable.get_entry_l4(indices.0).unwrap().addr,
                MissingPageTableLevel::L2 => {
                    let l4_entry = pagetable.get_entry_l4(indices.0).unwrap();
                    pagetable.get_entry_l3(indices.0, indices.1, &l4_entry).unwrap().addr
                },
            };
        }

        proof {
            assert(lctx.lock_map_contains(KernelObjId::Page(page_index))) by { reveal(page_locked_match_lctx); };
        }
        let page = self.page_array.borrow_mut(
            page_index,
            Tracked(&*lctx),
            page_lock_perm,
        );
        let Tracked(page_perm) = take_perm_4k(page);
        page.state = PageState::Allocated4k {
            state: Allocated4KPageState::PageTable {
                pagetable_root: pagetable_ptr,
            },
        };
        let (page_map_ptr, Tracked(page_map_perm)) = page_perm_to_page_map(
            page_ptr,
            Tracked(page_perm),
        );

        {
            let thread = self.thread_map.borrow_mut(
                thread_ptr,
                Tracked(&*lctx),
                thread_lock_perm,
            );
            thread.temp_alloc_cache_4k = Ghost(
                thread.temp_alloc_cache_4k.view().remove(page_ptr),
            );
            thread.quota_4k = thread.quota_4k - 1;
        }
        proof {
            lctx.update_lock_id(
                KernelObjId::Page(page_index),
                self.page_array.lock_id_by_index(page_index),
            );
        }

        let pagetable = self.pagetable_map.borrow_mut(
            pagetable_ptr,
            Tracked(&*lctx),
            pagetable_lock_perm,
        );
        match level {
            MissingPageTableLevel::L4 => {
                pagetable.create_entry_l4(
                    indices.0,
                    indices.1,
                    page_map_ptr,
                    Tracked(page_map_perm),
                    Tracked(&*lctx),
                );
            },
            MissingPageTableLevel::L3 => {
                pagetable.create_entry_l3(
                    indices.0,
                    indices.1,
                    indices.2,
                    parent_page_map_ptr,
                    page_map_ptr,
                    Tracked(page_map_perm),
                    Tracked(&*lctx),
                );
            },
            MissingPageTableLevel::L2 => {
                pagetable.create_entry_l2(
                    indices.0,
                    indices.1,
                    indices.2,
                    parent_page_map_ptr,
                    page_map_ptr,
                    Tracked(page_map_perm),
                    Tracked(&*lctx),
                );
            },
        }

        proof {
            assert(self.subsystems_inv()) by {
                assert(self.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
                assert(pagetable_perms_wf(self.pagetable_map)) by { reveal(pagetable_perms_wf); };
                assert(page_array_wf(self.page_array)) by { reveal(page_array_wf); };
                assert(thread_perms_wf(self.thread_map)) by {
                    reveal(thread_perms_wf);
                    reveal(thread_temp_alloc_empty_unless_wlocked);
                    reveal(thread_free_quota_pending_empty_unless_wlocked);
                    lemma_set_remove_len(old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view(), page_ptr);
                };
            };
            assert(self.memory_management_inv()) by {
                assert(allocator_pages_wf(
                    self.page_array,
                    self.allocator_4k_map,
                    self.allocator_2m_map,
                    self.allocator_1g_map,
                )) by {
                    allocator_4k_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_4k_map, self.allocator_4k_map);
                    allocator_2m_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_2m_map, self.allocator_2m_map);
                    allocator_1g_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_1g_map, self.allocator_1g_map);
                };
                assert(container_page_owner_wf(self.container_map, self.page_array)) by { container_page_owner_wf_preserved_for_owning_container_eq(old(self).container_map, self.container_map, old(self).page_array, self.page_array); };
                assert(hugepage_2m_wf(self.page_array)) by { hugepage_2m_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array); };
                assert(hugepage_1g_wf(self.page_array)) by { hugepage_1g_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array); };
                assert(page_pagetable_wf(self.pagetable_map, self.page_array)) by { page_pagetable_wf_preserved_for_page_table_page_insert(old(self).pagetable_map, self.pagetable_map, old(self).page_array, self.page_array, pagetable_ptr, page_ptr); };
                assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { process_pagetable_match_preserved_for_pagetable_payload_change(self.process_map, old(self).pagetable_map, self.pagetable_map, pagetable_ptr); };
                assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by { container_process_page_pagetable_wf_preserved_for_page_table_page_insert(self.container_map, self.process_map, old(self).pagetable_map, self.pagetable_map, old(self).page_array, self.page_array, pagetable_ptr, page_ptr); };
                assert(container_pages_wf(self.page_array, self.container_map)) by { container_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).container_map, self.container_map); };
                assert(process_pages_wf(self.page_array, self.process_map)) by { process_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).process_map, self.process_map); };
                assert(pagetable_pages_wf(self.pagetable_map, self.page_array)) by { pagetable_pages_wf_preserved_for_page_table_page_insert(old(self).pagetable_map, self.pagetable_map, old(self).page_array, self.page_array, pagetable_ptr, page_ptr); };
                assert(iommu_table_pages_wf(self.iommu_table_map, self.page_array)) by { iommu_table_pages_wf_preserved_for_non_iommu_page_change(self.iommu_table_map, old(self).page_array, self.page_array, page_ptr); };
                assert(thread_pages_wf(self.thread_map, self.page_array)) by { thread_pages_wf_preserved_for_page_state_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array); };
                assert(pcid_allocator_pages_wf(self.page_array, self.pcid_allocator_map)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).pcid_allocator_map, self.pcid_allocator_map); };
                assert(thread_staged_pages_wf(self.thread_map, self.page_array)) by {
                    assert(thread_staged_pages_4k_wf(self.thread_map, self.page_array)) by { thread_staged_pages_4k_wf_preserved_for_single_consume(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array, thread_ptr, page_ptr); };
                    assert(thread_staged_pages_2m_wf(self.thread_map, self.page_array)) by { thread_staged_pages_2m_wf_preserved_for_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array); };
                    assert(thread_staged_pages_1g_wf(self.thread_map, self.page_array)) by { thread_staged_pages_1g_wf_preserved_for_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array); };
                };
                assert(endpoint_pages_wf(self.endpoint_map, self.page_array)) by { endpoint_pages_wf_preserved_for_page_state_eq(old(self).endpoint_map, self.endpoint_map, old(self).page_array, self.page_array); };
                assert(container_process_allocator_quota_wf(
                    self.container_map,
                    self.process_map,
                    self.thread_map,
                    self.allocator_4k_map,
                    self.allocator_2m_map,
                    self.allocator_1g_map,
                )) by {
                    reveal(thread_quota_4k_fields_unchanged);
                    reveal(thread_quota_2m_fields_unchanged);
                    reveal(thread_quota_1g_fields_unchanged);
                    container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields_forall();
                    container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields_forall();
                    container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields_forall();
                };
                assert(container_allocator_free_4k_page_wf(self.container_map, self.allocator_4k_map, self.page_array)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(self.container_map, self.allocator_4k_map, old(self).page_array, self.page_array, page_index); };
                assert(container_allocator_free_2m_page_wf(self.container_map, self.allocator_2m_map, self.page_array)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(self.container_map, self.allocator_2m_map, old(self).page_array, self.page_array, page_index); };
                assert(container_allocator_free_1g_page_wf(self.container_map, self.allocator_1g_map, self.page_array)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(self.container_map, self.allocator_1g_map, old(self).page_array, self.page_array, page_index); };
            };
            assert(self.process_management_inv()) by {
                assert(thread_endpoint_ref_counter_wf(self.thread_map, self.endpoint_map)) by { thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(old(self).thread_map, self.thread_map, self.endpoint_map); };
                assert(thread_endpoint_queue_wf(self.thread_map, self.endpoint_map)) by { thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(old(self).thread_map, self.thread_map, self.endpoint_map); };
                assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by { container_thread_endpoint_wf_preserved_for_thread_process_management_fields(self.container_map, old(self).thread_map, self.thread_map, self.endpoint_map); };
                assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by { container_thread_scheduler_wf_preserved_for_thread_process_management_fields(self.container_map, old(self).thread_map, self.thread_map, self.scheduler_map); };
                assert(container_thread_wf(self.container_map, self.thread_map)) by { container_thread_wf_preserved_for_thread_process_management_fields(self.container_map, old(self).thread_map, self.thread_map); };
                assert(process_thread_wf(self.process_map, self.thread_map)) by { process_thread_wf_preserved_for_thread_process_management_fields(self.process_map, old(self).thread_map, self.thread_map); };
                assert(thread_cpu_wf(self.thread_map, self.cpu_array)) by { thread_cpu_wf_preserved_for_thread_process_management_fields(old(self).thread_map, self.thread_map, self.cpu_array); };
            };
            assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by { cpu_dirty_map_contains_pagetable_pcid_match_preserved_for_pagetable_payload_change(self.cpu_array, old(self).pagetable_map, self.pagetable_map, pagetable_ptr); };
            assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { tlb_wf_spec_preserved_for_pagetable_mappings_unchanged(self.cpu_tlb, self.cpu_array, old(self).pagetable_map, self.pagetable_map, pagetable_ptr); };
            assert(self.locked_objects_match_lctx(&*lctx)) by {
                reveal(thread_locked_match_lctx);
                reveal(pagetable_locked_match_lctx);
                reveal(page_locked_match_lctx);
            };
            assert(lock_id_aligned(self, &*lctx)) by { reveal(page_lock_id_aligned); };
        }
    }
}

}
