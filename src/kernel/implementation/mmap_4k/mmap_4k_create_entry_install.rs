use vstd::prelude::*;
use vstd::set::lemma_set_remove_len;

use super::mmap_4k_context::{staged_4k_page_op_ensures, staged_4k_page_op_requires};

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
    /// Hidden Page/Thread state is made consistent while the kernel phase is
    /// Acquire. The single parent-entry store closes it into Release. Directory
    /// topology is absent from `PageTableU`, so the following boundary stutters.
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
            staged_4k_page_op_requires(
                old(self), old(lctx), page_ptr, thread_ptr, pagetable_ptr, va,
                page_lock_perm.view(), thread_lock_perm.view(),
                pagetable_lock_perm.view(),
            ),
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
        ensures
            staged_4k_page_op_ensures(
                final(self), final(lctx), old(self), old(lctx), page_ptr,
                thread_ptr, pagetable_ptr, page_lock_perm.view(),
                thread_lock_perm.view(), pagetable_lock_perm.view(),
            ),
            kernel_k_to_kernel_u(*final(self))
                == kernel_k_to_kernel_u(*old(self)),
            pagetable_map_user_view(final(self).pagetable_map)
                == pagetable_map_user_view(old(self).pagetable_map),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger final(self).pagetable_map.spec_index(pagetable_ptr)
                    .view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
                old(self).pagetable_map.spec_index(pagetable_ptr).view()
                    .kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i)
                    && pei_valid(l2i)
                    && old(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                ==> final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i)
                    == old(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i),
            final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                == (PageState::Allocated4k {
                    state: Allocated4KPageState::PageTable {
                        pagetable_root: pagetable_ptr,
                    },
                }),
            final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count
                == old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
                    .ref_count,
            final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().mappings()
                == old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
                    .mappings(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().page_closure()
                =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().page_closure()
                    .insert(page_ptr),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
                =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
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
    {
        let page_index = page_ptr2page_index(page_ptr);
        let indices = va2index(va);
        assert(
            self.pagetable_map.perms_wf()
            && self.pagetable_map.spec_index(pagetable_ptr).inv()
            && self.thread_map.perms_wf()
            && self.thread_map.spec_index(thread_ptr).inv()
        ) by {
            reveal(pagetable_perms_wf);
            reveal(thread_perms_wf);
        };
        assert(
            index_valid(NUM_PAGES, page_index)
            && self.page_array.inv()
            && self.page_array.spec_index(page_index).view().is_init()
            && self.page_array.spec_index(page_index).view().inv()
            && self.page_array.spec_index(page_index).view().view().inv()
            && self.page_array.spec_index(page_index).view().view().addr == page_ptr
        ) by {
            reveal(page_array_wf);
            page_ptr_valid_imply_page_index_valid();
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

        let ghost old_page_lock_id = self.page_array.lock_id_by_index(page_index);
        proof {
            assert(lctx.lock_entry_contains_for(
                old_page_lock_id,
                KernelObjId::Page(page_index),
                MUTABLE_LOCK_ID,
            )) by { reveal(lock_id_aligned); };
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
                    Tracked(&mut *lctx),
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
                    Tracked(&mut *lctx),
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
                    Tracked(&mut *lctx),
                );
            },
        }

        proof {
            lctx.update_lock_id(
                KernelObjId::Page(page_index),
                old_page_lock_id,
                self.page_array.lock_id_by_index(page_index),
            );
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
                assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { reveal(process_pagetable_match); };
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
                assert(container_allocator_free_4k_page_wf(self.allocator_4k_map, self.page_array)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(self.allocator_4k_map, old(self).page_array, self.page_array, page_index); };
                assert(container_allocator_free_2m_page_wf(self.allocator_2m_map, self.page_array)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(self.allocator_2m_map, old(self).page_array, self.page_array, page_index); };
                assert(container_allocator_free_1g_page_wf(self.allocator_1g_map, self.page_array)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(self.allocator_1g_map, old(self).page_array, self.page_array, page_index); };
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
            assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
            assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { tlb_wf_spec_preserved_for_pagetable_mappings_unchanged(self.cpu_tlb, self.cpu_array, old(self).pagetable_map, self.pagetable_map, pagetable_ptr); };
            assert(lock_id_aligned(self, &*lctx)) by {
                reveal(lock_id_aligned);
            };
            assert(kernel_k_to_kernel_u(*self)
                == kernel_k_to_kernel_u(*old(self))) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(
                    old(self), self,
                );
            };
        }
    }
}

}
