use vstd::prelude::*;
use vstd::set::lemma_set_remove_len;

use super::mmap_4k_context::{staged_4k_page_op_ensures, staged_4k_page_table_op_requires};


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


    /// Consume one staged 4K page and publish it as exactly one page-table
    /// structure page.  The parent pointer is intentionally recovered from the
    /// locked PageTable here rather than accepted from the caller: the semantic
    /// missing level determines both the parent and the PageTable operation.
    ///
    /// Hidden Page/Thread state is made consistent while the kernel phase is
    /// Acquire. The single parent-entry store closes it into Release. Directory
    /// topology is absent from `PageTableU`, so the following boundary stutters.
    pub(super) fn install_staged_4k_page_table_page(
        kernel: &mut KernelK,
        level: MissingPageTableLevel,
        page_ptr: PagePtr,
        thread_ptr: RwLockThreadPtr,
        pagetable_ptr: RwLockPageTableRoot,
        indices: (L4Index, L3Index, L2Index),
        Tracked(lctx): Tracked<&mut LocalContext>,
        page_lock_perm: Tracked<&LockPerm>,
        thread_lock_perm: Tracked<&LockPerm>,
        pagetable_lock_perm: Tracked<&LockPerm>,
    )
        requires
            staged_4k_page_table_op_requires(
                old(kernel), old(lctx), page_ptr, thread_ptr, pagetable_ptr, indices,
                page_lock_perm.view(), thread_lock_perm.view(),
                pagetable_lock_perm.view(),
            ),
            match level {
                MissingPageTableLevel::L4 =>
                    old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l4(indices.0) is None,
                MissingPageTableLevel::L3 => {
                    &&& old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l4(indices.0) is Some
                    &&& old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            indices.0,
                            indices.1,
                        ) is None
                    &&& old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_1g_l3(
                            indices.0,
                            indices.1,
                        ) is None
                },
                MissingPageTableLevel::L2 => {
                    &&& old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            indices.0,
                            indices.1,
                        ) is Some
                    &&& old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(
                            indices.0,
                            indices.1,
                            indices.2,
                        ) is None
                    &&& old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_2m_l2(
                            indices.0,
                            indices.1,
                            indices.2,
                        ) is None
                },
            },
        ensures
            staged_4k_page_op_ensures(
                final(kernel), final(lctx), old(kernel), old(lctx), page_ptr,
                thread_ptr, pagetable_ptr, page_lock_perm.view(),
                thread_lock_perm.view(), pagetable_lock_perm.view(),
            ),
            forall|t: RwLockThreadPtr|
                #![trigger old(kernel).thread_map.spec_index(t)]
                #![trigger final(kernel).thread_map.spec_index(t)]
                t != thread_ptr && old(kernel).thread_map.dom().contains(t)
                ==> final(kernel).thread_map.dom().contains(t)
                    && final(kernel).thread_map.spec_index(t)
                        == old(kernel).thread_map.spec_index(t)
                    && final(kernel).thread_map.lock_id_by_key(t)
                        == old(kernel).thread_map.lock_id_by_key(t),
            forall|p: RwLockPageTableRoot|
                #![trigger old(kernel).pagetable_map.spec_index(p)]
                #![trigger final(kernel).pagetable_map.spec_index(p)]
                p != pagetable_ptr && old(kernel).pagetable_map.dom().contains(p)
                ==> final(kernel).pagetable_map.dom().contains(p)
                    && final(kernel).pagetable_map.spec_index(p)
                        == old(kernel).pagetable_map.spec_index(p)
                    && final(kernel).pagetable_map.lock_id_by_key(p)
                        == old(kernel).pagetable_map.lock_id_by_key(p),
            kernel_k_to_kernel_u(*final(kernel))
                == kernel_k_to_kernel_u(*old(kernel)),
            pagetable_map_user_view(final(kernel).pagetable_map)
                == pagetable_map_user_view(old(kernel).pagetable_map),
            final(kernel).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                == (PageState::Allocated4k {
                    state: Allocated4KPageState::PageTable {
                        pagetable_root: pagetable_ptr,
                    },
                }),
            final(kernel).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
                .perm_4k.view().is_none(),
            final(kernel).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count
                == old(kernel).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
                    .ref_count,
            final(kernel).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().mappings()
                == old(kernel).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
                    .mappings(),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().page_closure()
                =~= old(kernel).pagetable_map.spec_index(pagetable_ptr).view().page_closure()
                    .insert(page_ptr),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
                =~= old(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k(),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                =~= old(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                =~= old(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
            match level {
                MissingPageTableLevel::L4 => {
                    &&& final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l4(indices.0) is Some
                    &&& final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l4(indices.0)->0.addr == page_ptr
                    &&& final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            indices.0,
                            indices.1,
                        ) is None
                    &&& final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_1g_l3(
                            indices.0,
                            indices.1,
                        ) is None
                },
                MissingPageTableLevel::L3 => {
                    &&& final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l4(indices.0)
                        == old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                            .spec_resolve_mapping_l4(indices.0)
                    &&& final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            indices.0,
                            indices.1,
                        ) is Some
                    &&& final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            indices.0,
                            indices.1,
                        )->0.addr == page_ptr
                    &&& final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_1g_l3(
                            indices.0,
                            indices.1,
                        ) is None
                    &&& final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(
                            indices.0,
                            indices.1,
                            indices.2,
                        ) is None
                    &&& final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_2m_l2(
                            indices.0,
                            indices.1,
                            indices.2,
                        ) is None
                },
                MissingPageTableLevel::L2 => {
                    &&& final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l4(indices.0)
                        == old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                            .spec_resolve_mapping_l4(indices.0)
                    &&& final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            indices.0,
                            indices.1,
                        )
                        == old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                            .spec_resolve_mapping_l3(
                                indices.0,
                                indices.1,
                            )
                    &&& final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(
                            indices.0,
                            indices.1,
                            indices.2,
                        ) is Some
                    &&& final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(
                            indices.0,
                            indices.1,
                            indices.2,
                        )->0.addr == page_ptr
                    &&& final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_2m_l2(
                            indices.0,
                            indices.1,
                            indices.2,
                        ) is None
                },
            },
    {
        let page_index = page_ptr2page_index(page_ptr);
        assert(
            kernel.pagetable_map.perms_wf()
            && kernel.pagetable_map.spec_index(pagetable_ptr).inv()
            && kernel.thread_map.perms_wf()
            && kernel.thread_map.spec_index(thread_ptr).inv()
        ) by {
            reveal(pagetable_perms_wf);
            reveal(thread_perms_wf);
        };
        assert(
            index_valid(NUM_PAGES, page_index)
            && kernel.page_array.inv()
            && kernel.page_array.spec_index(page_index).view().is_init()
            && kernel.page_array.spec_index(page_index).view().inv()
            && kernel.page_array.spec_index(page_index).view().view().inv()
            && kernel.page_array.spec_index(page_index).view().view().addr == page_ptr
        ) by {
            reveal(page_array_wf);
            page_ptr_valid_imply_page_index_valid();
        };
        assert(!kernel.pagetable_map.spec_index(pagetable_ptr).view().page_closure().contains(page_ptr)) by { reveal(pagetable_pages_wf); };

        let parent_page_map_ptr;
        {
            let pagetable = kernel.pagetable_map.borrow(
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

        let ghost old_page_lock_id = kernel.page_array.lock_id_by_index(page_index);
        let page = kernel.page_array.borrow_mut(
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
            let thread = kernel.thread_map.borrow_mut(
                thread_ptr,
                Tracked(&*lctx),
                thread_lock_perm,
            );
            thread.temp_alloc_cache_4k = Ghost(
                thread.temp_alloc_cache_4k.view().remove(page_ptr),
            );
            thread.quota_4k = thread.quota_4k - 1;
        }
        let pagetable = kernel.pagetable_map.borrow_mut(
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
                TypedHeldLock {
                    lock_id: old_page_lock_id,
                    mode: TypedLockMode::Write,
                },
                kernel.page_array.lock_id_by_index(page_index),
            );
            assert(kernel.subsystems_inv()) by {
                assert(kernel.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
                assert(pagetable_perms_wf(kernel.pagetable_map)) by { reveal(pagetable_perms_wf); };
                assert(page_array_wf(kernel.page_array)) by { reveal(page_array_wf); };
                assert(thread_perms_wf(kernel.thread_map)) by {
                    reveal(thread_perms_wf);
                    reveal(thread_temp_alloc_empty_unless_wlocked);
                    reveal(thread_free_quota_pending_empty_unless_wlocked);
                    lemma_set_remove_len(old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view(), page_ptr);
                };
            };
            assert(kernel.memory_management_inv()) by {
                assert(allocator_pages_wf(
                    kernel.page_array,
                    kernel.allocator_4k_map,
                    kernel.allocator_2m_map,
                    kernel.allocator_1g_map,
                )) by {
                    allocator_4k_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).allocator_4k_map, kernel.allocator_4k_map);
                    allocator_2m_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).allocator_2m_map, kernel.allocator_2m_map);
                    allocator_1g_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).allocator_1g_map, kernel.allocator_1g_map);
                };
                assert(container_page_owner_wf(kernel.container_map, kernel.page_array)) by { container_page_owner_wf_preserved_for_owning_container_eq(old(kernel).container_map, kernel.container_map, old(kernel).page_array, kernel.page_array); };
                assert(hugepage_2m_wf(kernel.page_array)) by { hugepage_2m_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array); };
                assert(hugepage_1g_wf(kernel.page_array)) by { hugepage_1g_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array); };
                assert(page_pagetable_wf(kernel.pagetable_map, kernel.page_array)) by { page_pagetable_wf_preserved_for_page_table_page_insert(old(kernel).pagetable_map, kernel.pagetable_map, old(kernel).page_array, kernel.page_array, pagetable_ptr, page_ptr); };
                assert(process_pagetable_match(
                    kernel.process_map, kernel.pagetable_map,
                )) by {
                    assert({
                        &&& kernel.process_map == old(kernel).process_map
                        &&& kernel.pagetable_map.unchanged_except(
                            &old(kernel).pagetable_map, pagetable_ptr,
                        )
                        &&& kernel.pagetable_map.spec_index(pagetable_ptr).view().proc_ptr
                            == old(kernel).pagetable_map.spec_index(pagetable_ptr).view().proc_ptr
                        &&& kernel.pagetable_map.spec_index(pagetable_ptr).view().pcid
                            == old(kernel).pagetable_map.spec_index(pagetable_ptr).view().pcid
                    }) by {
                        reveal(process_pagetable_match);
                    };
                    reveal(process_pagetable_match);
                };
                assert(container_process_page_pagetable_wf(kernel.container_map, kernel.process_map, kernel.pagetable_map, kernel.page_array)) by { container_process_page_pagetable_wf_preserved_for_page_table_page_insert(kernel.container_map, kernel.process_map, old(kernel).pagetable_map, kernel.pagetable_map, old(kernel).page_array, kernel.page_array, pagetable_ptr, page_ptr); };
                assert(container_pages_wf(kernel.page_array, kernel.container_map)) by { container_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).container_map, kernel.container_map); };
                assert(process_pages_wf(kernel.page_array, kernel.process_map)) by { process_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).process_map, kernel.process_map); };
                assert(pagetable_pages_wf(kernel.pagetable_map, kernel.page_array)) by { pagetable_pages_wf_preserved_for_page_table_page_insert(old(kernel).pagetable_map, kernel.pagetable_map, old(kernel).page_array, kernel.page_array, pagetable_ptr, page_ptr); };
                assert(iommu_table_pages_wf(kernel.iommu_table_map, kernel.page_array)) by { iommu_table_pages_wf_preserved_for_non_iommu_page_change(kernel.iommu_table_map, old(kernel).page_array, kernel.page_array, page_ptr); };
                assert(thread_pages_wf(kernel.thread_map, kernel.page_array)) by { thread_pages_wf_preserved_for_page_state_eq(old(kernel).thread_map, kernel.thread_map, old(kernel).page_array, kernel.page_array); };
                assert(pcid_allocator_pages_wf(kernel.page_array, kernel.pcid_allocator_map)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).pcid_allocator_map, kernel.pcid_allocator_map); };
                assert(thread_staged_pages_wf(kernel.thread_map, kernel.page_array)) by {
                    assert(thread_staged_pages_4k_wf(kernel.thread_map, kernel.page_array)) by { thread_staged_pages_4k_wf_preserved_for_single_consume(old(kernel).thread_map, kernel.thread_map, old(kernel).page_array, kernel.page_array, thread_ptr, page_ptr); };
                    assert(thread_staged_pages_2m_wf(kernel.thread_map, kernel.page_array)) by { thread_staged_pages_2m_wf_preserved_for_eq(old(kernel).thread_map, kernel.thread_map, old(kernel).page_array, kernel.page_array); };
                    assert(thread_staged_pages_1g_wf(kernel.thread_map, kernel.page_array)) by { thread_staged_pages_1g_wf_preserved_for_eq(old(kernel).thread_map, kernel.thread_map, old(kernel).page_array, kernel.page_array); };
                };
                assert(endpoint_pages_wf(kernel.endpoint_map, kernel.page_array)) by { endpoint_pages_wf_preserved_for_page_state_eq(old(kernel).endpoint_map, kernel.endpoint_map, old(kernel).page_array, kernel.page_array); };
                assert(container_process_allocator_quota_wf(
                    kernel.container_map,
                    kernel.process_map,
                    kernel.thread_map,
                    kernel.allocator_4k_map,
                    kernel.allocator_2m_map,
                    kernel.allocator_1g_map,
                )) by {
                    reveal(thread_quota_4k_fields_unchanged);
                    reveal(thread_quota_2m_fields_unchanged);
                    reveal(thread_quota_1g_fields_unchanged);
                    container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields_forall();
                    container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields_forall();
                    container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields_forall();
                };
                assert(container_allocator_free_4k_page_wf(kernel.allocator_4k_map, kernel.page_array)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(kernel.allocator_4k_map, old(kernel).page_array, kernel.page_array, page_index); };
                assert(container_allocator_free_2m_page_wf(kernel.allocator_2m_map, kernel.page_array)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(kernel.allocator_2m_map, old(kernel).page_array, kernel.page_array, page_index); };
                assert(container_allocator_free_1g_page_wf(kernel.allocator_1g_map, kernel.page_array)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(kernel.allocator_1g_map, old(kernel).page_array, kernel.page_array, page_index); };
            };
            assert(kernel.process_management_inv()) by {
                assert(thread_caller_callee_wf(kernel.thread_map)) by {
                    assert(thread_process_management_fields_unchanged(
                        old(kernel).thread_map, kernel.thread_map,
                    )) by { reveal(thread_perms_wf); };
                    thread_caller_callee_wf_preserved_for_thread_process_management_fields(
                        old(kernel).thread_map, kernel.thread_map,
                    );
                };
                assert(thread_endpoint_ref_counter_wf(kernel.thread_map, kernel.endpoint_map)) by { thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(old(kernel).thread_map, kernel.thread_map, kernel.endpoint_map); };
                assert(thread_endpoint_queue_wf(kernel.thread_map, kernel.endpoint_map)) by { thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(old(kernel).thread_map, kernel.thread_map, kernel.endpoint_map); };
                assert(container_thread_endpoint_wf(kernel.container_map, kernel.thread_map, kernel.endpoint_map)) by { container_thread_endpoint_wf_preserved_for_thread_process_management_fields(kernel.container_map, old(kernel).thread_map, kernel.thread_map, kernel.endpoint_map); };
                assert(container_thread_scheduler_wf(kernel.container_map, kernel.thread_map, kernel.scheduler_map)) by { container_thread_scheduler_wf_preserved_for_thread_process_management_fields(kernel.container_map, old(kernel).thread_map, kernel.thread_map, kernel.scheduler_map); };
                assert(container_thread_wf(kernel.container_map, kernel.thread_map)) by { container_thread_wf_preserved_for_thread_process_management_fields(kernel.container_map, old(kernel).thread_map, kernel.thread_map); };
                assert(process_thread_wf(kernel.process_map, kernel.thread_map)) by { process_thread_wf_preserved_for_thread_process_management_fields(kernel.process_map, old(kernel).thread_map, kernel.thread_map); };
                assert(thread_cpu_wf(kernel.thread_map, kernel.cpu_array)) by { thread_cpu_wf_preserved_for_thread_process_management_fields(old(kernel).thread_map, kernel.thread_map, kernel.cpu_array); };
            };
            assert(cpu_dirty_map_wf(kernel.container_map, kernel.process_map, kernel.cpu_array, kernel.cpu_tlb, kernel.pagetable_map)) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
            assert(tlb_wf_spec(kernel.cpu_tlb, kernel.pagetable_map, kernel.cpu_array)) by { tlb_wf_spec_preserved_for_pagetable_mappings_unchanged(kernel.cpu_tlb, kernel.cpu_array, old(kernel).pagetable_map, kernel.pagetable_map, pagetable_ptr); };
            assert(typed_lock_maps_aligned(kernel, &*lctx)) by {
                reveal(typed_lock_maps_aligned);
            };
            assert(kernel_k_to_kernel_u(*kernel)
                == kernel_k_to_kernel_u(*old(kernel))) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(
                    old(kernel), kernel,
                );
            };
        }
    }


}
