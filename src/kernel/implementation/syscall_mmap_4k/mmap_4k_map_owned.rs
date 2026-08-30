use vstd::prelude::*;
use vstd::set::lemma_set_remove_len;

verus! {

use crate::*;


    /// Publish one staged 4K page at a fresh virtual address whose L1 table
    /// already exists.
    ///
    /// The caller holds the page, owner-thread, and target-page-table write
    /// locks. The thread lock is needed because mapping consumes the page from
    /// its temporary allocation cache and charges its quota. Hidden page/thread
    /// metadata is updated while the kernel phase is Acquire; the published PTE
    /// store is the operation that closes the section into Release. The caller
    /// later ends the kernel step, which observes the changed `PageTableU` and
    /// records exactly one non-stuttering transition.
    pub(super) fn map_owned_4k_page(
        kernel: &mut KernelK,
        page_ptr: PagePtr,
        thread_ptr: RwLockThreadPtr,
        pagetable_ptr: RwLockPageTableRoot,
        va: VAddr,
        write: bool,
        execute_disable: bool,
        Tracked(lctx): Tracked<&mut LocalContext>,
        page_lock_perm: Tracked<&LockPerm>,
        thread_lock_perm: Tracked<&LockPerm>,
        pagetable_lock_perm: Tracked<&LockPerm>,
    )
        requires
            staged_4k_page_op_requires(
                old(kernel), old(lctx), page_ptr, thread_ptr, pagetable_ptr, va,
                page_lock_perm.view(), thread_lock_perm.view(),
                pagetable_lock_perm.view(),
            ),
            old(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k().dom().contains(va)
                == false,
            old(kernel).pagetable_map.spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(
                spec_va2index(va).0,
                spec_va2index(va).1,
                spec_va2index(va).2,
            ) is Some,
        ensures
            staged_4k_page_op_ensures(
                final(kernel), final(lctx), old(kernel), old(lctx), page_ptr,
                thread_ptr, pagetable_ptr, page_lock_perm.view(),
                thread_lock_perm.view(), pagetable_lock_perm.view(),
            ),
            kernel_k_to_kernel_u(*final(kernel))
                != kernel_k_to_kernel_u(*old(kernel)),
            final(kernel).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                == PageState::Mapped4k,
            final(kernel).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
                .perm_4k.view()
                == old(kernel).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
                    .perm_4k.view(),
            final(kernel).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().mappings()
                == Set::empty().insert((pagetable_ptr, va)),
            final(kernel).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count == 1,
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
                == old(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k().insert(
                    va,
                    MapEntry {
                        addr: page_ptr,
                        present: true,
                        write,
                        execute_disable,
                        owning_container: Ghost(final(kernel).page_array
                            .spec_index(page_ptr2page_index(page_ptr))
                            .view().view().owning_container),
                    },
                ),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_resolve_mapping_4k_l1(
                    spec_va2index(va).0,
                    spec_va2index(va).1,
                    spec_va2index(va).2,
                    spec_va2index(va).3,
                ) == Some(PageEntry {
                    addr: page_ptr,
                    perm: PageEntryPerm {
                        present: true,
                        ps: false,
                        write,
                        execute_disable,
                        user: true,
                        kernel_present: true,
                    },
                }),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                == old(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                == old(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_resolve_mapping_l4(spec_va2index(va).0)
                == old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                    .spec_resolve_mapping_l4(spec_va2index(va).0),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_resolve_mapping_l3(spec_va2index(va).0, spec_va2index(va).1)
                == old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                    .spec_resolve_mapping_l3(spec_va2index(va).0, spec_va2index(va).1),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_resolve_mapping_l2(
                    spec_va2index(va).0,
                    spec_va2index(va).1,
                    spec_va2index(va).2,
                )
                == old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                    .spec_resolve_mapping_l2(
                        spec_va2index(va).0,
                        spec_va2index(va).1,
                        spec_va2index(va).2,
                    ),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger final(kernel).pagetable_map.spec_index(pagetable_ptr)
                    .view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
                final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                    .kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i)
                    && pei_valid(l2i)
                ==> final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i)
                    == old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().page_closure()
                == old(kernel).pagetable_map.spec_index(pagetable_ptr).view().page_closure(),
    {
        let page_index = page_ptr2page_index(page_ptr);
        let indices = va2index(va);
        assert(
            kernel.pagetable_map.perms_wf()
            && kernel.pagetable_map.spec_index(pagetable_ptr).inv()
            && kernel.page_array.inv()
            && kernel.page_array.spec_index(page_index).view().inv()
            && kernel.thread_map.perms_wf()
            && kernel.thread_map.spec_index(thread_ptr).inv()
        ) by {
            reveal(pagetable_perms_wf);
            reveal(page_array_wf);
            reveal(thread_perms_wf);
        };
        let target_l1_ptr;
        {
            let pagetable = kernel.pagetable_map.borrow(
                pagetable_ptr,
                pagetable_lock_perm,
            );
            let l4_entry = pagetable.get_entry_l4(indices.0).unwrap();
            let l3_entry = pagetable.get_entry_l3(indices.0, indices.1, &l4_entry).unwrap();
            let l2_entry = pagetable.get_entry_l2(
                indices.0,
                indices.1,
                indices.2,
                &l3_entry,
            ).unwrap();
            target_l1_ptr = l2_entry.addr;
        }

        let page_owner;
        let ghost old_page_lock_id = kernel.page_array.lock_id_by_index(page_index);
        {
            let page = kernel.page_array.borrow_mut(
                page_index,
                Tracked(&*lctx),
                page_lock_perm,
            );
            page_owner = page.owning_container;
            page.state = PageState::Mapped4k;
            page.mappings = Ghost(Set::empty().insert((pagetable_ptr, va)));
            page.ref_count = 1;
        }
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
        let target_entry = MapEntry {
            addr: page_ptr,
            present: true,
            write,
            execute_disable,
            owning_container: Ghost(page_owner),
        };
        proof {
            assert(spec_index2va(indices) == va) by {
                spec_va_4k_index_roundtrip();
            };
        }
        let pagetable = kernel.pagetable_map.borrow_mut(
            pagetable_ptr,
            Tracked(&mut *lctx),
            pagetable_lock_perm,
        );
        pagetable.map_4k_page(
            indices.0,
            indices.1,
            indices.2,
            indices.3,
            target_l1_ptr,
            &target_entry,
            Tracked(&mut *lctx),
        );

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
                assert(allocator_pages_wf(kernel.page_array, kernel.allocator_4k_map, kernel.allocator_2m_map, kernel.allocator_1g_map)) by {
                    allocator_4k_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).allocator_4k_map, kernel.allocator_4k_map);
                    allocator_2m_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).allocator_2m_map, kernel.allocator_2m_map);
                    allocator_1g_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).allocator_1g_map, kernel.allocator_1g_map);
                };
                assert(container_page_owner_wf(kernel.container_map, kernel.page_array)) by { container_page_owner_wf_preserved_for_owning_container_eq(old(kernel).container_map, kernel.container_map, old(kernel).page_array, kernel.page_array); };
                assert(hugepage_2m_wf(kernel.page_array)) by { hugepage_2m_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array); };
                assert(hugepage_1g_wf(kernel.page_array)) by { hugepage_1g_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array); };
                assert(page_pagetable_wf(kernel.pagetable_map, kernel.page_array)) by { page_pagetable_wf_preserved_for_4k_mapping_insert(old(kernel).pagetable_map, kernel.pagetable_map, old(kernel).page_array, kernel.page_array, pagetable_ptr, page_ptr, va); };
                assert(container_process_page_pagetable_wf(kernel.container_map, kernel.process_map, kernel.pagetable_map, kernel.page_array)) by {
                    reveal(process_thread_wf);
                    reveal(process_pagetable_match);
                    container_process_page_pagetable_wf_preserved_for_4k_mapping_insert(kernel.container_map, kernel.process_map, old(kernel).pagetable_map, kernel.pagetable_map, old(kernel).page_array, kernel.page_array, pagetable_ptr, page_ptr, va);
                };
                assert(container_pages_wf(kernel.page_array, kernel.container_map)) by { container_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).container_map, kernel.container_map); };
                assert(process_pages_wf(kernel.page_array, kernel.process_map)) by { process_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).process_map, kernel.process_map); };
                assert(pagetable_pages_wf(
                    kernel.pagetable_map, kernel.page_array,
                )) by {
                    assert({
                        &&& kernel.pagetable_map.unchanged_except(
                            &old(kernel).pagetable_map, pagetable_ptr,
                        )
                        &&& kernel.pagetable_map.spec_index(pagetable_ptr).view()
                            .page_closure()
                            == old(kernel).pagetable_map.spec_index(pagetable_ptr)
                                .view().page_closure()
                    }) by {
                        reveal(pagetable_pages_wf);
                    };
                    reveal(pagetable_pages_wf);
                };
                assert(iommu_table_pages_wf(kernel.iommu_table_map, kernel.page_array)) by { reveal(iommu_table_pages_wf); };
                assert(thread_pages_wf(kernel.thread_map, kernel.page_array)) by { thread_pages_wf_preserved_for_page_state_eq(old(kernel).thread_map, kernel.thread_map, old(kernel).page_array, kernel.page_array); };
                assert(pcid_allocator_pages_wf(kernel.page_array, kernel.pcid_allocator_map)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).pcid_allocator_map, kernel.pcid_allocator_map); };
                assert(thread_staged_pages_wf(kernel.thread_map, kernel.page_array)) by {
                    reveal(thread_staged_pages_4k_wf);
                    thread_staged_pages_2m_wf_preserved_for_eq(old(kernel).thread_map, kernel.thread_map, old(kernel).page_array, kernel.page_array);
                    thread_staged_pages_1g_wf_preserved_for_eq(old(kernel).thread_map, kernel.thread_map, old(kernel).page_array, kernel.page_array);
                };
                assert(endpoint_pages_wf(kernel.endpoint_map, kernel.page_array)) by { endpoint_pages_wf_preserved_for_page_state_eq(old(kernel).endpoint_map, kernel.endpoint_map, old(kernel).page_array, kernel.page_array); };
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
                assert(container_process_allocator_quota_wf(kernel.container_map, kernel.process_map, kernel.thread_map, kernel.allocator_4k_map, kernel.allocator_2m_map, kernel.allocator_1g_map)) by {
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
            assert(tlb_wf_spec(kernel.cpu_tlb, kernel.pagetable_map, kernel.cpu_array)) by { tlb_wf_spec_preserved_for_4k_mapping_insert(kernel.cpu_tlb, kernel.cpu_array, old(kernel).pagetable_map, kernel.pagetable_map, pagetable_ptr, va); };
            assert(typed_lock_maps_aligned(kernel, &*lctx)) by {
                reveal(typed_lock_maps_aligned);
            };
            assert({
                let process_ptr = kernel.thread_map.spec_index(thread_ptr)
                    .view().owning_proc;
                &&& kernel_k_to_kernel_u(*old(kernel)).process_map.dom()
                    .contains(process_ptr)
                &&& kernel_k_to_kernel_u(*kernel).process_map.dom()
                    .contains(process_ptr)
                &&& !kernel_k_to_kernel_u(*old(kernel)).process_map
                    .spec_index(process_ptr).pagetable.mapping_4k.dom()
                    .contains(va)
                &&& kernel_k_to_kernel_u(*kernel).process_map
                    .spec_index(process_ptr).pagetable.mapping_4k.dom()
                    .contains(va)
            }) by {

                reveal(process_thread_wf);
                reveal(process_pagetable_match);
            };
        }
    }


}
