use super::*;
use super::allocate_free_4k_impl_basd::allocator_objects_unlocked_except_cache_pool;
use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;

verus! {

// TODO(AGENTS): Replace the two quota-fold assert-forall bridges in this module
// with a trigger/postcondition on the fold producer. They are the remaining
// non-local proof steps in these otherwise framed allocator transitions.



    // ================================================================
    // pop_stage_4k_page: cache[cpu_id] + thread are already write-locked and
    // the cache is non-empty. Peek the head, lock the page slot, pop the head,
    // retype it Free4k{PreCpuCache}→Owned4k, stage it in the thread's
    // temp_alloc_cache_4k, decrement the allocator's total_free_pages. Leaves
    // page + cache still write-locked; re-establishes inv().
    // ================================================================
    #[verifier::spinoff_prover]
    pub(super) fn pop_stage_4k_page(
        kernel: &mut KernelK,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        cpu_id: CpuId,
        thread_ptr: RwLockThreadPtr,
        container_ptr: RwLockContainerPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(cache_lock_perm): Tracked<&LockPerm>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(kernel).inv(),
            index_valid(NUM_CPUS, cpu_id),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(kernel).container_map.dom().contains(container_ptr),
            old(kernel).container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(kernel).thread_map.dom().contains(thread_ptr),
            old(kernel).thread_map.spec_index(thread_ptr).view().owning_container == container_ptr,
            old(kernel).allocator_4k_map.dom().contains(alloc_ptr_4k),
            allocator_objects_unlocked_except_cache_pool(
                old(kernel).allocator_4k_map, alloc_ptr_4k,
                old(lctx).thread_id()),
            cache_lock_perm.state() is WriteLock,
            cache_lock_perm.thread_id() == old(lctx).thread_id(),
            cache_lock_perm.lock_id() == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().view().len() > 0,
            old(kernel).thread_map.spec_index(thread_ptr).being_killed() == false,
            thread_effective_quota_4k(old(kernel).thread_map.spec_index(thread_ptr)) >= 1,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(kernel).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(kernel).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
            page_objects_unlocked(
                old(kernel).page_array, old(lctx).thread_id()),
            lock_id_aligned(old(kernel), old(lctx)),
            old(lctx).held_lock_majors_lt(FREE_PAGE_LOCK_MAJOR),
        ensures
            final(kernel).inv(),
            allocator_objects_unlocked_except_cache_pool(
                final(kernel).allocator_4k_map, alloc_ptr_4k,
                final(lctx).thread_id()),
            forall|other_cpu: CpuId|
                #![trigger final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.spec_index(other_cpu).view()
                    .locked_by_thread(final(lctx).thread_id())]
                index_valid(NUM_CPUS, other_cpu)
                ==> final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(other_cpu).view()
                        .locked_by_thread(final(lctx).thread_id())
                    == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(other_cpu).view()
                        .locked_by_thread(old(lctx).thread_id()),
            page_ptr_valid(ret.0),
            old(kernel).page_array.spec_index(page_ptr2page_index(ret.0))
                .view().view().state is Free4k,
            !old(kernel).thread_map.spec_index(thread_ptr).view()
                .temp_alloc_cache_4k.view().contains(ret.0),
            final(kernel).allocator_4k_map.dom() == old(kernel).allocator_4k_map.dom(),
            final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).quota
                == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
            forall|p: RwLockPageAllocatorPtr|
                #![trigger final(kernel).allocator_4k_map.spec_index(p)]
                old(kernel).allocator_4k_map.dom().contains(p) && p != alloc_ptr_4k
                ==> final(kernel).allocator_4k_map.spec_index(p)
                    == old(kernel).allocator_4k_map.spec_index(p),
            final(kernel).allocator_2m_map == old(kernel).allocator_2m_map,
            final(kernel).allocator_1g_map == old(kernel).allocator_1g_map,
            final(kernel).page_array.entries_unchanged_except(
                &old(kernel).page_array, page_ptr2page_index(ret.0)),
            // ---- user view unchanged: staging is kernel-internal ----
            kernel_k_to_kernel_u(*final(kernel)) == kernel_k_to_kernel_u(*old(kernel)),
            // ---- cache + thread lock state preserved, phase still Acquire ----
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            cache_lock_perm.lock_id() == final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).lock_id()
                == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).lock_id(),
            final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.entries_unchanged_except(
                &old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches, cpu_id),
            final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view().view().view()
                == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.spec_index(cpu_id).view().view().view().skip(1),
            final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view().wlocked_by(final(lctx)),
            final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view()
                .locked_by_thread(final(lctx).thread_id()),
            final(kernel).thread_map.spec_index(thread_ptr).being_killed() == false,
            final(kernel).thread_map.spec_index(thread_ptr).view().owning_proc
                == old(kernel).thread_map.spec_index(thread_ptr).view().owning_proc,
            final(kernel).thread_map.spec_index(thread_ptr).view().owning_container
                == old(kernel).thread_map.spec_index(thread_ptr).view().owning_container,
            final(kernel).thread_map.spec_index(thread_ptr).view()
                .stable_allocation_root_equal(
                    &old(kernel).thread_map.spec_index(thread_ptr).view(),
                ),
            final(kernel).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                == old(kernel).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr,
            final(kernel).thread_map.unchanged_except(&old(kernel).thread_map, thread_ptr),
            forall|t: RwLockThreadPtr|
                #![trigger old(kernel).thread_map.spec_index(t)]
                #![trigger final(kernel).thread_map.spec_index(t)]
                t != thread_ptr && old(kernel).thread_map.dom().contains(t)
                ==> final(kernel).thread_map.dom().contains(t)
                    && final(kernel).thread_map.lock_id_by_key(t)
                        == old(kernel).thread_map.lock_id_by_key(t),
            forall|t: RwLockThreadPtr|
                #![trigger old(kernel).thread_map.spec_index(t)
                    .locked_by_thread(old(lctx).thread_id())]
                #![trigger final(kernel).thread_map.spec_index(t)
                    .locked_by_thread(final(lctx).thread_id())]
                (old(kernel).thread_map.dom().contains(t)
                    && old(kernel).thread_map.spec_index(t)
                        .locked_by_thread(old(lctx).thread_id()))
                == (final(kernel).thread_map.dom().contains(t)
                    && final(kernel).thread_map.spec_index(t)
                        .locked_by_thread(final(lctx).thread_id())),
            final(kernel).thread_map.spec_index(thread_ptr).wlocked_by(final(lctx)),
            final(kernel).thread_map.spec_index(thread_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            thread_lock_perm.lock_id() == final(kernel).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            final(kernel).thread_map.lock_id_by_key(thread_ptr)
                == old(kernel).thread_map.lock_id_by_key(thread_ptr),
            // ---- page slot left write-locked, perm handed back ----
            index_valid(NUM_PAGES, page_ptr2page_index(ret.0)),
            page_objects_unlocked_except(
                final(kernel).page_array, final(lctx).thread_id(),
                set![page_ptr2page_index(ret.0)]),
            final(kernel).page_array.spec_index(page_ptr2page_index(ret.0)).view().wlocked_by(final(lctx)),
            final(kernel).page_array.spec_index(page_ptr2page_index(ret.0)).view()
                .locked_by_thread(final(lctx).thread_id()),
            final(kernel).page_array.spec_index(page_ptr2page_index(ret.0)).view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(kernel).page_array.spec_index(page_ptr2page_index(ret.0)).view().locking_thread()->Write_lock_id,
            // ---- held-lock set: gained exactly the page slot ----
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert(
                (
                    final(kernel).page_array.lock_id_by_index(page_ptr2page_index(ret.0)),
                    KernelObjId::Page(page_ptr2page_index(ret.0)),
                ),
            ),
            lock_id_aligned(final(kernel), final(lctx)),
            // ---- staging: ret staged Owned4k; 4k cache gained exactly ret, 2m/1g caches + nominal quota untouched ----
            final(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
                =~= old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().insert(ret.0),
            final(kernel).page_array.spec_index(page_ptr2page_index(ret.0)).view().view().state == (PageState::Owned4k{ thread_ptr }),
            final(kernel).page_array.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container
                == container_ptr,
            final(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m
                == old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m,
            final(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g
                == old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            final(kernel).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_fields_equal(
                    &old(kernel).thread_map.spec_index(thread_ptr).view(),
                ),
            final(kernel).thread_map.spec_index(thread_ptr).view().quota_4k
                == old(kernel).thread_map.spec_index(thread_ptr).view().quota_4k,
            final(kernel).thread_map.spec_index(thread_ptr).view().endpoint_descriptors
                == old(kernel).thread_map.spec_index(thread_ptr).view().endpoint_descriptors,
            // ---- container_map + scheduler_map untouched (staging never writes them) ----
            final(kernel).container_map == old(kernel).container_map,
            final(kernel).process_map == old(kernel).process_map,
            final(kernel).pagetable_map == old(kernel).pagetable_map,
            final(kernel).scheduler_map == old(kernel).scheduler_map,
            final(kernel).pcid_allocator_map == old(kernel).pcid_allocator_map,
            final(kernel).endpoint_map == old(kernel).endpoint_map,
            final(kernel).iommu_root_table == old(kernel).iommu_root_table,
            final(kernel).iommu_table_map == old(kernel).iommu_table_map,
            final(kernel).iommu_tlb == old(kernel).iommu_tlb,
            final(kernel).cpu_array == old(kernel).cpu_array,
            final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool
                == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
    {
        assert(
            kernel.allocator_4k_map.perms_wf()
            && kernel.allocator_4k_map.spec_index(alloc_ptr_4k).wf()
            && kernel.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.inv()
            && kernel.thread_map.perms_wf()
            && kernel.page_array.inv()
        ) by {
            reveal(allocator_perms_wf);
            reveal(thread_perms_wf);
            reveal(page_array_wf);
        };
        let cache_ref = kernel.allocator_4k_map.borrow_cache(
            alloc_ptr_4k, cpu_id, Tracked(cache_lock_perm),
        );
        let (node_addr, page_ptr) = cache_ref.linked_list.peek_head();
        assert(page_ptr_valid(page_ptr)) by {
            reveal(allocator_perms_wf);
            reveal(allocator_free_page_ptrs_wf);
        };
        let page_index = page_ptr2page_index(page_ptr);
        assert(index_valid(NUM_PAGES, page_index)) by {
            page_ptr_valid_imply_page_index_valid();
        };
        assert(
            old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view().view().view().contains(page_ptr)
        ) by {
            reveal(LinkedList::wf_value_list);
        };
        assert(lctx.lock_id_acyclic(
            kernel.page_array.lock_id_by_index(page_index),
        )) by {
            reveal(container_allocator_free_4k_page_wf);
            reveal(container_allocator_cpu_cache_free_4k_page_wf);
        };
        // Lock the page slot after deriving its ordering id from the cache head.
        let Tracked(page_lock_perm) = kernel.wlock_page(page_index, Tracked(&mut *lctx));

        // Mutation block: pop + decrement (PageAllocator::inv() re-established by
        // the wrapper), retype Free4k→Owned4k, stage.
        let alloc_mut = kernel.allocator_4k_map.borrow_mut(alloc_ptr_4k);
        let (node_addr2, Tracked(node_perm)) = alloc_mut.pop_cache_page(cpu_id, Tracked(&*lctx), Tracked(cache_lock_perm));
        assert(node_addr2 == node_addr) by {
            old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view().view().linked_list
                .lemma_value_addr_unique(node_addr, node_addr2);
        };
        assert(
            kernel.page_array.inv()
            && kernel.thread_map.perms_wf()
            && kernel.thread_map.spec_index(thread_ptr).is_init()
        ) by {
            reveal(page_array_wf);
            reveal(thread_perms_wf);
        };
        let ghost old_page_lock_id = kernel.page_array.lock_id_by_index(page_index);
        {
            let mut page = kernel.page_array.borrow_mut(
                page_index, Tracked(&*lctx), Tracked(&page_lock_perm),
            );
            assert(
                page.state == PageState::Free4k {
                    allocator_ptr: Ghost(alloc_ptr_4k),
                    state: FreePageAllocatorState::PreCpuCache { cpu_id },
                }
                && page.owning_container == container_ptr
            ) by {
                reveal(container_allocator_free_4k_page_wf);
                reveal(container_allocator_cpu_cache_free_4k_page_wf);
                reveal(container_allocator_wf);
            };
            page.state = PageState::Owned4k { thread_ptr };
            assert(node_addr == page.free_list_node_storage.addr()) by {
                reveal(container_allocator_free_4k_page_wf);
                reveal(container_allocator_cpu_cache_free_4k_page_wf);
                reveal(LinkedList::wf_map);
            };
            page.free_list_node_storage.put(Tracked(node_perm));

            let thread_mut = kernel.thread_map.borrow_mut(
                thread_ptr, Tracked(&*lctx), Tracked(thread_lock_perm),
            );
            thread_mut.temp_alloc_cache_4k = Ghost(thread_mut.temp_alloc_cache_4k.view().insert(page_ptr));
        }
        proof {
            lctx.enter_kernel_view_release();
            lctx.update_lock_id(
                KernelObjId::Page(page_index),
                old_page_lock_id,
                kernel.page_array.lock_id_by_index(page_index),
            );
            assert(kernel.allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.lock_id_by_index(cpu_id)
                == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.lock_id_by_index(cpu_id)
            ) by {
                reveal(allocator_perms_wf);
            };
            assert(lctx.lock_entry_contains(
                kernel.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.lock_id_by_index(cpu_id),
                KernelObjId::AllocatorCache(
                    PageSize::SZ4k, alloc_ptr_4k, cpu_id,
                ),
            )) by {
                reveal(lock_id_aligned);
                lock_id_fields_eq_imply_eq();
            };
            assert(lock_id_aligned(kernel, &*lctx)) by {
                assert({
                    &&& kernel.thread_map.spec_index(thread_ptr).view().state
                        == old(kernel).thread_map.spec_index(thread_ptr).view().state
                    &&& kernel.thread_map.spec_index(thread_ptr).view()
                        .blocking_endpoint_ptr
                        == old(kernel).thread_map.spec_index(thread_ptr).view()
                            .blocking_endpoint_ptr
                    &&& kernel.thread_map.lock_id_by_key(thread_ptr)
                        == old(kernel).thread_map.lock_id_by_key(thread_ptr)
                }) by {
                    reveal(thread_perms_wf);
                    lock_id_fields_eq_imply_eq();
                };
                assert(
                    PAGE_TABLE_LOCK_MAJOR < ALLOCATOR_CACHE_MAJOR
                        && IOMMU_TABLE_LOCK_MAJOR < ALLOCATOR_CACHE_MAJOR
                ) by (compute);
                reveal(lock_id_aligned);
                lock_id_fields_eq_imply_eq();
            };
        }
        // ---- staging delta: page_ptr fresh in temp_alloc_cache_4k ⟹ effective_quota_4k −1 ----
        assert(old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) == false) by {
            reveal(thread_staged_pages_4k_wf);
            if old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) {
                assert(old(kernel).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == PageState::Owned4k { thread_ptr }) by {
                    reveal(thread_staged_pages_4k_wf);
                };
            }
        };
        proof {
            // ---- user view unchanged: only page_array / temp_alloc / total moved ----
            assert(kernel_k_to_kernel_u(*kernel) == kernel_k_to_kernel_u(*old(kernel))) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(kernel), kernel);
            };
        }
        proof {
            assert(
                thread_quota_2m_fields_unchanged(old(kernel).thread_map, kernel.thread_map)
                && thread_quota_1g_fields_unchanged(old(kernel).thread_map, kernel.thread_map)
            ) by {
                reveal(thread_quota_2m_fields_unchanged);
                reveal(thread_quota_1g_fields_unchanged);
            };
            // ---- subsystems_inv ----
            assert(kernel.subsystems_inv()) by {
                reveal(KernelK::default_pagetable_wf);
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(container_tree_fields_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
                reveal(thread_temp_alloc_empty_unless_wlocked);
                reveal(page_array_wf);
                reveal(thread_perms_wf);
                reveal(thread_free_quota_pending_empty_unless_wlocked);
            };
            // ---- memory_management_inv ----
            assert(kernel.memory_management_inv()) by {
                assert(allocator_pages_wf(kernel.page_array, kernel.allocator_4k_map, kernel.allocator_2m_map, kernel.allocator_1g_map)) by {
                    allocator_4k_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).allocator_4k_map, kernel.allocator_4k_map);
                    allocator_2m_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).allocator_2m_map, kernel.allocator_2m_map);
                    allocator_1g_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).allocator_1g_map, kernel.allocator_1g_map);
                };
                assert(container_page_owner_wf(kernel.container_map, kernel.page_array)) by { container_page_owner_wf_preserved_for_owning_container_eq(old(kernel).container_map, kernel.container_map, old(kernel).page_array, kernel.page_array); };
                assert(container_process_page_pagetable_wf(kernel.container_map, kernel.process_map, kernel.pagetable_map, kernel.page_array)) by {
                    reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                    reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                };
                assert(container_pages_wf(kernel.page_array, kernel.container_map)) by { container_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).container_map, kernel.container_map); };
                assert(process_pages_wf(kernel.page_array, kernel.process_map)) by { process_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).process_map, kernel.process_map); };
                assert(container_process_allocator_quota_4k_wf(kernel.container_map, kernel.process_map, kernel.thread_map, kernel.allocator_4k_map)) by {
                    reveal(container_process_allocator_quota_4k_wf);
                    reveal(container_process_wf);
                    reveal(container_thread_wf);
                    reveal(container_allocator_wf);
                    lemma_thread_effective_quota_4k_fold_change_by_forall(thread_ptr, -1);
                    assert forall|c_ptr: RwLockContainerPtr|
                        #![trigger
                            thread_effective_quota_4k_fold_sum(
                                kernel.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                                kernel.thread_map,
                            ),
                            thread_effective_quota_4k_fold_sum(
                                kernel.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                                old(kernel).thread_map,
                            )
                        ]
                        (kernel.container_map.dom().contains(c_ptr)
                        && (forall|t: RwLockThreadPtr|
                            #![trigger thread_effective_quota_4k(old(kernel).thread_map.spec_index(t))]
                            kernel.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().contains(t)
                                ==> {
                                    &&& kernel.thread_map.dom().contains(t)
                                    &&& old(kernel).thread_map.dom().contains(t)
                                    &&& thread_effective_quota_4k(kernel.thread_map.spec_index(t))
                                        == thread_effective_quota_4k(old(kernel).thread_map.spec_index(t))
                                }))
                        implies thread_effective_quota_4k_fold_sum(
                            kernel.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                            kernel.thread_map,
                        ) == thread_effective_quota_4k_fold_sum(
                            kernel.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                            old(kernel).thread_map,
                        ) by {
                        lemma_thread_effective_quota_4k_fold_sum_eq(
                            kernel.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                            old(kernel).thread_map,
                            kernel.thread_map,
                        );
                    };
                    lemma_thread_pending_4k_folds_eq_forall(
                        kernel.container_map,
                        old(kernel).thread_map,
                        kernel.thread_map,
                    );
                    lemma_process_effective_quota_4k_fold_sum_eq_forall();
                };
                assert(container_process_allocator_quota_2m_wf(kernel.container_map, kernel.process_map, kernel.thread_map, kernel.allocator_2m_map)) by {
                    container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields_forall();
                };
                assert(container_process_allocator_quota_1g_wf(kernel.container_map, kernel.process_map, kernel.thread_map, kernel.allocator_1g_map)) by {
                    container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields_forall();
                };
                assert(container_allocator_wf(kernel.container_map, kernel.allocator_4k_map, kernel.allocator_2m_map, kernel.allocator_1g_map)) by {
                    reveal(container_allocator_wf);
                };
                assert(allocator_free_page_ptrs_wf(kernel.allocator_4k_map)) by {
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(hugepage_2m_wf(kernel.page_array)) by {
                    hugepage_2m_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array);
                };
                assert(hugepage_1g_wf(kernel.page_array)) by {
                    hugepage_1g_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array);
                };
                assert(page_pagetable_wf(kernel.pagetable_map, kernel.page_array)) by {
                    page_pagetable_wf_preserved_for_nonmapped_page_change(old(kernel).pagetable_map, kernel.pagetable_map, old(kernel).page_array, kernel.page_array, page_index);
                };
                assert(pagetable_pages_wf(kernel.pagetable_map, kernel.page_array)) by { reveal(pagetable_pages_wf); };
                assert(iommu_table_pages_wf(kernel.iommu_table_map, kernel.page_array)) by {
                    reveal(iommu_table_pages_wf);
                };
                assert(pcid_allocator_pages_wf(
                    kernel.page_array,
                    kernel.pcid_allocator_map,
                )) by {
                    pcid_allocator_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).pcid_allocator_map, kernel.pcid_allocator_map);
                };
                assert(thread_pages_wf(kernel.thread_map, kernel.page_array)) by { thread_pages_wf_preserved_for_page_state_eq(old(kernel).thread_map, kernel.thread_map, old(kernel).page_array, kernel.page_array); };
                assert(thread_staged_pages_4k_wf(kernel.thread_map, kernel.page_array)) by {
                    reveal(thread_staged_pages_4k_wf);
                };
                assert(thread_staged_pages_wf(kernel.thread_map, kernel.page_array)) by {
                    thread_staged_pages_2m_wf_preserved_for_eq(old(kernel).thread_map, kernel.thread_map, old(kernel).page_array, kernel.page_array);
                    thread_staged_pages_1g_wf_preserved_for_eq(old(kernel).thread_map, kernel.thread_map, old(kernel).page_array, kernel.page_array);
                };
                assert(endpoint_pages_wf(kernel.endpoint_map, kernel.page_array)) by { endpoint_pages_wf_preserved_for_page_state_eq(old(kernel).endpoint_map, kernel.endpoint_map, old(kernel).page_array, kernel.page_array); };
                assert(container_allocator_global_free_4k_page_wf(
                    kernel.allocator_4k_map, kernel.page_array,
                )) by {
                    reveal(container_allocator_free_4k_page_wf);
                    reveal(container_allocator_global_free_4k_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                    page_ptr_valid_imply_page_index_valid();
                };
                assert(container_allocator_cpu_cache_free_4k_page_wf(
                    kernel.allocator_4k_map, kernel.page_array,
                )) by {
                    reveal(container_allocator_free_4k_page_wf);
                    reveal(container_allocator_cpu_cache_free_4k_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                    reveal(LinkedList::value_list_unique);
                    seq_skip_lemma::<PagePtr>();
                };
                assert(container_allocator_free_4k_page_wf(
                    kernel.allocator_4k_map, kernel.page_array,
                )) by {
                    reveal(container_allocator_free_4k_page_wf);
                };
                assert(container_allocator_global_free_2m_page_wf(
                    kernel.allocator_2m_map, kernel.page_array,
                )) by {
                    reveal(container_allocator_free_2m_page_wf);
                    reveal(container_allocator_global_free_2m_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(container_allocator_cpu_cache_free_2m_page_wf(
                    kernel.allocator_2m_map, kernel.page_array,
                )) by {
                    reveal(container_allocator_free_2m_page_wf);
                    reveal(container_allocator_cpu_cache_free_2m_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(container_allocator_free_2m_page_wf(
                    kernel.allocator_2m_map, kernel.page_array,
                )) by {
                    reveal(container_allocator_free_2m_page_wf);
                };
                assert(container_allocator_global_free_1g_page_wf(
                    kernel.allocator_1g_map, kernel.page_array,
                )) by {
                    reveal(container_allocator_free_1g_page_wf);
                    reveal(container_allocator_global_free_1g_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(container_allocator_cpu_cache_free_1g_page_wf(
                    kernel.allocator_1g_map, kernel.page_array,
                )) by {
                    reveal(container_allocator_free_1g_page_wf);
                    reveal(container_allocator_cpu_cache_free_1g_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(container_allocator_free_1g_page_wf(
                    kernel.allocator_1g_map, kernel.page_array,
                )) by {
                    reveal(container_allocator_free_1g_page_wf);
                };
            };
            // ---- process_management_inv: container_map, thread_map, etc. all byte-equal ----
            assert(kernel.process_management_inv()) by {
                assert(thread_caller_callee_wf(kernel.thread_map)) by {
                    assert(thread_process_management_fields_unchanged(
                        old(kernel).thread_map, kernel.thread_map,
                    )) by { reveal(thread_perms_wf); };
                    thread_caller_callee_wf_preserved_for_thread_process_management_fields(
                        old(kernel).thread_map, kernel.thread_map,
                    );
                };
                assert(per_container_process_tree_wf(kernel.container_map, kernel.process_map)) by {
                    per_container_process_tree_wf_preserved_for_tree_fields_eq(
                        kernel.container_map, old(kernel).process_map, kernel.process_map,
                    );
                };
                thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(old(kernel).thread_map, kernel.thread_map, kernel.endpoint_map);
                thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(old(kernel).thread_map, kernel.thread_map, kernel.endpoint_map);
                container_thread_endpoint_wf_preserved_for_thread_process_management_fields(kernel.container_map, old(kernel).thread_map, kernel.thread_map, kernel.endpoint_map);
                container_thread_scheduler_wf_preserved_for_thread_process_management_fields(kernel.container_map, old(kernel).thread_map, kernel.thread_map, kernel.scheduler_map);
                container_thread_wf_preserved_for_thread_process_management_fields(kernel.container_map, old(kernel).thread_map, kernel.thread_map);
                process_thread_wf_preserved_for_thread_process_management_fields(kernel.process_map, old(kernel).thread_map, kernel.thread_map);
                thread_cpu_wf_preserved_for_thread_process_management_fields(old(kernel).thread_map, kernel.thread_map, kernel.cpu_array);
            };
            assert(allocator_objects_unlocked_except_cache_pool(
                kernel.allocator_4k_map, alloc_ptr_4k, lctx.thread_id(),
            )) by {
                reveal(allocator_objects_unlocked_except_cache_pool);
            };
        }
        assert(kernel.thread_map.spec_index(thread_ptr).view()
            .stable_allocation_root_equal(
                &old(kernel).thread_map.spec_index(thread_ptr).view(),
            )) by {
            reveal(Thread::stable_allocation_root_equal);
            reveal(thread_perms_wf);
        };
        assert(page_objects_unlocked_except(
            kernel.page_array, lctx.thread_id(), set![page_index],
        )) by {
            reveal(page_objects_unlocked_except);
        };
        (page_ptr, Tracked(page_lock_perm))
    }

    // ================================================================
    // pop_stage_global_4k_page: global-pool twin of pop_stage_4k_page. The
    // allocator's global_pool + the thread are already write-locked and the
    // pool is non-empty. Peek the head, lock the page slot, pop the head,
    // retype it Free4k{GlobalList}→Owned4k, stage it in the thread's
    // temp_alloc_cache_4k, decrement the allocator's total_free_pages. Leaves
    // page + global_pool still write-locked; re-establishes inv().
    // ================================================================
    #[verifier::spinoff_prover]
    pub(super) fn pop_stage_global_4k_page(
        kernel: &mut KernelK,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        container_ptr: RwLockContainerPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(global_pool_lock_perm): Tracked<&LockPerm>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(kernel).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(kernel).container_map.dom().contains(container_ptr),
            old(kernel).container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(kernel).thread_map.dom().contains(thread_ptr),
            old(kernel).thread_map.spec_index(thread_ptr).view().owning_container == container_ptr,
            old(kernel).allocator_4k_map.dom().contains(alloc_ptr_4k),
            global_pool_lock_perm.state() is WriteLock,
            global_pool_lock_perm.thread_id() == old(lctx).thread_id(),
            global_pool_lock_perm.lock_id() == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.locking_thread()->Write_lock_id,
            old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.wlocked_by(old(lctx)),
            old(lctx).lock_id_set().contains((
                old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.lock_id(),
                KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k),
            )),
            old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().view().len() > 0,
            old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().len() > 0,
            old(kernel).thread_map.spec_index(thread_ptr).being_killed() == false,
            thread_effective_quota_4k(old(kernel).thread_map.spec_index(thread_ptr)) >= 1,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(kernel).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(kernel).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
            page_objects_unlocked(
                old(kernel).page_array, old(lctx).thread_id()),
            lock_id_aligned(old(kernel), old(lctx)),
            old(lctx).held_lock_majors_lt(FREE_PAGE_LOCK_MAJOR),
        ensures
            final(kernel).inv(),
            page_ptr_valid(ret.0),
            old(kernel).page_array.spec_index(page_ptr2page_index(ret.0))
                .view().view().state is Free4k,
            !old(kernel).thread_map.spec_index(thread_ptr).view()
                .temp_alloc_cache_4k.view().contains(ret.0),
            final(kernel).allocator_4k_map.dom() == old(kernel).allocator_4k_map.dom(),
            final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).quota
                == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
            forall|p: RwLockPageAllocatorPtr|
                #![trigger final(kernel).allocator_4k_map.spec_index(p)]
                old(kernel).allocator_4k_map.dom().contains(p) && p != alloc_ptr_4k
                ==> final(kernel).allocator_4k_map.spec_index(p)
                    == old(kernel).allocator_4k_map.spec_index(p),
            final(kernel).allocator_2m_map == old(kernel).allocator_2m_map,
            final(kernel).allocator_1g_map == old(kernel).allocator_1g_map,
            final(kernel).page_array.entries_unchanged_except(
                &old(kernel).page_array, page_ptr2page_index(ret.0)),
            // ---- user view unchanged: staging is kernel-internal ----
            kernel_k_to_kernel_u(*final(kernel)) == kernel_k_to_kernel_u(*old(kernel)),
            // ---- global_pool + process lock state preserved, phase still Acquire ----
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            global_pool_lock_perm.lock_id() == final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.locking_thread()->Write_lock_id,
            final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.lock_id()
                == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.lock_id(),
            final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches
                == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches,
            final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.wlocked_by(final(lctx)),
            final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.locked_by_thread(final(lctx).thread_id()),
            final(kernel).thread_map.spec_index(thread_ptr).being_killed() == false,
            final(kernel).thread_map.spec_index(thread_ptr).view().owning_proc
                == old(kernel).thread_map.spec_index(thread_ptr).view().owning_proc,
            final(kernel).thread_map.spec_index(thread_ptr).view().owning_container
                == old(kernel).thread_map.spec_index(thread_ptr).view().owning_container,
            final(kernel).thread_map.spec_index(thread_ptr).view()
                .stable_allocation_root_equal(
                    &old(kernel).thread_map.spec_index(thread_ptr).view(),
                ),
            final(kernel).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                == old(kernel).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr,
            final(kernel).thread_map.unchanged_except(&old(kernel).thread_map, thread_ptr),
            forall|t: RwLockThreadPtr|
                #![trigger old(kernel).thread_map.spec_index(t)]
                #![trigger final(kernel).thread_map.spec_index(t)]
                t != thread_ptr && old(kernel).thread_map.dom().contains(t)
                ==> final(kernel).thread_map.dom().contains(t)
                    && final(kernel).thread_map.lock_id_by_key(t)
                        == old(kernel).thread_map.lock_id_by_key(t),
            forall|t: RwLockThreadPtr|
                #![trigger old(kernel).thread_map.spec_index(t)
                    .locked_by_thread(old(lctx).thread_id())]
                #![trigger final(kernel).thread_map.spec_index(t)
                    .locked_by_thread(final(lctx).thread_id())]
                (old(kernel).thread_map.dom().contains(t)
                    && old(kernel).thread_map.spec_index(t)
                        .locked_by_thread(old(lctx).thread_id()))
                == (final(kernel).thread_map.dom().contains(t)
                    && final(kernel).thread_map.spec_index(t)
                        .locked_by_thread(final(lctx).thread_id())),
            final(kernel).thread_map.spec_index(thread_ptr).wlocked_by(final(lctx)),
            final(kernel).thread_map.spec_index(thread_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            thread_lock_perm.lock_id() == final(kernel).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            final(kernel).thread_map.lock_id_by_key(thread_ptr)
                == old(kernel).thread_map.lock_id_by_key(thread_ptr),
            // ---- page slot left write-locked, perm handed back ----
            index_valid(NUM_PAGES, page_ptr2page_index(ret.0)),
            page_objects_unlocked_except(
                final(kernel).page_array, final(lctx).thread_id(),
                set![page_ptr2page_index(ret.0)]),
            final(kernel).page_array.spec_index(page_ptr2page_index(ret.0)).view().wlocked_by(final(lctx)),
            final(kernel).page_array.spec_index(page_ptr2page_index(ret.0)).view()
                .locked_by_thread(final(lctx).thread_id()),
            final(kernel).page_array.spec_index(page_ptr2page_index(ret.0)).view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(kernel).page_array.spec_index(page_ptr2page_index(ret.0)).view().locking_thread()->Write_lock_id,
            // ---- held-lock set: gained exactly the page slot ----
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert(
                (
                    final(kernel).page_array.lock_id_by_index(page_ptr2page_index(ret.0)),
                    KernelObjId::Page(page_ptr2page_index(ret.0)),
                ),
            ),
            lock_id_aligned(final(kernel), final(lctx)),
            // ---- staging: ret staged Owned4k; 4k cache gained exactly ret, 2m/1g caches + nominal quota untouched ----
            final(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
                =~= old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().insert(ret.0),
            final(kernel).page_array.spec_index(page_ptr2page_index(ret.0)).view().view().state == (PageState::Owned4k{ thread_ptr }),
            final(kernel).page_array.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container
                == container_ptr,
            final(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m
                == old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m,
            final(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g
                == old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            final(kernel).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_fields_equal(
                    &old(kernel).thread_map.spec_index(thread_ptr).view(),
                ),
            final(kernel).thread_map.spec_index(thread_ptr).view().quota_4k
                == old(kernel).thread_map.spec_index(thread_ptr).view().quota_4k,
            final(kernel).thread_map.spec_index(thread_ptr).view().endpoint_descriptors
                == old(kernel).thread_map.spec_index(thread_ptr).view().endpoint_descriptors,
            // ---- container_map + scheduler_map untouched (staging never writes them) ----
            final(kernel).container_map == old(kernel).container_map,
            final(kernel).process_map == old(kernel).process_map,
            final(kernel).pagetable_map == old(kernel).pagetable_map,
            final(kernel).scheduler_map == old(kernel).scheduler_map,
            final(kernel).pcid_allocator_map == old(kernel).pcid_allocator_map,
            final(kernel).endpoint_map == old(kernel).endpoint_map,
            final(kernel).iommu_root_table == old(kernel).iommu_root_table,
            final(kernel).iommu_table_map == old(kernel).iommu_table_map,
            final(kernel).iommu_tlb == old(kernel).iommu_tlb,
            final(kernel).cpu_array == old(kernel).cpu_array,
    {
        assert(
            kernel.allocator_4k_map.perms_wf()
            && kernel.allocator_4k_map.spec_index(alloc_ptr_4k).wf()
            && kernel.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.inv()
            && kernel.thread_map.perms_wf()
            && kernel.page_array.inv()
        ) by {
            reveal(allocator_perms_wf);
            reveal(thread_perms_wf);
            reveal(page_array_wf);
        };
        let poll_ref = kernel.allocator_4k_map.borrow_global_pool(
            alloc_ptr_4k, Tracked(global_pool_lock_perm),
        );
        let (node_addr, page_ptr) = poll_ref.peek_head();
        assert(page_ptr_valid(page_ptr)) by {
            reveal(allocator_perms_wf);
            reveal(allocator_free_page_ptrs_wf);
        };
        let page_index = page_ptr2page_index(page_ptr);
        assert(index_valid(NUM_PAGES, page_index)) by {
            page_ptr_valid_imply_page_index_valid();
        };

        assert(
            old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.view().view().contains(page_ptr)
        ) by {
            reveal(LinkedList::wf_value_list);
        };
        assert({
            &&& kernel.page_array.spec_index(page_index).view().view().state
                == PageState::Free4k {
                allocator_ptr: Ghost(alloc_ptr_4k),
                state: FreePageAllocatorState::GlobalList,
            }
            &&& lctx.lock_id_acyclic(
                kernel.page_array.lock_id_by_index(page_index),
            )
        }) by {
            reveal(container_allocator_free_4k_page_wf);
            reveal(container_allocator_global_free_4k_page_wf);
        };
        // Lock the page slot after deriving its ordering id from the pool head.
        let Tracked(page_lock_perm) = kernel.wlock_page(page_index, Tracked(&mut *lctx));

        // Mutation block: pop + decrement (PageAllocator::inv() re-established by
        // the wrapper), retype Free4k→Owned4k, stage.
        let alloc_mut = kernel.allocator_4k_map.borrow_mut(alloc_ptr_4k);
        let (node_addr2, Tracked(node_perm)) = alloc_mut.pop_global_pool_page(Tracked(&*lctx), Tracked(global_pool_lock_perm));
        assert(node_addr2 == node_addr) by {
            old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.view().linked_list
                .lemma_value_addr_unique(node_addr, node_addr2);
        };
        assert(
            kernel.page_array.inv()
            && kernel.thread_map.perms_wf()
            && kernel.thread_map.spec_index(thread_ptr).is_init()
        ) by {
            reveal(page_array_wf);
            reveal(thread_perms_wf);
        };
        let ghost old_page_lock_id = kernel.page_array.lock_id_by_index(page_index);

        {
            let mut page = kernel.page_array.borrow_mut(page_index, Tracked(&*lctx), Tracked(&page_lock_perm));
            assert(
                page.state == PageState::Free4k {
                    allocator_ptr: Ghost(alloc_ptr_4k),
                    state: FreePageAllocatorState::GlobalList,
                }
                && page.owning_container == container_ptr
            ) by {
                reveal(container_allocator_free_4k_page_wf);
                reveal(container_allocator_global_free_4k_page_wf);
                reveal(container_allocator_wf);
            };
            page.state = PageState::Owned4k { thread_ptr };
            assert(node_addr == page.free_list_node_storage.addr()) by {
                reveal(container_allocator_free_4k_page_wf);
                reveal(container_allocator_global_free_4k_page_wf);
                reveal(LinkedList::wf_map);
            };
            page.free_list_node_storage.put(Tracked(node_perm));

            let thread_mut = kernel.thread_map.borrow_mut(
                thread_ptr, Tracked(&*lctx), Tracked(thread_lock_perm),
            );
            thread_mut.temp_alloc_cache_4k = Ghost(thread_mut.temp_alloc_cache_4k.view().insert(page_ptr));
        }
        proof {
            lctx.enter_kernel_view_release();
            lctx.update_lock_id(
                KernelObjId::Page(page_index),
                old_page_lock_id,
                kernel.page_array.lock_id_by_index(page_index),
            );
            assert(kernel.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.lock_id()
                    == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .global_pool.lock_id()
            ) by {
                reveal(allocator_perms_wf);
            };
            assert(lctx.lock_entry_contains(
                kernel.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.lock_id(),
                KernelObjId::AllocatorGlobalPoll(
                    PageSize::SZ4k, alloc_ptr_4k),
            )) by {
                reveal(lock_id_aligned);
                lock_id_fields_eq_imply_eq();
            };
        }
        // ---- staging delta: page_ptr fresh in temp_alloc_cache_4k ⟹ effective_quota_4k −1 ----
        assert(old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) == false) by {
            reveal(thread_staged_pages_4k_wf);
            if old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) {
                assert(old(kernel).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == PageState::Owned4k { thread_ptr }) by {
                    reveal(thread_staged_pages_4k_wf);
                };
            }
        };
        proof {
            // ---- user view unchanged: only page_array / temp_alloc / total moved ----
            assert(kernel_k_to_kernel_u(*kernel) == kernel_k_to_kernel_u(*old(kernel))) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(kernel), kernel);
            };
        }
        proof {
            assert(
                thread_quota_2m_fields_unchanged(old(kernel).thread_map, kernel.thread_map)
                && thread_quota_1g_fields_unchanged(old(kernel).thread_map, kernel.thread_map)
            ) by {
                reveal(thread_quota_2m_fields_unchanged);
                reveal(thread_quota_1g_fields_unchanged);
            };
            // ---- subsystems_inv ----
            assert(kernel.subsystems_inv()) by {
                reveal(KernelK::default_pagetable_wf);
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(container_tree_fields_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
                reveal(thread_temp_alloc_empty_unless_wlocked);
                reveal(page_array_wf);
                reveal(thread_perms_wf);
                reveal(thread_free_quota_pending_empty_unless_wlocked);
            };
            // ---- memory_management_inv ----
            assert(kernel.memory_management_inv()) by {
                assert(allocator_pages_wf(kernel.page_array, kernel.allocator_4k_map, kernel.allocator_2m_map, kernel.allocator_1g_map)) by {
                    allocator_4k_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).allocator_4k_map, kernel.allocator_4k_map);
                    allocator_2m_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).allocator_2m_map, kernel.allocator_2m_map);
                    allocator_1g_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).allocator_1g_map, kernel.allocator_1g_map);
                };
                assert(container_page_owner_wf(kernel.container_map, kernel.page_array)) by { container_page_owner_wf_preserved_for_owning_container_eq(old(kernel).container_map, kernel.container_map, old(kernel).page_array, kernel.page_array); };
                assert(container_process_page_pagetable_wf(kernel.container_map, kernel.process_map, kernel.pagetable_map, kernel.page_array)) by {
                    reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                    reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                };
                assert(container_pages_wf(kernel.page_array, kernel.container_map)) by { container_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).container_map, kernel.container_map); };
                assert(process_pages_wf(kernel.page_array, kernel.process_map)) by { process_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).process_map, kernel.process_map); };
                assert(container_process_allocator_quota_4k_wf(kernel.container_map, kernel.process_map, kernel.thread_map, kernel.allocator_4k_map)) by {
                    reveal(container_process_allocator_quota_4k_wf);
                    reveal(container_process_wf);
                    reveal(container_thread_wf);
                    reveal(container_allocator_wf);
                    lemma_thread_effective_quota_4k_fold_change_by_forall(thread_ptr, -1);
                    assert forall|c_ptr: RwLockContainerPtr|
                        #![trigger
                            thread_effective_quota_4k_fold_sum(
                                kernel.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                                kernel.thread_map,
                            ),
                            thread_effective_quota_4k_fold_sum(
                                kernel.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                                old(kernel).thread_map,
                            )
                        ]
                        (kernel.container_map.dom().contains(c_ptr)
                        && (forall|t: RwLockThreadPtr|
                            #![trigger thread_effective_quota_4k(old(kernel).thread_map.spec_index(t))]
                            kernel.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().contains(t)
                                ==> {
                                    &&& kernel.thread_map.dom().contains(t)
                                    &&& old(kernel).thread_map.dom().contains(t)
                                    &&& thread_effective_quota_4k(kernel.thread_map.spec_index(t))
                                        == thread_effective_quota_4k(old(kernel).thread_map.spec_index(t))
                                }))
                        implies thread_effective_quota_4k_fold_sum(
                            kernel.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                            kernel.thread_map,
                        ) == thread_effective_quota_4k_fold_sum(
                            kernel.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                            old(kernel).thread_map,
                        ) by {
                        lemma_thread_effective_quota_4k_fold_sum_eq(
                            kernel.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                            old(kernel).thread_map,
                            kernel.thread_map,
                        );
                    };
                    lemma_thread_pending_4k_folds_eq_forall(
                        kernel.container_map,
                        old(kernel).thread_map,
                        kernel.thread_map,
                    );
                    lemma_process_effective_quota_4k_fold_sum_eq_forall();
                };
                assert(container_process_allocator_quota_2m_wf(kernel.container_map, kernel.process_map, kernel.thread_map, kernel.allocator_2m_map)) by {
                    container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields_forall();
                };
                assert(container_process_allocator_quota_1g_wf(kernel.container_map, kernel.process_map, kernel.thread_map, kernel.allocator_1g_map)) by {
                    container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields_forall();
                };
                assert(container_allocator_wf(kernel.container_map, kernel.allocator_4k_map, kernel.allocator_2m_map, kernel.allocator_1g_map)) by {
                    reveal(container_allocator_wf);
                };
                assert(allocator_free_page_ptrs_wf(kernel.allocator_4k_map)) by {
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(hugepage_2m_wf(kernel.page_array)) by {
                    hugepage_2m_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array);
                };
                assert(hugepage_1g_wf(kernel.page_array)) by {
                    hugepage_1g_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array);
                };
                assert(page_pagetable_wf(kernel.pagetable_map, kernel.page_array)) by {
                    page_pagetable_wf_preserved_for_nonmapped_page_change(old(kernel).pagetable_map, kernel.pagetable_map, old(kernel).page_array, kernel.page_array, page_index);
                };
                assert(pagetable_pages_wf(kernel.pagetable_map, kernel.page_array)) by { reveal(pagetable_pages_wf); };
                assert(iommu_table_pages_wf(kernel.iommu_table_map, kernel.page_array)) by {
                    reveal(iommu_table_pages_wf);
                };
                assert(pcid_allocator_pages_wf(
                    kernel.page_array,
                    kernel.pcid_allocator_map,
                )) by {
                    pcid_allocator_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).pcid_allocator_map, kernel.pcid_allocator_map);
                };
                assert(thread_pages_wf(kernel.thread_map, kernel.page_array)) by { thread_pages_wf_preserved_for_page_state_eq(old(kernel).thread_map, kernel.thread_map, old(kernel).page_array, kernel.page_array); };
                assert(thread_staged_pages_4k_wf(kernel.thread_map, kernel.page_array)) by {
                    reveal(thread_staged_pages_4k_wf);
                };
                assert(thread_staged_pages_wf(kernel.thread_map, kernel.page_array)) by {
                    thread_staged_pages_2m_wf_preserved_for_eq(old(kernel).thread_map, kernel.thread_map, old(kernel).page_array, kernel.page_array);
                    thread_staged_pages_1g_wf_preserved_for_eq(old(kernel).thread_map, kernel.thread_map, old(kernel).page_array, kernel.page_array);
                };
                assert(endpoint_pages_wf(kernel.endpoint_map, kernel.page_array)) by { endpoint_pages_wf_preserved_for_page_state_eq(old(kernel).endpoint_map, kernel.endpoint_map, old(kernel).page_array, kernel.page_array); };
                assert(container_allocator_global_free_4k_page_wf(
                    kernel.allocator_4k_map, kernel.page_array,
                )) by {
                    reveal(container_allocator_free_4k_page_wf);
                    reveal(container_allocator_global_free_4k_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                    reveal(LinkedList::value_list_unique);
                    seq_skip_lemma::<PagePtr>();
                };
                assert(container_allocator_cpu_cache_free_4k_page_wf(
                    kernel.allocator_4k_map, kernel.page_array,
                )) by {
                    reveal(container_allocator_free_4k_page_wf);
                    reveal(container_allocator_global_free_4k_page_wf);
                    reveal(container_allocator_cpu_cache_free_4k_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                    page_ptr_valid_imply_page_index_valid();
                    page_ptr2page_index_injective();
                };
                assert(container_allocator_free_4k_page_wf(
                    kernel.allocator_4k_map, kernel.page_array,
                )) by {
                    reveal(container_allocator_free_4k_page_wf);
                };
                assert(container_allocator_global_free_2m_page_wf(
                    kernel.allocator_2m_map, kernel.page_array,
                )) by {
                    reveal(container_allocator_free_2m_page_wf);
                    reveal(container_allocator_global_free_2m_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(container_allocator_cpu_cache_free_2m_page_wf(
                    kernel.allocator_2m_map, kernel.page_array,
                )) by {
                    reveal(container_allocator_free_2m_page_wf);
                    reveal(container_allocator_cpu_cache_free_2m_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(container_allocator_free_2m_page_wf(
                    kernel.allocator_2m_map, kernel.page_array,
                )) by {
                    reveal(container_allocator_free_2m_page_wf);
                };
                assert(container_allocator_global_free_1g_page_wf(
                    kernel.allocator_1g_map, kernel.page_array,
                )) by {
                    reveal(container_allocator_free_1g_page_wf);
                    reveal(container_allocator_global_free_1g_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(container_allocator_cpu_cache_free_1g_page_wf(
                    kernel.allocator_1g_map, kernel.page_array,
                )) by {
                    reveal(container_allocator_free_1g_page_wf);
                    reveal(container_allocator_cpu_cache_free_1g_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(container_allocator_free_1g_page_wf(
                    kernel.allocator_1g_map, kernel.page_array,
                )) by {
                    reveal(container_allocator_free_1g_page_wf);
                };
            };
            // ---- process_management_inv: container_map, thread_map, etc. all byte-equal ----
            assert(kernel.process_management_inv()) by {
                assert(thread_caller_callee_wf(kernel.thread_map)) by {
                    assert(thread_process_management_fields_unchanged(
                        old(kernel).thread_map, kernel.thread_map,
                    )) by { reveal(thread_perms_wf); };
                    thread_caller_callee_wf_preserved_for_thread_process_management_fields(
                        old(kernel).thread_map, kernel.thread_map,
                    );
                };
                assert(per_container_process_tree_wf(kernel.container_map, kernel.process_map)) by {
                    per_container_process_tree_wf_preserved_for_tree_fields_eq(kernel.container_map, old(kernel).process_map, kernel.process_map);
                };
                assert(process_cpu_wf(kernel.process_map, kernel.cpu_array)) by {
                    reveal(process_cpu_wf);
                };
                thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(old(kernel).thread_map, kernel.thread_map, kernel.endpoint_map);
                thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(old(kernel).thread_map, kernel.thread_map, kernel.endpoint_map);
                container_thread_endpoint_wf_preserved_for_thread_process_management_fields(kernel.container_map, old(kernel).thread_map, kernel.thread_map, kernel.endpoint_map);
                container_thread_scheduler_wf_preserved_for_thread_process_management_fields(kernel.container_map, old(kernel).thread_map, kernel.thread_map, kernel.scheduler_map);
                container_thread_wf_preserved_for_thread_process_management_fields(kernel.container_map, old(kernel).thread_map, kernel.thread_map);
                process_thread_wf_preserved_for_thread_process_management_fields(kernel.process_map, old(kernel).thread_map, kernel.thread_map);
                thread_cpu_wf_preserved_for_thread_process_management_fields(old(kernel).thread_map, kernel.thread_map, kernel.cpu_array);
            };
        }
        assert(kernel.thread_map.spec_index(thread_ptr).view()
            .stable_allocation_root_equal(
                &old(kernel).thread_map.spec_index(thread_ptr).view(),
            )) by {
            reveal(Thread::stable_allocation_root_equal);
            reveal(thread_perms_wf);
        };
        assert(page_objects_unlocked_except(
            kernel.page_array, lctx.thread_id(), set![page_index],
        )) by {
            reveal(page_objects_unlocked_except);
        };
        assert(lock_id_aligned(kernel, &*lctx)) by {
            reveal(lock_id_aligned);
        };
        (page_ptr, Tracked(page_lock_perm))
    }



} // verus!
