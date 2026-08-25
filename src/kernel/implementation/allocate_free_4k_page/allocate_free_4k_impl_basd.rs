use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal};
use crate::*;
use super::allocate_free_4k_page_pop_impl::{pop_stage_4k_page, pop_stage_global_4k_page};

verus! {





    // ================================================================
    // Main allocate function
    // ================================================================

    /// Allocate a single 4k page from the container's allocator.
    /// Caller holds the allocating thread's write-lock.
    #[verifier::spinoff_prover]
    pub fn allocate_free_4k_page(
        kernel: &mut KernelK,
        thread_ptr: RwLockThreadPtr,
        container_ptr: RwLockContainerPtr,
        cpu_id: CpuId,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(kernel).inv(),
            index_valid(NUM_CPUS, cpu_id),
            old(kernel).thread_map.dom().contains(thread_ptr),
            old(kernel).thread_map.spec_index(thread_ptr).view().owning_container == container_ptr,
            old(kernel).thread_map.spec_index(thread_ptr).being_killed() == false,
            // Thread write-lock perm, needed to mutate the thread payload
            // (insert the freshly-allocated page into `temp_alloc_cache_4k`).
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(kernel).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
            thread_effective_quota_4k(old(kernel).thread_map.spec_index(thread_ptr)) >= 1,
            old(kernel).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
            page_objects_unlocked(
                old(kernel).page_array, old(lctx).thread_id()),
            allocator_objects_unlocked(
                old(kernel).allocator_4k_map, old(lctx).thread_id()),
            lock_id_aligned(old(kernel), old(lctx)),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        ensures
            final(kernel).inv(),
            // ---- held thread: not killed, perm still matches ----
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
            thread_lock_perm.lock_id() == final(kernel).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            final(kernel).thread_map.lock_id_by_key(thread_ptr)
                == old(kernel).thread_map.lock_id_by_key(thread_ptr),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            lock_id_aligned(final(kernel), final(lctx)),
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
            forall|t: RwLockThreadPtr|
                #![trigger old(kernel).thread_map.spec_index(t)]
                #![trigger final(kernel).thread_map.spec_index(t)]
                t != thread_ptr
                    && old(kernel).thread_map.dom().contains(t)
                    && old(kernel).thread_map.spec_index(t)
                        .locked_by_thread(old(lctx).thread_id())
                ==> final(kernel).thread_map.dom().contains(t)
                    && final(kernel).thread_map.spec_index(t)
                        == old(kernel).thread_map.spec_index(t)
                    && final(kernel).thread_map.lock_id_by_key(t)
                        == old(kernel).thread_map.lock_id_by_key(t),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
            page_ptr_valid(ret.0),
            // ---- page slot left write-locked, perm handed back (rides across the boundary as a held object) ----
            final(kernel).page_array.spec_index(page_ptr2page_index(ret.0)).view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(kernel).page_array.spec_index(page_ptr2page_index(ret.0)).view().locking_thread()->Write_lock_id,
            final(kernel).page_array.spec_index(page_ptr2page_index(ret.0)).view()
                .wlocked_by(final(lctx)),
            page_objects_unlocked_except(
                final(kernel).page_array, final(lctx).thread_id(),
                set![page_ptr2page_index(ret.0)]),
            final(kernel).thread_map.dom().contains(thread_ptr),
            final(kernel).thread_map.spec_index(thread_ptr).wlocked_by(final(lctx)),
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((
                final(kernel).page_array.lock_id_by_index(page_ptr2page_index(ret.0)),
                KernelObjId::Page(page_ptr2page_index(ret.0)),
            )),
            held_containers_unchanged(
                old(kernel).container_map, final(kernel).container_map, old(lctx)),
            final(kernel).container_map.dom().contains(container_ptr),
            final(kernel).container_map.spec_index(container_ptr).view_rodata()
                == old(kernel).container_map.spec_index(container_ptr).view_rodata(),
            held_processes_unchanged(
                old(kernel).process_map, final(kernel).process_map, old(lctx)),
            held_endpoints_unchanged(
                old(kernel).endpoint_map, final(kernel).endpoint_map, old(lctx)),
            held_schedulers_unchanged(
                old(kernel).scheduler_map, final(kernel).scheduler_map, old(lctx)),
            held_pcid_allocators_unchanged(
                old(kernel).pcid_allocator_map, final(kernel).pcid_allocator_map,
                old(lctx)),
            held_pagetables_unchanged(
                old(kernel).pagetable_map, final(kernel).pagetable_map, old(lctx)),
            held_iommu_tables_unchanged(
                old(kernel).iommu_table_map, final(kernel).iommu_table_map, old(lctx)),
            held_cpus_unchanged(
                old(kernel).cpu_array, final(kernel).cpu_array, old(lctx)),
            allocator_objects_unlocked(
                old(kernel).allocator_2m_map, old(lctx).thread_id(),
            ) ==> allocator_objects_unlocked(
                final(kernel).allocator_2m_map, final(lctx).thread_id(),
            ),
            allocator_objects_unlocked(
                old(kernel).allocator_1g_map, old(lctx).thread_id(),
            ) ==> allocator_objects_unlocked(
                final(kernel).allocator_1g_map, final(lctx).thread_id(),
            ),
            allocator_objects_unlocked(
                final(kernel).allocator_4k_map, final(lctx).thread_id()),
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
            final(kernel).thread_map.spec_index(thread_ptr).view().quota_4k
                == old(kernel).thread_map.spec_index(thread_ptr).view().quota_4k,
            final(kernel).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_fields_equal(
                    &old(kernel).thread_map.spec_index(thread_ptr).view(),
                ),
            final(kernel).thread_map.spec_index(thread_ptr).view().endpoint_descriptors
                == old(kernel).thread_map.spec_index(thread_ptr).view().endpoint_descriptors,
    {
        assert(kernel.container_map.perms_wf()
            && kernel.container_map.dom().contains(container_ptr)) by {
            reveal(container_perms_wf);
            reveal(container_thread_wf);
        };
        let alloc_ptr_4k = kernel.container_map
            .borrow_rodata(container_ptr).borrow().allocator_ptr_4k;
        assert(kernel.allocator_4k_map.dom().contains(alloc_ptr_4k)) by {
            reveal(container_allocator_wf);
        };
        assert(kernel.allocator_4k_map.spec_index(alloc_ptr_4k).wf()) by {
            reveal(allocator_perms_wf);
        };
        // Fast path: lock the running cpu's cache.
        let Tracked(cache_lock_perm) = kernel.wlock_allocator_cache(
            alloc_ptr_4k, cpu_id, Tracked(&mut *lctx),
        );
        proof {
            assert(allocator_objects_unlocked_except_cache_pool(
                kernel.allocator_4k_map, alloc_ptr_4k, lctx.thread_id(),
            )) by {
                reveal(allocator_objects_unlocked_except_cache_pool);
            };
        }

        // Read the cache length via a shared borrow (preserves wf() for the slow path).
        let cache_ref = kernel.allocator_4k_map.borrow_cache(
            alloc_ptr_4k, cpu_id, Tracked(&cache_lock_perm),
        );
        let cache_len = cache_ref.linked_list.len();

        if cache_len > 0 {
            let (page_ptr, Tracked(page_lock_perm)) = pop_stage_4k_page(kernel,
                alloc_ptr_4k, cpu_id, thread_ptr, container_ptr,
                Tracked(&mut *lctx), Tracked(&cache_lock_perm), Tracked(thread_lock_perm),
            );
            kernel.wunlock_allocator_cache(
                alloc_ptr_4k, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm),
            );
            proof {
                assert(allocator_objects_unlocked(
                    kernel.allocator_4k_map, lctx.thread_id(),
                )) by {
                    reveal(allocator_objects_unlocked_except_cache_pool);
                };
                kernel.kernel_step_boundary(&mut *lctx, &mut *steps);
                assert(kernel.container_map.dom().contains(container_ptr)) by {
                    reveal(container_thread_wf);
                };
            }
            return (page_ptr, Tracked(page_lock_perm));
        }

        let Tracked(gp_lock_perm) = kernel.wlock_allocator_global_pool(
            alloc_ptr_4k, Tracked(&mut *lctx),
        );
        proof {
            assert(allocator_objects_unlocked_except_cache_pool(
                kernel.allocator_4k_map, alloc_ptr_4k, lctx.thread_id(),
            )) by {
                reveal(allocator_objects_unlocked_except_cache_pool);
            };
        }
        assert(kernel.allocator_4k_map.perms_wf()) by {
            reveal(allocator_perms_wf);
        };
        let pool_ref = kernel.allocator_4k_map.borrow_global_pool(
            alloc_ptr_4k, Tracked(&gp_lock_perm),
        );
        let pool_len = pool_ref.len();

        if pool_len > 0 {
            let (page_ptr, Tracked(page_lock_perm)) = pop_stage_global_4k_page(kernel,
                alloc_ptr_4k, thread_ptr, container_ptr,
                Tracked(&mut *lctx), Tracked(&gp_lock_perm), Tracked(thread_lock_perm),
            );
            kernel.wunlock_allocator_global_pool(
                alloc_ptr_4k, Tracked(&mut *lctx), Tracked(gp_lock_perm),
            );
            kernel.wunlock_allocator_cache(
                alloc_ptr_4k, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm),
            );
            proof {
                assert(allocator_objects_unlocked(
                    kernel.allocator_4k_map, lctx.thread_id(),
                )) by {
                    reveal(allocator_objects_unlocked_except_cache_pool);
                };
                kernel.kernel_step_boundary(&mut *lctx, &mut *steps);
                assert(kernel.container_map.dom().contains(container_ptr)) by {
                    reveal(container_thread_wf);
                };
            }
            return (page_ptr, Tracked(page_lock_perm));
        }

        kernel.wunlock_allocator_global_pool(
            alloc_ptr_4k, Tracked(&mut *lctx), Tracked(gp_lock_perm),
        );
        kernel.wunlock_allocator_cache(
            alloc_ptr_4k, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm),
        );
            proof {
                assert(kernel_k_to_kernel_u(*kernel) == kernel_k_to_kernel_u(*old(kernel))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(kernel), kernel);
                };
                kernel.kernel_step_boundary(&mut *lctx, &mut *steps);
                assert(kernel.container_map.dom().contains(container_ptr)) by {
                    reveal(container_thread_wf);
                };
        }
        alloc_4k_scan_all_caches_and_pool(kernel,
            thread_ptr, container_ptr,
            Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm),
        )
    }

    // ================================================================
    // Case 3: scan all caches + global pool after an internal boundary.
    // ================================================================

    fn alloc_4k_scan_all_caches_and_pool(
        kernel: &mut KernelK,
        thread_ptr: RwLockThreadPtr,
        container_ptr: RwLockContainerPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(kernel).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(kernel).thread_map.dom().contains(thread_ptr),
            old(kernel).thread_map.spec_index(thread_ptr).being_killed() == false,
            old(kernel).thread_map.spec_index(thread_ptr).view().owning_container
                == container_ptr,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(kernel).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(kernel).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
            page_objects_unlocked(
                old(kernel).page_array, old(lctx).thread_id()),
            allocator_objects_unlocked(
                old(kernel).allocator_4k_map, old(lctx).thread_id()),
            lock_id_aligned(old(kernel), old(lctx)),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
            thread_effective_quota_4k(old(kernel).thread_map.spec_index(thread_ptr)) >= 1,
            old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        ensures
            final(kernel).inv(),
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
            thread_lock_perm.lock_id() == final(kernel).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            final(kernel).thread_map.lock_id_by_key(thread_ptr)
                == old(kernel).thread_map.lock_id_by_key(thread_ptr),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            lock_id_aligned(final(kernel), final(lctx)),
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
            forall|t: RwLockThreadPtr|
                #![trigger old(kernel).thread_map.spec_index(t)]
                #![trigger final(kernel).thread_map.spec_index(t)]
                t != thread_ptr
                    && old(kernel).thread_map.dom().contains(t)
                    && old(kernel).thread_map.spec_index(t)
                        .locked_by_thread(old(lctx).thread_id())
                ==> final(kernel).thread_map.dom().contains(t)
                    && final(kernel).thread_map.spec_index(t)
                        == old(kernel).thread_map.spec_index(t)
                    && final(kernel).thread_map.lock_id_by_key(t)
                        == old(kernel).thread_map.lock_id_by_key(t),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
            page_ptr_valid(ret.0),
            final(kernel).page_array.spec_index(page_ptr2page_index(ret.0)).view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(kernel).page_array.spec_index(page_ptr2page_index(ret.0)).view().locking_thread()->Write_lock_id,
            final(kernel).page_array.spec_index(page_ptr2page_index(ret.0)).view()
                .wlocked_by(final(lctx)),
            page_objects_unlocked_except(
                final(kernel).page_array, final(lctx).thread_id(),
                set![page_ptr2page_index(ret.0)]),
            final(kernel).thread_map.dom().contains(thread_ptr),
            final(kernel).thread_map.spec_index(thread_ptr).wlocked_by(final(lctx)),
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((
                final(kernel).page_array.lock_id_by_index(page_ptr2page_index(ret.0)),
                KernelObjId::Page(page_ptr2page_index(ret.0)),
            )),
            held_containers_unchanged(
                old(kernel).container_map, final(kernel).container_map, old(lctx)),
            final(kernel).container_map.dom().contains(container_ptr),
            final(kernel).container_map.spec_index(container_ptr).view_rodata()
                == old(kernel).container_map.spec_index(container_ptr).view_rodata(),
            held_processes_unchanged(
                old(kernel).process_map, final(kernel).process_map, old(lctx)),
            held_endpoints_unchanged(
                old(kernel).endpoint_map, final(kernel).endpoint_map, old(lctx)),
            held_schedulers_unchanged(
                old(kernel).scheduler_map, final(kernel).scheduler_map, old(lctx)),
            held_pcid_allocators_unchanged(
                old(kernel).pcid_allocator_map, final(kernel).pcid_allocator_map,
                old(lctx)),
            held_pagetables_unchanged(
                old(kernel).pagetable_map, final(kernel).pagetable_map, old(lctx)),
            held_iommu_tables_unchanged(
                old(kernel).iommu_table_map, final(kernel).iommu_table_map, old(lctx)),
            held_cpus_unchanged(
                old(kernel).cpu_array, final(kernel).cpu_array, old(lctx)),
            allocator_objects_unlocked(
                old(kernel).allocator_2m_map, old(lctx).thread_id(),
            ) ==> allocator_objects_unlocked(
                final(kernel).allocator_2m_map, final(lctx).thread_id(),
            ),
            allocator_objects_unlocked(
                old(kernel).allocator_1g_map, old(lctx).thread_id(),
            ) ==> allocator_objects_unlocked(
                final(kernel).allocator_1g_map, final(lctx).thread_id(),
            ),
            allocator_objects_unlocked(
                final(kernel).allocator_4k_map, final(lctx).thread_id()),
            final(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
                =~= old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().insert(ret.0),
            final(kernel).page_array.spec_index(page_ptr2page_index(ret.0)).view().view().state == (PageState::Owned4k{ thread_ptr }),
            final(kernel).page_array.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container
                == container_ptr,
            final(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m
                == old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m,
            final(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g
                == old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            final(kernel).thread_map.spec_index(thread_ptr).view().quota_4k
                == old(kernel).thread_map.spec_index(thread_ptr).view().quota_4k,
            final(kernel).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_fields_equal(
                    &old(kernel).thread_map.spec_index(thread_ptr).view(),
                ),
            final(kernel).thread_map.spec_index(thread_ptr).view().endpoint_descriptors
                == old(kernel).thread_map.spec_index(thread_ptr).view().endpoint_descriptors,
    {
        assert(kernel.container_map.perms_wf()
            && kernel.container_map.dom().contains(container_ptr)) by {
            reveal(container_perms_wf);
            reveal(container_thread_wf);
        };
        let alloc_ptr_4k = kernel.container_map
            .borrow_rodata(container_ptr).borrow().allocator_ptr_4k;
        assert(kernel.allocator_4k_map.dom().contains(alloc_ptr_4k)) by {
            reveal(container_allocator_wf);
        };
        let (cache_perms, pool_perm) = wlock_all_caches_and_global_pool(kernel,
            alloc_ptr_4k, thread_ptr, Tracked(&mut *lctx),
        );

        let tracked cache_perms_ref = cache_perms.borrow();
        let (found, slot) = scan_caches_and_alloc(kernel,
            alloc_ptr_4k, thread_ptr, container_ptr,
            Tracked(&mut *lctx), Tracked(cache_perms_ref), Tracked(thread_lock_perm),
        );

        if found {
            // A cache held a free page: it is popped + staged, page slot held.
            // Release the page, every cache, then the pool, and close the step.
            let (_scan_cpu, page_ptr, Tracked(page_lock_perm)) = slot.unwrap();
            // Keep the page slot write-locked so it rides across the boundary as
            // a held object (its state is pinned); release the caches + pool.
            wunlock_all_caches(kernel,
                alloc_ptr_4k, thread_ptr,
                page_ptr2page_index(page_ptr),
                Tracked(&mut *lctx), Tracked(cache_perms.get()),
            );
            kernel.wunlock_allocator_global_pool(alloc_ptr_4k, Tracked(&mut *lctx), Tracked(pool_perm.get()));

            proof {
                assert(allocator_objects_unlocked(
                    kernel.allocator_4k_map, lctx.thread_id(),
                )) by {
                    reveal(allocator_objects_unlocked_except_cache_pool);
                    reveal(allocator_caches_unlocked);
                };
                kernel.kernel_step_boundary(&mut *lctx, &mut *steps);
                assert(kernel.container_map.dom().contains(container_ptr)) by {
                    reveal(container_thread_wf);
                };
            }
            return (page_ptr, Tracked(page_lock_perm));
        }

        // Every cache was empty. By conservation the free pages must sit in the
        // global pool: total_free_pages == pool.len() + Σ cache.len(), the caches
        // are all empty, and the held thread still has effective_quota_4k >= 1,
        // so total_free_pages >= 1 and hence pool.len() >= 1.
        assert(kernel.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().len() > 0) by {
            assert(kernel.container_map.spec_index(container_ptr).view_user_ghost()
                .owned_threads.view().contains(thread_ptr)) by {
                reveal(container_thread_wf);
            };
            lemma_scan_fail_pool_nonempty(kernel, container_ptr, alloc_ptr_4k, thread_ptr);
            reveal(allocator_perms_wf);
            kernel.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().lemma_len_view();
        };
        let (page_ptr, Tracked(page_lock_perm)) = pop_stage_global_4k_page(kernel,
            alloc_ptr_4k, thread_ptr, container_ptr,
            Tracked(&mut *lctx), Tracked(pool_perm.borrow()), Tracked(thread_lock_perm),
        );
        // Keep the page slot write-locked so it rides across the boundary as a
        // held object (its state is pinned); release the caches + pool.
        let tracked cache_perms_ref = cache_perms.borrow();
        assert(cache_perms_match_lctx(
            kernel.allocator_4k_map, alloc_ptr_4k, &*lctx,
            cache_perms_ref,
        )) by {
            reveal(cache_perms_match_lctx);
        };
        assert(allocator_objects_unlocked_except_cache_pool(
            kernel.allocator_4k_map, alloc_ptr_4k, lctx.thread_id(),
        )) by {
            reveal(allocator_objects_unlocked_except_cache_pool);
        };
        wunlock_all_caches(kernel,
            alloc_ptr_4k, thread_ptr,
            page_ptr2page_index(page_ptr),
            Tracked(&mut *lctx), Tracked(cache_perms.get()),
        );
        kernel.wunlock_allocator_global_pool(alloc_ptr_4k, Tracked(&mut *lctx), Tracked(pool_perm.get()));

        proof {
            assert(allocator_objects_unlocked(
                kernel.allocator_4k_map, lctx.thread_id(),
            )) by {
                reveal(allocator_objects_unlocked_except_cache_pool);
                reveal(allocator_caches_unlocked);
            };
            kernel.kernel_step_boundary(&mut *lctx, &mut *steps);
            assert(kernel.container_map.dom().contains(container_ptr)) by {
                reveal(container_thread_wf);
            };
        }
        (page_ptr, Tracked(page_lock_perm))
    }
    // ================================================================
    // wlock_all_caches_and_global_pool: acquire every cpu cache (cpu 0..NUM_CPUS,
    // ascending) then the global pool of `alloc_ptr_4k`. Entry state holds no
    // allocator cache/pool of this allocator, and every held lock id sits at or
    // below ALLOCATOR_CACHE_MAJOR — so each cache (ordered by minor, ascending)
    // and then the pool top every prior id, keeping the acquisition
    // acyclic. Returns the per-cpu cache perms (keyed by cpu) + the pool perm;
    // each wrapper re-establishes inv() internally.
    // ================================================================
    pub(crate) closed spec fn allocator_cache_lock_id(cache_cpu: CpuId) -> LockId {
        LockId {
            container: LockOwnerId::NotApp,
            process: LockOwnerId::NotApp,
            major: ALLOCATOR_CACHE_MAJOR,
            minor: cache_cpu,
        }
    }

    #[verifier::opaque]
    pub(crate) open spec fn allocator_objects_unlocked_except_cache_pool(
        alloc_map: PageAllocatorUnLockedMap,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_id: LockThreadId,
    ) -> bool {
        &&& forall|p: RwLockPageAllocatorPtr|
            #![trigger alloc_map.spec_index(p).quota]
            alloc_map.dom().contains(p)
            ==> !alloc_map.spec_index(p).quota.locked_by_thread(thread_id)
        &&& forall|p: RwLockPageAllocatorPtr|
            #![trigger alloc_map.spec_index(p).global_pool]
            alloc_map.dom().contains(p) && p != alloc_ptr_4k
            ==> !alloc_map.spec_index(p).global_pool.locked_by_thread(thread_id)
        &&& forall|p: RwLockPageAllocatorPtr, c: CpuId|
            #![trigger alloc_map.spec_index(p).cpu_caches.spec_index(c)]
            alloc_map.dom().contains(p) && p != alloc_ptr_4k && index_valid(NUM_CPUS, c)
            ==> !alloc_map.spec_index(p).cpu_caches.spec_index(c).view()
                .locked_by_thread(thread_id)
    }

    #[verifier::opaque]
    pub(crate) open spec fn allocator_caches_unlocked(
        alloc_map: PageAllocatorUnLockedMap,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
    ) -> bool {
        forall|c: CpuId|
            #![trigger alloc_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(c)]
            index_valid(NUM_CPUS, c)
            ==> !alloc_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(c).view().locked()
    }

    spec fn allocator_cache_lock_entry_prefix_seq(
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        upper: CpuId,
    ) -> Seq<HeldLock> {
        Seq::new(upper as nat, |i: int| (
            allocator_cache_lock_id(i as CpuId),
            KernelObjId::AllocatorCache(
                PageSize::SZ4k, alloc_ptr_4k, i as CpuId),
        ))
    }

    pub(crate) closed spec fn allocator_cache_lock_entry_prefix(
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        upper: CpuId,
    ) -> Set<HeldLock> {
        allocator_cache_lock_entry_prefix_seq(alloc_ptr_4k, upper).to_set()
    }

    pub(crate) fn wlock_all_caches_and_global_pool(
        kernel: &mut KernelK,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
    ) -> (ret: (Tracked<Map<CpuId, LockPerm>>, Tracked<LockPerm>))
        requires
            old(kernel).inv(),
            old(kernel).allocator_4k_map.dom().contains(alloc_ptr_4k),
            old(kernel).thread_map.dom().contains(thread_ptr),
            old(kernel).thread_map.spec_index(thread_ptr)
                .locked_by_thread(old(lctx).thread_id()),
            old(lctx).kernel_view_locking_state() is Acquire,
            lock_id_aligned(old(kernel), old(lctx)),
            allocator_objects_unlocked(
                old(kernel).allocator_4k_map, old(lctx).thread_id()),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        ensures
            final(kernel).inv(),
            final(kernel).thread_map.spec_index(thread_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            kernel_k_to_kernel_u(*final(kernel)) == kernel_k_to_kernel_u(*old(kernel)),
            // ---- only allocator_4k_map lock state moves; every other field byte-equal ----
            final(kernel).pagetable_map     == old(kernel).pagetable_map,
            final(kernel).iommu_table_map     == old(kernel).iommu_table_map,
            final(kernel).iommu_root_table     == old(kernel).iommu_root_table,
            final(kernel).page_array        == old(kernel).page_array,
            final(kernel).cpu_array         == old(kernel).cpu_array,
            final(kernel).cpu_tlb           == old(kernel).cpu_tlb,
            final(kernel).iommu_tlb           == old(kernel).iommu_tlb,
            final(kernel).root_container    == old(kernel).root_container,
            final(kernel).container_map     == old(kernel).container_map,
            final(kernel).scheduler_map     == old(kernel).scheduler_map,
            final(kernel).pcid_allocator_map == old(kernel).pcid_allocator_map,
            final(kernel).process_map       == old(kernel).process_map,
            final(kernel).thread_map        == old(kernel).thread_map,
            final(kernel).endpoint_map      == old(kernel).endpoint_map,
            final(kernel).allocator_2m_map  == old(kernel).allocator_2m_map,
            final(kernel).allocator_1g_map  == old(kernel).allocator_1g_map,
            final(kernel).default_pagetable == old(kernel).default_pagetable,
            final(kernel).allocator_4k_map.dom() == old(kernel).allocator_4k_map.dom(),
            final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).quota
                == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
            forall|p: RwLockPageAllocatorPtr|
                #![trigger final(kernel).allocator_4k_map.spec_index(p)]
                old(kernel).allocator_4k_map.dom().contains(p) && p != alloc_ptr_4k
                ==> final(kernel).allocator_4k_map.spec_index(p)
                    == old(kernel).allocator_4k_map.spec_index(p),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).lock_id_set() =~= old(lctx).lock_id_set()
                + allocator_cache_lock_entry_prefix(
                    alloc_ptr_4k, NUM_CPUS).insert((
                        ret.1.view().ordering_lock_id(),
                        KernelObjId::AllocatorGlobalPoll(
                            PageSize::SZ4k, alloc_ptr_4k),
                    )),
            final(lctx).lock_entry_contains(
                final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.lock_id(),
                KernelObjId::AllocatorGlobalPoll(
                    PageSize::SZ4k, alloc_ptr_4k,
                )),
            forall|c: CpuId|
                #![trigger final(lctx).lock_id_set().contains((
                    allocator_cache_lock_id(c),
                    KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c)))]
                index_valid(NUM_CPUS, c)
                ==> final(lctx).lock_id_set().contains((
                    allocator_cache_lock_id(c),
                    KernelObjId::AllocatorCache(
                        PageSize::SZ4k, alloc_ptr_4k, c),
                )),
            lock_id_aligned(final(kernel), final(lctx)),
            // ---- every cache + the pool is write-locked by us, perm recorded ----
            cache_perms_match_lctx(
                final(kernel).allocator_4k_map, alloc_ptr_4k,
                final(lctx), &ret.0.view()),
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.locking_thread()->Write_lock_id,
            final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.wlocked_by(final(lctx)),
            // ---- every held id ≤ pool major (caches 106, pool 107, pre-entry ≤ 105) ----
            final(lctx).held_lock_majors_le(ALLOCATOR_GLOBAL_POLL_MAJOR),
            allocator_objects_unlocked_except_cache_pool(
                final(kernel).allocator_4k_map,
                alloc_ptr_4k,
                final(lctx).thread_id(),
            ),
    {
        let tracked mut cache_perms: Map<CpuId, LockPerm> = Map::tracked_empty();

        let mut cpu: CpuId = 0;
        while cpu < NUM_CPUS
            invariant
                kernel.inv(),
                kernel.thread_map.dom().contains(thread_ptr),
                kernel.thread_map.spec_index(thread_ptr)
                    .locked_by_thread(lctx.thread_id()),
                lock_id_aligned(kernel, &*lctx),
                kernel.allocator_4k_map.dom().contains(alloc_ptr_4k),
                kernel.pagetable_map     == old(kernel).pagetable_map,
                kernel.iommu_table_map     == old(kernel).iommu_table_map,
                kernel.iommu_root_table     == old(kernel).iommu_root_table,
                kernel.page_array        == old(kernel).page_array,
                kernel.cpu_array         == old(kernel).cpu_array,
                kernel.cpu_tlb           == old(kernel).cpu_tlb,
                kernel.iommu_tlb           == old(kernel).iommu_tlb,
                kernel.root_container    == old(kernel).root_container,
                kernel.container_map     == old(kernel).container_map,
                kernel.scheduler_map     == old(kernel).scheduler_map,
                kernel.pcid_allocator_map == old(kernel).pcid_allocator_map,
                kernel.process_map       == old(kernel).process_map,
                kernel.thread_map        == old(kernel).thread_map,
                kernel.endpoint_map      == old(kernel).endpoint_map,
                kernel.allocator_2m_map  == old(kernel).allocator_2m_map,
                kernel.allocator_1g_map  == old(kernel).allocator_1g_map,
                kernel.default_pagetable == old(kernel).default_pagetable,
                kernel.allocator_4k_map.dom() == old(kernel).allocator_4k_map.dom(),
                kernel.allocator_4k_map.spec_index(alloc_ptr_4k).quota
                    == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                forall|p: RwLockPageAllocatorPtr|
                    #![trigger kernel.allocator_4k_map.spec_index(p)]
                    old(kernel).allocator_4k_map.dom().contains(p) && p != alloc_ptr_4k
                    ==> kernel.allocator_4k_map.spec_index(p)
                        == old(kernel).allocator_4k_map.spec_index(p),
                lctx.thread_id() == old(lctx).thread_id(),
                lctx.kernel_view_locking_state() is Acquire,
                0 <= cpu <= NUM_CPUS,
                lctx.lock_id_set() =~= old(lctx).lock_id_set()
                    + allocator_cache_lock_entry_prefix(
                        alloc_ptr_4k, cpu),
                !kernel.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.wlocked_by(&*lctx),
                forall|c: CpuId|
                    #![trigger kernel.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(c)]
                    index_valid(NUM_CPUS, c) && c >= cpu
                    ==> !kernel.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(c).view().wlocked_by(&*lctx),
                // Caches [0, cpu) are locked, perm collected; [cpu, NUM_CPUS) untouched.
                forall|c: CpuId|
                    #![trigger cache_perms.spec_index(c)]
                    index_valid(NUM_CPUS, c) && c < cpu
                    ==> {
                        &&& cache_perms.dom().contains(c)
                        &&& cache_perms.spec_index(c).state() is WriteLock
                        &&& cache_perms.spec_index(c).thread_id() == lctx.thread_id()
                        &&& cache_perms.spec_index(c).lock_id() == kernel.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(c).view().locking_thread()->Write_lock_id
                        &&& cache_perms.spec_index(c).ordering_lock_id()
                            == allocator_cache_lock_id(c)
                        &&& kernel.allocator_4k_map.spec_index(alloc_ptr_4k)
                            .cpu_caches.spec_index(c).view().wlocked_by(&*lctx)
                    },
                forall|c: CpuId|
                    #![trigger lctx.lock_id_set().contains((
                        allocator_cache_lock_id(c),
                        KernelObjId::AllocatorCache(
                            PageSize::SZ4k, alloc_ptr_4k, c)))]
                    index_valid(NUM_CPUS, c) && c < cpu
                    ==> lctx.lock_id_set().contains((
                        allocator_cache_lock_id(c),
                        KernelObjId::AllocatorCache(
                            PageSize::SZ4k, alloc_ptr_4k, c),
                    )),
                // Every held id is a pre-entry id (major ≤ 105) or a cache we just
                // took (major 106, minor < cpu) — so cache[cpu] (minor = cpu) tops all.
                lctx.lock_id_acyclic(allocator_cache_lock_id(cpu)),
            decreases NUM_CPUS - cpu,
        {
            proof {
                assert(kernel.allocator_4k_map.spec_index(alloc_ptr_4k).wf()) by {
                    reveal(allocator_perms_wf);
                };
            }
            let Tracked(cache_perm) = kernel.wlock_allocator_cache(alloc_ptr_4k, cpu, Tracked(&mut *lctx));
            proof {
                assert(kernel.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.lock_id_by_index(cpu)
                    == allocator_cache_lock_id(cpu)) by {
                    reveal(allocator_perms_wf);
                    reveal(allocator_cache_lock_id);
                };
                assert(allocator_cache_lock_entry_prefix_seq(
                    alloc_ptr_4k, (cpu + 1) as CpuId,
                ) =~= allocator_cache_lock_entry_prefix_seq(
                    alloc_ptr_4k, cpu,
                ).push((
                    allocator_cache_lock_id(cpu),
                    KernelObjId::AllocatorCache(
                        PageSize::SZ4k, alloc_ptr_4k, cpu),
                ))) by {
                    reveal(allocator_cache_lock_entry_prefix_seq);
                };
                assert(allocator_cache_lock_entry_prefix(
                    alloc_ptr_4k, (cpu + 1) as CpuId,
                ) =~= allocator_cache_lock_entry_prefix(
                    alloc_ptr_4k, cpu,
                ).insert((
                    allocator_cache_lock_id(cpu),
                    KernelObjId::AllocatorCache(
                        PageSize::SZ4k, alloc_ptr_4k, cpu),
                ))) by {
                    allocator_cache_lock_entry_prefix_seq(
                        alloc_ptr_4k, cpu,
                    ).lemma_push_to_set_commute((
                        allocator_cache_lock_id(cpu),
                        KernelObjId::AllocatorCache(
                            PageSize::SZ4k, alloc_ptr_4k, cpu),
                    ));
                    reveal(allocator_cache_lock_entry_prefix_seq);
                    reveal(allocator_cache_lock_entry_prefix);
                };
                assert(lctx.lock_id_set() =~= old(lctx).lock_id_set()
                    + allocator_cache_lock_entry_prefix(
                        alloc_ptr_4k, (cpu + 1) as CpuId,
                    )) by {
                    reveal(allocator_cache_lock_entry_prefix_seq);
                    reveal(allocator_cache_lock_entry_prefix);
                };
                cache_perms.tracked_insert(cpu, cache_perm);
            }
            cpu = cpu + 1;
        }

        // After the loop: all caches held (major 106), pool (major 107) tops them.
        proof {
            assert(kernel.allocator_4k_map.spec_index(alloc_ptr_4k).wf()) by {
                reveal(allocator_perms_wf);
            };
        }
        let Tracked(pool_perm) = kernel.wlock_allocator_global_pool(alloc_ptr_4k, Tracked(&mut *lctx));
        proof {
            assert(cache_perms_match_lctx(
                kernel.allocator_4k_map, alloc_ptr_4k, &*lctx, &cache_perms)) by {
                reveal(cache_perms_match_lctx);
            };
            assert(allocator_objects_unlocked_except_cache_pool(
                kernel.allocator_4k_map, alloc_ptr_4k, lctx.thread_id(),
            )) by {
                reveal(allocator_objects_unlocked_except_cache_pool);
            };
            assert(kernel_k_to_kernel_u(*kernel) == kernel_k_to_kernel_u(*old(kernel))) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(kernel), kernel);
            };
        }
        (Tracked(cache_perms), Tracked(pool_perm))
    }

    // ================================================================
    // wunlock_all_caches: release every cpu cache of `alloc_ptr_4k` (cpu
    // 0..NUM_CPUS), consuming the per-cpu perm map minted by
    // `wlock_all_caches_and_global_pool`. Each wrapper re-establishes inv()
    // internally. After this every cache of the allocator is unlocked and its
    // lock_map entry removed.
    // ================================================================
    pub(crate) fn wunlock_all_caches(
        kernel: &mut KernelK,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        page_index: PageIndex,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(cache_perms): Tracked<Map<CpuId, LockPerm>>,
    )
        requires
            old(kernel).inv(),
            old(kernel).thread_map.dom().contains(thread_ptr),
            old(kernel).thread_map.spec_index(thread_ptr)
                .locked_by_thread(old(lctx).thread_id()),
            index_valid(NUM_PAGES, page_index),
            old(kernel).page_array.spec_index(page_index).view()
                .locked_by_thread(old(lctx).thread_id()),
            lock_id_aligned(old(kernel), old(lctx)),
            allocator_objects_unlocked_except_cache_pool(
                old(kernel).allocator_4k_map,
                alloc_ptr_4k,
                old(lctx).thread_id(),
            ),
            cache_perms_match_lctx(
                old(kernel).allocator_4k_map, alloc_ptr_4k, old(lctx), &cache_perms),
            allocator_cache_lock_entry_prefix(
                alloc_ptr_4k, NUM_CPUS).subset_of(old(lctx).lock_id_set()),
            forall|c: CpuId|
                #![trigger old(lctx).lock_id_set().contains((
                    allocator_cache_lock_id(c),
                    KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c)))]
                index_valid(NUM_CPUS, c)
                ==> old(lctx).lock_id_set().contains((
                    allocator_cache_lock_id(c),
                    KernelObjId::AllocatorCache(
                        PageSize::SZ4k, alloc_ptr_4k, c),
                )),
            old(kernel).allocator_4k_map.dom().contains(alloc_ptr_4k),
            old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.wlocked_by(old(lctx)),
            old(lctx).lock_entry_contains(
                old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.lock_id(),
                KernelObjId::AllocatorGlobalPoll(
                    PageSize::SZ4k, alloc_ptr_4k,
                )),
        ensures
            final(kernel).inv(),
            final(kernel).thread_map.dom().contains(thread_ptr),
            final(kernel).thread_map.spec_index(thread_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            final(kernel).page_array.spec_index(page_index).view()
                .locked_by_thread(final(lctx).thread_id()),
            kernel_k_to_kernel_u(*final(kernel)) == kernel_k_to_kernel_u(*old(kernel)),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).lock_id_set() =~= old(lctx).lock_id_set()
                - allocator_cache_lock_entry_prefix(
                    alloc_ptr_4k, NUM_CPUS),
            lock_id_aligned(final(kernel), final(lctx)),
            // ---- only allocator_4k_map cache lock state moves; every other field byte-equal ----
            final(kernel).pagetable_map     == old(kernel).pagetable_map,
            final(kernel).iommu_table_map     == old(kernel).iommu_table_map,
            final(kernel).iommu_root_table     == old(kernel).iommu_root_table,
            final(kernel).page_array        == old(kernel).page_array,
            final(kernel).cpu_array         == old(kernel).cpu_array,
            final(kernel).cpu_tlb           == old(kernel).cpu_tlb,
            final(kernel).iommu_tlb           == old(kernel).iommu_tlb,
            final(kernel).root_container    == old(kernel).root_container,
            final(kernel).container_map     == old(kernel).container_map,
            final(kernel).scheduler_map     == old(kernel).scheduler_map,
            final(kernel).pcid_allocator_map == old(kernel).pcid_allocator_map,
            final(kernel).process_map       == old(kernel).process_map,
            final(kernel).thread_map        == old(kernel).thread_map,
            final(kernel).endpoint_map      == old(kernel).endpoint_map,
            final(kernel).allocator_2m_map  == old(kernel).allocator_2m_map,
            final(kernel).allocator_1g_map  == old(kernel).allocator_1g_map,
            final(kernel).default_pagetable == old(kernel).default_pagetable,
            final(kernel).allocator_4k_map.dom() == old(kernel).allocator_4k_map.dom(),
            final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).quota
                == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
            forall|p: RwLockPageAllocatorPtr|
                #![trigger final(kernel).allocator_4k_map.spec_index(p)]
                old(kernel).allocator_4k_map.dom().contains(p) && p != alloc_ptr_4k
                ==> final(kernel).allocator_4k_map.spec_index(p)
                    == old(kernel).allocator_4k_map.spec_index(p),
            final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
            final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.wlocked_by(final(lctx)),
            final(lctx).lock_entry_contains(
                old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.lock_id(),
                KernelObjId::AllocatorGlobalPoll(
                    PageSize::SZ4k, alloc_ptr_4k,
                )),
            allocator_caches_unlocked(
                final(kernel).allocator_4k_map, alloc_ptr_4k),
            allocator_objects_unlocked_except_cache_pool(
                final(kernel).allocator_4k_map,
                alloc_ptr_4k,
                final(lctx).thread_id(),
            ),
    {
        let tracked mut perms = cache_perms;
        assert(cache_perms_match_lctx_from(
            kernel.allocator_4k_map, alloc_ptr_4k, &*lctx, &perms, 0,
        )) by {
            reveal(cache_perms_match_lctx);
            reveal(cache_perms_match_lctx_from);
        };
        let mut cpu: CpuId = 0;
        while cpu < NUM_CPUS
            invariant
                kernel.inv(),
                kernel.thread_map.dom().contains(thread_ptr),
                kernel.thread_map.spec_index(thread_ptr)
                    .locked_by_thread(lctx.thread_id()),
                kernel.page_array.spec_index(page_index).view()
                    .locked_by_thread(lctx.thread_id()),
                lock_id_aligned(kernel, &*lctx),
                kernel.pagetable_map     == old(kernel).pagetable_map,
                kernel.iommu_table_map     == old(kernel).iommu_table_map,
                kernel.iommu_root_table     == old(kernel).iommu_root_table,
                kernel.page_array        == old(kernel).page_array,
                kernel.cpu_array         == old(kernel).cpu_array,
                kernel.cpu_tlb           == old(kernel).cpu_tlb,
                kernel.iommu_tlb           == old(kernel).iommu_tlb,
                kernel.root_container    == old(kernel).root_container,
                kernel.container_map     == old(kernel).container_map,
                kernel.scheduler_map     == old(kernel).scheduler_map,
                kernel.pcid_allocator_map == old(kernel).pcid_allocator_map,
                kernel.process_map       == old(kernel).process_map,
                kernel.thread_map        == old(kernel).thread_map,
                kernel.endpoint_map      == old(kernel).endpoint_map,
                kernel.allocator_2m_map  == old(kernel).allocator_2m_map,
                kernel.allocator_1g_map  == old(kernel).allocator_1g_map,
                kernel.default_pagetable == old(kernel).default_pagetable,
                kernel.allocator_4k_map.dom().contains(alloc_ptr_4k),
                kernel.allocator_4k_map.dom() == old(kernel).allocator_4k_map.dom(),
                kernel.allocator_4k_map.spec_index(alloc_ptr_4k).quota
                    == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                forall|p: RwLockPageAllocatorPtr|
                    #![trigger kernel.allocator_4k_map.spec_index(p)]
                    old(kernel).allocator_4k_map.dom().contains(p) && p != alloc_ptr_4k
                    ==> kernel.allocator_4k_map.spec_index(p)
                        == old(kernel).allocator_4k_map.spec_index(p),
                kernel.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
                lctx.thread_id() == old(lctx).thread_id(),
                0 <= cpu <= NUM_CPUS,
                lctx.lock_id_set() =~= old(lctx).lock_id_set()
                    - allocator_cache_lock_entry_prefix(
                        alloc_ptr_4k, cpu),
                forall|c: CpuId|
                    #![trigger lctx.lock_id_set().contains((
                        allocator_cache_lock_id(c),
                        KernelObjId::AllocatorCache(
                            PageSize::SZ4k, alloc_ptr_4k, c)))]
                    index_valid(NUM_CPUS, c) && c >= cpu
                    ==> lctx.lock_id_set().contains((
                        allocator_cache_lock_id(c),
                        KernelObjId::AllocatorCache(
                            PageSize::SZ4k, alloc_ptr_4k, c),
                    )),
                lctx.lock_entry_contains(
                    old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .global_pool.lock_id(),
                    KernelObjId::AllocatorGlobalPoll(
                        PageSize::SZ4k, alloc_ptr_4k,
                    )),
                kernel.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.wlocked_by(&*lctx),
                forall|c: CpuId|
                    #![trigger kernel.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(c).view().locked()]
                    index_valid(NUM_CPUS, c) && c < cpu
                    ==> kernel.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(c).view().locked() == false,
                forall|c: CpuId|
                    #![trigger kernel.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(c)]
                    index_valid(NUM_CPUS, c) && c < cpu
                    ==> !kernel.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(c).view()
                        .wlocked_by_thread(lctx.thread_id()),
                cache_perms_match_lctx_from(
                    kernel.allocator_4k_map, alloc_ptr_4k, &*lctx, &perms, cpu),
            decreases NUM_CPUS - cpu,
        {
            proof {
                assert(
                    perms.dom().contains(cpu)
                    && perms.spec_index(cpu).state() is WriteLock
                    && perms.spec_index(cpu).thread_id() == lctx.thread_id()
                    && perms.spec_index(cpu).lock_id()
                        == kernel.allocator_4k_map.spec_index(alloc_ptr_4k)
                            .cpu_caches.spec_index(cpu).view().locking_thread()->Write_lock_id
                    && perms.spec_index(cpu).ordering_lock_id()
                        == allocator_cache_lock_id(cpu)
                    && kernel.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(cpu).view().wlocked_by(&*lctx)
                ) by {
                    reveal(cache_perms_match_lctx_from);
                };
                assert(kernel.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.spec_index(cpu).view().being_killed() == false) by {
                    reveal(allocator_perms_wf);
                };
                assert(kernel.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.lock_id_by_index(cpu)
                    == allocator_cache_lock_id(cpu)) by {
                    reveal(allocator_perms_wf);
                    reveal(allocator_cache_lock_id);
                };
            }
            let tracked cache_perm = perms.tracked_remove(cpu);
            kernel.wunlock_allocator_cache(alloc_ptr_4k, cpu, Tracked(&mut *lctx), Tracked(cache_perm));
            proof {
                assert(allocator_cache_lock_entry_prefix_seq(
                    alloc_ptr_4k, (cpu + 1) as CpuId,
                ) =~= allocator_cache_lock_entry_prefix_seq(
                    alloc_ptr_4k, cpu,
                ).push((
                    allocator_cache_lock_id(cpu),
                    KernelObjId::AllocatorCache(
                        PageSize::SZ4k, alloc_ptr_4k, cpu),
                ))) by {
                    reveal(allocator_cache_lock_entry_prefix_seq);
                };
                assert(allocator_cache_lock_entry_prefix(
                    alloc_ptr_4k, (cpu + 1) as CpuId,
                ) =~= allocator_cache_lock_entry_prefix(
                    alloc_ptr_4k, cpu,
                ).insert((
                    allocator_cache_lock_id(cpu),
                    KernelObjId::AllocatorCache(
                        PageSize::SZ4k, alloc_ptr_4k, cpu),
                ))) by {
                    allocator_cache_lock_entry_prefix_seq(
                        alloc_ptr_4k, cpu,
                    ).lemma_push_to_set_commute((
                        allocator_cache_lock_id(cpu),
                        KernelObjId::AllocatorCache(
                            PageSize::SZ4k, alloc_ptr_4k, cpu),
                    ));
                    reveal(allocator_cache_lock_entry_prefix_seq);
                    reveal(allocator_cache_lock_entry_prefix);
                };
                assert(lctx.lock_id_set() =~= old(lctx).lock_id_set()
                    - allocator_cache_lock_entry_prefix(
                        alloc_ptr_4k, (cpu + 1) as CpuId,
                    )) by {
                    reveal(allocator_cache_lock_entry_prefix_seq);
                    reveal(allocator_cache_lock_entry_prefix);
                };
                assert(cache_perms_match_lctx_from(
                    kernel.allocator_4k_map, alloc_ptr_4k, &*lctx, &perms,
                    (cpu + 1) as CpuId,
                )) by {
                    reveal(cache_perms_match_lctx_from);
                    reveal(allocator_perms_wf);
                };
            }
            cpu = cpu + 1;
        }
        proof {
            assert(allocator_caches_unlocked(
                kernel.allocator_4k_map, alloc_ptr_4k,
            )) by {
                reveal(allocator_caches_unlocked);
            };
            assert(allocator_objects_unlocked_except_cache_pool(
                kernel.allocator_4k_map,
                alloc_ptr_4k,
                lctx.thread_id(),
            )) by {
                reveal(allocator_objects_unlocked_except_cache_pool);
            };
            assert(kernel_k_to_kernel_u(*kernel) == kernel_k_to_kernel_u(*old(kernel))) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(kernel), kernel);
            };
        }
    }

    // ================================================================
    // scan_caches_and_alloc: every cpu cache of `alloc_ptr_4k` is already
    // write-locked (perm for cpu `c` at `cache_perms[c]`) and the thread is
    // write-locked. Every held lock remains below the Free4k page-slot major;
    // this permits mmap to retain the global-pool and PageTable locks. Iterate
    // cpu 0..NUM_CPUS; on the first
    // non-empty cache, pop + stage a page via `pop_stage_4k_page` and return
    // `(true, Some((cpu, page_ptr, page_perm)))` with that cache + the page slot
    // still write-locked. If every cache is empty, return `(false, None)` — a
    // complete no-op, all caches still held. inv() preserved throughout.
    // ================================================================
    #[verifier::opaque]
    spec fn cache_perms_match_lctx_from(
        alloc_map: PageAllocatorUnLockedMap,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        lctx: &LocalContext,
        cache_perms: &Map<CpuId, LockPerm>,
        first_cpu: CpuId,
    ) -> bool {
        &&& alloc_map.dom().contains(alloc_ptr_4k)
        &&& forall|c: CpuId|
                #![trigger cache_perms.spec_index(c)]
                index_valid(NUM_CPUS, c) && c >= first_cpu
                ==> {
                    &&& cache_perms.dom().contains(c)
                    &&& cache_perms.spec_index(c).state() is WriteLock
                    &&& cache_perms.spec_index(c).thread_id() == lctx.thread_id()
                    &&& cache_perms.spec_index(c).lock_id()
                        == alloc_map.spec_index(alloc_ptr_4k)
                            .cpu_caches.spec_index(c).view().locking_thread()->Write_lock_id
                    &&& cache_perms.spec_index(c).ordering_lock_id()
                        == allocator_cache_lock_id(c)
                    &&& alloc_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(c).view().wlocked_by(lctx)
                }
    }

    #[verifier::opaque]
    pub(crate) open spec fn cache_perms_match_lctx(
        alloc_map: PageAllocatorUnLockedMap,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        lctx: &LocalContext,
        cache_perms: &Map<CpuId, LockPerm>,
    ) -> bool {
        &&& alloc_map.dom().contains(alloc_ptr_4k)
        &&& forall|c: CpuId|
                #![trigger cache_perms.spec_index(c)]
                index_valid(NUM_CPUS, c)
                ==> {
                    &&& cache_perms.dom().contains(c)
                    &&& cache_perms.spec_index(c).state() is WriteLock
                    &&& cache_perms.spec_index(c).thread_id() == lctx.thread_id()
                    &&& cache_perms.spec_index(c).lock_id()
                        == alloc_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(c).view().locking_thread()->Write_lock_id
                    &&& cache_perms.spec_index(c).ordering_lock_id()
                        == allocator_cache_lock_id(c)
                    &&& alloc_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(c).view().wlocked_by(lctx)
                }
    }

    fn scan_caches_and_alloc(
        kernel: &mut KernelK,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        container_ptr: RwLockContainerPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(cache_perms): Tracked<&Map<CpuId, LockPerm>>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (bool, Option<(CpuId, PagePtr, Tracked<LockPerm>)>))
        requires
            old(kernel).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(kernel).container_map.dom().contains(container_ptr),
            old(kernel).thread_map.dom().contains(thread_ptr),
            page_objects_unlocked(
                old(kernel).page_array, old(lctx).thread_id()),
            old(kernel).allocator_4k_map.dom().contains(alloc_ptr_4k),
            allocator_objects_unlocked_except_cache_pool(
                old(kernel).allocator_4k_map,
                alloc_ptr_4k,
                old(lctx).thread_id(),
            ),
            old(kernel).container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(kernel).thread_map.spec_index(thread_ptr).view().owning_container == container_ptr,
            old(kernel).thread_map.spec_index(thread_ptr).being_killed() == false,
            thread_effective_quota_4k(old(kernel).thread_map.spec_index(thread_ptr)) >= 1,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(kernel).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(kernel).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
            lock_id_aligned(old(kernel), old(lctx)),
            cache_perms_match_lctx(
                old(kernel).allocator_4k_map, alloc_ptr_4k, old(lctx), cache_perms),
            old(lctx).held_lock_majors_lt(FREE_PAGE_LOCK_MAJOR),
        ensures
            final(kernel).inv(),
            final(kernel).thread_map.spec_index(thread_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            final(kernel).process_map == old(kernel).process_map,
            final(kernel).pagetable_map == old(kernel).pagetable_map,
            final(kernel).container_map == old(kernel).container_map,
            final(kernel).scheduler_map == old(kernel).scheduler_map,
            final(kernel).pcid_allocator_map == old(kernel).pcid_allocator_map,
            final(kernel).endpoint_map == old(kernel).endpoint_map,
            final(kernel).iommu_root_table == old(kernel).iommu_root_table,
            final(kernel).iommu_table_map == old(kernel).iommu_table_map,
            final(kernel).iommu_tlb == old(kernel).iommu_tlb,
            final(kernel).cpu_array == old(kernel).cpu_array,
            final(kernel).allocator_2m_map == old(kernel).allocator_2m_map,
            final(kernel).allocator_1g_map == old(kernel).allocator_1g_map,
            final(kernel).thread_map.unchanged_except(&old(kernel).thread_map, thread_ptr),
            forall|t: RwLockThreadPtr|
                #![trigger old(kernel).thread_map.spec_index(t)
                    .locked_by_thread(old(lctx).thread_id())]
                #![trigger final(kernel).thread_map.spec_index(t)
                    .locked_by_thread(final(lctx).thread_id())]
                t != thread_ptr
                    && old(kernel).thread_map.dom().contains(t)
                    && old(kernel).thread_map.spec_index(t)
                        .locked_by_thread(old(lctx).thread_id())
                ==> final(kernel).thread_map.dom().contains(t)
                    && final(kernel).thread_map.spec_index(t)
                        == old(kernel).thread_map.spec_index(t)
                    && final(kernel).thread_map.lock_id_by_key(t)
                        == old(kernel).thread_map.lock_id_by_key(t),
            allocator_objects_unlocked_except_cache_pool(
                final(kernel).allocator_4k_map,
                alloc_ptr_4k,
                final(lctx).thread_id(),
            ),
            final(kernel).allocator_4k_map.unchanged_except(
                &old(kernel).allocator_4k_map, alloc_ptr_4k),
            final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).quota
                == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(kernel).thread_map.lock_id_by_key(thread_ptr)
                == old(kernel).thread_map.lock_id_by_key(thread_ptr),
            lock_id_aligned(final(kernel), final(lctx)),
            // ---- user view unchanged: staging is kernel-internal ----
            kernel_k_to_kernel_u(*final(kernel)) == kernel_k_to_kernel_u(*old(kernel)),
            // ---- failure: every cache was empty; complete no-op ----
            ret.0 == false ==> {
                &&& ret.1 is None
                &&& *final(kernel) == *old(kernel)
                &&& *final(lctx) == *old(lctx)
                &&& forall|c: CpuId|
                    #![trigger final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(c)]
                    index_valid(NUM_CPUS, c)
                    ==> final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(c).view().view().view().len() == 0
            },
            // ---- success: popped + staged a page from cache `cpu`, page slot held ----
            ret.0 == true ==> {
                &&& ret.1 is Some
                &&& final(lctx).kernel_view_locking_state() is Release
                &&& index_valid(NUM_CPUS, ret.1.unwrap().0)
                &&& page_ptr_valid(ret.1.unwrap().1)
                &&& old(kernel).page_array.spec_index(
                    page_ptr2page_index(ret.1.unwrap().1),
                ).view().view().state is Free4k
                &&& !old(kernel).thread_map.spec_index(thread_ptr).view()
                    .temp_alloc_cache_4k.view().contains(ret.1.unwrap().1)
                &&& index_valid(NUM_PAGES, page_ptr2page_index(ret.1.unwrap().1))
                &&& final(kernel).page_array.entries_unchanged_except(
                    &old(kernel).page_array, page_ptr2page_index(ret.1.unwrap().1))
                &&& final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool
                    == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool
                &&& final(kernel).page_array.spec_index(page_ptr2page_index(ret.1.unwrap().1)).view().being_killed() == false
                &&& ret.1.unwrap().2.view().state() is WriteLock
                &&& ret.1.unwrap().2.view().thread_id() == final(lctx).thread_id()
                &&& ret.1.unwrap().2.view().lock_id() == final(kernel).page_array.spec_index(page_ptr2page_index(ret.1.unwrap().1)).view().locking_thread()->Write_lock_id
                &&& final(kernel).page_array.spec_index(page_ptr2page_index(ret.1.unwrap().1)).view()
                    .wlocked_by(final(lctx))
                &&& final(kernel).page_array.spec_index(page_ptr2page_index(ret.1.unwrap().1)).view()
                    .locked_by_thread(final(lctx).thread_id())
                &&& page_objects_unlocked_except(
                    final(kernel).page_array, final(lctx).thread_id(),
                    set![page_ptr2page_index(ret.1.unwrap().1)])
                &&& final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((
                    final(kernel).page_array.lock_id_by_index(
                        page_ptr2page_index(ret.1.unwrap().1)),
                    KernelObjId::Page(page_ptr2page_index(ret.1.unwrap().1)),
                ))
                &&& cache_perms_match_lctx(
                    final(kernel).allocator_4k_map, alloc_ptr_4k, final(lctx), cache_perms)
                &&& final(kernel).thread_map.spec_index(thread_ptr)
                    .wlocked_by(final(lctx))
                &&& final(kernel).thread_map.spec_index(thread_ptr).being_killed() == false
                &&& final(kernel).thread_map.spec_index(thread_ptr).view().owning_proc
                    == old(kernel).thread_map.spec_index(thread_ptr).view().owning_proc
                &&& final(kernel).thread_map.spec_index(thread_ptr).view().owning_container
                    == old(kernel).thread_map.spec_index(thread_ptr).view().owning_container
                &&& final(kernel).thread_map.spec_index(thread_ptr).view()
                    .stable_allocation_root_equal(
                        &old(kernel).thread_map.spec_index(thread_ptr).view(),
                    )
                &&& final(kernel).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                    == old(kernel).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                &&& thread_lock_perm.lock_id() == final(kernel).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id
                &&& final(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
                    =~= old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().insert(ret.1.unwrap().1)
                &&& final(kernel).page_array.spec_index(page_ptr2page_index(ret.1.unwrap().1)).view().view().state == (PageState::Owned4k{ thread_ptr })
                &&& final(kernel).page_array.spec_index(page_ptr2page_index(ret.1.unwrap().1)).view().view().owning_container
                    == container_ptr
                &&& final(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m
                    == old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m
                &&& final(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g
                    == old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g
                &&& final(kernel).thread_map.spec_index(thread_ptr).view()
                    .free_quota_pending_fields_equal(
                        &old(kernel).thread_map.spec_index(thread_ptr).view(),
                    )
                &&& final(kernel).thread_map.spec_index(thread_ptr).view().quota_4k
                    == old(kernel).thread_map.spec_index(thread_ptr).view().quota_4k
                &&& final(kernel).thread_map.spec_index(thread_ptr).view().endpoint_descriptors
                    == old(kernel).thread_map.spec_index(thread_ptr).view().endpoint_descriptors
            },
    {
        let mut cpu: CpuId = 0;
        while cpu < NUM_CPUS
            invariant
                *kernel == *old(kernel),
                *lctx == *old(lctx),
                kernel.inv(),
                lock_id_aligned(kernel, &*lctx),
                lctx.kernel_view_locking_state() is Acquire,
                0 <= cpu <= NUM_CPUS,
                kernel.container_map.dom().contains(container_ptr),
                kernel.allocator_4k_map.dom().contains(alloc_ptr_4k),
                allocator_objects_unlocked_except_cache_pool(
                    kernel.allocator_4k_map, alloc_ptr_4k, lctx.thread_id(),
                ),
                kernel.container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
                kernel.thread_map.spec_index(thread_ptr).view().owning_container == container_ptr,
                kernel.thread_map.spec_index(thread_ptr).being_killed() == false,
                thread_effective_quota_4k(kernel.thread_map.spec_index(thread_ptr)) >= 1,
                thread_lock_perm.state() is WriteLock,
                thread_lock_perm.thread_id() == lctx.thread_id(),
                thread_lock_perm.lock_id() == kernel.thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
                kernel.thread_map.dom().contains(thread_ptr),
                kernel.thread_map.spec_index(thread_ptr).wlocked_by(&*lctx),
                kernel.thread_map.spec_index(thread_ptr)
                    .locked_by_thread(lctx.thread_id()),
                page_objects_unlocked(kernel.page_array, lctx.thread_id()),
                cache_perms_match_lctx(
                    kernel.allocator_4k_map, alloc_ptr_4k, &*lctx, cache_perms),
                lctx.held_lock_majors_lt(FREE_PAGE_LOCK_MAJOR),
                // Caches [0, cpu) were all found empty.
                forall|c: CpuId|
                    #![trigger kernel.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(c)]
                    index_valid(NUM_CPUS, c) && c < cpu
                    ==> kernel.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(c).view().view().view().len() == 0,
            decreases NUM_CPUS - cpu,
        {
            proof {
                assert(
                    kernel.allocator_4k_map.perms_wf()
                    && kernel.allocator_4k_map.dom().contains(alloc_ptr_4k)
                    && kernel.allocator_4k_map.spec_index(alloc_ptr_4k).wf()
                    && kernel.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.inv()
                    && kernel.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches_wf()
                    && cache_perms.dom().contains(cpu)
                    && cache_perms.spec_index(cpu).state() is WriteLock
                    && cache_perms.spec_index(cpu).thread_id() == lctx.thread_id()
                    && cache_perms.spec_index(cpu).lock_id()
                        == kernel.allocator_4k_map.spec_index(alloc_ptr_4k)
                            .cpu_caches.spec_index(cpu).view().locking_thread()->Write_lock_id
                    && kernel.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(cpu).view()
                        .write_lock_perm_match(&cache_perms.spec_index(cpu))
                    && kernel.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(cpu).view().being_killed() == false
                ) by {
                    reveal(allocator_perms_wf);
                    reveal(cache_perms_match_lctx);
                };
            }
            let cache_ref = kernel.allocator_4k_map.borrow_cache(
                alloc_ptr_4k, cpu, Tracked(cache_perms.tracked_borrow(cpu)),
            );
            assert(cache_ref.linked_list.wf()) by {
                assert(
                    index_valid(NUM_CPUS, cpu)
                    && kernel.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches_wf()
                ) by {
                    reveal(allocator_perms_wf);
                };
            };
            let cache_len = cache_ref.linked_list.len();
            assert(cache_len == kernel.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu).view().view().view().len()) by {
                cache_ref.linked_list.lemma_len_view();
            };
            if cache_len > 0 {
                let tracked selected_cache_perm = cache_perms.tracked_borrow(cpu);
                let (page_ptr, Tracked(page_lock_perm)) = pop_stage_4k_page(kernel,
                    alloc_ptr_4k, cpu, thread_ptr, container_ptr,
                    Tracked(&mut *lctx), Tracked(selected_cache_perm), Tracked(thread_lock_perm),
                );
                assert(cache_perms_match_lctx(
                    kernel.allocator_4k_map, alloc_ptr_4k, &*lctx, cache_perms,
                )) by {
                    reveal(cache_perms_match_lctx);
                };
                assert(allocator_objects_unlocked_except_cache_pool(
                    kernel.allocator_4k_map, alloc_ptr_4k, lctx.thread_id(),
                )) by {
                    reveal(allocator_objects_unlocked_except_cache_pool);
                };
                return (true, Some((cpu, page_ptr, Tracked(page_lock_perm))));
            }
            cpu = cpu + 1;
        }
        (false, None)
    }



} // verus!



verus! {


/// After a failed cache scan (every cpu cache of `alloc_ptr_4k` empty), the
/// container conservation law forces the global pool to be non-empty: the
/// total free-page count equals the pool length (all cache summands are zero),
/// and that total is at least the held thread's `effective_quota_4k >= 1`
/// because every other conservation summand is non-negative.
pub proof fn lemma_scan_fail_pool_nonempty(
    k: &KernelK,
    container_ptr: RwLockContainerPtr,
    alloc_ptr_4k: RwLockPageAllocatorPtr,
    thread_ptr: RwLockThreadPtr,
)
    requires
        k.inv(),
        k.container_map.dom().contains(container_ptr),
        k.container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
        k.container_map.spec_index(container_ptr).view_user_ghost().owned_threads.view().contains(thread_ptr),
        thread_effective_quota_4k(k.thread_map.spec_index(thread_ptr)) >= 1,
        forall|c: CpuId|
            #![trigger k.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(c)]
            index_valid(NUM_CPUS, c)
            ==> k.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(c).view().view().view().len() == 0,
    ensures
        k.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().view().len() > 0,
{
    assert(
        allocator_perms_wf(k.allocator_4k_map)
        && container_allocator_wf(
            k.container_map,
            k.allocator_4k_map,
            k.allocator_2m_map,
            k.allocator_1g_map,
        )
        && container_process_wf(k.container_map, k.process_map)
        && container_thread_wf(k.container_map, k.thread_map)
        && container_process_allocator_quota_4k_wf(
            k.container_map,
            k.process_map,
            k.thread_map,
            k.allocator_4k_map,
        )
        && process_perms_wf(k.process_map)
        && thread_perms_wf(k.thread_map)
    ) by {
        reveal(allocator_perms_wf);
        reveal(container_allocator_wf);
        reveal(container_process_wf);
        reveal(container_thread_wf);
        reveal(container_process_allocator_quota_4k_wf);
        reveal(process_perms_wf);
        reveal(thread_perms_wf);
    };
    let owned_processes = k.container_map.spec_index(container_ptr).view().owned_processes.view();
    let owned_threads = k.container_map.spec_index(container_ptr).view_user_ghost().owned_threads.view();
    let caches = k.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches;
    assert(
        k.allocator_4k_map.spec_index(alloc_ptr_4k)
            .global_pool.view().view().len() > 0
    ) by {
        assert(k.allocator_4k_map.dom().contains(alloc_ptr_4k)) by {
            reveal(container_allocator_wf);
        };
        assert(k.thread_map.dom().contains(thread_ptr)) by {
            reveal(container_thread_wf);
        };
        assert forall|j: int| #![trigger caches.view().spec_index(j)]
            0 <= j < caches.view().len()
            implies {
                &&& caches.view().spec_index(j) == caches.spec_index(j as usize).value
                &&& caches.view().spec_index(j).view().linked_list.view().len() == 0
            } by {
                reveal(allocator_perms_wf);
                reveal(container_allocator_wf);
                lemma_usize_int(j);
                caches.lemma_view_index(j as usize);
            };
        lemma_cache_len_fold_all_zero(caches.view());
        assert forall|p: RwLockProcessPtr|
            #![trigger process_effective_quota_4k(k.process_map.spec_index(p))]
            owned_processes.contains(p)
            implies process_effective_quota_4k(k.process_map.spec_index(p)) >= 0 by {
            reveal(container_process_wf);
        };
        lemma_process_effective_quota_4k_fold_nonneg(owned_processes, k.process_map);
        assert forall|t: RwLockThreadPtr|
            #![trigger thread_effective_quota_4k(k.thread_map.spec_index(t))]
            owned_threads.contains(t)
            implies thread_effective_quota_4k(k.thread_map.spec_index(t)) >= 0 by {
            reveal(container_thread_wf);
            reveal(thread_perms_wf);
        };
        lemma_thread_effective_quota_4k_fold_ge_member(
            owned_threads, k.thread_map, thread_ptr,
        );
        lemma_thread_direct_pending_4k_fold_nonneg(
            k.container_map.spec_index(container_ptr)
                .view_user_ghost().owned_threads.view(),
            k.thread_map,
        );
        lemma_thread_indirect_pending_4k_fold_nonneg(
            k.container_map.spec_index(container_ptr)
                .view_kernel_ghost().owned_indirect_threads.view(),
            k.thread_map,
            k.container_map.spec_index(container_ptr)
                .view_rodata().view().depth as int,
        );
        reveal(allocator_perms_wf);
        reveal(container_allocator_wf);
        reveal(container_process_wf);
        reveal(container_thread_wf);
        reveal(container_process_allocator_quota_4k_wf);
        reveal(process_perms_wf);
        reveal(thread_perms_wf);
    };
}

}
