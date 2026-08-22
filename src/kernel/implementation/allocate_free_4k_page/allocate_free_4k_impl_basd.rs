use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal};
use crate::*;

verus! {

impl KernelK {


    // ================================================================
    // Main allocate function
    // ================================================================

    /// Allocate a single 4k page from the container's allocator.
    /// Caller holds the allocating thread's write-lock.
    #[verifier::spinoff_prover]
    pub fn allocate_free_4k_page(
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        cpu_id: CpuId,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(self).inv(),
            index_valid(NUM_CPUS, cpu_id),
            old(self).thread_map.dom().contains(thread_ptr),
            old(self).process_map.dom().contains(process_ptr),
            old(self).process_map.spec_index(process_ptr).view_rodata()
                .view().owning_container == container_ptr,
            old(self).container_map.dom().contains(container_ptr),
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            old(self).container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(self).thread_map.spec_index(thread_ptr).view().owning_container == container_ptr,
            old(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            // Thread write-lock perm, needed to mutate the thread payload
            // (insert the freshly-allocated page into `temp_alloc_cache_4k`).
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(self).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
            thread_effective_quota_4k(old(self).thread_map.spec_index(thread_ptr)) >= 1,
            old(self).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
            old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
            old(self).cpu_array.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            old(self).thread_map.spec_index(thread_ptr)
                .locked_by_thread(old(lctx).thread_id()),
            old(self).process_map.spec_index(process_ptr)
                .locked_by_thread(old(lctx).thread_id()),
            old(self).cpu_array.spec_index(cpu_id).view()
                .locked_by_thread(old(lctx).thread_id()),
            page_objects_unlocked(
                old(self).page_array, old(lctx).thread_id()),
            allocator_objects_unlocked(
                old(self).allocator_4k_map, old(lctx).thread_id()),
            lock_id_aligned(old(self), old(lctx)),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        ensures
            final(self).inv(),
            // ---- held thread: not killed, perm still matches ----
            final(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            final(self).thread_map.spec_index(thread_ptr).view().owning_proc
                == old(self).thread_map.spec_index(thread_ptr).view().owning_proc,
            final(self).thread_map.spec_index(thread_ptr).view().owning_container
                == old(self).thread_map.spec_index(thread_ptr).view().owning_container,
            final(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                == old(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr,
            thread_lock_perm.lock_id() == final(self).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            final(self).thread_map.lock_id_by_key(thread_ptr)
                == old(self).thread_map.lock_id_by_key(thread_ptr),
            final(self).process_map.dom().contains(process_ptr),
            final(self).process_map.spec_index(process_ptr)
                == old(self).process_map.spec_index(process_ptr),
            final(self).process_map.lock_id_by_key(process_ptr)
                == old(self).process_map.lock_id_by_key(process_ptr),
            final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx)),
            final(self).container_map.dom().contains(container_ptr),
            final(self).container_map.spec_index(container_ptr).view_rodata()
                == old(self).container_map.spec_index(container_ptr).view_rodata(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            lock_id_aligned(final(self), final(lctx)),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            page_ptr_valid(ret.0),
            // ---- page slot left write-locked, perm handed back (rides across the boundary as a held object) ----
            index_valid(NUM_PAGES, page_ptr2page_index(ret.0)),
            final(self).page_array.spec_index(page_ptr2page_index(ret.0)).view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(self).page_array.spec_index(page_ptr2page_index(ret.0)).view().locking_thread()->Write_lock_id,
            final(self).page_array.spec_index(page_ptr2page_index(ret.0)).view()
                .wlocked_by(final(lctx)),
            page_objects_unlocked_except(
                final(self).page_array, final(lctx).thread_id(),
                set![page_ptr2page_index(ret.0)]),
            forall|i: PageIndex|
                #![trigger final(self).page_array.spec_index(i)]
                index_valid(NUM_PAGES, i)
                    && i != page_ptr2page_index(ret.0)
                    && final(self).page_array.spec_index(i).view()
                        .locked_by_thread(final(lctx).thread_id())
                ==> old(self).page_array.spec_index(i).view()
                    .locked_by_thread(old(lctx).thread_id()),
            final(self).thread_map.dom().contains(thread_ptr),
            final(self).thread_map.spec_index(thread_ptr).wlocked_by(final(lctx)),
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((
                final(self).page_array.lock_id_by_index(page_ptr2page_index(ret.0)),
                KernelObjId::Page(page_ptr2page_index(ret.0)),
            )),
            held_containers_unchanged(
                old(self).container_map, final(self).container_map, old(lctx)),
            held_processes_unchanged(
                old(self).process_map, final(self).process_map, old(lctx)),
            held_endpoints_unchanged(
                old(self).endpoint_map, final(self).endpoint_map, old(lctx)),
            held_schedulers_unchanged(
                old(self).scheduler_map, final(self).scheduler_map, old(lctx)),
            held_pcid_allocators_unchanged(
                old(self).pcid_allocator_map, final(self).pcid_allocator_map,
                old(lctx)),
            held_pagetables_unchanged(
                old(self).pagetable_map, final(self).pagetable_map, old(lctx)),
            held_iommu_tables_unchanged(
                old(self).iommu_table_map, final(self).iommu_table_map, old(lctx)),
            held_cpus_unchanged(
                old(self).cpu_array, final(self).cpu_array, old(lctx)),
            thread_objects_unlocked_except(
                old(self).thread_map, old(lctx).thread_id(), set![thread_ptr],
            ) ==> thread_objects_unlocked_except(
                final(self).thread_map, final(lctx).thread_id(), set![thread_ptr],
            ),
            allocator_objects_unlocked(
                old(self).allocator_2m_map, old(lctx).thread_id(),
            ) ==> allocator_objects_unlocked(
                final(self).allocator_2m_map, final(lctx).thread_id(),
            ),
            allocator_objects_unlocked(
                old(self).allocator_1g_map, old(lctx).thread_id(),
            ) ==> allocator_objects_unlocked(
                final(self).allocator_1g_map, final(lctx).thread_id(),
            ),
            allocator_objects_unlocked(
                final(self).allocator_4k_map, final(lctx).thread_id()),
            final(self).cpu_array.spec_index(cpu_id).view() == old(self).cpu_array.spec_index(cpu_id).view(),
            final(self).cpu_array.spec_index(cpu_id).view().wlocked_by(final(lctx)),
            // ---- staging: ret staged Owned4k; 4k cache gained exactly ret, 2m/1g caches + nominal quota untouched ----
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
                =~= old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().insert(ret.0),
            final(self).page_array.spec_index(page_ptr2page_index(ret.0)).view().view().state == (PageState::Owned4k{ thread_ptr }),
            final(self).page_array.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container
                == container_ptr,
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m,
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            final(self).thread_map.spec_index(thread_ptr).view().quota_4k
                == old(self).thread_map.spec_index(thread_ptr).view().quota_4k,
            final(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_fields_equal(
                    &old(self).thread_map.spec_index(thread_ptr).view(),
                ),
            final(self).thread_map.spec_index(thread_ptr).view().endpoint_descriptors
                == old(self).thread_map.spec_index(thread_ptr).view().endpoint_descriptors,
    {
        assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).wf()) by {
            reveal(allocator_perms_wf);
        };
        // Fast path: lock the running cpu's cache.
        let Tracked(cache_lock_perm) = self.wlock_allocator_cache(
            alloc_ptr_4k, cpu_id, Tracked(&mut *lctx),
        );
        proof {
            assert(Self::allocator_objects_unlocked_except_cache_pool(
                self.allocator_4k_map, alloc_ptr_4k, lctx.thread_id(),
            )) by {
                reveal(KernelK::allocator_objects_unlocked_except_cache_pool);
            };
        }

        // Read the cache length via a shared borrow (preserves wf() for the slow path).
        let cache_ref = self.allocator_4k_map.borrow_cache(
            alloc_ptr_4k, cpu_id, Tracked(&cache_lock_perm),
        );
        let cache_len = cache_ref.linked_list.len();

        if cache_len > 0 {
            if cache_len == ALLOCATOR_MIN_WATERMARK + 1 {
                let Tracked(gp_lock_perm) = self.wlock_allocator_global_pool(
                    alloc_ptr_4k, Tracked(&mut *lctx),
                );
                proof {
                    assert(Self::allocator_objects_unlocked_except_cache_pool(
                        self.allocator_4k_map, alloc_ptr_4k, lctx.thread_id(),
                    )) by {
                        reveal(KernelK::allocator_objects_unlocked_except_cache_pool);
                    };
                }
                assert(self.allocator_4k_map.perms_wf()) by {
                    reveal(allocator_perms_wf);
                };
                let pool_ref = self.allocator_4k_map.borrow_global_pool(
                    alloc_ptr_4k, Tracked(&gp_lock_perm),
                );
                let pool_len = pool_ref.len();

                if pool_len > 0 {
                    self.refill_cpu_cache_4k_batch(
                        alloc_ptr_4k,
                        cpu_id,
                        thread_ptr,
                        process_ptr,
                        container_ptr,
                        Tracked(&mut *lctx),
                        Tracked(&mut *steps),
                        Tracked(&cache_lock_perm),
                        Tracked(&gp_lock_perm),
                    );
                }
                let (page_ptr, Tracked(page_lock_perm)) = self.pop_stage_4k_page(
                    alloc_ptr_4k, cpu_id, thread_ptr, container_ptr,
                    Tracked(&mut *lctx), Tracked(&cache_lock_perm), Tracked(thread_lock_perm),
                );
                self.wunlock_allocator_global_pool(
                    alloc_ptr_4k, Tracked(&mut *lctx), Tracked(gp_lock_perm),
                );
                self.wunlock_allocator_cache(
                    alloc_ptr_4k, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm),
                );
                proof {
                    assert(allocator_objects_unlocked(
                        self.allocator_4k_map, lctx.thread_id(),
                    )) by {
                        reveal(KernelK::allocator_objects_unlocked_except_cache_pool);
                    };
                    self.kernel_step_boundary(&mut *lctx, &mut *steps);
                    assert(thread_objects_unlocked_except(
                        old(self).thread_map, old(lctx).thread_id(), set![thread_ptr],
                    ) ==> thread_objects_unlocked_except(
                        self.thread_map, lctx.thread_id(), set![thread_ptr],
                    )) by {
                        reveal(thread_objects_unlocked_except);
                    };
                }
                return (page_ptr, Tracked(page_lock_perm));
            }
            let (page_ptr, Tracked(page_lock_perm)) = self.pop_stage_4k_page(
                alloc_ptr_4k, cpu_id, thread_ptr, container_ptr,
                Tracked(&mut *lctx), Tracked(&cache_lock_perm), Tracked(thread_lock_perm),
            );
            self.wunlock_allocator_cache(
                alloc_ptr_4k, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm),
            );
            proof {
                assert(allocator_objects_unlocked(
                    self.allocator_4k_map, lctx.thread_id(),
                )) by {
                    reveal(KernelK::allocator_objects_unlocked_except_cache_pool);
                };
                self.kernel_step_boundary(&mut *lctx, &mut *steps);
                assert(thread_objects_unlocked_except(
                    old(self).thread_map, old(lctx).thread_id(), set![thread_ptr],
                ) ==> thread_objects_unlocked_except(
                    self.thread_map, lctx.thread_id(), set![thread_ptr],
                )) by {
                    reveal(thread_objects_unlocked_except);
                };
            }
            return (page_ptr, Tracked(page_lock_perm));
        }

        let Tracked(gp_lock_perm) = self.wlock_allocator_global_pool(
            alloc_ptr_4k, Tracked(&mut *lctx),
        );
        proof {
            assert(Self::allocator_objects_unlocked_except_cache_pool(
                self.allocator_4k_map, alloc_ptr_4k, lctx.thread_id(),
            )) by {
                reveal(KernelK::allocator_objects_unlocked_except_cache_pool);
            };
        }
        assert(self.allocator_4k_map.perms_wf()) by {
            reveal(allocator_perms_wf);
        };
        let pool_ref = self.allocator_4k_map.borrow_global_pool(
            alloc_ptr_4k, Tracked(&gp_lock_perm),
        );
        let pool_len = pool_ref.len();

        if pool_len > 0 {
            self.refill_cpu_cache_4k_batch(
                alloc_ptr_4k,
                cpu_id,
                thread_ptr,
                process_ptr,
                container_ptr,
                Tracked(&mut *lctx),
                Tracked(&mut *steps),
                Tracked(&cache_lock_perm),
                Tracked(&gp_lock_perm),
            );
            let (page_ptr, Tracked(page_lock_perm)) = self.pop_stage_4k_page(
                alloc_ptr_4k, cpu_id, thread_ptr, container_ptr,
                Tracked(&mut *lctx), Tracked(&cache_lock_perm), Tracked(thread_lock_perm),
            );
            self.wunlock_allocator_global_pool(
                alloc_ptr_4k, Tracked(&mut *lctx), Tracked(gp_lock_perm),
            );
            self.wunlock_allocator_cache(
                alloc_ptr_4k, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm),
            );
            proof {
                assert(allocator_objects_unlocked(
                    self.allocator_4k_map, lctx.thread_id(),
                )) by {
                    reveal(KernelK::allocator_objects_unlocked_except_cache_pool);
                };
                self.kernel_step_boundary(&mut *lctx, &mut *steps);
                assert(thread_objects_unlocked_except(
                    old(self).thread_map, old(lctx).thread_id(), set![thread_ptr],
                ) ==> thread_objects_unlocked_except(
                    self.thread_map, lctx.thread_id(), set![thread_ptr],
                )) by {
                    reveal(thread_objects_unlocked_except);
                };
            }
            return (page_ptr, Tracked(page_lock_perm));
        }

        self.wunlock_allocator_global_pool(
            alloc_ptr_4k, Tracked(&mut *lctx), Tracked(gp_lock_perm),
        );
        self.wunlock_allocator_cache(
            alloc_ptr_4k, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm),
        );
            proof {
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
                self.kernel_step_boundary(&mut *lctx, &mut *steps);
                assert(self.allocator_4k_map.dom().contains(alloc_ptr_4k)) by {
                    reveal(container_allocator_wf);
                };
                assert(thread_objects_unlocked_except(
                    old(self).thread_map, old(lctx).thread_id(), set![thread_ptr],
                ) ==> thread_objects_unlocked_except(
                    self.thread_map, lctx.thread_id(), set![thread_ptr],
                )) by {
                    reveal(thread_objects_unlocked_except);
                };
        }
        self.alloc_4k_scan_all_caches_and_pool(
            alloc_ptr_4k, thread_ptr, process_ptr, container_ptr,
            Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm),
        )
    }

    // ================================================================
    // Case 3: scan all caches + global pool after an internal boundary.
    // ================================================================

    #[verifier::spinoff_prover]
    fn alloc_4k_scan_all_caches_and_pool(
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(self).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(self).thread_map.dom().contains(thread_ptr),
            old(self).process_map.dom().contains(process_ptr),
            old(self).process_map.spec_index(process_ptr).view_rodata()
                .view().owning_container == container_ptr,
            old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
            old(self).process_map.spec_index(process_ptr)
                .locked_by_thread(old(lctx).thread_id()),
            old(self).container_map.dom().contains(container_ptr),
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            old(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            old(self).thread_map.spec_index(thread_ptr).view().owning_container
                == container_ptr,
            old(self).container_map.spec_index(container_ptr)
                .view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(self).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(self).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
            old(self).thread_map.spec_index(thread_ptr)
                .locked_by_thread(old(lctx).thread_id()),
            page_objects_unlocked(
                old(self).page_array, old(lctx).thread_id()),
            allocator_objects_unlocked(
                old(self).allocator_4k_map, old(lctx).thread_id()),
            lock_id_aligned(old(self), old(lctx)),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
            thread_effective_quota_4k(old(self).thread_map.spec_index(thread_ptr)) >= 1,
            old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        ensures
            final(self).inv(),
            final(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            final(self).thread_map.spec_index(thread_ptr).view().owning_proc
                == old(self).thread_map.spec_index(thread_ptr).view().owning_proc,
            final(self).thread_map.spec_index(thread_ptr).view().owning_container
                == old(self).thread_map.spec_index(thread_ptr).view().owning_container,
            final(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                == old(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr,
            thread_lock_perm.lock_id() == final(self).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            final(self).thread_map.lock_id_by_key(thread_ptr)
                == old(self).thread_map.lock_id_by_key(thread_ptr),
            final(self).process_map.dom().contains(process_ptr),
            final(self).process_map.spec_index(process_ptr)
                == old(self).process_map.spec_index(process_ptr),
            final(self).process_map.lock_id_by_key(process_ptr)
                == old(self).process_map.lock_id_by_key(process_ptr),
            final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx)),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            lock_id_aligned(final(self), final(lctx)),
            final(self).container_map.dom().contains(container_ptr),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            page_ptr_valid(ret.0),
            index_valid(NUM_PAGES, page_ptr2page_index(ret.0)),
            final(self).page_array.spec_index(page_ptr2page_index(ret.0)).view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(self).page_array.spec_index(page_ptr2page_index(ret.0)).view().locking_thread()->Write_lock_id,
            final(self).page_array.spec_index(page_ptr2page_index(ret.0)).view()
                .wlocked_by(final(lctx)),
            page_objects_unlocked_except(
                final(self).page_array, final(lctx).thread_id(),
                set![page_ptr2page_index(ret.0)]),
            forall|i: PageIndex|
                #![trigger final(self).page_array.spec_index(i)]
                index_valid(NUM_PAGES, i)
                    && i != page_ptr2page_index(ret.0)
                    && final(self).page_array.spec_index(i).view()
                        .locked_by_thread(final(lctx).thread_id())
                ==> old(self).page_array.spec_index(i).view()
                    .locked_by_thread(old(lctx).thread_id()),
            final(self).thread_map.dom().contains(thread_ptr),
            final(self).thread_map.spec_index(thread_ptr).wlocked_by(final(lctx)),
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((
                final(self).page_array.lock_id_by_index(page_ptr2page_index(ret.0)),
                KernelObjId::Page(page_ptr2page_index(ret.0)),
            )),
            held_containers_unchanged(
                old(self).container_map, final(self).container_map, old(lctx)),
            held_processes_unchanged(
                old(self).process_map, final(self).process_map, old(lctx)),
            held_endpoints_unchanged(
                old(self).endpoint_map, final(self).endpoint_map, old(lctx)),
            held_schedulers_unchanged(
                old(self).scheduler_map, final(self).scheduler_map, old(lctx)),
            held_pcid_allocators_unchanged(
                old(self).pcid_allocator_map, final(self).pcid_allocator_map,
                old(lctx)),
            held_pagetables_unchanged(
                old(self).pagetable_map, final(self).pagetable_map, old(lctx)),
            held_iommu_tables_unchanged(
                old(self).iommu_table_map, final(self).iommu_table_map, old(lctx)),
            held_cpus_unchanged(
                old(self).cpu_array, final(self).cpu_array, old(lctx)),
            thread_objects_unlocked_except(
                old(self).thread_map, old(lctx).thread_id(), set![thread_ptr],
            ) ==> thread_objects_unlocked_except(
                final(self).thread_map, final(lctx).thread_id(), set![thread_ptr],
            ),
            allocator_objects_unlocked(
                old(self).allocator_2m_map, old(lctx).thread_id(),
            ) ==> allocator_objects_unlocked(
                final(self).allocator_2m_map, final(lctx).thread_id(),
            ),
            allocator_objects_unlocked(
                old(self).allocator_1g_map, old(lctx).thread_id(),
            ) ==> allocator_objects_unlocked(
                final(self).allocator_1g_map, final(lctx).thread_id(),
            ),
            allocator_objects_unlocked(
                final(self).allocator_4k_map, final(lctx).thread_id()),
            final(self).container_map.spec_index(container_ptr).view_rodata()
                == old(self).container_map.spec_index(container_ptr).view_rodata(),
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
                =~= old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().insert(ret.0),
            final(self).page_array.spec_index(page_ptr2page_index(ret.0)).view().view().state == (PageState::Owned4k{ thread_ptr }),
            final(self).page_array.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container
                == container_ptr,
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m,
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            final(self).thread_map.spec_index(thread_ptr).view().quota_4k
                == old(self).thread_map.spec_index(thread_ptr).view().quota_4k,
            final(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_fields_equal(
                    &old(self).thread_map.spec_index(thread_ptr).view(),
                ),
            final(self).thread_map.spec_index(thread_ptr).view().endpoint_descriptors
                == old(self).thread_map.spec_index(thread_ptr).view().endpoint_descriptors,
    {
        let (cache_perms, pool_perm) = self.wlock_all_caches_and_global_pool(
            alloc_ptr_4k, thread_ptr, process_ptr, Tracked(&mut *lctx),
        );

        let tracked cache_perms_ref = cache_perms.borrow();
        let (found, slot) = self.scan_caches_and_alloc(
            alloc_ptr_4k, thread_ptr, process_ptr, container_ptr,
            Tracked(&mut *lctx), Tracked(cache_perms_ref), Tracked(thread_lock_perm),
        );

        if found {
            // A cache held a free page: it is popped + staged, page slot held.
            // Release the page, every cache, then the pool, and close the step.
            let (_scan_cpu, page_ptr, Tracked(page_lock_perm)) = slot.unwrap();
            // Keep the page slot write-locked so it rides across the boundary as
            // a held object (its state is pinned); release the caches + pool.
            self.wunlock_all_caches(
                alloc_ptr_4k, thread_ptr, process_ptr,
                page_ptr2page_index(page_ptr),
                Tracked(&mut *lctx), Tracked(cache_perms.get()),
            );
            self.wunlock_allocator_global_pool(alloc_ptr_4k, Tracked(&mut *lctx), Tracked(pool_perm.get()));

            proof {
                assert(allocator_objects_unlocked(
                    self.allocator_4k_map, lctx.thread_id(),
                )) by {
                    reveal(KernelK::allocator_objects_unlocked_except_cache_pool);
                    reveal(KernelK::allocator_caches_unlocked);
                };
                self.kernel_step_boundary(&mut *lctx, &mut *steps);
                assert(thread_objects_unlocked_except(
                    old(self).thread_map, old(lctx).thread_id(), set![thread_ptr],
                ) ==> thread_objects_unlocked_except(
                    self.thread_map, lctx.thread_id(), set![thread_ptr],
                )) by {
                    reveal(thread_objects_unlocked_except);
                };
            }
            return (page_ptr, Tracked(page_lock_perm));
        }

        // Every cache was empty. By conservation the free pages must sit in the
        // global pool: total_free_pages == pool.len() + Σ cache.len(), the caches
        // are all empty, and the held thread still has effective_quota_4k >= 1,
        // so total_free_pages >= 1 and hence pool.len() >= 1.
        assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().len() > 0) by {
            assert(self.container_map.spec_index(container_ptr).view_user_ghost()
                .owned_threads.view().contains(thread_ptr)) by {
                reveal(container_thread_wf);
            };
            lemma_scan_fail_pool_nonempty(self, container_ptr, alloc_ptr_4k, thread_ptr);
            reveal(allocator_perms_wf);
            self.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().lemma_len_view();
        };
        let (page_ptr, Tracked(page_lock_perm)) = self.pop_stage_global_4k_page(
            alloc_ptr_4k, thread_ptr, container_ptr,
            Tracked(&mut *lctx), Tracked(pool_perm.borrow()), Tracked(thread_lock_perm),
        );
        // Keep the page slot write-locked so it rides across the boundary as a
        // held object (its state is pinned); release the caches + pool.
        let tracked cache_perms_ref = cache_perms.borrow();
        assert(Self::cache_perms_match_lctx(
            self.allocator_4k_map, alloc_ptr_4k, &*lctx,
            cache_perms_ref,
        )) by {
            reveal(KernelK::cache_perms_match_lctx);
        };
        assert(Self::allocator_objects_unlocked_except_cache_pool(
            self.allocator_4k_map, alloc_ptr_4k, lctx.thread_id(),
        )) by {
            reveal(KernelK::allocator_objects_unlocked_except_cache_pool);
        };
        self.wunlock_all_caches(
            alloc_ptr_4k, thread_ptr, process_ptr,
            page_ptr2page_index(page_ptr),
            Tracked(&mut *lctx), Tracked(cache_perms.get()),
        );
        self.wunlock_allocator_global_pool(alloc_ptr_4k, Tracked(&mut *lctx), Tracked(pool_perm.get()));

        proof {
            assert(allocator_objects_unlocked(
                self.allocator_4k_map, lctx.thread_id(),
            )) by {
                reveal(KernelK::allocator_objects_unlocked_except_cache_pool);
                reveal(KernelK::allocator_caches_unlocked);
            };
            self.kernel_step_boundary(&mut *lctx, &mut *steps);
            assert(thread_objects_unlocked_except(
                old(self).thread_map, old(lctx).thread_id(), set![thread_ptr],
            ) ==> thread_objects_unlocked_except(
                self.thread_map, lctx.thread_id(), set![thread_ptr],
            )) by {
                reveal(thread_objects_unlocked_except);
            };
        }
        (page_ptr, Tracked(page_lock_perm))
    }

    /// Move one allocator-owned free 4K page from the global pool into a CPU
    /// cache. The page slot is locked while its redundant location tag changes.
    #[verifier::spinoff_prover]
    fn move_global_pool_head_to_cache_4k_one(
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        cpu_id: CpuId,
        thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(cache_lock_perm): Tracked<&LockPerm>,
        Tracked(global_pool_lock_perm): Tracked<&LockPerm>,
    )
        requires
            old(self).inv(),
            index_valid(NUM_CPUS, cpu_id),
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            Self::allocator_objects_unlocked_except_cache_pool(
                old(self).allocator_4k_map, alloc_ptr_4k,
                old(lctx).thread_id()),
            old(self).thread_map.dom().contains(thread_ptr),
            old(self).thread_map.spec_index(thread_ptr)
                .locked_by_thread(old(lctx).thread_id()),
            old(self).process_map.dom().contains(process_ptr),
            old(self).process_map.spec_index(process_ptr)
                .locked_by_thread(old(lctx).thread_id()),
            old(self).cpu_array.spec_index(cpu_id).view()
                .locked_by_thread(old(lctx).thread_id()),
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view()
                .locked_by_thread(old(lctx).thread_id()),
            cache_lock_perm.state() is WriteLock,
            cache_lock_perm.thread_id() == old(lctx).thread_id(),
            cache_lock_perm.lock_id() == old(self).allocator_4k_map
                .spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view()
                .locking_thread()->Write_lock_id,
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.wlocked_by(old(lctx)),
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.locked_by_thread(old(lctx).thread_id()),
            global_pool_lock_perm.state() is WriteLock,
            global_pool_lock_perm.thread_id() == old(lctx).thread_id(),
            global_pool_lock_perm.lock_id() == old(self).allocator_4k_map
                .spec_index(alloc_ptr_4k).global_pool
                .locking_thread()->Write_lock_id,
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.view().view().len() > 0,
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view().view().view().len() < ALLOCATOR_MAX_WATERMARK,
            page_ptr_valid(old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.view().view().spec_index(0)),
            page_objects_unlocked(
                old(self).page_array, old(lctx).thread_id()),
            old(lctx).kernel_view_locking_state() is Acquire,
            lock_id_aligned(old(self), old(lctx)),
            old(lctx).lock_id_acyclic(old(self).page_array.lock_id_by_index(
                page_ptr2page_index(old(self).allocator_4k_map
                    .spec_index(alloc_ptr_4k).global_pool.view().view().spec_index(0)))),
        ensures
            final(self).inv(),
            Self::allocator_objects_unlocked_except_cache_pool(
                final(self).allocator_4k_map, alloc_ptr_4k,
                final(lctx).thread_id()),
            forall|other_cpu: CpuId|
                #![trigger final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.spec_index(other_cpu).view()
                    .locked_by_thread(final(lctx).thread_id())]
                index_valid(NUM_CPUS, other_cpu)
                ==> final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(other_cpu).view()
                        .locked_by_thread(final(lctx).thread_id())
                    == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(other_cpu).view()
                        .locked_by_thread(old(lctx).thread_id()),
            final(self).thread_map.spec_index(thread_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            final(self).process_map.dom().contains(process_ptr),
            final(self).process_map.spec_index(process_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            final(self).cpu_array.spec_index(cpu_id).view()
                .locked_by_thread(final(lctx).thread_id()),
            kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
            page_objects_unlocked(
                final(self).page_array, final(lctx).thread_id()),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).lock_id_set() =~= old(lctx).lock_id_set(),
            lock_id_aligned(final(self), final(lctx)),
            final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.view().view().len() + 1
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.view().view().len(),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view().view().view().len()
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.spec_index(cpu_id).view().view().view().len() + 1,
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view().wlocked_by(final(lctx)),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view()
                .locked_by_thread(final(lctx).thread_id()),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).lock_id()
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.spec_index(cpu_id).lock_id(),
            cache_lock_perm.lock_id() == final(self).allocator_4k_map
                .spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view()
                .locking_thread()->Write_lock_id,
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.wlocked_by(final(lctx)),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.locked_by_thread(final(lctx).thread_id()),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.lock_id()
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.lock_id(),
            global_pool_lock_perm.lock_id() == final(self).allocator_4k_map
                .spec_index(alloc_ptr_4k).global_pool
                .locking_thread()->Write_lock_id,
            held_pages_unchanged(
                old(self).page_array, final(self).page_array, old(lctx)),
            final(self).pagetable_map == old(self).pagetable_map,
            final(self).cpu_array == old(self).cpu_array,
            final(self).cpu_tlb == old(self).cpu_tlb,
            final(self).root_container == old(self).root_container,
            final(self).container_map == old(self).container_map,
            final(self).scheduler_map == old(self).scheduler_map,
            final(self).process_map == old(self).process_map,
            final(self).thread_map == old(self).thread_map,
            final(self).endpoint_map == old(self).endpoint_map,
            final(self).pcid_allocator_map == old(self).pcid_allocator_map,
            final(self).iommu_root_table == old(self).iommu_root_table,
            final(self).iommu_table_map == old(self).iommu_table_map,
            final(self).iommu_tlb == old(self).iommu_tlb,
            final(self).allocator_2m_map == old(self).allocator_2m_map,
            final(self).allocator_1g_map == old(self).allocator_1g_map,
            final(self).default_pagetable == old(self).default_pagetable,
    {
        assert(
            self.allocator_4k_map.perms_wf()
            && self.allocator_4k_map.spec_index(alloc_ptr_4k).wf()
            && self.page_array.inv()
            && page_array_wf(self.page_array)
        ) by {
            reveal(allocator_perms_wf);
            reveal(page_array_wf);
        };
        assert(self.allocator_4k_map.spec_index(alloc_ptr_4k)
            .global_pool.view().linked_list.len() != 0) by {
            self.allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.view().lemma_len_view();
        };
        assert({
            let page_index = page_ptr2page_index(
                self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.view().view().spec_index(0));
            &&& self.page_array.spec_index(page_index).view().view().state
                == PageState::Free4k {
                    allocator_ptr: Ghost(alloc_ptr_4k),
                    state: FreePageAllocatorState::GlobalList,
                }
            &&& self.allocator_4k_map.dom().contains(alloc_ptr_4k)
            &&& self.page_array.spec_index(page_index).view().view().owning_container
                == self.allocator_4k_map.spec_index(alloc_ptr_4k).owning_container
        }) by {
            reveal(container_allocator_free_4k_page_wf);
            reveal(container_allocator_global_free_4k_page_wf);
        };
        assert(
            !self.allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view().view().view().contains(
                    self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .global_pool.view().view().spec_index(0),
                )
        ) by {
            reveal(container_allocator_free_4k_page_wf);
            reveal(container_allocator_cpu_cache_free_4k_page_wf);
            reveal(allocator_free_page_ptrs_wf);
            reveal(LinkedList::wf_value_list);
        };
        let (expected_node_addr, expected_page_ptr) = {
            let pool_ref = self.allocator_4k_map.borrow_global_pool(
                alloc_ptr_4k, Tracked(global_pool_lock_perm),
            );
            pool_ref.peek_head()
        };
        let page_index = page_ptr2page_index(expected_page_ptr);
        assert(index_valid(NUM_PAGES, page_index)) by {
            page_ptr_valid_imply_page_index_valid();
        };
        let Tracked(page_lock_perm) = self.wlock_page(
            page_index, Tracked(&mut *lctx),
        );
        assert(self.page_array.inv()) by {
            reveal(page_array_wf);
        };
        let (node_addr, page_ptr) = {
            let allocator = self.allocator_4k_map.borrow_mut(alloc_ptr_4k);
            allocator.move_global_pool_head_to_cache(
                cpu_id,
                Tracked(&*lctx),
                Tracked(cache_lock_perm),
                Tracked(global_pool_lock_perm),
            )
        };
        assert(node_addr == expected_node_addr) by {
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.view().linked_list.lemma_value_addr_unique(
                    node_addr, expected_node_addr,
                );
        };
        assert(
            node_addr == old(self).page_array.spec_index(
                page_ptr2page_index(page_ptr),
            ).view().view().free_list_node_storage.addr()
        ) by {
            reveal(container_allocator_free_4k_page_wf);
            reveal(container_allocator_global_free_4k_page_wf);
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.view().linked_list
                .lemma_value_addr_unique(
                    node_addr,
                    old(self).page_array.spec_index(
                        page_ptr2page_index(page_ptr),
                    ).view().view().free_list_node_storage.addr(),
                );
        };
        let page = self.page_array.borrow_mut(
            page_index, Tracked(&*lctx), Tracked(&page_lock_perm),
        );
        page.state = PageState::Free4k {
            allocator_ptr: Ghost(alloc_ptr_4k),
            state: FreePageAllocatorState::PreCpuCache { cpu_id },
        };
        assert(lock_id_aligned(self, &*lctx)) by {
            reveal(lock_id_aligned);
        };
        proof {
            assert(page_array_wf(self.page_array)) by {
                reveal(page_array_wf);
            };
            assert(self.subsystems_inv()) by {
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
                assert(container_page_owner_wf(
                    self.container_map,
                    self.page_array,
                )) by {
                    container_page_owner_wf_preserved_for_owning_container_eq(old(self).container_map, self.container_map, old(self).page_array, self.page_array);
                };
                assert(hugepage_2m_wf(self.page_array)) by {
                    hugepage_2m_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array);
                };
                assert(hugepage_1g_wf(self.page_array)) by {
                    hugepage_1g_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array);
                };
                assert(page_pagetable_wf(
                    self.pagetable_map,
                    self.page_array,
                )) by {
                    page_pagetable_wf_preserved_for_nonmapped_page_change(old(self).pagetable_map, self.pagetable_map, old(self).page_array, self.page_array, page_ptr2page_index(page_ptr));
                };
                assert(container_process_page_pagetable_wf(
                    self.container_map,
                    self.process_map,
                    self.pagetable_map,
                    self.page_array,
                )) by {
                    reveal(container_process_page_pagetable_wf);
                    reveal(container_process_wf);
                    reveal(process_pagetable_match);
                    reveal(container_page_owner_wf);
                    reveal(mapped_4k_page_pagetable_wf);
                    reveal(mapped_2m_page_pagetable_wf);
                    reveal(mapped_1g_page_pagetable_wf);
                };
                assert(container_pages_wf(
                    self.page_array,
                    self.container_map,
                )) by {
                    container_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).container_map, self.container_map);
                };
                assert(process_pages_wf(
                    self.page_array,
                    self.process_map,
                )) by {
                    process_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).process_map, self.process_map);
                };
                assert(pagetable_pages_wf(
                    self.pagetable_map,
                    self.page_array,
                )) by {
                    reveal(pagetable_pages_wf);
                };
                assert(iommu_table_pages_wf(
                    self.iommu_table_map,
                    self.page_array,
                )) by {
                    reveal(iommu_table_pages_wf);
                };
                assert(pcid_allocator_pages_wf(
                    self.page_array,
                    self.pcid_allocator_map,
                )) by {
                    pcid_allocator_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).pcid_allocator_map, self.pcid_allocator_map);
                };
                assert(thread_pages_wf(
                    self.thread_map,
                    self.page_array,
                )) by {
                    thread_pages_wf_preserved_for_page_state_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array);
                };
                assert(thread_staged_pages_wf(
                    self.thread_map,
                    self.page_array,
                )) by {
                    thread_staged_pages_4k_wf_preserved_for_eq(
                        old(self).thread_map,
                        self.thread_map,
                        old(self).page_array,
                        self.page_array,
                    );
                    thread_staged_pages_2m_wf_preserved_for_eq(
                        old(self).thread_map,
                        self.thread_map,
                        old(self).page_array,
                        self.page_array,
                    );
                    thread_staged_pages_1g_wf_preserved_for_eq(
                        old(self).thread_map,
                        self.thread_map,
                        old(self).page_array,
                        self.page_array,
                    );
                };
                assert(endpoint_pages_wf(
                    self.endpoint_map,
                    self.page_array,
                )) by {
                    endpoint_pages_wf_preserved_for_page_state_eq(old(self).endpoint_map, self.endpoint_map, old(self).page_array, self.page_array);
                };
                assert(allocator_free_page_ptrs_wf(
                    self.allocator_4k_map,
                )) by {
                    reveal(allocator_free_page_ptrs_wf);
                    seq_skip_lemma::<PagePtr>();
                    seq_push_head_lemma::<PagePtr>();
                };
                assert(container_process_allocator_quota_4k_wf(
                    self.container_map,
                    self.process_map,
                    self.thread_map,
                    self.allocator_4k_map,
                )) by {
                    reveal(container_process_allocator_quota_4k_wf);
                    reveal(container_allocator_wf);
                };
                assert(container_allocator_wf(
                    self.container_map,
                    self.allocator_4k_map,
                    self.allocator_2m_map,
                    self.allocator_1g_map,
                )) by {
                    reveal(container_allocator_wf);
                };
                assert(container_allocator_global_free_4k_page_wf(
                    self.allocator_4k_map,
                    self.page_array,
                )) by {
                    reveal(container_allocator_free_4k_page_wf);
                    reveal(container_allocator_global_free_4k_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                    page_ptr_valid_imply_page_index_valid();
                    page_index_roundtrip();
                    page_ptr2page_index_injective();
                    seq_skip_lemma::<PagePtr>();
                };
                assert(container_allocator_cpu_cache_free_4k_page_wf(
                    self.allocator_4k_map,
                    self.page_array,
                )) by {
                    reveal(container_allocator_free_4k_page_wf);
                    reveal(container_allocator_cpu_cache_free_4k_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                    page_ptr_valid_imply_page_index_valid();
                    page_ptr_roundtrip();
                    seq_push_head_lemma::<PagePtr>();
                };
                assert(container_allocator_free_4k_page_wf(
                    self.allocator_4k_map,
                    self.page_array,
                )) by {
                    reveal(container_allocator_free_4k_page_wf);
                };
                assert(container_allocator_global_free_2m_page_wf(
                    self.allocator_2m_map,
                    self.page_array,
                )) by {
                    reveal(container_allocator_free_2m_page_wf);
                    reveal(container_allocator_global_free_2m_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(container_allocator_cpu_cache_free_2m_page_wf(
                    self.allocator_2m_map,
                    self.page_array,
                )) by {
                    reveal(container_allocator_free_2m_page_wf);
                    reveal(container_allocator_cpu_cache_free_2m_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(container_allocator_free_2m_page_wf(
                    self.allocator_2m_map,
                    self.page_array,
                )) by {
                    reveal(container_allocator_free_2m_page_wf);
                };
                assert(container_allocator_global_free_1g_page_wf(
                    self.allocator_1g_map,
                    self.page_array,
                )) by {
                    reveal(container_allocator_free_1g_page_wf);
                    reveal(container_allocator_global_free_1g_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(container_allocator_cpu_cache_free_1g_page_wf(
                    self.allocator_1g_map,
                    self.page_array,
                )) by {
                    reveal(container_allocator_free_1g_page_wf);
                    reveal(container_allocator_cpu_cache_free_1g_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(container_allocator_free_1g_page_wf(
                    self.allocator_1g_map,
                    self.page_array,
                )) by {
                    reveal(container_allocator_free_1g_page_wf);
                };
            };
        }
        self.wunlock_page(
            page_index, Tracked(&mut *lctx), Tracked(page_lock_perm),
        );
        proof {
            assert(Self::allocator_objects_unlocked_except_cache_pool(
                self.allocator_4k_map, alloc_ptr_4k, lctx.thread_id(),
            )) by {
                reveal(KernelK::allocator_objects_unlocked_except_cache_pool);
            };
            assert(
                kernel_k_to_kernel_u(*self)
                    == kernel_k_to_kernel_u(*old(self))
            ) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
            };
        }
    }

    /// Refill a low-water 4K CPU cache from the global pool, moving at most one
    /// allocator batch. Each relocation is KernelU-neutral; a boundary restores
    /// Acquire before the next page.
    fn refill_cpu_cache_4k_batch(
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        cpu_id: CpuId,
        thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(cache_lock_perm): Tracked<&LockPerm>,
        Tracked(global_pool_lock_perm): Tracked<&LockPerm>,
    )
        requires
            old(self).inv(),
            index_valid(NUM_CPUS, cpu_id),
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            Self::allocator_objects_unlocked_except_cache_pool(
                old(self).allocator_4k_map, alloc_ptr_4k,
                old(lctx).thread_id()),
            old(self).thread_map.dom().contains(thread_ptr),
            old(self).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
            old(self).thread_map.spec_index(thread_ptr)
                .locked_by_thread(old(lctx).thread_id()),
            old(self).process_map.dom().contains(process_ptr),
            old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
            old(self).process_map.spec_index(process_ptr)
                .locked_by_thread(old(lctx).thread_id()),
            old(self).process_map.spec_index(process_ptr).view_rodata()
                .view().owning_container == container_ptr,
            old(self).container_map.dom().contains(container_ptr),
            old(self).thread_map.spec_index(thread_ptr).view()
                .owning_container == container_ptr,
            old(self).cpu_array.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            old(self).cpu_array.spec_index(cpu_id).view()
                .locked_by_thread(old(lctx).thread_id()),
            page_objects_unlocked(
                old(self).page_array, old(lctx).thread_id()),
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view().view().view().len() <= ALLOCATOR_MIN_WATERMARK + 1,
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.view().view().len() > 0,
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view()
                .locked_by_thread(old(lctx).thread_id()),
            cache_lock_perm.state() is WriteLock,
            cache_lock_perm.thread_id() == old(lctx).thread_id(),
            cache_lock_perm.lock_id() == old(self).allocator_4k_map
                .spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view()
                .locking_thread()->Write_lock_id,
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.wlocked_by(old(lctx)),
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.locked_by_thread(old(lctx).thread_id()),
            global_pool_lock_perm.state() is WriteLock,
            global_pool_lock_perm.thread_id() == old(lctx).thread_id(),
            global_pool_lock_perm.lock_id() == old(self).allocator_4k_map
                .spec_index(alloc_ptr_4k).global_pool
                .locking_thread()->Write_lock_id,
            old(lctx).kernel_view_locking_state() is Acquire,
            lock_id_aligned(old(self), old(lctx)),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
            old(lctx).held_lock_majors_le(ALLOCATOR_GLOBAL_POLL_MAJOR),
        ensures
            final(self).inv(),
            Self::allocator_objects_unlocked_except_cache_pool(
                final(self).allocator_4k_map, alloc_ptr_4k,
                final(lctx).thread_id()),
            forall|other_cpu: CpuId|
                #![trigger final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.spec_index(other_cpu).view()
                    .locked_by_thread(final(lctx).thread_id())]
                index_valid(NUM_CPUS, other_cpu)
                ==> final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(other_cpu).view()
                        .locked_by_thread(final(lctx).thread_id())
                    == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(other_cpu).view()
                        .locked_by_thread(old(lctx).thread_id()),
            page_objects_unlocked(
                final(self).page_array, final(lctx).thread_id()),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).lock_id_set() =~= old(lctx).lock_id_set(),
            lock_id_aligned(final(self), final(lctx)),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            final(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            final(self).thread_map.dom().contains(thread_ptr),
            final(self).thread_map.spec_index(thread_ptr)
                == old(self).thread_map.spec_index(thread_ptr),
            final(self).thread_map.lock_id_by_key(thread_ptr)
                == old(self).thread_map.lock_id_by_key(thread_ptr),
            final(self).thread_map.spec_index(thread_ptr).wlocked_by(final(lctx)),
            final(self).thread_map.spec_index(thread_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            final(self).process_map.dom().contains(process_ptr),
            final(self).process_map.spec_index(process_ptr)
                == old(self).process_map.spec_index(process_ptr),
            final(self).process_map.lock_id_by_key(process_ptr)
                == old(self).process_map.lock_id_by_key(process_ptr),
            final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx)),
            final(self).process_map.spec_index(process_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            final(self).container_map.dom().contains(container_ptr),
            final(self).container_map.spec_index(container_ptr).view_rodata()
                == old(self).container_map.spec_index(container_ptr).view_rodata(),
            held_containers_unchanged(
                old(self).container_map, final(self).container_map, old(lctx)),
            held_processes_unchanged(
                old(self).process_map, final(self).process_map, old(lctx)),
            held_threads_unchanged(
                old(self).thread_map, final(self).thread_map, old(lctx)),
            held_endpoints_unchanged(
                old(self).endpoint_map, final(self).endpoint_map, old(lctx)),
            held_schedulers_unchanged(
                old(self).scheduler_map, final(self).scheduler_map, old(lctx)),
            held_pcid_allocators_unchanged(
                old(self).pcid_allocator_map, final(self).pcid_allocator_map,
                old(lctx)),
            held_pagetables_unchanged(
                old(self).pagetable_map, final(self).pagetable_map, old(lctx)),
            held_iommu_tables_unchanged(
                old(self).iommu_table_map, final(self).iommu_table_map, old(lctx)),
            held_pages_unchanged(
                old(self).page_array, final(self).page_array, old(lctx)),
            held_cpus_unchanged(
                old(self).cpu_array, final(self).cpu_array, old(lctx)),
            allocator_objects_unlocked(
                old(self).allocator_2m_map, old(lctx).thread_id(),
            ) ==> allocator_objects_unlocked(
                final(self).allocator_2m_map, final(lctx).thread_id(),
            ),
            allocator_objects_unlocked(
                old(self).allocator_1g_map, old(lctx).thread_id(),
            ) ==> allocator_objects_unlocked(
                final(self).allocator_1g_map, final(lctx).thread_id(),
            ),
            final(self).cpu_array.spec_index(cpu_id).view() == old(self).cpu_array.spec_index(cpu_id).view(),
            final(self).cpu_array.spec_index(cpu_id).view().wlocked_by(final(lctx)),
            final(self).cpu_array.spec_index(cpu_id).view()
                .locked_by_thread(final(lctx).thread_id()),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view().view().view().len()
                > 0,
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view().wlocked_by(final(lctx)),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view()
                .locked_by_thread(final(lctx).thread_id()),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).lock_id()
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.spec_index(cpu_id).lock_id(),
            cache_lock_perm.lock_id() == final(self).allocator_4k_map
                .spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view()
                .locking_thread()->Write_lock_id,
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.wlocked_by(final(lctx)),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.locked_by_thread(final(lctx).thread_id()),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.lock_id()
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.lock_id(),
            global_pool_lock_perm.lock_id() == final(self).allocator_4k_map
                .spec_index(alloc_ptr_4k).global_pool
                .locking_thread()->Write_lock_id,
    {
        assert(
            self.allocator_4k_map.perms_wf()
            && self.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.is_init()
            && self.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.inv()
        ) by {
            reveal(allocator_perms_wf);
        };
        let pool_ref = self.allocator_4k_map.borrow_global_pool(
            alloc_ptr_4k, Tracked(global_pool_lock_perm),
        );
        let pool_len = pool_ref.len();
        assert(
            pool_len == self.allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.view().view().len()
        ) by {
            pool_ref.lemma_len_view();
        };
        let batch = if pool_len < ALLOCATOR_BATCH {
            pool_len
        } else {
            ALLOCATOR_BATCH
        };
        let mut moved: usize = 0;
        while moved < batch
            invariant
                self.inv(),
                page_objects_unlocked(self.page_array, lctx.thread_id()),
                lctx.thread_id() == old(lctx).thread_id(),
                lctx.kernel_view_locking_state() is Acquire,
                lctx.lock_id_set() == old(lctx).lock_id_set(),
                lock_id_aligned(self, &*lctx),
                steps.steps == old(steps).steps,
                steps.snap_shot == kernel_k_to_kernel_u(*self),
                index_valid(NUM_CPUS, cpu_id),
                self.allocator_4k_map.dom().contains(alloc_ptr_4k),
                Self::allocator_objects_unlocked_except_cache_pool(
                    self.allocator_4k_map, alloc_ptr_4k, lctx.thread_id()),
                forall|other_cpu: CpuId|
                    #![trigger self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(other_cpu).view()
                        .locked_by_thread(lctx.thread_id())]
                    index_valid(NUM_CPUS, other_cpu)
                    ==> self.allocator_4k_map.spec_index(alloc_ptr_4k)
                            .cpu_caches.spec_index(other_cpu).view()
                            .locked_by_thread(lctx.thread_id())
                        == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                            .cpu_caches.spec_index(other_cpu).view()
                            .locked_by_thread(old(lctx).thread_id()),
                self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.spec_index(cpu_id).view().wlocked_by(&*lctx),
                self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.lock_id_by_index(cpu_id)
                    == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.lock_id_by_index(cpu_id),
                cache_lock_perm.state() is WriteLock,
                cache_lock_perm.thread_id() == lctx.thread_id(),
                cache_lock_perm.lock_id() == self.allocator_4k_map
                    .spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view()
                    .locking_thread()->Write_lock_id,
                self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.wlocked_by(&*lctx),
                self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.lock_id()
                    == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .global_pool.lock_id(),
                global_pool_lock_perm.state() is WriteLock,
                global_pool_lock_perm.thread_id() == lctx.thread_id(),
                global_pool_lock_perm.lock_id() == self.allocator_4k_map
                    .spec_index(alloc_ptr_4k).global_pool
                    .locking_thread()->Write_lock_id,
                0 <= moved <= batch <= ALLOCATOR_BATCH,
                0 < batch,
                batch <= pool_len,
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.spec_index(cpu_id).view().view().view().len() <= ALLOCATOR_MIN_WATERMARK + 1,
                batch == if pool_len < ALLOCATOR_BATCH {
                    pool_len
                } else {
                    ALLOCATOR_BATCH
                },
                pool_len == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.view().view().len(),
                self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.view().view().len() + moved == pool_len,
                self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.spec_index(cpu_id).view().view().view().len()
                    == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(cpu_id).view().view().view().len() + moved,
                moved < batch ==> self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.spec_index(cpu_id).view().view().view().len() < ALLOCATOR_MAX_WATERMARK,
                lctx.held_lock_majors_le(ALLOCATOR_GLOBAL_POLL_MAJOR),
                self.thread_map.dom().contains(thread_ptr),
                self.thread_map.spec_index(thread_ptr)
                    == old(self).thread_map.spec_index(thread_ptr),
                self.thread_map.lock_id_by_key(thread_ptr)
                    == old(self).thread_map.lock_id_by_key(thread_ptr),
                self.thread_map.spec_index(thread_ptr).wlocked_by(&*lctx),
                self.thread_map.spec_index(thread_ptr)
                    .locked_by_thread(lctx.thread_id()),
                self.process_map.dom().contains(process_ptr),
                self.process_map.spec_index(process_ptr)
                    == old(self).process_map.spec_index(process_ptr),
                self.process_map.lock_id_by_key(process_ptr)
                    == old(self).process_map.lock_id_by_key(process_ptr),
                self.process_map.spec_index(process_ptr).wlocked_by(&*lctx),
                self.process_map.spec_index(process_ptr)
                    .locked_by_thread(lctx.thread_id()),
                self.process_map.spec_index(process_ptr).view_rodata()
                    .view().owning_container == container_ptr,
                self.thread_map.spec_index(thread_ptr).view()
                    .owning_container == container_ptr,
                self.container_map.dom().contains(container_ptr),
                self.container_map.spec_index(container_ptr).view_rodata()
                    == old(self).container_map.spec_index(container_ptr).view_rodata(),
                held_containers_unchanged(
                    old(self).container_map, self.container_map, old(lctx)),
                held_processes_unchanged(
                    old(self).process_map, self.process_map, old(lctx)),
                held_threads_unchanged(
                    old(self).thread_map, self.thread_map, old(lctx)),
                held_endpoints_unchanged(
                    old(self).endpoint_map, self.endpoint_map, old(lctx)),
                held_schedulers_unchanged(
                    old(self).scheduler_map, self.scheduler_map, old(lctx)),
                held_pcid_allocators_unchanged(
                    old(self).pcid_allocator_map, self.pcid_allocator_map,
                    old(lctx)),
                held_pagetables_unchanged(
                    old(self).pagetable_map, self.pagetable_map, old(lctx)),
                held_iommu_tables_unchanged(
                    old(self).iommu_table_map, self.iommu_table_map, old(lctx)),
                held_pages_unchanged(
                    old(self).page_array, self.page_array, old(lctx)),
                held_cpus_unchanged(
                    old(self).cpu_array, self.cpu_array, old(lctx)),
                allocator_objects_unlocked(
                    old(self).allocator_2m_map, old(lctx).thread_id(),
                ) ==> allocator_objects_unlocked(
                    self.allocator_2m_map, lctx.thread_id(),
                ),
                allocator_objects_unlocked(
                    old(self).allocator_1g_map, old(lctx).thread_id(),
                ) ==> allocator_objects_unlocked(
                    self.allocator_1g_map, lctx.thread_id(),
                ),
                self.cpu_array.spec_index(cpu_id).view() == old(self).cpu_array.spec_index(cpu_id).view(),
                self.cpu_array.spec_index(cpu_id).view().wlocked_by(&*lctx),
            decreases batch - moved,
        {
            assert({
                let page_ptr = self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.view().view().spec_index(0);
                &&& page_ptr_valid(page_ptr)
                &&& lctx.lock_id_acyclic(self.page_array.lock_id_by_index(
                    page_ptr2page_index(page_ptr)))
            }) by {
                reveal(allocator_free_page_ptrs_wf);
                reveal(allocator_perms_wf);
                page_ptr_valid_imply_page_index_valid();
                reveal(container_allocator_free_4k_page_wf);
                reveal(container_allocator_global_free_4k_page_wf);
            };
            self.move_global_pool_head_to_cache_4k_one(
                alloc_ptr_4k,
                cpu_id,
                thread_ptr,
                process_ptr,
                Tracked(&mut *lctx),
                Tracked(cache_lock_perm),
                Tracked(global_pool_lock_perm),
            );
            moved = moved + 1;
            proof {
                self.kernel_step_boundary(&mut *lctx, &mut *steps);
                assert(Self::allocator_objects_unlocked_except_cache_pool(
                    self.allocator_4k_map, alloc_ptr_4k, lctx.thread_id(),
                )) by {
                    reveal(KernelK::allocator_objects_unlocked_except_cache_pool);
                };
            }
        }
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
            Self::allocator_cache_lock_id(i as CpuId),
            KernelObjId::AllocatorCache(
                PageSize::SZ4k, alloc_ptr_4k, i as CpuId),
        ))
    }

    pub(crate) closed spec fn allocator_cache_lock_entry_prefix(
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        upper: CpuId,
    ) -> Set<HeldLock> {
        Self::allocator_cache_lock_entry_prefix_seq(alloc_ptr_4k, upper).to_set()
    }

    pub(crate) fn wlock_all_caches_and_global_pool(
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
    ) -> (ret: (Tracked<Map<CpuId, LockPerm>>, Tracked<LockPerm>))
        requires
            old(self).inv(),
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            old(self).thread_map.dom().contains(thread_ptr),
            old(self).thread_map.spec_index(thread_ptr)
                .locked_by_thread(old(lctx).thread_id()),
            old(self).process_map.dom().contains(process_ptr),
            old(self).process_map.spec_index(process_ptr)
                .locked_by_thread(old(lctx).thread_id()),
            old(lctx).kernel_view_locking_state() is Acquire,
            lock_id_aligned(old(self), old(lctx)),
            allocator_objects_unlocked(
                old(self).allocator_4k_map, old(lctx).thread_id()),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        ensures
            final(self).inv(),
            final(self).thread_map.spec_index(thread_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            final(self).process_map.dom().contains(process_ptr),
            final(self).process_map.spec_index(process_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
            // ---- only allocator_4k_map lock state moves; every other field byte-equal ----
            final(self).pagetable_map     == old(self).pagetable_map,
            final(self).iommu_table_map     == old(self).iommu_table_map,
            final(self).iommu_root_table     == old(self).iommu_root_table,
            final(self).page_array        == old(self).page_array,
            final(self).cpu_array         == old(self).cpu_array,
            final(self).cpu_tlb           == old(self).cpu_tlb,
            final(self).iommu_tlb           == old(self).iommu_tlb,
            final(self).root_container    == old(self).root_container,
            final(self).container_map     == old(self).container_map,
            final(self).scheduler_map     == old(self).scheduler_map,
            final(self).pcid_allocator_map == old(self).pcid_allocator_map,
            final(self).process_map       == old(self).process_map,
            final(self).thread_map        == old(self).thread_map,
            final(self).endpoint_map      == old(self).endpoint_map,
            final(self).allocator_2m_map  == old(self).allocator_2m_map,
            final(self).allocator_1g_map  == old(self).allocator_1g_map,
            final(self).default_pagetable == old(self).default_pagetable,
            final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
            forall|p: RwLockPageAllocatorPtr|
                #![trigger final(self).allocator_4k_map.spec_index(p)]
                old(self).allocator_4k_map.dom().contains(p) && p != alloc_ptr_4k
                ==> final(self).allocator_4k_map.spec_index(p)
                    == old(self).allocator_4k_map.spec_index(p),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).lock_id_set() =~= old(lctx).lock_id_set()
                + Self::allocator_cache_lock_entry_prefix(
                    alloc_ptr_4k, NUM_CPUS).insert((
                        ret.1.view().ordering_lock_id(),
                        KernelObjId::AllocatorGlobalPoll(
                            PageSize::SZ4k, alloc_ptr_4k),
                    )),
            final(lctx).lock_entry_contains(
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.lock_id(),
                KernelObjId::AllocatorGlobalPoll(
                    PageSize::SZ4k, alloc_ptr_4k,
                )),
            forall|c: CpuId|
                #![trigger final(lctx).lock_id_set().contains((
                    Self::allocator_cache_lock_id(c),
                    KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c)))]
                index_valid(NUM_CPUS, c)
                ==> final(lctx).lock_id_set().contains((
                    Self::allocator_cache_lock_id(c),
                    KernelObjId::AllocatorCache(
                        PageSize::SZ4k, alloc_ptr_4k, c),
                )),
            lock_id_aligned(final(self), final(lctx)),
            // ---- every cache + the pool is write-locked by us, perm recorded ----
            Self::cache_perms_match_lctx(
                final(self).allocator_4k_map, alloc_ptr_4k,
                final(lctx), &ret.0.view()),
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.locking_thread()->Write_lock_id,
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.wlocked_by(final(lctx)),
            // ---- every held id ≤ pool major (caches 106, pool 107, pre-entry ≤ 105) ----
            final(lctx).held_lock_majors_le(ALLOCATOR_GLOBAL_POLL_MAJOR),
            Self::allocator_objects_unlocked_except_cache_pool(
                final(self).allocator_4k_map,
                alloc_ptr_4k,
                final(lctx).thread_id(),
            ),
    {
        let tracked mut cache_perms: Map<CpuId, LockPerm> = Map::tracked_empty();

        let mut cpu: CpuId = 0;
        while cpu < NUM_CPUS
            invariant
                self.inv(),
                self.thread_map.dom().contains(thread_ptr),
                self.thread_map.spec_index(thread_ptr)
                    .locked_by_thread(lctx.thread_id()),
                self.process_map.dom().contains(process_ptr),
                self.process_map.spec_index(process_ptr)
                    .locked_by_thread(lctx.thread_id()),
                lock_id_aligned(self, &*lctx),
                self.allocator_4k_map.dom().contains(alloc_ptr_4k),
                self.pagetable_map     == old(self).pagetable_map,
                self.iommu_table_map     == old(self).iommu_table_map,
                self.iommu_root_table     == old(self).iommu_root_table,
                self.page_array        == old(self).page_array,
                self.cpu_array         == old(self).cpu_array,
                self.cpu_tlb           == old(self).cpu_tlb,
                self.iommu_tlb           == old(self).iommu_tlb,
                self.root_container    == old(self).root_container,
                self.container_map     == old(self).container_map,
                self.scheduler_map     == old(self).scheduler_map,
                self.pcid_allocator_map == old(self).pcid_allocator_map,
                self.process_map       == old(self).process_map,
                self.thread_map        == old(self).thread_map,
                self.endpoint_map      == old(self).endpoint_map,
                self.allocator_2m_map  == old(self).allocator_2m_map,
                self.allocator_1g_map  == old(self).allocator_1g_map,
                self.default_pagetable == old(self).default_pagetable,
                self.allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
                self.allocator_4k_map.spec_index(alloc_ptr_4k).quota
                    == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                forall|p: RwLockPageAllocatorPtr|
                    #![trigger self.allocator_4k_map.spec_index(p)]
                    old(self).allocator_4k_map.dom().contains(p) && p != alloc_ptr_4k
                    ==> self.allocator_4k_map.spec_index(p)
                        == old(self).allocator_4k_map.spec_index(p),
                lctx.thread_id() == old(lctx).thread_id(),
                lctx.kernel_view_locking_state() is Acquire,
                0 <= cpu <= NUM_CPUS,
                lctx.lock_id_set() =~= old(lctx).lock_id_set()
                    + Self::allocator_cache_lock_entry_prefix(
                        alloc_ptr_4k, cpu),
                !self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.wlocked_by(&*lctx),
                forall|c: CpuId|
                    #![trigger self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(c)]
                    index_valid(NUM_CPUS, c) && c >= cpu
                    ==> !self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(c).view().wlocked_by(&*lctx),
                // Caches [0, cpu) are locked, perm collected; [cpu, NUM_CPUS) untouched.
                forall|c: CpuId|
                    #![trigger cache_perms.spec_index(c)]
                    index_valid(NUM_CPUS, c) && c < cpu
                    ==> {
                        &&& cache_perms.dom().contains(c)
                        &&& cache_perms.spec_index(c).state() is WriteLock
                        &&& cache_perms.spec_index(c).thread_id() == lctx.thread_id()
                        &&& cache_perms.spec_index(c).lock_id() == self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(c).view().locking_thread()->Write_lock_id
                        &&& cache_perms.spec_index(c).ordering_lock_id()
                            == Self::allocator_cache_lock_id(c)
                        &&& self.allocator_4k_map.spec_index(alloc_ptr_4k)
                            .cpu_caches.spec_index(c).view().wlocked_by(&*lctx)
                    },
                forall|c: CpuId|
                    #![trigger lctx.lock_id_set().contains((
                        Self::allocator_cache_lock_id(c),
                        KernelObjId::AllocatorCache(
                            PageSize::SZ4k, alloc_ptr_4k, c)))]
                    index_valid(NUM_CPUS, c) && c < cpu
                    ==> lctx.lock_id_set().contains((
                        Self::allocator_cache_lock_id(c),
                        KernelObjId::AllocatorCache(
                            PageSize::SZ4k, alloc_ptr_4k, c),
                    )),
                // Every held id is a pre-entry id (major ≤ 105) or a cache we just
                // took (major 106, minor < cpu) — so cache[cpu] (minor = cpu) tops all.
                lctx.lock_id_acyclic(Self::allocator_cache_lock_id(cpu)),
            decreases NUM_CPUS - cpu,
        {
            proof {
                assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).wf()) by {
                    reveal(allocator_perms_wf);
                };
            }
            let Tracked(cache_perm) = self.wlock_allocator_cache(alloc_ptr_4k, cpu, Tracked(&mut *lctx));
            proof {
                assert(self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.lock_id_by_index(cpu)
                    == Self::allocator_cache_lock_id(cpu)) by {
                    reveal(allocator_perms_wf);
                    reveal(KernelK::allocator_cache_lock_id);
                };
                assert(Self::allocator_cache_lock_entry_prefix_seq(
                    alloc_ptr_4k, (cpu + 1) as CpuId,
                ) =~= Self::allocator_cache_lock_entry_prefix_seq(
                    alloc_ptr_4k, cpu,
                ).push((
                    Self::allocator_cache_lock_id(cpu),
                    KernelObjId::AllocatorCache(
                        PageSize::SZ4k, alloc_ptr_4k, cpu),
                ))) by {
                    reveal(KernelK::allocator_cache_lock_entry_prefix_seq);
                };
                assert(Self::allocator_cache_lock_entry_prefix(
                    alloc_ptr_4k, (cpu + 1) as CpuId,
                ) =~= Self::allocator_cache_lock_entry_prefix(
                    alloc_ptr_4k, cpu,
                ).insert((
                    Self::allocator_cache_lock_id(cpu),
                    KernelObjId::AllocatorCache(
                        PageSize::SZ4k, alloc_ptr_4k, cpu),
                ))) by {
                    Self::allocator_cache_lock_entry_prefix_seq(
                        alloc_ptr_4k, cpu,
                    ).lemma_push_to_set_commute((
                        Self::allocator_cache_lock_id(cpu),
                        KernelObjId::AllocatorCache(
                            PageSize::SZ4k, alloc_ptr_4k, cpu),
                    ));
                    reveal(KernelK::allocator_cache_lock_entry_prefix_seq);
                    reveal(KernelK::allocator_cache_lock_entry_prefix);
                };
                assert(lctx.lock_id_set() =~= old(lctx).lock_id_set()
                    + Self::allocator_cache_lock_entry_prefix(
                        alloc_ptr_4k, (cpu + 1) as CpuId,
                    )) by {
                    reveal(KernelK::allocator_cache_lock_entry_prefix_seq);
                    reveal(KernelK::allocator_cache_lock_entry_prefix);
                };
                cache_perms.tracked_insert(cpu, cache_perm);
            }
            cpu = cpu + 1;
        }

        // After the loop: all caches held (major 106), pool (major 107) tops them.
        proof {
            assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).wf()) by {
                reveal(allocator_perms_wf);
            };
        }
        let Tracked(pool_perm) = self.wlock_allocator_global_pool(alloc_ptr_4k, Tracked(&mut *lctx));
        proof {
            assert(Self::cache_perms_match_lctx(
                self.allocator_4k_map, alloc_ptr_4k, &*lctx, &cache_perms)) by {
                reveal(KernelK::cache_perms_match_lctx);
            };
            assert(Self::allocator_objects_unlocked_except_cache_pool(
                self.allocator_4k_map, alloc_ptr_4k, lctx.thread_id(),
            )) by {
                reveal(KernelK::allocator_objects_unlocked_except_cache_pool);
            };
            assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
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
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr,
        page_index: PageIndex,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(cache_perms): Tracked<Map<CpuId, LockPerm>>,
    )
        requires
            old(self).inv(),
            old(self).thread_map.dom().contains(thread_ptr),
            old(self).thread_map.spec_index(thread_ptr)
                .locked_by_thread(old(lctx).thread_id()),
            old(self).process_map.dom().contains(process_ptr),
            old(self).process_map.spec_index(process_ptr)
                .locked_by_thread(old(lctx).thread_id()),
            index_valid(NUM_PAGES, page_index),
            old(self).page_array.spec_index(page_index).view()
                .locked_by_thread(old(lctx).thread_id()),
            lock_id_aligned(old(self), old(lctx)),
            Self::allocator_objects_unlocked_except_cache_pool(
                old(self).allocator_4k_map,
                alloc_ptr_4k,
                old(lctx).thread_id(),
            ),
            Self::cache_perms_match_lctx(
                old(self).allocator_4k_map, alloc_ptr_4k, old(lctx), &cache_perms),
            Self::allocator_cache_lock_entry_prefix(
                alloc_ptr_4k, NUM_CPUS).subset_of(old(lctx).lock_id_set()),
            forall|c: CpuId|
                #![trigger old(lctx).lock_id_set().contains((
                    Self::allocator_cache_lock_id(c),
                    KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c)))]
                index_valid(NUM_CPUS, c)
                ==> old(lctx).lock_id_set().contains((
                    Self::allocator_cache_lock_id(c),
                    KernelObjId::AllocatorCache(
                        PageSize::SZ4k, alloc_ptr_4k, c),
                )),
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.wlocked_by(old(lctx)),
            old(lctx).lock_entry_contains(
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.lock_id(),
                KernelObjId::AllocatorGlobalPoll(
                    PageSize::SZ4k, alloc_ptr_4k,
                )),
        ensures
            final(self).inv(),
            final(self).thread_map.dom().contains(thread_ptr),
            final(self).thread_map.spec_index(thread_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            final(self).process_map.dom().contains(process_ptr),
            final(self).process_map.spec_index(process_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            final(self).page_array.spec_index(page_index).view()
                .locked_by_thread(final(lctx).thread_id()),
            kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).lock_id_set() =~= old(lctx).lock_id_set()
                - Self::allocator_cache_lock_entry_prefix(
                    alloc_ptr_4k, NUM_CPUS),
            lock_id_aligned(final(self), final(lctx)),
            // ---- only allocator_4k_map cache lock state moves; every other field byte-equal ----
            final(self).pagetable_map     == old(self).pagetable_map,
            final(self).iommu_table_map     == old(self).iommu_table_map,
            final(self).iommu_root_table     == old(self).iommu_root_table,
            final(self).page_array        == old(self).page_array,
            final(self).cpu_array         == old(self).cpu_array,
            final(self).cpu_tlb           == old(self).cpu_tlb,
            final(self).iommu_tlb           == old(self).iommu_tlb,
            final(self).root_container    == old(self).root_container,
            final(self).container_map     == old(self).container_map,
            final(self).scheduler_map     == old(self).scheduler_map,
            final(self).pcid_allocator_map == old(self).pcid_allocator_map,
            final(self).process_map       == old(self).process_map,
            final(self).thread_map        == old(self).thread_map,
            final(self).endpoint_map      == old(self).endpoint_map,
            final(self).allocator_2m_map  == old(self).allocator_2m_map,
            final(self).allocator_1g_map  == old(self).allocator_1g_map,
            final(self).default_pagetable == old(self).default_pagetable,
            final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
            forall|p: RwLockPageAllocatorPtr|
                #![trigger final(self).allocator_4k_map.spec_index(p)]
                old(self).allocator_4k_map.dom().contains(p) && p != alloc_ptr_4k
                ==> final(self).allocator_4k_map.spec_index(p)
                    == old(self).allocator_4k_map.spec_index(p),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.wlocked_by(final(lctx)),
            final(lctx).lock_entry_contains(
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.lock_id(),
                KernelObjId::AllocatorGlobalPoll(
                    PageSize::SZ4k, alloc_ptr_4k,
                )),
            Self::allocator_caches_unlocked(
                final(self).allocator_4k_map, alloc_ptr_4k),
            Self::allocator_objects_unlocked_except_cache_pool(
                final(self).allocator_4k_map,
                alloc_ptr_4k,
                final(lctx).thread_id(),
            ),
    {
        let tracked mut perms = cache_perms;
        assert(Self::cache_perms_match_lctx_from(
            self.allocator_4k_map, alloc_ptr_4k, &*lctx, &perms, 0,
        )) by {
            reveal(KernelK::cache_perms_match_lctx);
            reveal(KernelK::cache_perms_match_lctx_from);
        };
        let mut cpu: CpuId = 0;
        while cpu < NUM_CPUS
            invariant
                self.inv(),
                self.thread_map.dom().contains(thread_ptr),
                self.thread_map.spec_index(thread_ptr)
                    .locked_by_thread(lctx.thread_id()),
                self.process_map.dom().contains(process_ptr),
                self.process_map.spec_index(process_ptr)
                    .locked_by_thread(lctx.thread_id()),
                self.page_array.spec_index(page_index).view()
                    .locked_by_thread(lctx.thread_id()),
                lock_id_aligned(self, &*lctx),
                self.pagetable_map     == old(self).pagetable_map,
                self.iommu_table_map     == old(self).iommu_table_map,
                self.iommu_root_table     == old(self).iommu_root_table,
                self.page_array        == old(self).page_array,
                self.cpu_array         == old(self).cpu_array,
                self.cpu_tlb           == old(self).cpu_tlb,
                self.iommu_tlb           == old(self).iommu_tlb,
                self.root_container    == old(self).root_container,
                self.container_map     == old(self).container_map,
                self.scheduler_map     == old(self).scheduler_map,
                self.pcid_allocator_map == old(self).pcid_allocator_map,
                self.process_map       == old(self).process_map,
                self.thread_map        == old(self).thread_map,
                self.endpoint_map      == old(self).endpoint_map,
                self.allocator_2m_map  == old(self).allocator_2m_map,
                self.allocator_1g_map  == old(self).allocator_1g_map,
                self.default_pagetable == old(self).default_pagetable,
                self.allocator_4k_map.dom().contains(alloc_ptr_4k),
                self.allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
                self.allocator_4k_map.spec_index(alloc_ptr_4k).quota
                    == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                forall|p: RwLockPageAllocatorPtr|
                    #![trigger self.allocator_4k_map.spec_index(p)]
                    old(self).allocator_4k_map.dom().contains(p) && p != alloc_ptr_4k
                    ==> self.allocator_4k_map.spec_index(p)
                        == old(self).allocator_4k_map.spec_index(p),
                self.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
                lctx.thread_id() == old(lctx).thread_id(),
                0 <= cpu <= NUM_CPUS,
                lctx.lock_id_set() =~= old(lctx).lock_id_set()
                    - Self::allocator_cache_lock_entry_prefix(
                        alloc_ptr_4k, cpu),
                forall|c: CpuId|
                    #![trigger lctx.lock_id_set().contains((
                        Self::allocator_cache_lock_id(c),
                        KernelObjId::AllocatorCache(
                            PageSize::SZ4k, alloc_ptr_4k, c)))]
                    index_valid(NUM_CPUS, c) && c >= cpu
                    ==> lctx.lock_id_set().contains((
                        Self::allocator_cache_lock_id(c),
                        KernelObjId::AllocatorCache(
                            PageSize::SZ4k, alloc_ptr_4k, c),
                    )),
                lctx.lock_entry_contains(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .global_pool.lock_id(),
                    KernelObjId::AllocatorGlobalPoll(
                        PageSize::SZ4k, alloc_ptr_4k,
                    )),
                self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.wlocked_by(&*lctx),
                forall|c: CpuId|
                    #![trigger self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(c).view().locked()]
                    index_valid(NUM_CPUS, c) && c < cpu
                    ==> self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(c).view().locked() == false,
                forall|c: CpuId|
                    #![trigger self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(c)]
                    index_valid(NUM_CPUS, c) && c < cpu
                    ==> !self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(c).view()
                        .wlocked_by_thread(lctx.thread_id()),
                Self::cache_perms_match_lctx_from(
                    self.allocator_4k_map, alloc_ptr_4k, &*lctx, &perms, cpu),
            decreases NUM_CPUS - cpu,
        {
            proof {
                assert(
                    perms.dom().contains(cpu)
                    && perms.spec_index(cpu).state() is WriteLock
                    && perms.spec_index(cpu).thread_id() == lctx.thread_id()
                    && perms.spec_index(cpu).lock_id()
                        == self.allocator_4k_map.spec_index(alloc_ptr_4k)
                            .cpu_caches.spec_index(cpu).view().locking_thread()->Write_lock_id
                    && perms.spec_index(cpu).ordering_lock_id()
                        == Self::allocator_cache_lock_id(cpu)
                    && self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(cpu).view().wlocked_by(&*lctx)
                ) by {
                    reveal(KernelK::cache_perms_match_lctx_from);
                };
                assert(self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.spec_index(cpu).view().being_killed() == false) by {
                    reveal(allocator_perms_wf);
                };
                assert(self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.lock_id_by_index(cpu)
                    == Self::allocator_cache_lock_id(cpu)) by {
                    reveal(allocator_perms_wf);
                    reveal(KernelK::allocator_cache_lock_id);
                };
            }
            let tracked cache_perm = perms.tracked_remove(cpu);
            self.wunlock_allocator_cache(alloc_ptr_4k, cpu, Tracked(&mut *lctx), Tracked(cache_perm));
            proof {
                assert(Self::allocator_cache_lock_entry_prefix_seq(
                    alloc_ptr_4k, (cpu + 1) as CpuId,
                ) =~= Self::allocator_cache_lock_entry_prefix_seq(
                    alloc_ptr_4k, cpu,
                ).push((
                    Self::allocator_cache_lock_id(cpu),
                    KernelObjId::AllocatorCache(
                        PageSize::SZ4k, alloc_ptr_4k, cpu),
                ))) by {
                    reveal(KernelK::allocator_cache_lock_entry_prefix_seq);
                };
                assert(Self::allocator_cache_lock_entry_prefix(
                    alloc_ptr_4k, (cpu + 1) as CpuId,
                ) =~= Self::allocator_cache_lock_entry_prefix(
                    alloc_ptr_4k, cpu,
                ).insert((
                    Self::allocator_cache_lock_id(cpu),
                    KernelObjId::AllocatorCache(
                        PageSize::SZ4k, alloc_ptr_4k, cpu),
                ))) by {
                    Self::allocator_cache_lock_entry_prefix_seq(
                        alloc_ptr_4k, cpu,
                    ).lemma_push_to_set_commute((
                        Self::allocator_cache_lock_id(cpu),
                        KernelObjId::AllocatorCache(
                            PageSize::SZ4k, alloc_ptr_4k, cpu),
                    ));
                    reveal(KernelK::allocator_cache_lock_entry_prefix_seq);
                    reveal(KernelK::allocator_cache_lock_entry_prefix);
                };
                assert(lctx.lock_id_set() =~= old(lctx).lock_id_set()
                    - Self::allocator_cache_lock_entry_prefix(
                        alloc_ptr_4k, (cpu + 1) as CpuId,
                    )) by {
                    reveal(KernelK::allocator_cache_lock_entry_prefix_seq);
                    reveal(KernelK::allocator_cache_lock_entry_prefix);
                };
                assert(Self::cache_perms_match_lctx_from(
                    self.allocator_4k_map, alloc_ptr_4k, &*lctx, &perms,
                    (cpu + 1) as CpuId,
                )) by {
                    reveal(KernelK::cache_perms_match_lctx_from);
                    reveal(allocator_perms_wf);
                };
            }
            cpu = cpu + 1;
        }
        proof {
            assert(Self::allocator_caches_unlocked(
                self.allocator_4k_map, alloc_ptr_4k,
            )) by {
                reveal(KernelK::allocator_caches_unlocked);
            };
            assert(Self::allocator_objects_unlocked_except_cache_pool(
                self.allocator_4k_map,
                alloc_ptr_4k,
                lctx.thread_id(),
            )) by {
                reveal(KernelK::allocator_objects_unlocked_except_cache_pool);
            };
            assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
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
                        == Self::allocator_cache_lock_id(c)
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
                        == Self::allocator_cache_lock_id(c)
                    &&& alloc_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(c).view().wlocked_by(lctx)
                }
    }

    fn scan_caches_and_alloc(
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(cache_perms): Tracked<&Map<CpuId, LockPerm>>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (bool, Option<(CpuId, PagePtr, Tracked<LockPerm>)>))
        requires
            old(self).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(self).container_map.dom().contains(container_ptr),
            old(self).thread_map.dom().contains(thread_ptr),
            old(self).thread_map.spec_index(thread_ptr)
                .locked_by_thread(old(lctx).thread_id()),
            old(self).process_map.dom().contains(process_ptr),
            old(self).process_map.spec_index(process_ptr)
                .locked_by_thread(old(lctx).thread_id()),
            page_objects_unlocked(
                old(self).page_array, old(lctx).thread_id()),
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            Self::allocator_objects_unlocked_except_cache_pool(
                old(self).allocator_4k_map,
                alloc_ptr_4k,
                old(lctx).thread_id(),
            ),
            old(self).container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(self).thread_map.spec_index(thread_ptr).view().owning_container == container_ptr,
            old(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            thread_effective_quota_4k(old(self).thread_map.spec_index(thread_ptr)) >= 1,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(self).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(self).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            Self::cache_perms_match_lctx(
                old(self).allocator_4k_map, alloc_ptr_4k, old(lctx), cache_perms),
            old(lctx).held_lock_majors_lt(FREE_PAGE_LOCK_MAJOR),
        ensures
            final(self).inv(),
            final(self).thread_map.spec_index(thread_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            final(self).process_map == old(self).process_map,
            final(self).pagetable_map == old(self).pagetable_map,
            final(self).container_map == old(self).container_map,
            final(self).scheduler_map == old(self).scheduler_map,
            final(self).pcid_allocator_map == old(self).pcid_allocator_map,
            final(self).endpoint_map == old(self).endpoint_map,
            final(self).iommu_root_table == old(self).iommu_root_table,
            final(self).iommu_table_map == old(self).iommu_table_map,
            final(self).iommu_tlb == old(self).iommu_tlb,
            final(self).cpu_array == old(self).cpu_array,
            final(self).allocator_2m_map == old(self).allocator_2m_map,
            final(self).allocator_1g_map == old(self).allocator_1g_map,
            final(self).thread_map.unchanged_except(&old(self).thread_map, thread_ptr),
            Self::allocator_objects_unlocked_except_cache_pool(
                final(self).allocator_4k_map,
                alloc_ptr_4k,
                final(lctx).thread_id(),
            ),
            final(self).allocator_4k_map.unchanged_except(
                &old(self).allocator_4k_map, alloc_ptr_4k),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(self).thread_map.lock_id_by_key(thread_ptr)
                == old(self).thread_map.lock_id_by_key(thread_ptr),
            lock_id_aligned(final(self), final(lctx)),
            // ---- user view unchanged: staging is kernel-internal ----
            kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
            // ---- failure: every cache was empty; complete no-op ----
            ret.0 == false ==> {
                &&& ret.1 is None
                &&& *final(self) == *old(self)
                &&& *final(lctx) == *old(lctx)
                &&& forall|c: CpuId|
                    #![trigger final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(c)]
                    index_valid(NUM_CPUS, c)
                    ==> final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(c).view().view().view().len() == 0
            },
            // ---- success: popped + staged a page from cache `cpu`, page slot held ----
            ret.0 == true ==> {
                &&& ret.1 is Some
                &&& final(lctx).kernel_view_locking_state() is Release
                &&& index_valid(NUM_CPUS, ret.1.unwrap().0)
                &&& page_ptr_valid(ret.1.unwrap().1)
                &&& old(self).page_array.spec_index(
                    page_ptr2page_index(ret.1.unwrap().1),
                ).view().view().state is Free4k
                &&& !old(self).thread_map.spec_index(thread_ptr).view()
                    .temp_alloc_cache_4k.view().contains(ret.1.unwrap().1)
                &&& index_valid(NUM_PAGES, page_ptr2page_index(ret.1.unwrap().1))
                &&& final(self).page_array.entries_unchanged_except(
                    &old(self).page_array, page_ptr2page_index(ret.1.unwrap().1))
                &&& final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool
                    == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool
                &&& final(self).page_array.spec_index(page_ptr2page_index(ret.1.unwrap().1)).view().being_killed() == false
                &&& ret.1.unwrap().2.view().state() is WriteLock
                &&& ret.1.unwrap().2.view().thread_id() == final(lctx).thread_id()
                &&& ret.1.unwrap().2.view().lock_id() == final(self).page_array.spec_index(page_ptr2page_index(ret.1.unwrap().1)).view().locking_thread()->Write_lock_id
                &&& final(self).page_array.spec_index(page_ptr2page_index(ret.1.unwrap().1)).view()
                    .wlocked_by(final(lctx))
                &&& final(self).page_array.spec_index(page_ptr2page_index(ret.1.unwrap().1)).view()
                    .locked_by_thread(final(lctx).thread_id())
                &&& page_objects_unlocked_except(
                    final(self).page_array, final(lctx).thread_id(),
                    set![page_ptr2page_index(ret.1.unwrap().1)])
                &&& final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((
                    final(self).page_array.lock_id_by_index(
                        page_ptr2page_index(ret.1.unwrap().1)),
                    KernelObjId::Page(page_ptr2page_index(ret.1.unwrap().1)),
                ))
                &&& Self::cache_perms_match_lctx(
                    final(self).allocator_4k_map, alloc_ptr_4k, final(lctx), cache_perms)
                &&& final(self).thread_map.spec_index(thread_ptr)
                    .wlocked_by(final(lctx))
                &&& final(self).thread_map.spec_index(thread_ptr).being_killed() == false
                &&& final(self).thread_map.spec_index(thread_ptr).view().owning_proc
                    == old(self).thread_map.spec_index(thread_ptr).view().owning_proc
                &&& final(self).thread_map.spec_index(thread_ptr).view().owning_container
                    == old(self).thread_map.spec_index(thread_ptr).view().owning_container
                &&& final(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                    == old(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                &&& thread_lock_perm.lock_id() == final(self).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id
                &&& final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
                    =~= old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().insert(ret.1.unwrap().1)
                &&& final(self).page_array.spec_index(page_ptr2page_index(ret.1.unwrap().1)).view().view().state == (PageState::Owned4k{ thread_ptr })
                &&& final(self).page_array.spec_index(page_ptr2page_index(ret.1.unwrap().1)).view().view().owning_container
                    == container_ptr
                &&& final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m
                    == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m
                &&& final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g
                    == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g
                &&& final(self).thread_map.spec_index(thread_ptr).view()
                    .free_quota_pending_fields_equal(
                        &old(self).thread_map.spec_index(thread_ptr).view(),
                    )
                &&& final(self).thread_map.spec_index(thread_ptr).view().quota_4k
                    == old(self).thread_map.spec_index(thread_ptr).view().quota_4k
                &&& final(self).thread_map.spec_index(thread_ptr).view().endpoint_descriptors
                    == old(self).thread_map.spec_index(thread_ptr).view().endpoint_descriptors
            },
    {
        let mut cpu: CpuId = 0;
        while cpu < NUM_CPUS
            invariant
                *self == *old(self),
                *lctx == *old(lctx),
                self.inv(),
                lock_id_aligned(self, &*lctx),
                lctx.kernel_view_locking_state() is Acquire,
                0 <= cpu <= NUM_CPUS,
                self.container_map.dom().contains(container_ptr),
                self.allocator_4k_map.dom().contains(alloc_ptr_4k),
                Self::allocator_objects_unlocked_except_cache_pool(
                    self.allocator_4k_map, alloc_ptr_4k, lctx.thread_id(),
                ),
                self.container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
                self.thread_map.spec_index(thread_ptr).view().owning_container == container_ptr,
                self.thread_map.spec_index(thread_ptr).being_killed() == false,
                thread_effective_quota_4k(self.thread_map.spec_index(thread_ptr)) >= 1,
                thread_lock_perm.state() is WriteLock,
                thread_lock_perm.thread_id() == lctx.thread_id(),
                thread_lock_perm.lock_id() == self.thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
                self.thread_map.dom().contains(thread_ptr),
                self.thread_map.spec_index(thread_ptr).wlocked_by(&*lctx),
                self.thread_map.spec_index(thread_ptr)
                    .locked_by_thread(lctx.thread_id()),
                page_objects_unlocked(self.page_array, lctx.thread_id()),
                self.process_map.dom().contains(process_ptr),
                self.process_map.spec_index(process_ptr)
                    .locked_by_thread(lctx.thread_id()),
                Self::cache_perms_match_lctx(
                    self.allocator_4k_map, alloc_ptr_4k, &*lctx, cache_perms),
                lctx.held_lock_majors_lt(FREE_PAGE_LOCK_MAJOR),
                // Caches [0, cpu) were all found empty.
                forall|c: CpuId|
                    #![trigger self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(c)]
                    index_valid(NUM_CPUS, c) && c < cpu
                    ==> self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(c).view().view().view().len() == 0,
            decreases NUM_CPUS - cpu,
        {
            proof {
                assert(
                    self.allocator_4k_map.perms_wf()
                    && self.allocator_4k_map.dom().contains(alloc_ptr_4k)
                    && self.allocator_4k_map.spec_index(alloc_ptr_4k).wf()
                    && self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.inv()
                    && self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches_wf()
                    && cache_perms.dom().contains(cpu)
                    && cache_perms.spec_index(cpu).state() is WriteLock
                    && cache_perms.spec_index(cpu).thread_id() == lctx.thread_id()
                    && cache_perms.spec_index(cpu).lock_id()
                        == self.allocator_4k_map.spec_index(alloc_ptr_4k)
                            .cpu_caches.spec_index(cpu).view().locking_thread()->Write_lock_id
                    && self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(cpu).view()
                        .write_lock_perm_match(&cache_perms.spec_index(cpu))
                    && self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(cpu).view().being_killed() == false
                ) by {
                    reveal(allocator_perms_wf);
                    reveal(KernelK::cache_perms_match_lctx);
                };
            }
            let cache_ref = self.allocator_4k_map.borrow_cache(
                alloc_ptr_4k, cpu, Tracked(cache_perms.tracked_borrow(cpu)),
            );
            assert(cache_ref.linked_list.wf()) by {
                assert(
                    index_valid(NUM_CPUS, cpu)
                    && self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches_wf()
                ) by {
                    reveal(allocator_perms_wf);
                };
            };
            let cache_len = cache_ref.linked_list.len();
            assert(cache_len == self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu).view().view().view().len()) by {
                cache_ref.linked_list.lemma_len_view();
            };
            if cache_len > 0 {
                let tracked selected_cache_perm = cache_perms.tracked_borrow(cpu);
                let (page_ptr, Tracked(page_lock_perm)) = self.pop_stage_4k_page(
                    alloc_ptr_4k, cpu, thread_ptr, container_ptr,
                    Tracked(&mut *lctx), Tracked(selected_cache_perm), Tracked(thread_lock_perm),
                );
                assert(Self::cache_perms_match_lctx(
                    self.allocator_4k_map, alloc_ptr_4k, &*lctx, cache_perms,
                )) by {
                    reveal(KernelK::cache_perms_match_lctx);
                };
                assert(Self::allocator_objects_unlocked_except_cache_pool(
                    self.allocator_4k_map, alloc_ptr_4k, lctx.thread_id(),
                )) by {
                    reveal(KernelK::allocator_objects_unlocked_except_cache_pool);
                };
                return (true, Some((cpu, page_ptr, Tracked(page_lock_perm))));
            }
            cpu = cpu + 1;
        }
        (false, None)
    }

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
