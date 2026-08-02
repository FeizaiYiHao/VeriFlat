use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;

verus! {

impl KernelK {


    // ================================================================
    // Main allocate function
    // ================================================================

    /// Allocate a single 4k page from the container's allocator.
    /// Caller holds the process write-lock.
    #[verifier::spinoff_prover]
    pub fn allocate_free_4k_page(
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        cpu_id: CpuId,
        scheduler_ptr: RwLockSchedulerPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(process_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(self).inv(),
            cpu_id_valid(cpu_id),
            old(self).process_map.dom().contains(process_ptr),
            old(self).container_map.dom().contains(container_ptr),
            old(self).scheduler_map.dom().contains(scheduler_ptr),
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            old(self).container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(self).process_map.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            old(self).process_map.spec_index(process_ptr).being_killed() == false,
            // Process write-lock perm, needed to mutate the process payload
            // (insert the freshly-allocated page into `temp_alloc_cache_4k`).
            process_lock_perm.state() is WriteLock,
            process_lock_perm.thread_id() == old(lctx).thread_id(),
            process_lock_perm.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
            process_effective_quota_4k(old(self).process_map.spec_index(process_ptr)) >= 1,  
            old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
            old(self).scheduler_map.spec_index(scheduler_ptr).wlocked_by(old(lctx)),
            old(self).cpu_array[cpu_id]@.wlocked_by(old(lctx)),
            old(lctx).wf(),
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            old(lctx).lock_id_acyclic(
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches[cpu_id].lock_id()),

            forall|held_lock_id: LockId|
                #![trigger old(lctx).lock_id_set().contains(held_lock_id)]
                old(lctx).lock_id_set().contains(held_lock_id)
                ==> held_lock_id.major <= PROCESS_LOCK_MAJOR,
        ensures
            final(self).inv(),
            // ---- held process: not killed, perm still matches (process held throughout) ----
            final(self).process_map.spec_index(process_ptr).being_killed() == false,
            process_lock_perm.lock_id() == final(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            final(self).process_map.spec_index(process_ptr).view_rodata() == old(self).process_map.spec_index(process_ptr).view_rodata(),
            final(self).process_map.lock_id_by_key(process_ptr)
                == old(self).process_map.lock_id_by_key(process_ptr),
            final(self).container_map.dom().contains(container_ptr),
            final(self).container_map.spec_index(container_ptr).view_rodata()
                == old(self).container_map.spec_index(container_ptr).view_rodata(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
            final(self).locked_objects_match_lctx(final(lctx)),
            lock_id_aligned(final(self), final(lctx)),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            page_ptr_valid(ret.0),
            // ---- page slot left write-locked, perm handed back (rides across the boundary as a held object) ----
            page_index_wf(page_ptr2page_index(ret.0)),
            final(self).page_array[page_ptr2page_index(ret.0)].view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(self).page_array[page_ptr2page_index(ret.0)].view().locking_thread()->Write_lock_id,
            final(self).page_array[page_ptr2page_index(ret.0)]@
                .wlocked_by(final(lctx)),
            final(self).process_map.dom().contains(process_ptr),
            final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx)),
            final(lctx).wf(),
            final(lctx).lock_id_set() =~= old(lctx).lock_id_set().insert(
                final(self).page_array.lock_id_by_index(page_ptr2page_index(ret.0))),
            // ---- explicitly tracked held objects survive ----
            final(self).scheduler_map.dom().contains(scheduler_ptr),
            final(self).scheduler_map.spec_index(scheduler_ptr)
                == old(self).scheduler_map.spec_index(scheduler_ptr),
            final(self).scheduler_map.spec_index(scheduler_ptr).wlocked_by(final(lctx)),
            final(self).cpu_array[cpu_id]@ == old(self).cpu_array[cpu_id]@,
            final(self).cpu_array[cpu_id]@.wlocked_by(final(lctx)),
            // ---- staging: ret staged Owned4k; 4k cache gained exactly ret, 2m/1g caches + nominal quota untouched ----
            final(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view()
                =~= old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view().insert(ret.0),
            final(self).page_array[page_ptr2page_index(ret.0)].view().view().state == (PageState::Owned4k{ process_ptr }),
            final(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_2m
                == old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_2m,
            final(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_1g
                == old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_1g,
            final(self).process_map.spec_index(process_ptr).view().quota_4k
                == old(self).process_map.spec_index(process_ptr).view().quota_4k,
            final(self).process_map.spec_index(process_ptr).view().owned_threads
                == old(self).process_map.spec_index(process_ptr).view().owned_threads,
    {
        assert(
            self.allocator_4k_map.dom().contains(alloc_ptr_4k)
            && self.allocator_4k_map.perms_wf()
            && self.allocator_4k_map.spec_index(alloc_ptr_4k).wf()
        ) by {
            reveal(allocator_perms_wf);
        };

        // Fast path: lock the running cpu's cache.
        let Tracked(cache_lock_perm) = self.wlock_allocator_cache(
            alloc_ptr_4k, cpu_id, Tracked(&mut *lctx),
        );

        // Read the cache length via a shared borrow (preserves wf() for the slow path).
        assert(self.allocator_4k_map.perms_wf()) by {
            reveal(allocator_perms_wf);
        };
        let cache_ref = self.allocator_4k_map.borrow_cache(
            alloc_ptr_4k, cpu_id, Tracked(&cache_lock_perm),
        );
        let cache_len = cache_ref.linked_list.len();

        if cache_len > 0 {
            assert(lctx.lock_id_acyclic(
                self.page_array.lock_id_by_index(page_ptr2page_index(
                    self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches[cpu_id]@@.view()[0],
                )),
            )) by {
                reveal(allocator_free_page_ptrs_wf);
                reveal(allocator_perms_wf);
                page_ptr_lemma1();
                reveal(page_array_wf);
                reveal(container_allocator_free_4k_page_wf);
            };
            // Pop + stage the cache head, leaving the page slot + cache write-locked.
            let (page_ptr, Tracked(page_lock_perm)) = self.pop_stage_4k_page(
                alloc_ptr_4k, cpu_id, process_ptr, container_ptr,
                Tracked(&mut *lctx), Tracked(&cache_lock_perm), Tracked(process_lock_perm),
            );

            // Unlock the cache; keep the page slot write-locked so it rides
            // across the boundary as a held object (its state is pinned).
            self.wunlock_allocator_cache(alloc_ptr_4k, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm));

            // Close the kernel atomic step.
            proof {
                self.kernel_step_boundary(&mut *lctx, &mut *steps);
            }
            return (page_ptr, Tracked(page_lock_perm));
        }

        // Case 2: slow path — lock the global pool while holding the (empty) cache.
        // The pool's id (major 107, owners NotApp) tops every held id (Process +
        // AllocatorCache, major ≤ 106), so it is acyclic and fresh.
        assert(lctx.lock_id_acyclic(
            self.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.lock_id(),
        )) by {
            reveal(allocator_perms_wf);
        };
        let Tracked(gp_lock_perm) = self.wlock_allocator_global_pool(
            alloc_ptr_4k, Tracked(&mut *lctx),
        );

        // Read the pool length via a shared borrow (preserves wf()).
        assert(self.allocator_4k_map.perms_wf()) by {
            reveal(allocator_perms_wf);
        };
        let pool_ref = self.allocator_4k_map.borrow_global_pool(
            alloc_ptr_4k, Tracked(&gp_lock_perm),
        );
        let pool_len = pool_ref.len();

        if pool_len > 0 {
            assert(lctx.lock_id_acyclic(
                self.page_array.lock_id_by_index(page_ptr2page_index(
                    self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .global_pool.view().view()[0],
                )),
            )) by {
                reveal(allocator_free_page_ptrs_wf);
                reveal(allocator_perms_wf);
                page_ptr_lemma1();
                reveal(page_array_wf);
                reveal(container_allocator_free_4k_page_wf);
            };
            // Pop + stage the pool head, leaving the page slot + pool write-locked.
            let (page_ptr, Tracked(page_lock_perm)) = self.pop_stage_global_4k_page(
                alloc_ptr_4k, process_ptr, container_ptr,
                Tracked(&mut *lctx), Tracked(&gp_lock_perm), Tracked(process_lock_perm),
            );

            // Unlock the pool, then the cache; keep the page slot write-locked so
            // it rides across the boundary as a held object (its state is pinned).
            self.wunlock_allocator_global_pool(alloc_ptr_4k, Tracked(&mut *lctx), Tracked(gp_lock_perm));
            self.wunlock_allocator_cache(alloc_ptr_4k, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm));

            // Close the kernel atomic step.
            proof {
                self.kernel_step_boundary(&mut *lctx, &mut *steps);
            }
            return (page_ptr, Tracked(page_lock_perm));
        }

        // Case 3: cache + pool both empty. Release them, close the kernel step,
        // then lock every cache + the pool afresh and scan for a free page. The
        // running-cpu cache (major 106) and pool (major 107) must be dropped
        // before we can re-acquire the full cache set in ascending order.
        self.wunlock_allocator_global_pool(alloc_ptr_4k, Tracked(&mut *lctx), Tracked(gp_lock_perm));
        self.wunlock_allocator_cache(alloc_ptr_4k, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm));

        proof {
            assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
            };
            self.kernel_step_boundary(&mut *lctx, &mut *steps);
            assert(self.allocator_4k_map.dom().contains(alloc_ptr_4k)) by {
                reveal(container_allocator_wf);
            };
            assert(
                self.scheduler_map.dom().contains(scheduler_ptr)
                && self.scheduler_map.spec_index(scheduler_ptr)
                    == old(self).scheduler_map.spec_index(scheduler_ptr)
                && self.scheduler_map.spec_index(scheduler_ptr).wlocked_by(&*lctx)
            ) by {
                reveal(scheduler_locked_match_lctx);
            };
            assert(
                self.cpu_array[cpu_id]@ == old(self).cpu_array[cpu_id]@
                && self.cpu_array[cpu_id]@.wlocked_by(&*lctx)
            ) by {
                reveal(cpu_locked_match_lctx);
            };
        }
        let result = self.alloc_4k_scan_all_caches_and_pool(
            alloc_ptr_4k, process_ptr, container_ptr,
            Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(process_lock_perm),
        );
        result
    }

    // ================================================================
    // Case 3: scan all caches + global pool after an internal boundary.
    // ================================================================

    fn alloc_4k_scan_all_caches_and_pool(
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(process_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(self).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(self).locked_objects_match_lctx(old(lctx)),
            old(self).process_map.dom().contains(process_ptr),
            old(self).container_map.dom().contains(container_ptr),
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            old(self).process_map.spec_index(process_ptr).being_killed() == false,
            old(self).process_map.spec_index(process_ptr).view_rodata().view().owning_container
                == container_ptr,
            old(self).container_map.spec_index(container_ptr)
                .view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            process_lock_perm.state() is WriteLock,
            process_lock_perm.thread_id() == old(lctx).thread_id(),
            process_lock_perm.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
            old(lctx).wf(),
            lock_id_aligned(old(self), old(lctx)),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
            process_effective_quota_4k(old(self).process_map.spec_index(process_ptr)) >= 1,
            forall|held_lock_id: LockId|
                #![trigger old(lctx).lock_id_set().contains(held_lock_id)]
                old(lctx).lock_id_set().contains(held_lock_id)
                ==> held_lock_id.major <= PROCESS_LOCK_MAJOR,
        ensures
            final(self).inv(),
            final(self).process_map.spec_index(process_ptr).being_killed() == false,
            process_lock_perm.lock_id() == final(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            final(self).process_map.spec_index(process_ptr).view_rodata()
                == old(self).process_map.spec_index(process_ptr).view_rodata(),
            final(self).process_map.lock_id_by_key(process_ptr)
                == old(self).process_map.lock_id_by_key(process_ptr),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
            final(self).locked_objects_match_lctx(final(lctx)),
            lock_id_aligned(final(self), final(lctx)),
            final(self).container_map.dom().contains(container_ptr),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            page_ptr_valid(ret.0),
            page_index_wf(page_ptr2page_index(ret.0)),
            final(self).page_array[page_ptr2page_index(ret.0)].view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(self).page_array[page_ptr2page_index(ret.0)].view().locking_thread()->Write_lock_id,
            final(self).page_array[page_ptr2page_index(ret.0)]@
                .wlocked_by(final(lctx)),
            final(self).process_map.dom().contains(process_ptr),
            final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx)),
            final(lctx).wf(),
            final(lctx).lock_id_set() =~= old(lctx).lock_id_set().insert(
                final(self).page_array.lock_id_by_index(page_ptr2page_index(ret.0))),
            forall|s: RwLockSchedulerPtr|
                #![trigger old(self).scheduler_map.spec_index(s).wlocked_by(old(lctx))]
                old(self).scheduler_map.dom().contains(s)
                    && old(self).scheduler_map.spec_index(s).wlocked_by(old(lctx))
                ==> final(self).scheduler_map.dom().contains(s)
                    && final(self).scheduler_map.spec_index(s)
                        == old(self).scheduler_map.spec_index(s)
                    && final(self).scheduler_map.spec_index(s).wlocked_by(final(lctx)),
            forall|c: CpuId|
                #![trigger old(self).cpu_array[c]@.wlocked_by(old(lctx))]
                cpu_id_valid(c) && old(self).cpu_array[c]@.wlocked_by(old(lctx))
                ==> final(self).cpu_array[c]@ == old(self).cpu_array[c]@
                    && final(self).cpu_array[c]@.wlocked_by(final(lctx)),
            final(self).container_map.spec_index(container_ptr).view_rodata()
                == old(self).container_map.spec_index(container_ptr).view_rodata(),
            final(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view()
                =~= old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view().insert(ret.0),
            final(self).page_array[page_ptr2page_index(ret.0)].view().view().state == (PageState::Owned4k{ process_ptr }),
            final(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_2m
                == old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_2m,
            final(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_1g
                == old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_1g,
            final(self).process_map.spec_index(process_ptr).view().quota_4k
                == old(self).process_map.spec_index(process_ptr).view().quota_4k,
            final(self).process_map.spec_index(process_ptr).view().owned_threads
                == old(self).process_map.spec_index(process_ptr).view().owned_threads,
    {
        let (cache_perms, pool_perm) = self.wlock_all_caches_and_global_pool(
            alloc_ptr_4k, Tracked(&mut *lctx),
        );

        let tracked cache_perms_ref = cache_perms.borrow();
        let (found, slot) = self.scan_caches_and_alloc(
            alloc_ptr_4k, process_ptr, container_ptr,
            Tracked(&mut *lctx), Tracked(cache_perms_ref), Tracked(process_lock_perm),
        );

        if found {
            // A cache held a free page: it is popped + staged, page slot held.
            // Release the page, every cache, then the pool, and close the step.
            let (_scan_cpu, page_ptr, Tracked(page_lock_perm)) = slot.unwrap();
            // Keep the page slot write-locked so it rides across the boundary as
            // a held object (its state is pinned); release the caches + pool.
            self.wunlock_all_caches(alloc_ptr_4k, Tracked(&mut *lctx), Tracked(cache_perms.get()));
            self.wunlock_allocator_global_pool(alloc_ptr_4k, Tracked(&mut *lctx), Tracked(pool_perm.get()));

            proof {
                self.kernel_step_boundary(&mut *lctx, &mut *steps);
            }
            return (page_ptr, Tracked(page_lock_perm));
        }

        // Every cache was empty. By conservation the free pages must sit in the
        // global pool: total_free_pages == pool.len() + Σ cache.len(), the caches
        // are all empty, and the held process still has effective_quota_4k >= 1,
        // so total_free_pages >= 1 and hence pool.len() >= 1.
        assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().len() > 0) by {
            assert(self.container_map.spec_index(container_ptr).view()
                .owned_processes.view().contains(process_ptr)) by {
                reveal(container_process_wf);
            };
            lemma_scan_fail_pool_nonempty(self, container_ptr, alloc_ptr_4k, process_ptr);
            reveal(allocator_perms_wf);
            self.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().lemma_len_view();
        };
        assert(lctx.lock_id_acyclic(
            self.page_array.lock_id_by_index(page_ptr2page_index(
                self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.view().view()[0],
            )),
        )) by {
            assert(page_ptr_valid(
                self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.view().view()[0],
            )) by {
                reveal(allocator_free_page_ptrs_wf);
                reveal(allocator_perms_wf);
            };
            assert(page_index_wf(page_ptr2page_index(
                self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.view().view()[0],
            ))) by {
                page_ptr_lemma1();
            };
            reveal(allocator_perms_wf);
            reveal(page_array_wf);
            reveal(container_allocator_free_4k_page_wf);
        };

        let (page_ptr, Tracked(page_lock_perm)) = self.pop_stage_global_4k_page(
            alloc_ptr_4k, process_ptr, container_ptr,
            Tracked(&mut *lctx), Tracked(pool_perm.borrow()), Tracked(process_lock_perm),
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
        self.wunlock_all_caches(alloc_ptr_4k, Tracked(&mut *lctx), Tracked(cache_perms.get()));
        self.wunlock_allocator_global_pool(alloc_ptr_4k, Tracked(&mut *lctx), Tracked(pool_perm.get()));

        proof {
            self.kernel_step_boundary(&mut *lctx, &mut *steps);
        }
        (page_ptr, Tracked(page_lock_perm))
    }

    // ================================================================
    // wlock_all_caches_and_global_pool: acquire every cpu cache (cpu 0..NUM_CPUS,
    // ascending) then the global pool of `alloc_ptr_4k`. Entry state holds no
    // allocator cache/pool of this allocator, and every held lock id sits at or
    // below PROCESS_LOCK_MAJOR — so each cache (major 106, minor = cpu, ascending)
    // and the pool (major 107) tops every prior id, keeping the acquisition
    // acyclic. Returns the per-cpu cache perms (keyed by cpu) + the pool perm;
    // each wrapper re-establishes inv() internally.
    // ================================================================
    spec fn allocator_cache_lock_id(cache_cpu: CpuId) -> LockId {
        LockId {
            container: LockOwnerId::NotApp,
            process: LockOwnerId::NotApp,
            major: ALLOCATOR_CACHE_MAJOR,
            minor: cache_cpu,
        }
    }

    spec fn allocator_cache_lock_id_prefix_seq(upper: CpuId) -> Seq<LockId> {
        Seq::new(upper as nat, |i: int|
            Self::allocator_cache_lock_id(i as CpuId)
        )
    }

    spec fn allocator_cache_lock_id_prefix(upper: CpuId) -> Set<LockId> {
        Self::allocator_cache_lock_id_prefix_seq(upper).to_set()
    }

    fn wlock_all_caches_and_global_pool(
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
    ) -> (ret: (Tracked<Map<CpuId, LockPerm>>, Tracked<LockPerm>))
        requires
            old(self).inv(),
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            old(lctx).wf(),
            forall|held_lock_id: LockId|
                #![trigger old(lctx).lock_id_set().contains(held_lock_id)]
                old(lctx).lock_id_set().contains(held_lock_id)
                ==> held_lock_id.major <= PROCESS_LOCK_MAJOR,
        ensures
            final(self).inv(),
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
            final(self).process_map       == old(self).process_map,
            final(self).thread_map        == old(self).thread_map,
            final(self).endpoint_map      == old(self).endpoint_map,
            final(self).allocator_2m_map  == old(self).allocator_2m_map,
            final(self).allocator_1g_map  == old(self).allocator_1g_map,
            final(self).default_pagetable == old(self).default_pagetable,
            final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
            final(lctx).wf(),
            final(lctx).lock_id_set() =~= old(lctx).lock_id_set()
                + Self::allocator_cache_lock_id_prefix(NUM_CPUS).insert(
                    final(self).allocator_4k_map
                    .spec_index(alloc_ptr_4k).global_pool.lock_id()),
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
            forall|held_lock_id: LockId|
                #![trigger final(lctx).lock_id_set().contains(held_lock_id)]
                final(lctx).lock_id_set().contains(held_lock_id)
                ==> held_lock_id.major <= ALLOCATOR_GLOBAL_POLL_MAJOR,
            final(self).locked_objects_match_lctx(final(lctx)),
    {
        let tracked mut cache_perms: Map<CpuId, LockPerm> = Map::tracked_empty();

        let mut cpu: CpuId = 0;
        while cpu < NUM_CPUS
            invariant
                self.inv(),
                self.locked_objects_match_lctx(&*lctx),
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
                self.process_map       == old(self).process_map,
                self.thread_map        == old(self).thread_map,
                self.endpoint_map      == old(self).endpoint_map,
                self.allocator_2m_map  == old(self).allocator_2m_map,
                self.allocator_1g_map  == old(self).allocator_1g_map,
                self.default_pagetable == old(self).default_pagetable,
                self.allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
                lctx.thread_id() == old(lctx).thread_id(),
                lctx.kernel_view_locking_state() is Acquire,
                lctx.user_view_locking_state() == old(lctx).user_view_locking_state(),
                0 <= cpu <= NUM_CPUS,
                lctx.lock_id_set() =~= old(lctx).lock_id_set()
                    + Self::allocator_cache_lock_id_prefix(cpu),
                // Caches [0, cpu) are locked, perm collected; [cpu, NUM_CPUS) untouched.
                forall|c: CpuId|
                    #![trigger cache_perms.spec_index(c)]
                    cpu_id_valid(c) && c < cpu
                    ==> {
                        &&& cache_perms.dom().contains(c)
                        &&& cache_perms.spec_index(c).state() is WriteLock
                        &&& cache_perms.spec_index(c).thread_id() == lctx.thread_id()
                        &&& cache_perms.spec_index(c).lock_id() == self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().locking_thread()->Write_lock_id
                        &&& self.allocator_4k_map.spec_index(alloc_ptr_4k)
                            .cpu_caches[c]@.wlocked_by(&*lctx)
                    },
                // Every held id is a pre-entry id (major ≤ 105) or a cache we just
                // took (major 106, minor < cpu) — so cache[cpu] (minor = cpu) tops all.
                forall|held_lock_id: LockId|
                    #![trigger lctx.lock_id_set().contains(held_lock_id)]
                    lctx.lock_id_set().contains(held_lock_id)
                    ==> held_lock_id.major < ALLOCATOR_CACHE_MAJOR
                        || (held_lock_id.major == ALLOCATOR_CACHE_MAJOR
                            && held_lock_id.minor < cpu),
            decreases NUM_CPUS - cpu,
        {
            proof {
                assert({
                    &&& self.allocator_4k_map.spec_index(alloc_ptr_4k).wf()
                    &&& lctx.lock_id_acyclic(
                        self.allocator_4k_map.spec_index(alloc_ptr_4k)
                            .cpu_caches[cpu].lock_id()
                    )
                }) by {
                    reveal(allocator_perms_wf);
                };
            }
            let Tracked(cache_perm) = self.wlock_allocator_cache(alloc_ptr_4k, cpu, Tracked(&mut *lctx));
            proof {
                assert(
                    Self::allocator_cache_lock_id_prefix_seq(
                        (cpu + 1) as CpuId,
                    ) =~= Self::allocator_cache_lock_id_prefix_seq(
                        cpu,
                    ).push(Self::allocator_cache_lock_id(cpu))
                ) by {
                    reveal(KernelK::allocator_cache_lock_id_prefix_seq);
                };
                assert(Self::allocator_cache_lock_id_prefix(
                    (cpu + 1) as CpuId,
                ) =~= Self::allocator_cache_lock_id_prefix(
                    cpu,
                ).insert(Self::allocator_cache_lock_id(cpu))) by {
                    Self::allocator_cache_lock_id_prefix_seq(
                        cpu,
                    ).lemma_push_to_set_commute(Self::allocator_cache_lock_id(cpu));
                    reveal(KernelK::allocator_cache_lock_id_prefix_seq);
                    reveal(KernelK::allocator_cache_lock_id_prefix);
                };
                assert(self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.lock_id_by_index(cpu)
                    == Self::allocator_cache_lock_id(cpu)) by {
                    reveal(allocator_perms_wf);
                    reveal(KernelK::allocator_cache_lock_id);
                };
                assert(lctx.lock_id_set() =~= old(lctx).lock_id_set()
                    + Self::allocator_cache_lock_id_prefix(
                        (cpu + 1) as CpuId,
                    )) by {
                    reveal(KernelK::allocator_cache_lock_id_prefix_seq);
                    reveal(KernelK::allocator_cache_lock_id_prefix);
                };
                cache_perms.tracked_insert(cpu, cache_perm);
            }
            cpu = cpu + 1;
        }

        // After the loop: all caches held (major 106), pool (major 107) tops them.
        proof {
            assert({
                &&& self.allocator_4k_map.spec_index(alloc_ptr_4k).wf()
                &&& lctx.lock_id_acyclic(
                    self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .global_pool.lock_id()
                )
            }) by {
                reveal(allocator_perms_wf);
            };
        }
        let Tracked(pool_perm) = self.wlock_allocator_global_pool(alloc_ptr_4k, Tracked(&mut *lctx));
        proof {
            assert(Self::cache_perms_match_lctx(
                self.allocator_4k_map, alloc_ptr_4k, &*lctx, &cache_perms)) by {
                reveal(KernelK::cache_perms_match_lctx);
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
    fn wunlock_all_caches(
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(cache_perms): Tracked<Map<CpuId, LockPerm>>,
    )
        requires
            old(self).inv(),
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            Self::cache_perms_match_lctx(
                old(self).allocator_4k_map, alloc_ptr_4k, old(lctx), &cache_perms),
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.wlocked_by(old(lctx)),
        ensures
            final(self).inv(),
            kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
            final(lctx).wf(),
            final(lctx).lock_id_set() =~= old(lctx).lock_id_set()
                - Self::allocator_cache_lock_id_prefix(NUM_CPUS),
            final(self).locked_objects_match_lctx(final(lctx)),
            lock_id_aligned(final(self), final(lctx)),
            forall|page_index: PageIndex|
                #![trigger old(self).page_array[page_index]@.wlocked_by(old(lctx))]
                page_index_wf(page_index)
                    && old(self).page_array[page_index]@.wlocked_by(old(lctx))
                ==> final(self).page_array[page_index]@.wlocked_by(final(lctx))
                    && final(self).page_array[page_index]@.locked_by(final(lctx)),
            forall|process_ptr: RwLockProcessPtr|
                #![trigger old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx))]
                old(self).process_map.dom().contains(process_ptr)
                    && old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx))
                ==> final(self).process_map.dom().contains(process_ptr)
                    && final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx))
                    && final(self).process_map.spec_index(process_ptr).locked_by(final(lctx)),
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
            final(self).process_map       == old(self).process_map,
            final(self).thread_map        == old(self).thread_map,
            final(self).endpoint_map      == old(self).endpoint_map,
            final(self).allocator_2m_map  == old(self).allocator_2m_map,
            final(self).allocator_1g_map  == old(self).allocator_1g_map,
            final(self).default_pagetable == old(self).default_pagetable,
            final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.wlocked_by(final(lctx)),
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
                self.locked_objects_match_lctx(&*lctx),
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
                self.process_map       == old(self).process_map,
                self.thread_map        == old(self).thread_map,
                self.endpoint_map      == old(self).endpoint_map,
                self.allocator_2m_map  == old(self).allocator_2m_map,
                self.allocator_1g_map  == old(self).allocator_1g_map,
                self.default_pagetable == old(self).default_pagetable,
                self.allocator_4k_map.dom().contains(alloc_ptr_4k),
                self.allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
                self.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
                lctx.thread_id() == old(lctx).thread_id(),
                lctx.user_view_locking_state() == old(lctx).user_view_locking_state(),
                0 <= cpu <= NUM_CPUS,
                lctx.lock_id_set() =~= old(lctx).lock_id_set()
                    - Self::allocator_cache_lock_id_prefix(cpu),
                self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.wlocked_by(&*lctx),
                forall|c: CpuId|
                    #![trigger self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches[c]@.locked()]
                    cpu_id_valid(c) && c < cpu
                    ==> self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches[c]@.locked() == false,
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
                            .cpu_caches[cpu].view().locking_thread()->Write_lock_id
                    && self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches[cpu]@.wlocked_by(&*lctx)
                ) by {
                    reveal(KernelK::cache_perms_match_lctx_from);
                };
                assert(self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches[cpu].view().being_killed() == false) by {
                    reveal(allocator_perms_wf);
                };
            }
            let tracked cache_perm = perms.tracked_remove(cpu);
            self.wunlock_allocator_cache(alloc_ptr_4k, cpu, Tracked(&mut *lctx), Tracked(cache_perm));
            proof {
                assert(
                    Self::allocator_cache_lock_id_prefix_seq(
                        (cpu + 1) as CpuId,
                    ) =~= Self::allocator_cache_lock_id_prefix_seq(
                        cpu,
                    ).push(Self::allocator_cache_lock_id(cpu))
                ) by {
                    reveal(KernelK::allocator_cache_lock_id_prefix_seq);
                };
                assert(Self::allocator_cache_lock_id_prefix(
                    (cpu + 1) as CpuId,
                ) =~= Self::allocator_cache_lock_id_prefix(
                    cpu,
                ).insert(Self::allocator_cache_lock_id(cpu))) by {
                    Self::allocator_cache_lock_id_prefix_seq(
                        cpu,
                    ).lemma_push_to_set_commute(Self::allocator_cache_lock_id(cpu));
                    reveal(KernelK::allocator_cache_lock_id_prefix_seq);
                    reveal(KernelK::allocator_cache_lock_id_prefix);
                };
                assert(self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.lock_id_by_index(cpu)
                    == Self::allocator_cache_lock_id(cpu)) by {
                    reveal(allocator_perms_wf);
                    reveal(KernelK::allocator_cache_lock_id);
                };
                assert(lctx.lock_id_set() =~= old(lctx).lock_id_set()
                    - Self::allocator_cache_lock_id_prefix(
                        (cpu + 1) as CpuId,
                    )) by {
                    reveal(KernelK::allocator_cache_lock_id_prefix_seq);
                    reveal(KernelK::allocator_cache_lock_id_prefix);
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
            assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
            };
        }
    }

    // ================================================================
    // scan_caches_and_alloc: every cpu cache of `alloc_ptr_4k` is already
    // write-locked (perm for cpu `c` at `cache_perms[c]`), the process is
    // write-locked, and no lock above ALLOCATOR_CACHE_MAJOR is held (so the
    // global pool is NOT yet held). Iterate cpu 0..NUM_CPUS; on the first
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
        forall|c: CpuId|
            #![trigger cache_perms.spec_index(c)]
            cpu_id_valid(c) && c >= first_cpu
            ==> {
                &&& cache_perms.dom().contains(c)
                &&& cache_perms.spec_index(c).state() is WriteLock
                &&& cache_perms.spec_index(c).thread_id() == lctx.thread_id()
                &&& cache_perms.spec_index(c).lock_id()
                    == alloc_map.spec_index(alloc_ptr_4k)
                        .cpu_caches[c].view().locking_thread()->Write_lock_id
                &&& alloc_map.dom().contains(alloc_ptr_4k)
                &&& alloc_map.spec_index(alloc_ptr_4k)
                    .cpu_caches[c]@.wlocked_by(lctx)
            }
    }

    #[verifier::opaque]
    spec fn cache_perms_match_lctx(
        alloc_map: PageAllocatorUnLockedMap,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        lctx: &LocalContext,
        cache_perms: &Map<CpuId, LockPerm>,
    ) -> bool {
        forall|c: CpuId|
            #![trigger cache_perms.spec_index(c)]
            cpu_id_valid(c)
            ==> {
                &&& cache_perms.dom().contains(c)
                &&& cache_perms.spec_index(c).state() is WriteLock
                &&& cache_perms.spec_index(c).thread_id() == lctx.thread_id()
                &&& cache_perms.spec_index(c).lock_id()
                    == alloc_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().locking_thread()->Write_lock_id
                &&& alloc_map.dom().contains(alloc_ptr_4k)
                &&& alloc_map.spec_index(alloc_ptr_4k)
                    .cpu_caches[c]@.wlocked_by(lctx)
            }
    }

    fn scan_caches_and_alloc(
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(cache_perms): Tracked<&Map<CpuId, LockPerm>>,
        Tracked(process_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (bool, Option<(CpuId, PagePtr, Tracked<LockPerm>)>))
        requires
            old(self).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(self).container_map.dom().contains(container_ptr),
            old(self).process_map.dom().contains(process_ptr),
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            old(self).container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(self).process_map.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            old(self).process_map.spec_index(process_ptr).being_killed() == false,
            process_effective_quota_4k(old(self).process_map.spec_index(process_ptr)) >= 1,
            process_lock_perm.state() is WriteLock,
            process_lock_perm.thread_id() == old(lctx).thread_id(),
            process_lock_perm.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            Self::cache_perms_match_lctx(
                old(self).allocator_4k_map, alloc_ptr_4k, old(lctx), cache_perms),
            forall|held_lock_id: LockId|
                #![trigger old(lctx).lock_id_set().contains(held_lock_id)]
                old(lctx).lock_id_set().contains(held_lock_id)
                ==> held_lock_id.major <= ALLOCATOR_GLOBAL_POLL_MAJOR,
        ensures
            final(self).inv(),
            final(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
            final(self).process_map.lock_id_by_key(process_ptr)
                == old(self).process_map.lock_id_by_key(process_ptr),
            final(self).locked_objects_match_lctx(final(lctx)),
            lock_id_aligned(final(self), final(lctx)),
            // ---- user view unchanged: staging is kernel-internal ----
            kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
            // ---- failure: every cache was empty; complete no-op ----
            ret.0 == false ==> {
                &&& ret.1 is None
                &&& *final(self) == *old(self)
                &&& final(lctx).kernel_view_locking_state() is Acquire
                &&& final(lctx).wf()
                &&& final(lctx).lock_id_set() =~= old(lctx).lock_id_set()
                &&& lock_id_aligned(final(self), final(lctx))
                &&& forall|c: CpuId|
                    #![trigger final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c]]
                    cpu_id_valid(c)
                    ==> final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().view().view().len() == 0
            },
            // ---- success: popped + staged a page from cache `cpu`, page slot held ----
            ret.0 == true ==> {
                &&& ret.1 is Some
                &&& final(lctx).kernel_view_locking_state() is Release
                &&& cpu_id_valid(ret.1.unwrap().0)
                &&& page_ptr_valid(ret.1.unwrap().1)
                &&& page_index_wf(page_ptr2page_index(ret.1.unwrap().1))
                &&& final(self).page_array.unchanged_except(
                    &old(self).page_array, page_ptr2page_index(ret.1.unwrap().1))
                &&& final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool
                    == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool
                &&& final(self).page_array[page_ptr2page_index(ret.1.unwrap().1)].view().being_killed() == false
                &&& ret.1.unwrap().2.view().state() is WriteLock
                &&& ret.1.unwrap().2.view().thread_id() == final(lctx).thread_id()
                &&& ret.1.unwrap().2.view().lock_id() == final(self).page_array[page_ptr2page_index(ret.1.unwrap().1)].view().locking_thread()->Write_lock_id
                &&& final(self).page_array[page_ptr2page_index(ret.1.unwrap().1)]@
                    .wlocked_by(final(lctx))
                &&& final(lctx).wf()
                &&& final(lctx).lock_id_set() =~= old(lctx).lock_id_set().insert(
                    final(self).page_array.lock_id_by_index(
                        page_ptr2page_index(ret.1.unwrap().1)))
                &&& Self::cache_perms_match_lctx(
                    final(self).allocator_4k_map, alloc_ptr_4k, final(lctx), cache_perms)
                &&& final(self).process_map.dom().contains(process_ptr)
                &&& final(self).process_map.spec_index(process_ptr)
                    .wlocked_by(final(lctx))
                &&& final(self).process_map.spec_index(process_ptr).being_killed() == false
                &&& process_lock_perm.lock_id() == final(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id
                &&& final(self).process_map.spec_index(process_ptr).view_rodata()
                    == old(self).process_map.spec_index(process_ptr).view_rodata()
                &&& final(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view()
                    =~= old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view().insert(ret.1.unwrap().1)
                &&& final(self).page_array[page_ptr2page_index(ret.1.unwrap().1)].view().view().state == (PageState::Owned4k{ process_ptr })
                &&& final(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_2m
                    == old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_2m
                &&& final(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_1g
                    == old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_1g
                &&& final(self).process_map.spec_index(process_ptr).view().quota_4k
                    == old(self).process_map.spec_index(process_ptr).view().quota_4k
                &&& final(self).process_map.spec_index(process_ptr).view().owned_threads
                    == old(self).process_map.spec_index(process_ptr).view().owned_threads
                &&& final(self).container_map == old(self).container_map
                &&& final(self).scheduler_map == old(self).scheduler_map
                &&& final(self).pcid_allocator_map == old(self).pcid_allocator_map
                &&& final(self).cpu_array == old(self).cpu_array
            },
    {
        let mut cpu: CpuId = 0;
        while cpu < NUM_CPUS
            invariant
                *self == *old(self),
                self.inv(),
                self.locked_objects_match_lctx(&*lctx),
                lock_id_aligned(self, &*lctx),
                lctx.thread_id() == old(lctx).thread_id(),
                lctx.kernel_view_locking_state() is Acquire,
                lctx.user_view_locking_state() == old(lctx).user_view_locking_state(),
                lctx.lock_id_set() =~= old(lctx).lock_id_set(),
                0 <= cpu <= NUM_CPUS,
                self.container_map.dom().contains(container_ptr),
                self.allocator_4k_map.dom().contains(alloc_ptr_4k),
                self.container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
                self.process_map.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
                self.process_map.spec_index(process_ptr).being_killed() == false,
                process_effective_quota_4k(self.process_map.spec_index(process_ptr)) >= 1,
                process_lock_perm.state() is WriteLock,
                process_lock_perm.thread_id() == lctx.thread_id(),
                process_lock_perm.lock_id() == self.process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                self.process_map.dom().contains(process_ptr),
                self.process_map.spec_index(process_ptr).wlocked_by(&*lctx),
                Self::cache_perms_match_lctx(
                    self.allocator_4k_map, alloc_ptr_4k, &*lctx, cache_perms),
                forall|held_lock_id: LockId|
                    #![trigger lctx.lock_id_set().contains(held_lock_id)]
                    lctx.lock_id_set().contains(held_lock_id)
                    ==> held_lock_id.major <= ALLOCATOR_GLOBAL_POLL_MAJOR,
                // Caches [0, cpu) were all found empty.
                forall|c: CpuId|
                    #![trigger self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c]]
                    cpu_id_valid(c) && c < cpu
                    ==> self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().view().view().len() == 0,
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
                            .cpu_caches[cpu].view().locking_thread()->Write_lock_id
                    && self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches[cpu].view()
                        .write_lock_perm_match(&cache_perms.spec_index(cpu))
                    && self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches[cpu].view().being_killed() == false
                ) by {
                    reveal(allocator_perms_wf);
                    reveal(KernelK::cache_perms_match_lctx);
                };
            }
            let cache_ref = self.allocator_4k_map.borrow_cache(
                alloc_ptr_4k, cpu, Tracked(cache_perms.tracked_borrow(cpu)),
            );
            assert(cache_ref.linked_list.wf()) by {
                reveal(allocator_perms_wf);
                assert(
                    cpu_id_valid(cpu)
                    && self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches_wf()
                ) by {
                    reveal(allocator_perms_wf);
                };
            };
            let cache_len = cache_ref.linked_list.len();
            assert(cache_len == self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu].view().view().view().len()) by {
                reveal(allocator_perms_wf);
                cache_ref.linked_list.lemma_len_view();
            };
            if cache_len > 0 {
                let tracked selected_cache_perm = cache_perms.tracked_borrow(cpu);
                assert(lctx.lock_id_acyclic(
                    self.page_array.lock_id_by_index(page_ptr2page_index(
                        self.allocator_4k_map.spec_index(alloc_ptr_4k)
                            .cpu_caches[cpu]@@.view()[0],
                    )),
                )) by {
                    assert(page_ptr_valid(
                        self.allocator_4k_map.spec_index(alloc_ptr_4k)
                            .cpu_caches[cpu]@@.view()[0],
                    )) by {
                        reveal(allocator_free_page_ptrs_wf);
                        reveal(allocator_perms_wf);
                    };
                    assert(page_index_wf(page_ptr2page_index(
                        self.allocator_4k_map.spec_index(alloc_ptr_4k)
                            .cpu_caches[cpu]@@.view()[0],
                    ))) by {
                        page_ptr_lemma1();
                    };
                    reveal(allocator_perms_wf);
                    reveal(page_array_wf);
                    reveal(container_allocator_free_4k_page_wf);
                };
                let (page_ptr, Tracked(page_lock_perm)) = self.pop_stage_4k_page(
                    alloc_ptr_4k, cpu, process_ptr, container_ptr,
                    Tracked(&mut *lctx), Tracked(selected_cache_perm), Tracked(process_lock_perm),
                );
                assert(Self::cache_perms_match_lctx(
                    self.allocator_4k_map, alloc_ptr_4k, &*lctx, cache_perms,
                )) by {
                    reveal(KernelK::cache_perms_match_lctx);
                };
                return (true, Some((cpu, page_ptr, Tracked(page_lock_perm))));
            }
            cpu = cpu + 1;
        }
        (false, None)
    }

    // ================================================================
    // pop_stage_4k_page: cache[cpu_id] + process are already write-locked and
    // the cache is non-empty. Peek the head, lock the page slot, pop the head,
    // retype it Free4k{PreCpuCache}→Owned4k, stage it in the process's
    // temp_alloc_cache_4k, decrement the allocator's total_free_pages. Leaves
    // page + cache still write-locked; re-establishes inv().
    // ================================================================
    fn pop_stage_4k_page(
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        cpu_id: CpuId,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(cache_lock_perm): Tracked<&LockPerm>,
        Tracked(process_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(self).inv(),
            cpu_id_valid(cpu_id),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(self).container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(self).process_map.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            cache_lock_perm.state() is WriteLock,
            cache_lock_perm.thread_id() == old(lctx).thread_id(),
            cache_lock_perm.lock_id() == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@.locking_thread()->Write_lock_id,
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches[cpu_id]@.wlocked_by(old(lctx)),
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@@.view().len() > 0,
            old(self).process_map.spec_index(process_ptr).being_killed() == false,
            process_effective_quota_4k(old(self).process_map.spec_index(process_ptr)) >= 1,
            process_lock_perm.state() is WriteLock,
            process_lock_perm.thread_id() == old(lctx).thread_id(),
            process_lock_perm.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            old(self).process_map.dom().contains(process_ptr),
            old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            old(lctx).lock_id_acyclic(
                old(self).page_array.lock_id_by_index(page_ptr2page_index(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches[cpu_id]@@.view()[0],
                )),
            ),
        ensures
            final(self).inv(),
            page_ptr_valid(ret.0),
            final(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            final(self).page_array.unchanged_except(
                &old(self).page_array, page_ptr2page_index(ret.0)),
            // ---- user view unchanged: staging is kernel-internal ----
            kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
            // ---- cache + process lock state preserved, phase still Acquire ----
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
            cache_lock_perm.lock_id() == final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id].view().locking_thread()->Write_lock_id,
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id].lock_id()
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id].lock_id(),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.unchanged_except(
                &old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches, cpu_id),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches[cpu_id]@.wlocked_by(final(lctx)),
            final(self).process_map.spec_index(process_ptr).being_killed() == false,
            final(self).process_map.dom().contains(process_ptr),
            final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx)),
            process_lock_perm.lock_id() == final(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            final(self).process_map.spec_index(process_ptr).view_rodata() == old(self).process_map.spec_index(process_ptr).view_rodata(),
            final(self).process_map.lock_id_by_key(process_ptr)
                == old(self).process_map.lock_id_by_key(process_ptr),
            // ---- page slot left write-locked, perm handed back ----
            page_index_wf(page_ptr2page_index(ret.0)),
            final(self).page_array[page_ptr2page_index(ret.0)].view().wlocked_by(final(lctx)),
            final(self).page_array[page_ptr2page_index(ret.0)].view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(self).page_array[page_ptr2page_index(ret.0)].view().locking_thread()->Write_lock_id,
            // ---- lock_map: gained exactly the page slot; everything else preserved ----
            final(lctx).wf(),
            final(lctx).lock_id_set() =~= old(lctx).lock_id_set().insert(
                final(self).page_array.lock_id_by_index(page_ptr2page_index(ret.0))),
            final(self).locked_objects_match_lctx(final(lctx)),
            lock_id_aligned(final(self), final(lctx)),
            // ---- staging: ret staged Owned4k; 4k cache gained exactly ret, 2m/1g caches + nominal quota untouched ----
            final(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view()
                =~= old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view().insert(ret.0),
            final(self).page_array[page_ptr2page_index(ret.0)].view().view().state == (PageState::Owned4k{ process_ptr }),
            final(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_2m
                == old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_2m,
            final(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_1g
                == old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_1g,
            final(self).process_map.spec_index(process_ptr).view().quota_4k
                == old(self).process_map.spec_index(process_ptr).view().quota_4k,
            final(self).process_map.spec_index(process_ptr).view().owned_threads
                == old(self).process_map.spec_index(process_ptr).view().owned_threads,
            // ---- container_map + scheduler_map untouched (staging never writes them) ----
            final(self).container_map == old(self).container_map,
            final(self).scheduler_map == old(self).scheduler_map,
            final(self).pcid_allocator_map == old(self).pcid_allocator_map,
            final(self).cpu_array == old(self).cpu_array,
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
    {
        assert(
            self.allocator_4k_map.perms_wf()
            && self.allocator_4k_map.spec_index(alloc_ptr_4k).wf()
            && self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.inv()
            && self.process_map.perms_wf()
            && self.page_array.inv()
        ) by {
            reveal(allocator_perms_wf);
            reveal(process_perms_wf);
            reveal(page_array_wf);
        };
        let cache_ref = self.allocator_4k_map.borrow_cache(
            alloc_ptr_4k, cpu_id, Tracked(cache_lock_perm),
        );
        let (node_addr, page_ptr) = cache_ref.linked_list.peek_head();
        assert(page_ptr_valid(page_ptr)) by {
            reveal(allocator_perms_wf);
            reveal(allocator_free_page_ptrs_wf);
        };
        let page_index = page_ptr2page_index(page_ptr);
        assert(
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view().view().view().contains(page_ptr)
        ) by {
            reveal(LinkedList::wf_value_list);
        };
        // Lock the page slot: the caller established acyclicity for the list head.
        let Tracked(page_lock_perm) = self.wlock_page(page_index, Tracked(&mut *lctx));
        assert({
            &&& lctx.page_lock_map().dom().contains(page_index)
            &&& lctx.page_lock_map()[page_index]
                == old(self).page_array.lock_id_by_index(page_index)
        }) by {
            reveal(page_locked_match_lctx);
        };

        // Mutation block: pop + decrement (PageAllocator::inv() re-established by
        // the wrapper), retype Free4k→Owned4k, stage.
        assert(
            self.allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches[cpu_id]@@.linked_list.wf()
            && self.allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches[cpu_id]@@.linked_list.view().no_duplicates()
        ) by {
            reveal(allocator_perms_wf);
        };
        let alloc_mut = self.allocator_4k_map.borrow_mut(alloc_ptr_4k);
        let (node_addr2, Tracked(node_perm)) = alloc_mut.pop_cache_page(cpu_id, Tracked(&*lctx), Tracked(cache_lock_perm));
        assert(node_addr2 == node_addr) by {
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view().view().linked_list
                .lemma_value_addr_unique(node_addr, node_addr2);
        };
        assert(
            self.page_array.inv()
            && self.process_map.perms_wf()
            && self.process_map.spec_index(process_ptr).is_init()
        ) by {
            reveal(page_array_wf);
            reveal(process_perms_wf);
        };

        {
            let mut page = self.page_array.borrow_mut(page_index, Tracked(&*lctx), Tracked(&page_lock_perm));
            assert(page.state is Free4k) by {
                reveal(container_allocator_free_4k_page_wf);
            };
            page.state = PageState::Owned4k { process_ptr };
            assert(node_addr == page.free_list_node_storage.addr()) by {
                reveal(container_allocator_free_4k_page_wf);
                reveal(LinkedList::wf_map);
                assert(
                    old(self).container_map.spec_index(old(self).page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k
                ) by {
                    reveal(container_allocator_wf);
                };
            };
            page.free_list_node_storage.put(Tracked(node_perm));

            let process_mut = self.process_map.borrow_mut(
                process_ptr, Tracked(&*lctx), Tracked(process_lock_perm),
            );
            process_mut.temp_alloc_cache_4k = Ghost(process_mut.temp_alloc_cache_4k@.insert(page_ptr));
        }
        proof {
            lctx.enter_kernel_view_release();
            lctx.update_lock_id(
                KernelObjId::Page(page_index),
                self.page_array.lock_id_by_index(page_index),
            );
            assert(page_locked_match_lctx(
                self.page_array,
                lctx.page_lock_map(),
                lctx.thread_id(),
            )) by {
                reveal(page_locked_match_lctx);
            };
        }
        // ---- staging delta: page_ptr fresh in temp_alloc_cache_4k ⟹ effective_quota_4k −1 ----
        assert(old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) == false) by {
            page_ptr_lemma1();
            reveal(process_staged_pages_4k_wf);
            if old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) {
                assert(old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == PageState::Owned4k { process_ptr }) by {
                    reveal(process_staged_pages_4k_wf);
                };
            }
        };
        proof {
            // ---- user view unchanged: only page_array / temp_alloc / total moved ----
            assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
            };
            assert(self.locked_objects_match_lctx(&*lctx)) by {
                reveal(process_locked_match_lctx);
                reveal(allocator_4k_locked_match_lctx);
            };
        }
        proof {
            // ---- subsystems_inv ----
            assert(self.subsystems_inv()) by {
                reveal(KernelK::default_pagetable_wf);
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(container_tree_fields_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
                reveal(process_temp_alloc_empty_unless_wlocked);
                reveal(page_array_wf);
                reveal(thread_perms_wf);
                reveal(thread_free_quota_pending_empty_unless_wlocked);
            };
            // ---- memory_management_inv ----
            assert(self.memory_management_inv()) by {
                assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    allocator_4k_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_4k_map, self.allocator_4k_map);
                    allocator_2m_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_2m_map, self.allocator_2m_map);
                    allocator_1g_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_1g_map, self.allocator_1g_map);
                };
                assert(container_page_owner_wf(self.container_map, self.page_array)) by { container_page_owner_wf_preserved_for_owning_container_eq(old(self).container_map, self.container_map, old(self).page_array, self.page_array); };
                assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                    reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                    reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                };
                assert(container_pages_wf(self.page_array, self.container_map)) by { container_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).container_map, self.container_map); };
                assert(process_pages_wf(self.page_array, self.process_map)) by { process_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).process_map, self.process_map); };
                assert(container_process_allocator_quota_4k_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map)) by {
                    reveal(container_process_allocator_quota_4k_wf);
                    reveal(container_process_wf);
                    reveal(container_allocator_wf);
                    lemma_process_effective_quota_4k_fold_change_by_forall(process_ptr, -1);
                    lemma_process_effective_quota_4k_fold_sum_eq_forall();
                };
                assert(container_process_allocator_quota_2m_wf(self.container_map, self.process_map, self.thread_map, self.allocator_2m_map)) by {
                    container_process_allocator_quota_2m_wf_forall();
                };
                assert(container_process_allocator_quota_1g_wf(self.container_map, self.process_map, self.thread_map, self.allocator_1g_map)) by {
                    container_process_allocator_quota_1g_wf_forall();
                };
                assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    reveal(container_allocator_wf);
                };
                assert(allocator_free_page_ptrs_wf(self.allocator_4k_map)) by {
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { reveal(process_pagetable_match); };
                assert(process_iommu_table_match(self.process_map, self.iommu_table_map)) by {
                    reveal(process_iommu_table_match);
                };
                assert(hugepage_2m_wf(self.page_array)) by { hugepage_2m_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array); };
                assert(hugepage_1g_wf(self.page_array)) by { hugepage_1g_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array); };
                assert(page_pagetable_wf(self.pagetable_map, self.page_array)) by {
                    page_pagetable_wf_preserved_for_nonmapped_page_change(
                        old(self).pagetable_map,
                        self.pagetable_map,
                        old(self).page_array,
                        self.page_array,
                        page_index,
                    );
                };
                assert(pagetable_pages_wf(self.pagetable_map, self.page_array)) by { reveal(pagetable_pages_wf); };
                assert(iommu_table_pages_wf(self.iommu_table_map, self.page_array)) by {
                    reveal(iommu_table_pages_wf);
                };
                assert(thread_pages_wf(self.thread_map, self.page_array)) by { thread_pages_wf_preserved_for_page_state_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array); };
                assert(pcid_allocator_pages_wf(
                    self.page_array,
                    self.pcid_allocator_map,
                )) by {
                    pcid_allocator_pages_wf_preserved_for_page_state_eq(
                        old(self).page_array,
                        self.page_array,
                        old(self).pcid_allocator_map,
                        self.pcid_allocator_map,
                    );
                };
                assert(process_staged_pages_wf(self.process_map, self.page_array)) by {
                    reveal(process_staged_pages_4k_wf);
                    process_staged_pages_2m_wf_preserved_for_eq(old(self).process_map, self.process_map, old(self).page_array, self.page_array);
                    process_staged_pages_1g_wf_preserved_for_eq(old(self).process_map, self.process_map, old(self).page_array, self.page_array);
                };
                assert(endpoint_pages_wf(self.endpoint_map, self.page_array)) by { endpoint_pages_wf_preserved_for_page_state_eq(old(self).endpoint_map, self.endpoint_map, old(self).page_array, self.page_array); };
                assert(container_allocator_free_4k_page_wf(self.container_map, self.allocator_4k_map, self.page_array)) by {
                    reveal(container_allocator_free_4k_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                    reveal(container_allocator_wf);
                    reveal(container_page_owner_wf);
                    reveal(LinkedList::value_list_unique);
                    seq_skip_lemma::<PagePtr>();
                };
                assert(container_allocator_free_2m_page_wf(self.container_map, self.allocator_2m_map, self.page_array)) by {
                    reveal(container_allocator_free_2m_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                    page_ptr_lemma1();
                };
                assert(container_allocator_free_1g_page_wf(self.container_map, self.allocator_1g_map, self.page_array)) by {
                    reveal(container_allocator_free_1g_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                    page_ptr_lemma1();
                };
            };
            // ---- process_management_inv: container_map, thread_map, etc. all byte-equal ----
            assert(self.process_management_inv()) by {
                assert(process_pcid_fields_unchanged(
                    old(self).process_map,
                    self.process_map,
                )) by {
                    reveal(process_pcid_fields_unchanged);
                };
                process_pcid_allocator_wf_preserved_for_fields_unchanged(
                    self.container_map,
                    old(self).process_map,
                    self.process_map,
                    self.pcid_allocator_map,
                );
                assert(container_process_wf(self.container_map, self.process_map)) by {
                    reveal(container_process_wf);
                };
                assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                    per_container_process_tree_wf_preserved_for_tree_fields_eq(
                        self.container_map,
                        old(self).process_map,
                        self.process_map,
                    );
                };
                assert(process_cpu_wf(self.process_map, self.cpu_array)) by {
                    reveal(process_cpu_wf);
                };
                assert(process_thread_wf(self.process_map, self.thread_map)) by {
                    reveal(process_thread_wf);
                };
            };
            assert(process_reference_fields_unchanged(
                old(self).process_map,
                self.process_map,
            )) by {
                reveal(process_reference_fields_unchanged);
            };
            iommu_root_table_process_wf_preserved_for_process_reference_fields(
                &self.iommu_root_table,
                old(self).process_map,
                self.process_map,
                self.iommu_table_map,
            );
            process_pci_function_ownership_wf_preserved_for_process_reference_fields(
                &self.iommu_root_table,
                old(self).process_map,
                self.process_map,
            );
            iommu_tlb_wf_spec_preserved_for_process_reference_fields(
                self.iommu_tlb,
                &self.iommu_root_table,
                old(self).process_map,
                self.process_map,
                self.iommu_table_map,
            );
            // ---- inv() direct conjuncts ----
            assert(self.inv()) by {
                reveal(cpu_dirty_map_contains_container_processes);
                reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                reveal(cpu_dirty_map_proc_pcid_match);
                reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                reveal(container_cpu_wf);
                reveal(tlb_wf_spec);
            };
            assert(lock_id_aligned(&*self, &*lctx)) by {
                reveal(page_locked_match_lctx);
                reveal(page_lock_id_aligned);
            };
        }
        (page_ptr, Tracked(page_lock_perm))
    }

    // ================================================================
    // pop_stage_global_4k_page: global-pool twin of pop_stage_4k_page. The
    // allocator's global_pool + the process are already write-locked and the
    // pool is non-empty. Peek the head, lock the page slot, pop the head,
    // retype it Free4k{GlobalList}→Owned4k, stage it in the process's
    // temp_alloc_cache_4k, decrement the allocator's total_free_pages. Leaves
    // page + global_pool still write-locked; re-establishes inv().
    // ================================================================
    fn pop_stage_global_4k_page(
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(global_pool_lock_perm): Tracked<&LockPerm>,
        Tracked(process_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(self).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(self).container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(self).process_map.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            global_pool_lock_perm.state() is WriteLock,
            global_pool_lock_perm.thread_id() == old(lctx).thread_id(),
            global_pool_lock_perm.lock_id() == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.locking_thread()->Write_lock_id,
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.wlocked_by(old(lctx)),
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().view().len() > 0,
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().len() > 0,
            old(self).process_map.spec_index(process_ptr).being_killed() == false,
            process_effective_quota_4k(old(self).process_map.spec_index(process_ptr)) >= 1,
            process_lock_perm.state() is WriteLock,
            process_lock_perm.thread_id() == old(lctx).thread_id(),
            process_lock_perm.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            old(self).process_map.dom().contains(process_ptr),
            old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            old(lctx).lock_id_acyclic(
                old(self).page_array.lock_id_by_index(page_ptr2page_index(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .global_pool.view().view()[0],
                )),
            ),
        ensures
            final(self).inv(),
            page_ptr_valid(ret.0),
            final(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            final(self).page_array.unchanged_except(
                &old(self).page_array, page_ptr2page_index(ret.0)),
            // ---- user view unchanged: staging is kernel-internal ----
            kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
            // ---- global_pool + process lock state preserved, phase still Acquire ----
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
            global_pool_lock_perm.lock_id() == final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.locking_thread()->Write_lock_id,
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.lock_id()
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.lock_id(),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches,
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.wlocked_by(final(lctx)),
            final(self).process_map.spec_index(process_ptr).being_killed() == false,
            final(self).process_map.dom().contains(process_ptr),
            final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx)),
            process_lock_perm.lock_id() == final(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            final(self).process_map.spec_index(process_ptr).view_rodata() == old(self).process_map.spec_index(process_ptr).view_rodata(),
            final(self).process_map.lock_id_by_key(process_ptr)
                == old(self).process_map.lock_id_by_key(process_ptr),
            // ---- page slot left write-locked, perm handed back ----
            page_index_wf(page_ptr2page_index(ret.0)),
            final(self).page_array[page_ptr2page_index(ret.0)].view().wlocked_by(final(lctx)),
            final(self).page_array[page_ptr2page_index(ret.0)].view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(self).page_array[page_ptr2page_index(ret.0)].view().locking_thread()->Write_lock_id,
            // ---- lock_map: gained exactly the page slot; everything else preserved ----
            final(lctx).wf(),
            final(lctx).lock_id_set() =~= old(lctx).lock_id_set().insert(
                final(self).page_array.lock_id_by_index(page_ptr2page_index(ret.0))),
            final(self).locked_objects_match_lctx(final(lctx)),
            lock_id_aligned(final(self), final(lctx)),
            // ---- staging: ret staged Owned4k; 4k cache gained exactly ret, 2m/1g caches + nominal quota untouched ----
            final(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view()
                =~= old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view().insert(ret.0),
            final(self).page_array[page_ptr2page_index(ret.0)].view().view().state == (PageState::Owned4k{ process_ptr }),
            final(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_2m
                == old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_2m,
            final(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_1g
                == old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_1g,
            final(self).process_map.spec_index(process_ptr).view().quota_4k
                == old(self).process_map.spec_index(process_ptr).view().quota_4k,
            final(self).process_map.spec_index(process_ptr).view().owned_threads
                == old(self).process_map.spec_index(process_ptr).view().owned_threads,
            // ---- container_map + scheduler_map untouched (staging never writes them) ----
            final(self).container_map == old(self).container_map,
            final(self).scheduler_map == old(self).scheduler_map,
            final(self).pcid_allocator_map == old(self).pcid_allocator_map,
            final(self).cpu_array == old(self).cpu_array,
    {
        assert(
            self.allocator_4k_map.perms_wf()
            && self.allocator_4k_map.spec_index(alloc_ptr_4k).wf()
            && self.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.inv()
            && self.process_map.perms_wf()
            && self.page_array.inv()
        ) by {
            reveal(allocator_perms_wf);
            reveal(process_perms_wf);
            reveal(page_array_wf);
        };
        let poll_ref = self.allocator_4k_map.borrow_global_pool(
            alloc_ptr_4k, Tracked(global_pool_lock_perm),
        );
        let (node_addr, page_ptr) = poll_ref.peek_head();
        assert(page_ptr_valid(page_ptr))
        by {
            reveal(allocator_perms_wf);
            reveal(allocator_free_page_ptrs_wf);
        }
        ;
        let page_index = page_ptr2page_index(page_ptr);
        // The peeked page_ptr is the head of the global pool, so it is in that
        // pool's view() — the reverse-global_pool clause pins the page's state to
        // Free4k{GlobalList}.
        assert(
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().view().contains(page_ptr)
        ) by {
            reveal(LinkedList::wf_value_list);
        };
        assert(self.page_array.spec_index(page_index).view().view().state is Free4k) by {
            reveal(container_allocator_free_4k_page_wf);
        };
        // Lock the page slot: the caller established acyclicity for the list head.
        let Tracked(page_lock_perm) = self.wlock_page(page_index, Tracked(&mut *lctx));
        assert({
            &&& lctx.page_lock_map().dom().contains(page_index)
            &&& lctx.page_lock_map()[page_index]
                == old(self).page_array.lock_id_by_index(page_index)
        }) by {
            reveal(page_locked_match_lctx);
        };

        // Mutation block: pop + decrement (PageAllocator::inv() re-established by
        // the wrapper), retype Free4k→Owned4k, stage.
        let alloc_mut = self.allocator_4k_map.borrow_mut(alloc_ptr_4k);
        let (node_addr2, Tracked(node_perm)) = alloc_mut.pop_global_pool_page(Tracked(&*lctx), Tracked(global_pool_lock_perm));
        assert(node_addr2 == node_addr) by {
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.view().linked_list
                .lemma_value_addr_unique(node_addr, node_addr2);
        };
        assert(
            self.page_array.inv()
            && self.process_map.perms_wf()
            && self.process_map.spec_index(process_ptr).is_init()
        ) by {
            reveal(page_array_wf);
            reveal(process_perms_wf);
        };

        {
            let mut page = self.page_array.borrow_mut(page_index, Tracked(&*lctx), Tracked(&page_lock_perm));
            assert(page.state is Free4k) by {
                reveal(container_allocator_free_4k_page_wf);
            };
            page.state = PageState::Owned4k { process_ptr };
            assert(node_addr == page.free_list_node_storage.addr()) by {
                reveal(container_allocator_free_4k_page_wf);
                reveal(LinkedList::wf_map);
                assert(
                    old(self).container_map.spec_index(old(self).page_array.spec_index(page_index).view().view().owning_container).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k
                ) by {
                    reveal(container_allocator_wf);
                };
            };
            page.free_list_node_storage.put(Tracked(node_perm));

            let process_mut = self.process_map.borrow_mut(
                process_ptr, Tracked(&*lctx), Tracked(process_lock_perm),
            );
            process_mut.temp_alloc_cache_4k = Ghost(process_mut.temp_alloc_cache_4k.view().insert(page_ptr));
        }
        proof {
            lctx.enter_kernel_view_release();
            lctx.update_lock_id(
                KernelObjId::Page(page_index),
                self.page_array.lock_id_by_index(page_index),
            );
            assert(page_locked_match_lctx(
                self.page_array,
                lctx.page_lock_map(),
                lctx.thread_id(),
            )) by {
                reveal(page_locked_match_lctx);
            };
        }
        // ---- staging delta: page_ptr fresh in temp_alloc_cache_4k ⟹ effective_quota_4k −1 ----
        assert(old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) == false) by {
            page_ptr_lemma1();
            reveal(process_staged_pages_4k_wf);
            if old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) {
                assert(old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == PageState::Owned4k { process_ptr }) by {
                    reveal(process_staged_pages_4k_wf);
                };
            }
        };
        proof {
            // ---- user view unchanged: only page_array / temp_alloc / total moved ----
            assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
            };
            assert(self.locked_objects_match_lctx(&*lctx)) by {
                reveal(process_locked_match_lctx);
                reveal(allocator_4k_locked_match_lctx);
            };
        }
        proof {
            // ---- subsystems_inv ----
            assert(self.subsystems_inv()) by {
                reveal(KernelK::default_pagetable_wf);
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(container_tree_fields_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
                reveal(process_temp_alloc_empty_unless_wlocked);
                reveal(page_array_wf);
                reveal(thread_perms_wf);
                reveal(thread_free_quota_pending_empty_unless_wlocked);
            };
            // ---- memory_management_inv ----
            assert(self.memory_management_inv()) by {
                assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    allocator_4k_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_4k_map, self.allocator_4k_map);
                    allocator_2m_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_2m_map, self.allocator_2m_map);
                    allocator_1g_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_1g_map, self.allocator_1g_map);
                };
                assert(container_page_owner_wf(self.container_map, self.page_array)) by { container_page_owner_wf_preserved_for_owning_container_eq(old(self).container_map, self.container_map, old(self).page_array, self.page_array); };
                assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                    reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                    reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                };
                assert(container_pages_wf(self.page_array, self.container_map)) by { container_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).container_map, self.container_map); };
                assert(process_pages_wf(self.page_array, self.process_map)) by { process_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).process_map, self.process_map); };
                assert(container_process_allocator_quota_4k_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map)) by {
                    reveal(container_process_allocator_quota_4k_wf);
                    reveal(container_process_wf);
                    reveal(container_allocator_wf);
                    lemma_process_effective_quota_4k_fold_change_by_forall(process_ptr, -1);
                    lemma_process_effective_quota_4k_fold_sum_eq_forall();
                };
                assert(container_process_allocator_quota_2m_wf(self.container_map, self.process_map, self.thread_map, self.allocator_2m_map)) by {
                    container_process_allocator_quota_2m_wf_forall();
                };
                assert(container_process_allocator_quota_1g_wf(self.container_map, self.process_map, self.thread_map, self.allocator_1g_map)) by {
                    container_process_allocator_quota_1g_wf_forall();
                };
                assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    reveal(container_allocator_wf);
                };
                assert(allocator_free_page_ptrs_wf(self.allocator_4k_map)) by {
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { reveal(process_pagetable_match); };
                assert(process_iommu_table_match(self.process_map, self.iommu_table_map)) by {
                    reveal(process_iommu_table_match);
                };
                assert(hugepage_2m_wf(self.page_array)) by { hugepage_2m_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array); };
                assert(hugepage_1g_wf(self.page_array)) by { hugepage_1g_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array); };
                assert(page_pagetable_wf(self.pagetable_map, self.page_array)) by {
                    page_pagetable_wf_preserved_for_nonmapped_page_change(
                        old(self).pagetable_map,
                        self.pagetable_map,
                        old(self).page_array,
                        self.page_array,
                        page_index,
                    );
                };
                assert(pagetable_pages_wf(self.pagetable_map, self.page_array)) by { reveal(pagetable_pages_wf); };
                assert(iommu_table_pages_wf(self.iommu_table_map, self.page_array)) by {
                    reveal(iommu_table_pages_wf);
                };
                assert(thread_pages_wf(self.thread_map, self.page_array)) by { thread_pages_wf_preserved_for_page_state_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array); };
                assert(pcid_allocator_pages_wf(
                    self.page_array,
                    self.pcid_allocator_map,
                )) by {
                    pcid_allocator_pages_wf_preserved_for_page_state_eq(
                        old(self).page_array,
                        self.page_array,
                        old(self).pcid_allocator_map,
                        self.pcid_allocator_map,
                    );
                };
                assert(process_staged_pages_wf(self.process_map, self.page_array)) by {
                    reveal(process_staged_pages_4k_wf);
                    process_staged_pages_2m_wf_preserved_for_eq(old(self).process_map, self.process_map, old(self).page_array, self.page_array);
                    process_staged_pages_1g_wf_preserved_for_eq(old(self).process_map, self.process_map, old(self).page_array, self.page_array);
                };
                assert(endpoint_pages_wf(self.endpoint_map, self.page_array)) by { endpoint_pages_wf_preserved_for_page_state_eq(old(self).endpoint_map, self.endpoint_map, old(self).page_array, self.page_array); };
                assert(container_allocator_free_4k_page_wf(self.container_map, self.allocator_4k_map, self.page_array)) by {
                    reveal(container_allocator_free_4k_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                    reveal(container_allocator_wf);
                    reveal(container_page_owner_wf);
                    reveal(LinkedList::value_list_unique);
                    seq_skip_lemma::<PagePtr>();
                };
                assert(container_allocator_free_2m_page_wf(self.container_map, self.allocator_2m_map, self.page_array)) by {
                    reveal(container_allocator_free_2m_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                    page_ptr_lemma1();
                };
                assert(container_allocator_free_1g_page_wf(self.container_map, self.allocator_1g_map, self.page_array)) by {
                    reveal(container_allocator_free_1g_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                    page_ptr_lemma1();
                };
            };
            // ---- process_management_inv: container_map, thread_map, etc. all byte-equal ----
            assert(self.process_management_inv()) by {
                assert(process_pcid_fields_unchanged(
                    old(self).process_map,
                    self.process_map,
                )) by {
                    reveal(process_pcid_fields_unchanged);
                };
                process_pcid_allocator_wf_preserved_for_fields_unchanged(
                    self.container_map,
                    old(self).process_map,
                    self.process_map,
                    self.pcid_allocator_map,
                );
                assert(container_process_wf(self.container_map, self.process_map)) by {
                    reveal(container_process_wf);
                };
                assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                    per_container_process_tree_wf_preserved_for_tree_fields_eq(
                        self.container_map,
                        old(self).process_map,
                        self.process_map,
                    );
                };
                assert(process_cpu_wf(self.process_map, self.cpu_array)) by {
                    reveal(process_cpu_wf);
                };
                assert(process_thread_wf(self.process_map, self.thread_map)) by {
                    reveal(process_thread_wf);
                };
            };
            assert(process_reference_fields_unchanged(
                old(self).process_map,
                self.process_map,
            )) by {
                reveal(process_reference_fields_unchanged);
            };
            iommu_root_table_process_wf_preserved_for_process_reference_fields(
                &self.iommu_root_table,
                old(self).process_map,
                self.process_map,
                self.iommu_table_map,
            );
            process_pci_function_ownership_wf_preserved_for_process_reference_fields(
                &self.iommu_root_table,
                old(self).process_map,
                self.process_map,
            );
            iommu_tlb_wf_spec_preserved_for_process_reference_fields(
                self.iommu_tlb,
                &self.iommu_root_table,
                old(self).process_map,
                self.process_map,
                self.iommu_table_map,
            );
            // ---- inv() direct conjuncts ----
            assert(self.inv()) by {
                reveal(cpu_dirty_map_contains_container_processes);
                reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                reveal(cpu_dirty_map_proc_pcid_match);
                reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                reveal(container_cpu_wf);
                reveal(tlb_wf_spec);
            };
            assert(lock_id_aligned(&*self, &*lctx)) by {
                reveal(page_locked_match_lctx);
                reveal(page_lock_id_aligned);
            };
        }
        (page_ptr, Tracked(page_lock_perm))
    }

}

/// Quantified-fact form of the `container_process_allocator_quota_2m_wf`
/// conservation transport across a process-map mutation that leaves every
/// process's 2m effective quota intact (a 4k staging op does — it only touches
/// `temp_alloc_cache_4k`). One invocation installs the fact for ALL
/// `(container_map, thread_map, allocator_2m_map, old, new)`, so a caller need
/// not spell out the per-container fold argument or wrap it in an `assert forall`
/// — the SMT re-derives the target conjunct wherever the goal needs it. The
/// thread-folds and allocator terms are byte-equal (only `process_map` moved), so
/// only the process-fold is bridged, via `lemma_process_effective_quota_2m_fold_eq`.
/// Multi-trigger on the source + target `container_process_allocator_quota_2m_wf`
/// terms.
pub proof fn container_process_allocator_quota_2m_wf_forall()
    ensures
        forall|
            container_map: ContainerLockedMap,
            thread_map: ThreadLockedMap,
            allocator_2m_map: PageAllocatorUnLockedMap,
            old_process_map: ProcessLockedMap,
            new_process_map: ProcessLockedMap,
        |
            #![trigger container_process_allocator_quota_2m_wf(container_map, old_process_map, thread_map, allocator_2m_map), container_process_allocator_quota_2m_wf(container_map, new_process_map, thread_map, allocator_2m_map)]
            (container_process_allocator_quota_2m_wf(container_map, old_process_map, thread_map, allocator_2m_map)
            && container_process_wf(container_map, old_process_map)
            && forall|p: RwLockProcessPtr|
                #![trigger process_effective_quota_2m(new_process_map.spec_index(p))]
                old_process_map.dom().contains(p) ==>
                    process_effective_quota_2m(new_process_map.spec_index(p)) == process_effective_quota_2m(old_process_map.spec_index(p)))
            ==>
            container_process_allocator_quota_2m_wf(container_map, new_process_map, thread_map, allocator_2m_map),
{
    assert forall|
        container_map: ContainerLockedMap,
        thread_map: ThreadLockedMap,
        allocator_2m_map: PageAllocatorUnLockedMap,
        old_process_map: ProcessLockedMap,
        new_process_map: ProcessLockedMap,
    |  #![auto]
        (container_process_allocator_quota_2m_wf(container_map, old_process_map, thread_map, allocator_2m_map)
        && container_process_wf(container_map, old_process_map)
        && forall|p: RwLockProcessPtr|
            #![trigger process_effective_quota_2m(new_process_map.spec_index(p))]
            old_process_map.dom().contains(p) ==>
                process_effective_quota_2m(new_process_map.spec_index(p)) == process_effective_quota_2m(old_process_map.spec_index(p)))
        implies
        container_process_allocator_quota_2m_wf(container_map, new_process_map, thread_map, allocator_2m_map)
    by {
        reveal(container_process_allocator_quota_2m_wf);
        reveal(container_process_wf);
        assert forall|c_ptr: RwLockContainerPtr|
            #![trigger container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m]
            container_map.dom().contains(c_ptr)
        implies
            container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_2m(new_process_map.spec_index(p_ptr))})
                + container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + thread_map.spec_index(t_ptr).view().direct_free_quota_pending_2m.view()})
                + container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_2m.view().spec_index(container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                + allocator_2m_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).quota.view().view()
                == allocator_2m_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).total_free_pages.view()
        by {
            assert(container_map.spec_index(c_ptr).view().owned_processes.view().subset_of(old_process_map.dom())) by {
                reveal(container_process_wf);
            };
            lemma_process_effective_quota_2m_fold_eq(
                container_map.spec_index(c_ptr).view().owned_processes.view(),
                old_process_map, new_process_map);
        };
    };
}

/// 1g twin of `container_process_allocator_quota_2m_wf_forall` — identical shape,
/// process-fold bridged via `lemma_process_effective_quota_1g_fold_eq`.
pub proof fn container_process_allocator_quota_1g_wf_forall()
    ensures
        forall|
            container_map: ContainerLockedMap,
            thread_map: ThreadLockedMap,
            allocator_1g_map: PageAllocatorUnLockedMap,
            old_process_map: ProcessLockedMap,
            new_process_map: ProcessLockedMap,
        |
            #![trigger container_process_allocator_quota_1g_wf(container_map, old_process_map, thread_map, allocator_1g_map), container_process_allocator_quota_1g_wf(container_map, new_process_map, thread_map, allocator_1g_map)]
            (container_process_allocator_quota_1g_wf(container_map, old_process_map, thread_map, allocator_1g_map)
            && container_process_wf(container_map, old_process_map)
            && forall|p: RwLockProcessPtr|
                #![trigger process_effective_quota_1g(new_process_map.spec_index(p))]
                old_process_map.dom().contains(p) ==>
                    process_effective_quota_1g(new_process_map.spec_index(p)) == process_effective_quota_1g(old_process_map.spec_index(p)))
            ==>
            container_process_allocator_quota_1g_wf(container_map, new_process_map, thread_map, allocator_1g_map),
{
    assert forall|
        container_map: ContainerLockedMap,
        thread_map: ThreadLockedMap,
        allocator_1g_map: PageAllocatorUnLockedMap,
        old_process_map: ProcessLockedMap,
        new_process_map: ProcessLockedMap,
    |  #![auto]
        (container_process_allocator_quota_1g_wf(container_map, old_process_map, thread_map, allocator_1g_map)
        && container_process_wf(container_map, old_process_map)
        && forall|p: RwLockProcessPtr|
            #![trigger process_effective_quota_1g(new_process_map.spec_index(p))]
            old_process_map.dom().contains(p) ==>
                process_effective_quota_1g(new_process_map.spec_index(p)) == process_effective_quota_1g(old_process_map.spec_index(p)))
        implies
        container_process_allocator_quota_1g_wf(container_map, new_process_map, thread_map, allocator_1g_map)
    by {
        reveal(container_process_allocator_quota_1g_wf);
        reveal(container_process_wf);
        assert forall|c_ptr: RwLockContainerPtr|
            #![trigger container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g]
            container_map.dom().contains(c_ptr)
        implies
            container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_1g(new_process_map.spec_index(p_ptr))})
                + container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + thread_map.spec_index(t_ptr).view().direct_free_quota_pending_1g.view()})
                + container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_1g.view().spec_index(container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                + allocator_1g_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).quota.view().view()
                == allocator_1g_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).total_free_pages.view()
        by {
            assert(container_map.spec_index(c_ptr).view().owned_processes.view().subset_of(old_process_map.dom())) by {
                reveal(container_process_wf);
            };
            lemma_process_effective_quota_1g_fold_eq(
                container_map.spec_index(c_ptr).view().owned_processes.view(),
                old_process_map, new_process_map);
        };
    };
}

/// Forall-wrapped `lemma_process_effective_quota_4k_fold_eq`, triggered on the
/// `process_effective_quota_4k_fold_sum` terms so it fires directly off a
/// revealed `container_process_allocator_quota_4k_wf`.
pub proof fn lemma_process_effective_quota_4k_fold_sum_eq_forall()
    ensures
        forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap|
            #![trigger process_effective_quota_4k_fold_sum(s, post), process_effective_quota_4k_fold_sum(s, pre)]
            (forall|p: RwLockProcessPtr|
                #![trigger process_effective_quota_4k(pre.spec_index(p))]
                s.contains(p) ==> process_effective_quota_4k(post.spec_index(p)) == process_effective_quota_4k(pre.spec_index(p)))
            ==>
            process_effective_quota_4k_fold_sum(s, post) == process_effective_quota_4k_fold_sum(s, pre),
{
    assert forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap|  #![auto]
        (forall|p: RwLockProcessPtr|  #![auto]
            s.contains(p) ==> process_effective_quota_4k(post.spec_index(p)) == process_effective_quota_4k(pre.spec_index(p)))
    implies
        process_effective_quota_4k_fold_sum(s, post) == process_effective_quota_4k_fold_sum(s, pre)
    by {
        lemma_process_effective_quota_4k_fold_eq(s, pre, post);
    };
}

/// Forall-wrapped `lemma_process_effective_quota_4k_fold_change_by`, triggered on
/// the `process_effective_quota_4k_fold_sum` terms so it fires directly off a
/// revealed `container_process_allocator_quota_4k_wf`. `mod_p`/`x` are params
/// (the delta `x` can only appear additively in the conclusion, so it cannot be
/// trigger-bound).
pub proof fn lemma_process_effective_quota_4k_fold_change_by_forall(mod_p: RwLockProcessPtr, x: int)
    ensures
        forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap|
            #![trigger process_effective_quota_4k_fold_sum(s, post), process_effective_quota_4k_fold_sum(s, pre)]
            (s.contains(mod_p)
            && process_effective_quota_4k(post.spec_index(mod_p)) == process_effective_quota_4k(pre.spec_index(mod_p)) + x
            && forall|p: RwLockProcessPtr|
                #![trigger process_effective_quota_4k(pre.spec_index(p))]
                s.contains(p) && p != mod_p ==> process_effective_quota_4k(post.spec_index(p)) == process_effective_quota_4k(pre.spec_index(p)))
            ==>
            process_effective_quota_4k_fold_sum(s, post) == process_effective_quota_4k_fold_sum(s, pre) + x,
{
    assert forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap|  #![auto]
        (s.contains(mod_p)
        && process_effective_quota_4k(post.spec_index(mod_p)) == process_effective_quota_4k(pre.spec_index(mod_p)) + x
        && forall|p: RwLockProcessPtr|  #![auto]
            s.contains(p) && p != mod_p ==> process_effective_quota_4k(post.spec_index(p)) == process_effective_quota_4k(pre.spec_index(p)))
    implies
        process_effective_quota_4k_fold_sum(s, post) == process_effective_quota_4k_fold_sum(s, pre) + x
    by {
        lemma_process_effective_quota_4k_fold_change_by(s, pre, post, mod_p, x);
    };
}

/// After a failed cache scan (every cpu cache of `alloc_ptr_4k` empty), the
/// container conservation law forces the global pool to be non-empty: the
/// total free-page count equals the pool length (all cache summands are zero),
/// and that total is at least the held process's `effective_quota_4k >= 1`
/// because every other conservation summand (sibling processes' effective
/// quotas, both thread-pending folds, the allocator quota) is non-negative.
pub proof fn lemma_scan_fail_pool_nonempty(
    k: &KernelK,
    container_ptr: RwLockContainerPtr,
    alloc_ptr_4k: RwLockPageAllocatorPtr,
    process_ptr: RwLockProcessPtr,
)
    requires
        k.inv(),
        k.container_map.dom().contains(container_ptr),
        k.container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
        k.container_map.spec_index(container_ptr).view().owned_processes.view().contains(process_ptr),
        process_effective_quota_4k(k.process_map.spec_index(process_ptr)) >= 1,
        forall|c: CpuId|
            #![trigger k.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c]]
            cpu_id_valid(c)
            ==> k.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().view().view().len() == 0,
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
        && container_process_allocator_quota_4k_wf(
            k.container_map,
            k.process_map,
            k.thread_map,
            k.allocator_4k_map,
        )
        && process_perms_wf(k.process_map)
    ) by {
        reveal(allocator_perms_wf);
        reveal(container_allocator_wf);
        reveal(container_process_wf);
        reveal(container_process_allocator_quota_4k_wf);
        reveal(process_perms_wf);
    };
    let owned = k.container_map.spec_index(container_ptr).view().owned_processes.view();
    let caches = k.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches;
    assert(
        k.allocator_4k_map.spec_index(alloc_ptr_4k)
            .global_pool.view().view().len() > 0
    ) by {
        assert(k.allocator_4k_map.dom().contains(alloc_ptr_4k)) by {
            reveal(container_allocator_wf);
        };
        assert(k.process_map.dom().contains(process_ptr)) by {
            reveal(container_process_wf);
        };
        assert forall|j: int| #![trigger caches.view()[j]]
            0 <= j < caches.view().len()
            implies {
                &&& caches.view()[j] == caches.spec_index(j as usize).value
                &&& caches.view()[j].view().linked_list.view().len() == 0
            } by {
                reveal(allocator_perms_wf);
                reveal(container_allocator_wf);
                lemma_usize_int(j);
                caches.lemma_view_index(j as usize);
            };
        lemma_cache_len_fold_all_zero(caches.view());
        assert forall|p: RwLockProcessPtr|
            #![trigger process_effective_quota_4k(k.process_map.spec_index(p))]
            owned.contains(p)
            implies process_effective_quota_4k(k.process_map.spec_index(p)) >= 0 by {
            reveal(container_process_wf);
            assert(
                k.process_map.spec_index(p).view().quota_4k
                    >= k.process_map.spec_index(p).view().temp_alloc_cache_4k.view().len()
            ) by {
                reveal(process_perms_wf);
            };
        };
        lemma_process_effective_quota_4k_fold_ge_member(
            owned, k.process_map, process_ptr,
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
        reveal(container_process_allocator_quota_4k_wf);
        reveal(process_perms_wf);
    };
}

}
