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
    #[verifier::rlimit(80000000)]
    #[verifier::spinoff_prover]
    pub fn allocate_free_4k_page(
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        cpu_id: CpuId,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(process_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(self).inv(),
            cpu_id_valid(cpu_id),
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages.view() > 0,
            old(self).container_map.dom().contains(container_ptr),
            old(self).container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(self).process_map.dom().contains(process_ptr),
            old(self).process_map.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
            old(self).process_map.spec_index(process_ptr).being_killed() == false,
            // Process write-lock perm, needed to mutate the process payload
            // (insert the freshly-allocated page into `temp_alloc_cache_4k`).
            process_lock_perm.state() is WriteLock,
            process_lock_perm.thread_id() == old(lctx).thread_id(),
            process_lock_perm.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
            process_effective_quota_4k(old(self).process_map.spec_index(process_ptr)) >= 1,  
            // old(lctx).lock_id_acyclic(old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id].lock_id()),
            old(lctx).lock_map().dom().contains(KernelObjId::Process(process_ptr)),
            old(lctx).lock_map()[KernelObjId::Process(process_ptr)] == process_lock_perm.lock_id(),
            old(self).locked_objects_match_lctx(old(lctx)),

            forall|obj_id: KernelObjId|
                #![auto]
                old(lctx).lock_map().dom().contains(obj_id) ==>
                {
                    &&&
                    obj_id is AllocatorCache == false
                    &&&
                    obj_id is AllocatorGlobalPoll == false
                    &&&
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[0].lock_id().spec_gt(
                        old(lctx).lock_map().spec_index(obj_id))
                },
        ensures
            final(self).inv(),
            final(self).process_map.dom().contains(process_ptr),
            final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx)),
            // ---- held process: not killed, perm still matches (process held throughout) ----
            final(self).process_map.spec_index(process_ptr).being_killed() == false,
            process_lock_perm.lock_id() == final(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            final(self).process_map.spec_index(process_ptr).view_rodata() == old(self).process_map.spec_index(process_ptr).view_rodata(),
            // ---- container domain + rodata preserved (rodata immutable across the internal boundary) ----
            old(self).container_map.dom() == final(self).container_map.dom(),
            forall|c: RwLockContainerPtr|
                #![trigger final(self).container_map.spec_index(c).view_rodata()]
                old(self).container_map.dom().contains(c)
                ==> final(self).container_map.spec_index(c).view_rodata()
                    == old(self).container_map.spec_index(c).view_rodata(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
            final(self).locked_objects_match_lctx(final(lctx)),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            page_ptr_valid(ret.0),
            // ---- page slot left write-locked, perm handed back (rides across the boundary as a held object) ----
            page_index_wf(page_ptr2page_index(ret.0)),
            final(self).page_array[page_ptr2page_index(ret.0)].view().wlocked_by(final(lctx)),
            final(self).page_array[page_ptr2page_index(ret.0)].view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(self).page_array[page_ptr2page_index(ret.0)].view().locking_thread()->Write_lock_id,
            final(lctx).lock_map().dom().contains(KernelObjId::Page(page_ptr2page_index(ret.0))),
            final(lctx).lock_map()[KernelObjId::Page(page_ptr2page_index(ret.0))] == ret.1.view().lock_id(),
            // ---- a held scheduler survives: its dom + lock state carry across (needed so the caller keeps using the scheduler it locked before alloc) ----
            old(self).scheduler_map.dom() == final(self).scheduler_map.dom(),
            forall|s: RwLockSchedulerPtr|
                #![trigger final(self).scheduler_map.spec_index(s).locked_by(final(lctx))]
                old(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))
                ==> final(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))
                    && final(lctx).lock_map()[KernelObjId::Scheduler(s)] == old(lctx).lock_map()[KernelObjId::Scheduler(s)]
                    && final(self).scheduler_map.spec_index(s) == old(self).scheduler_map.spec_index(s),
            // ---- a held cpu survives (same, for the caller's cpu unlock) ----
            forall|c: CpuId|
                #![trigger final(self).cpu_array.spec_index(c).view().locked_by(final(lctx))]
                cpu_id_valid(c) && old(lctx).lock_map().dom().contains(KernelObjId::Cpu(c))
                ==> final(lctx).lock_map().dom().contains(KernelObjId::Cpu(c))
                    && final(lctx).lock_map()[KernelObjId::Cpu(c)] == old(lctx).lock_map()[KernelObjId::Cpu(c)]
                    && final(self).cpu_array.spec_index(c).view() == old(self).cpu_array.spec_index(c).view(),
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
    {
        proof {
            reveal(allocator_perms_wf);
        }

        // Fast path: lock the running cpu's cache; the cache is unlocked (no
        // AllocatorCache id held), so the wlock is fresh + acyclic.
        let ghost cache_lock_id = self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id].lock_id();
        assert(
            forall|cpu_i:CpuId|
                #![auto]
                cpu_id_valid(cpu_i)
                ==>
                self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_i]@.locked_by(&*lctx) == false
        ) by {
            reveal(allocator_locked_match_lctx);
        };
        let Tracked(cache_lock_perm) = self.wlock_allocator_cache(
            alloc_ptr_4k, cpu_id, Tracked(&mut *lctx),
        );

        // Read the cache length via a shared borrow (preserves wf() for the slow path).
        let cache_ref = self.allocator_4k_map.borrow_cache(
            alloc_ptr_4k, cpu_id, Tracked(&cache_lock_perm),
        );
        let cache_len = cache_ref.linked_list.len();

        if cache_len > 0 {
            // Every held id ≤ cache major, and match_lctx across the cache wlock.
            proof {
                assert forall|k: KernelObjId|
                    #![trigger lctx.lock_map().dom().contains(k)]
                    lctx.lock_map().dom().contains(k)
                    implies lctx.lock_map()[k].major <= ALLOCATOR_CACHE_MAJOR by {
                    if k == KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cpu_id) {
                        assert(lctx.lock_map()[k] == cache_lock_id);
                        assert(cache_lock_id.major == ALLOCATOR_CACHE_MAJOR);
                    } else {
                        assert(cache_lock_id.spec_gt(old(lctx).lock_map()[k]));
                        let held = old(lctx).lock_map()[k];
                        assert(cache_lock_id.container.spec_eq(held.container));
                        assert(cache_lock_id.process.spec_eq(held.process));
                    }
                };
                assert(self.container_map.spec_index(container_ptr).view().owned_processes.view().contains(process_ptr)) by {
                    reveal(container_process_wf);
                };
            }

            // Pop + stage the cache head, leaving the page slot + cache write-locked.
            let ghost pre_stage = *self;
            let (page_ptr, Tracked(page_lock_perm)) = self.pop_stage_4k_page(
                alloc_ptr_4k, cpu_id, process_ptr, container_ptr,
                Tracked(&mut *lctx), Tracked(&cache_lock_perm), Tracked(process_lock_perm),
            );
            let page_index = page_ptr2page_index(page_ptr);
            let ghost post_stage = *self;

            // Unlock the cache; keep the page slot write-locked so it rides
            // across the boundary as a held object (its state is pinned).
            self.wunlock_allocator_cache(alloc_ptr_4k, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm));

            // Close the kernel atomic step.
            proof {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), &pre_stage);
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(&post_stage, self);
                assert(lctx.lock_map().dom().contains(KernelObjId::Process(process_ptr))) by {
                    reveal(process_locked_match_lctx);
                };
                assert(lctx.lock_map().dom().contains(KernelObjId::Page(page_index))) by {
                    reveal(page_locked_match_lctx);
                };
                self.kernel_step_boundary(&mut *lctx, &mut *steps);
                assert(self.process_map.spec_index(process_ptr).view() == post_stage.process_map.spec_index(process_ptr).view());
                assert(self.page_array[page_index].view() == post_stage.page_array[page_index].view());
                assert forall|c: CpuId| #![auto]
                    cpu_id_valid(c) && old(lctx).lock_map().dom().contains(KernelObjId::Cpu(c))
                    implies lctx.lock_map().dom().contains(KernelObjId::Cpu(c))
                        && lctx.lock_map()[KernelObjId::Cpu(c)] == old(lctx).lock_map()[KernelObjId::Cpu(c)]
                        && self.cpu_array.spec_index(c).view() == old(self).cpu_array.spec_index(c).view() by {
                    lemma_alloc_preserves_held_cpu(old(self), self, old(lctx), &*lctx, c);
                };
            }
            return (page_ptr, Tracked(page_lock_perm));
        }

        // Case 2: slow path — lock the global pool while holding the (empty) cache.
        // The pool's id (major 107, owners NotApp) tops every held id (Process +
        // AllocatorCache, major ≤ 106), so it is acyclic and fresh.
        proof {
            reveal(allocator_locked_match_lctx);
            let gp_lock_id = LockId{
                container: self.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().container_depth(),
                process: self.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().process_depth(),
                major: self.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().current_lock_major(),
                minor: self.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().lock_minor(),
            };
            assert forall|k: KernelObjId| #![auto] lctx.lock_map().dom().contains(k)
            implies gp_lock_id.spec_gt(lctx.lock_map()[k]) by {
                reveal(allocator_perms_wf);
                let held = lctx.lock_map()[k];
                if k == KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cpu_id) {
                    assert(cache_lock_id.major == ALLOCATOR_CACHE_MAJOR);
                } else {
                    assert(cache_lock_id.spec_gt(old(lctx).lock_map()[k]));
                    assert(cache_lock_id.container.spec_eq(held.container));
                    assert(cache_lock_id.process.spec_eq(held.process));
                }
            };
            assert(lctx.obj_id_fresh(KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k)));
        }
        let Tracked(gp_lock_perm) = self.wlock_allocator_global_pool(
            alloc_ptr_4k, Tracked(&mut *lctx),
        );

        // Read the pool length via a shared borrow (preserves wf()).
        let pool_ref = self.allocator_4k_map.borrow_global_pool(
            alloc_ptr_4k, Tracked(&gp_lock_perm),
        );
        let pool_len = pool_ref.len();

        if pool_len > 0 {
            // match_lctx across the pool wlock, and owned_processes membership.
            proof {
                assert(self.container_map.spec_index(container_ptr).view().owned_processes.view().contains(process_ptr)) by {
                    reveal(container_process_wf);
                };
                reveal(allocator_locked_match_lctx);
                reveal(allocator_perms_wf);
                assert forall|k: KernelObjId| #![auto] lctx.lock_map().dom().contains(k)
                implies lctx.lock_map()[k].major <= ALLOCATOR_GLOBAL_POLL_MAJOR by {
                    if k == KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k) {
                        assert(lctx.lock_map()[k] == gp_lock_perm.lock_id());
                    } else if k == KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cpu_id) {
                        assert(cache_lock_id.major == ALLOCATOR_CACHE_MAJOR);
                    } else {
                        let held = old(lctx).lock_map()[k];
                        assert(cache_lock_id.spec_gt(held));
                        assert(cache_lock_id.container.spec_eq(held.container));
                        assert(cache_lock_id.process.spec_eq(held.process));
                    }
                };
            }

            // Pop + stage the pool head, leaving the page slot + pool write-locked.
            let ghost pre_stage = *self;
            let (page_ptr, Tracked(page_lock_perm)) = self.pop_stage_global_4k_page(
                alloc_ptr_4k, process_ptr, container_ptr,
                Tracked(&mut *lctx), Tracked(&gp_lock_perm), Tracked(process_lock_perm),
            );
            let page_index = page_ptr2page_index(page_ptr);
            let ghost post_stage = *self;

            // Unlock the pool, then the cache; keep the page slot write-locked so
            // it rides across the boundary as a held object (its state is pinned).
            self.wunlock_allocator_global_pool(alloc_ptr_4k, Tracked(&mut *lctx), Tracked(gp_lock_perm));
            self.wunlock_allocator_cache(alloc_ptr_4k, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm));

            // Close the kernel atomic step.
            proof {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), &pre_stage);
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(&post_stage, self);
                assert(lctx.lock_map().dom().contains(KernelObjId::Process(process_ptr))) by {
                    reveal(process_locked_match_lctx);
                };
                assert(lctx.lock_map().dom().contains(KernelObjId::Page(page_index))) by {
                    reveal(page_locked_match_lctx);
                };
                self.kernel_step_boundary(&mut *lctx, &mut *steps);
                assert(self.process_map.spec_index(process_ptr).view() == post_stage.process_map.spec_index(process_ptr).view());
                assert(self.page_array[page_index].view() == post_stage.page_array[page_index].view());
                assert forall|c: CpuId| #![auto]
                    cpu_id_valid(c) && old(lctx).lock_map().dom().contains(KernelObjId::Cpu(c))
                    implies lctx.lock_map().dom().contains(KernelObjId::Cpu(c))
                        && lctx.lock_map()[KernelObjId::Cpu(c)] == old(lctx).lock_map()[KernelObjId::Cpu(c)]
                        && self.cpu_array.spec_index(c).view() == old(self).cpu_array.spec_index(c).view() by {
                    lemma_alloc_preserves_held_cpu(old(self), self, old(lctx), &*lctx, c);
                };
            }
            return (page_ptr, Tracked(page_lock_perm));
        }

        // Case 3: cache + pool both empty. Release them, close the kernel step,
        // then lock every cache + the pool afresh and scan for a free page. The
        // running-cpu cache (major 106) and pool (major 107) must be dropped
        // before we can re-acquire the full cache set in ascending order.
        proof {
            reveal(allocator_locked_match_lctx);
        }
        self.wunlock_allocator_global_pool(alloc_ptr_4k, Tracked(&mut *lctx), Tracked(gp_lock_perm));
        self.wunlock_allocator_cache(alloc_ptr_4k, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm));

        proof {
            kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
            assert(lctx.lock_map().dom().contains(KernelObjId::Process(process_ptr))) by {
                reveal(process_locked_match_lctx);
            };
            // Any scheduler held at entry is still held here (the cache/pool
            // unlocks removed only their own keys), so it rides the boundary.
            assert forall|s: RwLockSchedulerPtr| #![auto]
                old(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))
                implies lctx.lock_map().dom().contains(KernelObjId::Scheduler(s))
                    && lctx.lock_map()[KernelObjId::Scheduler(s)] == old(lctx).lock_map()[KernelObjId::Scheduler(s)] by {};
            self.kernel_step_boundary(&mut *lctx, &mut *steps);
            assert forall|s: RwLockSchedulerPtr| #![auto]
                old(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))
                implies self.scheduler_map.spec_index(s) == old(self).scheduler_map.spec_index(s) by {};
        }
        let ghost post_first_boundary = *self;

        // Post-boundary: the world has run, but the held process is preserved in
        // full. Re-derive the allocator pointer from the process's container (its
        // rodata is lock-free readable), so the scan targets the current map.
        assert(self.process_map.perms_wf()) by { reveal(process_perms_wf); };
        let recov_container = self.process_map.borrow_rodata(process_ptr).borrow().owning_container;
        assert(self.container_map.dom().contains(recov_container)) by { reveal(container_process_wf); };
        assert(self.container_map.perms_wf()) by { reveal(container_perms_wf); };
        let recov_alloc = self.container_map.borrow_rodata(recov_container).borrow().allocator_ptr_4k;
        assert(self.container_map.spec_index(recov_container).view().owned_processes.view().contains(process_ptr)) by { reveal(container_process_wf); };
        assert(self.allocator_4k_map.dom().contains(recov_alloc)) by { reveal(container_allocator_wf); };

        let (cache_perms, pool_perm) = self.wlock_all_caches_and_global_pool(
            recov_alloc, Tracked(&mut *lctx),
        );

        let ghost pre_scan = *self;
        let (found, slot) = self.scan_caches_and_alloc(
            recov_alloc, process_ptr, recov_container,
            Tracked(&mut *lctx), Tracked(cache_perms.borrow()), Tracked(process_lock_perm),
        );

        if found {
            // A cache held a free page: it is popped + staged, page slot held.
            // Release the page, every cache, then the pool, and close the step.
            let (scan_cpu, page_ptr, Tracked(page_lock_perm)) = slot.unwrap();
            let page_index = page_ptr2page_index(page_ptr);
            let ghost pre_unlock = *self;

            // Keep the page slot write-locked so it rides across the boundary as
            // a held object (its state is pinned); release the caches + pool.
            self.wunlock_all_caches(recov_alloc, Tracked(&mut *lctx), Tracked(cache_perms.get()));
            self.wunlock_allocator_global_pool(recov_alloc, Tracked(&mut *lctx), Tracked(pool_perm.get()));

            proof {
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(post_first_boundary)) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(&post_first_boundary, &pre_scan);
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(&pre_unlock, self);
                }
                assert(lctx.lock_map().dom().contains(KernelObjId::Process(process_ptr))) by {
                    reveal(process_locked_match_lctx);
                };
                assert(lctx.lock_map().dom().contains(KernelObjId::Page(page_index))) by {
                    reveal(page_locked_match_lctx);
                };
                self.kernel_step_boundary(&mut *lctx, &mut *steps);
                assert(self.process_map.spec_index(process_ptr).view() == pre_unlock.process_map.spec_index(process_ptr).view());
                assert(self.page_array[page_index].view() == pre_unlock.page_array[page_index].view());
                // container rodata + dom preserved across both boundaries (rodata
                // immutable; the intervening lock ops leave container_map byte-equal).
                assert(old(self).container_map.dom() == self.container_map.dom());
                assert forall|c: RwLockContainerPtr| #![auto]
                    old(self).container_map.dom().contains(c)
                    implies self.container_map.spec_index(c).view_rodata()
                        == old(self).container_map.spec_index(c).view_rodata() by {
                    assert(post_first_boundary.container_map.spec_index(c).view_rodata()
                        == old(self).container_map.spec_index(c).view_rodata());
                };
                // scheduler_map domain preserved across both boundaries.
                assert(old(self).scheduler_map.dom() == self.scheduler_map.dom());
                // Held schedulers + cpus survive (see lemmas: the scan-found path
                // removes caches in a loop that resists the inline lock_map chain).
                assert forall|s: RwLockSchedulerPtr| #![auto]
                    old(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))
                    implies lctx.lock_map().dom().contains(KernelObjId::Scheduler(s))
                        && lctx.lock_map()[KernelObjId::Scheduler(s)] == old(lctx).lock_map()[KernelObjId::Scheduler(s)]
                        && self.scheduler_map.spec_index(s) == old(self).scheduler_map.spec_index(s) by {
                    lemma_alloc_preserves_held_scheduler(old(self), self, old(lctx), &*lctx, s);
                };
                assert forall|c: CpuId| #![auto]
                    cpu_id_valid(c) && old(lctx).lock_map().dom().contains(KernelObjId::Cpu(c))
                    implies lctx.lock_map().dom().contains(KernelObjId::Cpu(c))
                        && lctx.lock_map()[KernelObjId::Cpu(c)] == old(lctx).lock_map()[KernelObjId::Cpu(c)]
                        && self.cpu_array.spec_index(c).view() == old(self).cpu_array.spec_index(c).view() by {
                    lemma_alloc_preserves_held_cpu(old(self), self, old(lctx), &*lctx, c);
                };
            }
            return (page_ptr, Tracked(page_lock_perm));
        }

        // Every cache was empty. By conservation the free pages must sit in the
        // global pool: total_free_pages == pool.len() + Σ cache.len(), the caches
        // are all empty, and the held process still has effective_quota_4k >= 1,
        // so total_free_pages >= 1 and hence pool.len() >= 1.
        assert(self.allocator_4k_map.spec_index(recov_alloc).global_pool.view().len() > 0) by {
            lemma_scan_fail_pool_nonempty(self, recov_container, recov_alloc, process_ptr);
            reveal(allocator_perms_wf);
            self.allocator_4k_map.spec_index(recov_alloc).global_pool.view().lemma_len_view();
        };

        proof {
            assert(self.process_map.spec_index(process_ptr).wlocked_by(&*lctx)) by { reveal(process_locked_match_lctx); };
        }
        let ghost pre_pool_stage = *self;
        let (page_ptr, Tracked(page_lock_perm)) = self.pop_stage_global_4k_page(
            recov_alloc, process_ptr, recov_container,
            Tracked(&mut *lctx), Tracked(pool_perm.borrow()), Tracked(process_lock_perm),
        );
        let page_index = page_ptr2page_index(page_ptr);
        let ghost pre_unlock = *self;

        // Keep the page slot write-locked so it rides across the boundary as a
        // held object (its state is pinned); release the caches + pool.
        self.wunlock_all_caches(recov_alloc, Tracked(&mut *lctx), Tracked(cache_perms.get()));
        self.wunlock_allocator_global_pool(recov_alloc, Tracked(&mut *lctx), Tracked(pool_perm.get()));

        proof {
            assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(post_first_boundary)) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(&post_first_boundary, &pre_pool_stage);
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(&pre_unlock, self);
            }
            assert(lctx.lock_map().dom().contains(KernelObjId::Process(process_ptr))) by {
                reveal(process_locked_match_lctx);
            };
            assert(lctx.lock_map().dom().contains(KernelObjId::Page(page_index))) by {
                reveal(page_locked_match_lctx);
            };
            // A scheduler held at entry is still held here (survived the first
            // boundary + the cache/pool relock-scan-unlock, which don't touch
            // Scheduler keys), so it rides the second boundary too.
            self.kernel_step_boundary(&mut *lctx, &mut *steps);
            assert(self.process_map.spec_index(process_ptr).view() == pre_unlock.process_map.spec_index(process_ptr).view());
            assert(self.page_array[page_index].view() == pre_unlock.page_array[page_index].view());
            // container rodata + dom preserved across both boundaries (rodata
            // immutable; the intervening lock ops leave container_map byte-equal).
            assert(old(self).container_map.dom() == self.container_map.dom());
            assert forall|c: RwLockContainerPtr| #![auto]
                old(self).container_map.dom().contains(c)
                implies self.container_map.spec_index(c).view_rodata()
                    == old(self).container_map.spec_index(c).view_rodata() by {
                assert(post_first_boundary.container_map.spec_index(c).view_rodata()
                    == old(self).container_map.spec_index(c).view_rodata());
            };
            // scheduler_map domain preserved across both boundaries.
            assert(old(self).scheduler_map.dom() == self.scheduler_map.dom());
            // Held schedulers + cpus survive (see lemmas: the removal loop resists
            // the inline lock_map chain).
            assert forall|s: RwLockSchedulerPtr| #![auto]
                old(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))
                implies lctx.lock_map().dom().contains(KernelObjId::Scheduler(s))
                    && lctx.lock_map()[KernelObjId::Scheduler(s)] == old(lctx).lock_map()[KernelObjId::Scheduler(s)]
                    && self.scheduler_map.spec_index(s) == old(self).scheduler_map.spec_index(s) by {
                lemma_alloc_preserves_held_scheduler(old(self), self, old(lctx), &*lctx, s);
            };
            assert forall|c: CpuId| #![auto]
                cpu_id_valid(c) && old(lctx).lock_map().dom().contains(KernelObjId::Cpu(c))
                implies lctx.lock_map().dom().contains(KernelObjId::Cpu(c))
                    && lctx.lock_map()[KernelObjId::Cpu(c)] == old(lctx).lock_map()[KernelObjId::Cpu(c)]
                    && self.cpu_array.spec_index(c).view() == old(self).cpu_array.spec_index(c).view() by {
                lemma_alloc_preserves_held_cpu(old(self), self, old(lctx), &*lctx, c);
            };
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
    fn wlock_all_caches_and_global_pool(
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
    ) -> (ret: (Tracked<Map<CpuId, LockPerm>>, Tracked<LockPerm>))
        requires
            old(self).inv(),
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            old(lctx).kernel_view_locking_state() is Acquire,
            forall|c: CpuId|
                #![trigger old(lctx).lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c))]
                cpu_id_valid(c)
                ==> old(lctx).lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c)) == false,
            old(lctx).lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k)) == false,
            old(self).locked_objects_match_lctx(old(lctx)),
            forall|k: KernelObjId|
                #![trigger old(lctx).lock_map().dom().contains(k)]
                old(lctx).lock_map().dom().contains(k)
                ==> old(lctx).lock_map()[k].major <= PROCESS_LOCK_MAJOR,
        ensures
            final(self).inv(),
            final(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
            // ---- only allocator_4k_map lock state moves; every other field byte-equal ----
            final(self).pagetable_map     == old(self).pagetable_map,
            final(self).page_array        == old(self).page_array,
            final(self).cpu_array         == old(self).cpu_array,
            final(self).cpu_tlb           == old(self).cpu_tlb,
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
            // ---- every cache + the pool is write-locked by us, perm recorded ----
            forall|c: CpuId|
                #![trigger ret.0.view().spec_index(c)]
                cpu_id_valid(c)
                ==> {
                    &&& ret.0.view().dom().contains(c)
                    &&& final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().wlocked_by(final(lctx))
                    &&& final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().being_killed() == false
                    &&& ret.0.view().spec_index(c).state() is WriteLock
                    &&& ret.0.view().spec_index(c).thread_id() == final(lctx).thread_id()
                    &&& ret.0.view().spec_index(c).lock_id() == final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().locking_thread()->Write_lock_id
                    &&& final(lctx).lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c))
                    &&& final(lctx).lock_map()[KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c)] == ret.0.view().spec_index(c).lock_id()
                },
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.wlocked_by(final(lctx)),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.locking_thread()->Write_lock_id,
            final(lctx).lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k)),
            final(lctx).lock_map()[KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k)] == ret.1.view().lock_id(),
            // ---- pre-existing lock_map entries preserved (only caches + pool added) ----
            forall|k: KernelObjId|
                #![trigger old(lctx).lock_map().dom().contains(k)]
                old(lctx).lock_map().dom().contains(k)
                ==> final(lctx).lock_map().dom().contains(k) && final(lctx).lock_map()[k] == old(lctx).lock_map()[k],
            // ---- every held id ≤ pool major (caches 106, pool 107, pre-entry ≤ 105) ----
            forall|k: KernelObjId|
                #![trigger final(lctx).lock_map().dom().contains(k)]
                final(lctx).lock_map().dom().contains(k)
                ==> final(lctx).lock_map()[k].major <= ALLOCATOR_GLOBAL_POLL_MAJOR,
            final(self).locked_objects_match_lctx(final(lctx)),
    {
        let tracked mut cache_perms: Map<CpuId, LockPerm> = Map::tracked_empty();
        assert(
            forall|c: CpuId|
                #![auto]
                cpu_id_valid(c)
                ==>
                self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(c).view().locked_by(&*lctx) == false
        ) by {
            reveal(allocator_locked_match_lctx);
        };

        let mut cpu: CpuId = 0;
        while cpu < NUM_CPUS
            invariant
                self.inv(),
                self.locked_objects_match_lctx(&*lctx),
                self.allocator_4k_map.dom().contains(alloc_ptr_4k),
                self.pagetable_map     == old(self).pagetable_map,
                self.page_array        == old(self).page_array,
                self.cpu_array         == old(self).cpu_array,
                self.cpu_tlb           == old(self).cpu_tlb,
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
                // Caches [0, cpu) are locked, perm collected; [cpu, NUM_CPUS) untouched.
                forall|c: CpuId|
                    #![trigger cache_perms.spec_index(c)]
                    cpu_id_valid(c) && c < cpu
                    ==> {
                        &&& cache_perms.dom().contains(c)
                        &&& self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().wlocked_by(&*lctx)
                        &&& self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().being_killed() == false
                        &&& cache_perms.spec_index(c).state() is WriteLock
                        &&& cache_perms.spec_index(c).thread_id() == lctx.thread_id()
                        &&& cache_perms.spec_index(c).lock_id() == self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().locking_thread()->Write_lock_id
                        &&& lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c))
                        &&& lctx.lock_map()[KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c)] == cache_perms.spec_index(c).lock_id()
                    },
                // Caches [cpu, NUM_CPUS) are NOT yet recorded and NOT yet locked.
                forall|c: CpuId|
                    #![trigger self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(c)]
                    cpu_id_valid(c) && c >= cpu
                    ==> lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c)) == false
                        && self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(c).view().locked_by(&*lctx) == false,
                // The pool is not yet held.
                lctx.lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k)) == false,
                // Every held id is a pre-entry id (major ≤ 105) or a cache we just
                // took (major 106, minor < cpu) — so cache[cpu] (minor = cpu) tops all.
                forall|k: KernelObjId|
                    #![trigger lctx.lock_map().dom().contains(k)]
                    lctx.lock_map().dom().contains(k)
                    ==> lctx.lock_map()[k].major < ALLOCATOR_CACHE_MAJOR
                        || (lctx.lock_map()[k].major == ALLOCATOR_CACHE_MAJOR
                            && lctx.lock_map()[k].minor < cpu),
                // Pre-entry lock_map entries are all preserved (we only insert caches).
                forall|k: KernelObjId|
                    #![trigger old(lctx).lock_map().dom().contains(k)]
                    old(lctx).lock_map().dom().contains(k)
                    ==> lctx.lock_map().dom().contains(k) && lctx.lock_map()[k] == old(lctx).lock_map()[k],
            decreases NUM_CPUS - cpu,
        {
            let ghost cache_lid = self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu].lock_id();
            proof {
                reveal(allocator_perms_wf);
                assert forall|k: KernelObjId| #![auto] lctx.lock_map().dom().contains(k)
                implies cache_lid.spec_gt(lctx.lock_map()[k]) by {};
            }
            let Tracked(cache_perm) = self.wlock_allocator_cache(alloc_ptr_4k, cpu, Tracked(&mut *lctx));
            proof {
                cache_perms.tracked_insert(cpu, cache_perm);
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(endpoint_locked_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(pagetable_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(allocator_locked_match_lctx);
                }
            }
            cpu = cpu + 1;
        }

        // After the loop: all caches held (major 106), pool (major 107) tops them.
        let ghost pool_lid = LockId{
            container: self.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().container_depth(),
            process: self.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().process_depth(),
            major: self.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().current_lock_major(),
            minor: self.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().lock_minor(),
        };
        proof {
            reveal(allocator_perms_wf);
            reveal(allocator_locked_match_lctx);
            assert forall|k: KernelObjId| #![auto] lctx.lock_map().dom().contains(k)
            implies pool_lid.spec_gt(lctx.lock_map()[k]) by {};
        }
        let Tracked(pool_perm) = self.wlock_allocator_global_pool(alloc_ptr_4k, Tracked(&mut *lctx));
        proof {
            assert(self.locked_objects_match_lctx(&*lctx)) by {
                reveal(container_locked_match_lctx);
                reveal(process_locked_match_lctx);
                reveal(thread_locked_match_lctx);
                reveal(endpoint_locked_match_lctx);
                reveal(scheduler_locked_match_lctx);
                reveal(pagetable_locked_match_lctx);
                reveal(page_locked_match_lctx);
                reveal(cpu_locked_match_lctx);
                reveal(allocator_locked_match_lctx);
            }
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
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            old(self).locked_objects_match_lctx(old(lctx)),
            forall|c: CpuId|
                #![trigger cache_perms.spec_index(c)]
                cpu_id_valid(c)
                ==> {
                    &&& cache_perms.dom().contains(c)
                    &&& old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().wlocked_by(old(lctx))
                    &&& old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().being_killed() == false
                    &&& cache_perms.spec_index(c).state() is WriteLock
                    &&& cache_perms.spec_index(c).thread_id() == old(lctx).thread_id()
                    &&& cache_perms.spec_index(c).lock_id() == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().locking_thread()->Write_lock_id
                    &&& old(lctx).lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c))
                    &&& old(lctx).lock_map()[KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c)] == cache_perms.spec_index(c).lock_id()
                },
        ensures
            final(self).inv(),
            final(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
            final(self).locked_objects_match_lctx(final(lctx)),
            // ---- only allocator_4k_map cache lock state moves; every other field byte-equal ----
            final(self).pagetable_map     == old(self).pagetable_map,
            final(self).page_array        == old(self).page_array,
            final(self).cpu_array         == old(self).cpu_array,
            final(self).cpu_tlb           == old(self).cpu_tlb,
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
            // ---- every cache lock_map entry dropped; everything else preserved ----
            forall|c: CpuId|
                #![trigger final(lctx).lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c))]
                cpu_id_valid(c)
                ==> final(lctx).lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c)) == false,
            forall|k: KernelObjId|
                #![trigger final(lctx).lock_map().dom().contains(k)]
                final(lctx).lock_map().dom().contains(k)
                ==> old(lctx).lock_map().dom().contains(k) && final(lctx).lock_map()[k] == old(lctx).lock_map()[k],
    {
        let tracked mut perms = cache_perms;
        let mut cpu: CpuId = 0;
        while cpu < NUM_CPUS
            invariant
                self.inv(),
                self.locked_objects_match_lctx(&*lctx),
                self.allocator_4k_map.dom().contains(alloc_ptr_4k),
                self.pagetable_map     == old(self).pagetable_map,
                self.page_array        == old(self).page_array,
                self.cpu_array         == old(self).cpu_array,
                self.cpu_tlb           == old(self).cpu_tlb,
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
                self.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
                lctx.thread_id() == old(lctx).thread_id(),
                lctx.user_view_locking_state() == old(lctx).user_view_locking_state(),
                0 <= cpu <= NUM_CPUS,
                forall|c: CpuId|
                    #![trigger perms.spec_index(c)]
                    cpu_id_valid(c) && c >= cpu
                    ==> {
                        &&& perms.dom().contains(c)
                        &&& self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().wlocked_by(&*lctx)
                        &&& self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().being_killed() == false
                        &&& perms.spec_index(c).state() is WriteLock
                        &&& perms.spec_index(c).thread_id() == lctx.thread_id()
                        &&& perms.spec_index(c).lock_id() == self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().locking_thread()->Write_lock_id
                        &&& lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c))
                        &&& lctx.lock_map()[KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c)] == perms.spec_index(c).lock_id()
                    },
                forall|c: CpuId|
                    #![trigger lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c))]
                    cpu_id_valid(c) && c < cpu
                    ==> lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c)) == false,
                forall|k: KernelObjId|
                    #![trigger lctx.lock_map().dom().contains(k)]
                    lctx.lock_map().dom().contains(k)
                    ==> old(lctx).lock_map().dom().contains(k) && lctx.lock_map()[k] == old(lctx).lock_map()[k],
            decreases NUM_CPUS - cpu,
        {
            proof {
                reveal(allocator_perms_wf);
                assert(perms.spec_index(cpu).state() is WriteLock);
            }
            let tracked cache_perm = perms.tracked_remove(cpu);
            self.wunlock_allocator_cache(alloc_ptr_4k, cpu, Tracked(&mut *lctx), Tracked(cache_perm));
            proof {
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(endpoint_locked_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(pagetable_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(allocator_locked_match_lctx);
                }
            }
            cpu = cpu + 1;
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
            old(self).container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            old(self).process_map.dom().contains(process_ptr),
            old(self).process_map.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            old(self).container_map.spec_index(container_ptr).view().owned_processes.view().contains(process_ptr),
            old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
            old(self).process_map.spec_index(process_ptr).being_killed() == false,
            process_effective_quota_4k(old(self).process_map.spec_index(process_ptr)) >= 1,
            process_lock_perm.state() is WriteLock,
            process_lock_perm.thread_id() == old(lctx).thread_id(),
            process_lock_perm.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            old(lctx).lock_map().dom().contains(KernelObjId::Process(process_ptr)),
            old(lctx).lock_map()[KernelObjId::Process(process_ptr)] == process_lock_perm.lock_id(),
            old(self).locked_objects_match_lctx(old(lctx)),
            forall|c: CpuId|
                #![trigger cache_perms.spec_index(c)]
                cpu_id_valid(c)
                ==> {
                    &&& cache_perms.dom().contains(c)
                    &&& old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().wlocked_by(old(lctx))
                    &&& old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().being_killed() == false
                    &&& cache_perms.spec_index(c).state() is WriteLock
                    &&& cache_perms.spec_index(c).thread_id() == old(lctx).thread_id()
                    &&& cache_perms.spec_index(c).lock_id() == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().locking_thread()->Write_lock_id
                    &&& old(lctx).lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c))
                    &&& old(lctx).lock_map()[KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c)] == cache_perms.spec_index(c).lock_id()
                },
            forall|k: KernelObjId|
                #![trigger old(lctx).lock_map().dom().contains(k)]
                old(lctx).lock_map().dom().contains(k)
                ==> old(lctx).lock_map()[k].major <= ALLOCATOR_GLOBAL_POLL_MAJOR,
        ensures
            final(self).inv(),
            final(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
            final(self).locked_objects_match_lctx(final(lctx)),
            // ---- user view unchanged: staging is kernel-internal ----
            kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
            // ---- failure: every cache was empty; complete no-op ----
            ret.0 == false ==> {
                &&& ret.1 is None
                &&& *final(self) == *old(self)
                &&& final(lctx).lock_map() == old(lctx).lock_map()
                &&& forall|c: CpuId|
                    #![trigger final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c]]
                    cpu_id_valid(c)
                    ==> final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().view().view().len() == 0
            },
            // ---- success: popped + staged a page from cache `cpu`, page slot held ----
            ret.0 == true ==> {
                &&& ret.1 is Some
                &&& cpu_id_valid(ret.1.unwrap().0)
                &&& page_ptr_valid(ret.1.unwrap().1)
                &&& page_index_wf(page_ptr2page_index(ret.1.unwrap().1))
                &&& final(self).page_array[page_ptr2page_index(ret.1.unwrap().1)].view().wlocked_by(final(lctx))
                &&& final(self).page_array[page_ptr2page_index(ret.1.unwrap().1)].view().being_killed() == false
                &&& ret.1.unwrap().2.view().state() is WriteLock
                &&& ret.1.unwrap().2.view().thread_id() == final(lctx).thread_id()
                &&& ret.1.unwrap().2.view().lock_id() == final(self).page_array[page_ptr2page_index(ret.1.unwrap().1)].view().locking_thread()->Write_lock_id
                &&& final(lctx).lock_map().dom().contains(KernelObjId::Page(page_ptr2page_index(ret.1.unwrap().1)))
                &&& final(lctx).lock_map() == old(lctx).lock_map().insert(KernelObjId::Page(page_ptr2page_index(ret.1.unwrap().1)), ret.1.unwrap().2.view().lock_id())
                // Every cache still write-locked with its original perm (for unlock-all).
                &&& forall|c: CpuId|
                    #![trigger cache_perms.spec_index(c)]
                    cpu_id_valid(c)
                    ==> {
                        &&& final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().wlocked_by(final(lctx))
                        &&& final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().being_killed() == false
                        &&& cache_perms.spec_index(c).lock_id() == final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().locking_thread()->Write_lock_id
                    }
                // The held process's lock state is preserved (only its payload's
                // temp_alloc_cache moved), so the caller keeps using it + unlocks it.
                &&& final(self).process_map.dom().contains(process_ptr)
                &&& final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx))
                &&& final(self).process_map.spec_index(process_ptr).being_killed() == false
                &&& process_lock_perm.lock_id() == final(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id
                // Staging: 4k cache gained exactly the popped page; 2m/1g caches + nominal quota untouched.
                &&& final(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view()
                    =~= old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view().insert(ret.1.unwrap().1)
                &&& final(self).page_array[page_ptr2page_index(ret.1.unwrap().1)].view().view().state == (PageState::Owned4k{ process_ptr })
                &&& final(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_2m
                    == old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_2m
                &&& final(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_1g
                    == old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_1g
                &&& final(self).process_map.spec_index(process_ptr).view().quota_4k
                    == old(self).process_map.spec_index(process_ptr).view().quota_4k
                // container_map + scheduler_map untouched (scan only stages via pop_stage).
                &&& final(self).container_map == old(self).container_map
                &&& final(self).scheduler_map == old(self).scheduler_map
                &&& final(self).process_map.spec_index(process_ptr).view_rodata()
                    == old(self).process_map.spec_index(process_ptr).view_rodata()
            },
    {
        let mut cpu: CpuId = 0;
        while cpu < NUM_CPUS
            invariant
                *self == *old(self),
                self.inv(),
                self.locked_objects_match_lctx(&*lctx),
                self.allocator_4k_map.dom().contains(alloc_ptr_4k),
                lctx.lock_map() == old(lctx).lock_map(),
                lctx.thread_id() == old(lctx).thread_id(),
                lctx.kernel_view_locking_state() is Acquire,
                lctx.user_view_locking_state() == old(lctx).user_view_locking_state(),
                0 <= cpu <= NUM_CPUS,
                self.container_map.dom().contains(container_ptr),
                self.container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
                self.process_map.dom().contains(process_ptr),
                self.process_map.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
                self.container_map.spec_index(container_ptr).view().owned_processes.view().contains(process_ptr),
                self.process_map.spec_index(process_ptr).wlocked_by(&*lctx),
                self.process_map.spec_index(process_ptr).being_killed() == false,
                process_effective_quota_4k(self.process_map.spec_index(process_ptr)) >= 1,
                process_lock_perm.state() is WriteLock,
                process_lock_perm.thread_id() == lctx.thread_id(),
                process_lock_perm.lock_id() == self.process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                lctx.lock_map().dom().contains(KernelObjId::Process(process_ptr)),
                lctx.lock_map()[KernelObjId::Process(process_ptr)] == process_lock_perm.lock_id(),
                forall|c: CpuId|
                    #![trigger cache_perms.spec_index(c)]
                    cpu_id_valid(c)
                    ==> {
                        &&& cache_perms.dom().contains(c)
                        &&& self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().wlocked_by(&*lctx)
                        &&& self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().being_killed() == false
                        &&& cache_perms.spec_index(c).state() is WriteLock
                        &&& cache_perms.spec_index(c).thread_id() == lctx.thread_id()
                        &&& cache_perms.spec_index(c).lock_id() == self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().locking_thread()->Write_lock_id
                        &&& lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c))
                        &&& lctx.lock_map()[KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c)] == cache_perms.spec_index(c).lock_id()
                    },
                forall|k: KernelObjId|
                    #![trigger lctx.lock_map().dom().contains(k)]
                    lctx.lock_map().dom().contains(k)
                    ==> lctx.lock_map()[k].major <= ALLOCATOR_GLOBAL_POLL_MAJOR,
                // Caches [0, cpu) were all found empty.
                forall|c: CpuId|
                    #![trigger self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c]]
                    cpu_id_valid(c) && c < cpu
                    ==> self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().view().view().len() == 0,
            decreases NUM_CPUS - cpu,
        {
            proof {
                reveal(allocator_perms_wf);
                assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu].view().write_lock_perm_match(&cache_perms.spec_index(cpu)));
            }
            let cache_ref = self.allocator_4k_map.borrow_cache(
                alloc_ptr_4k, cpu, Tracked(cache_perms.tracked_borrow(cpu)),
            );
            assert(cache_ref.linked_list.wf()) by {
                reveal(allocator_perms_wf);
                assert(cpu_id_valid(cpu));
                assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches_wf());
            };
            let cache_len = cache_ref.linked_list.len();
            assert(cache_len == self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu].view().view().view().len()) by {
                reveal(allocator_perms_wf);
                cache_ref.linked_list.lemma_len_view();
            };
            if cache_len > 0 {
                let (page_ptr, Tracked(page_lock_perm)) = self.pop_stage_4k_page(
                    alloc_ptr_4k, cpu, process_ptr, container_ptr,
                    Tracked(&mut *lctx), Tracked(cache_perms.tracked_borrow(cpu)), Tracked(process_lock_perm),
                );
                assert forall|c: CpuId|
                    #![trigger cache_perms.spec_index(c)]
                    cpu_id_valid(c)
                    implies {
                        &&& self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().wlocked_by(&*lctx)
                        &&& self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().being_killed() == false
                        &&& cache_perms.spec_index(c).lock_id() == self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().locking_thread()->Write_lock_id
                    } by {
                    reveal(allocator_locked_match_lctx);
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
            old(self).container_map.dom().contains(container_ptr),
            old(self).container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            old(self).process_map.dom().contains(process_ptr),
            old(self).process_map.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            old(self).container_map.spec_index(container_ptr).view().owned_processes.view().contains(process_ptr),
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@.wlocked_by(old(lctx)),
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@.being_killed() == false,
            cache_lock_perm.state() is WriteLock,
            cache_lock_perm.thread_id() == old(lctx).thread_id(),
            cache_lock_perm.lock_id() == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@.locking_thread()->Write_lock_id,
            old(lctx).lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cpu_id)),
            old(lctx).lock_map()[KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cpu_id)] == cache_lock_perm.lock_id(),
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@@.view().len() > 0,
            old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
            old(self).process_map.spec_index(process_ptr).being_killed() == false,
            process_effective_quota_4k(old(self).process_map.spec_index(process_ptr)) >= 1,
            process_lock_perm.state() is WriteLock,
            process_lock_perm.thread_id() == old(lctx).thread_id(),
            process_lock_perm.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            old(lctx).lock_map().dom().contains(KernelObjId::Process(process_ptr)),
            old(lctx).lock_map()[KernelObjId::Process(process_ptr)] == process_lock_perm.lock_id(),
            old(self).locked_objects_match_lctx(old(lctx)),
            forall|k: KernelObjId|
                #![trigger old(lctx).lock_map().dom().contains(k)]
                old(lctx).lock_map().dom().contains(k)
                ==> old(lctx).lock_map()[k].major <= ALLOCATOR_GLOBAL_POLL_MAJOR,
        ensures
            final(self).inv(),
            page_ptr_valid(ret.0),
            // ---- user view unchanged: staging is kernel-internal ----
            kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
            // ---- cache + process lock state preserved, phase still Acquire ----
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
            final(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id].view().wlocked_by(final(lctx)),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id].view().being_killed() == false,
            cache_lock_perm.lock_id() == final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id].view().locking_thread()->Write_lock_id,
            final(self).process_map.dom().contains(process_ptr),
            final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx)),
            final(self).process_map.spec_index(process_ptr).being_killed() == false,
            process_lock_perm.lock_id() == final(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            final(self).process_map.spec_index(process_ptr).view_rodata() == old(self).process_map.spec_index(process_ptr).view_rodata(),
            // ---- page slot left write-locked, perm handed back ----
            page_index_wf(page_ptr2page_index(ret.0)),
            final(self).page_array[page_ptr2page_index(ret.0)].view().wlocked_by(final(lctx)),
            final(self).page_array[page_ptr2page_index(ret.0)].view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(self).page_array[page_ptr2page_index(ret.0)].view().locking_thread()->Write_lock_id,
            final(lctx).lock_map().dom().contains(KernelObjId::Page(page_ptr2page_index(ret.0))),
            final(lctx).lock_map()[KernelObjId::Page(page_ptr2page_index(ret.0))] == ret.1.view().lock_id(),
            // ---- lock_map: gained exactly the page slot; everything else preserved ----
            final(lctx).lock_map() == old(lctx).lock_map().insert(KernelObjId::Page(page_ptr2page_index(ret.0)), ret.1.view().lock_id()),
            final(self).locked_objects_match_lctx(final(lctx)),
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
            // ---- container_map + scheduler_map untouched (staging never writes them) ----
            final(self).container_map == old(self).container_map,
            final(self).scheduler_map == old(self).scheduler_map,
    {
        proof {
            reveal(allocator_perms_wf);
            page_ptr_lemma1();
            reveal(process_perms_wf);
            reveal(page_array_wf);
            reveal(page_locked_match_lctx);
        }
        let cache_ref = self.allocator_4k_map.borrow_cache(
            alloc_ptr_4k, cpu_id, Tracked(cache_lock_perm),
        );
        let (node_addr, page_ptr) = cache_ref.linked_list.peek_head();
        assert(page_ptr_valid(page_ptr)) 
        by {
            reveal(allocator_perms_wf);
            reveal(allocator_free_page_ptrs_wf);
        }
        ;
        let page_index = page_ptr2page_index(page_ptr);
        // The peeked page_ptr is the head of the param-cpu cache, so it is in that
        // cache's view() — the antecedent clause 4 needs to pin the page's recorded
        // cpu to the parameter cpu_id.
        assert(
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_ptr)
        );

        // Lock the page slot (still Free4k ⟹ fresh, id tops every held id).
        let Tracked(page_lock_perm) = self.wlock_page(page_index, Tracked(&mut *lctx));

        // Mutation block: pop + decrement (PageAllocator::inv() re-established by
        // the wrapper), retype Free4k→Owned4k, stage.
        let alloc_mut = self.allocator_4k_map.borrow_mut(alloc_ptr_4k);
        let (node_addr2, Tracked(node_perm)) = alloc_mut.pop_cache_page(cpu_id, Tracked(&*lctx), Tracked(cache_lock_perm));
        assert(node_addr2 == node_addr);

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
        // ---- staging delta: page_ptr fresh in temp_alloc_cache_4k ⟹ effective_quota_4k −1 ----
        assert(old(self).page_array.spec_index(page_index).view().view().state is Free4k) by {
            reveal(container_allocator_free_4k_page_wf);
        };
        assert(old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) == false) by {
            page_ptr_lemma1();
            reveal(process_staged_pages_4k_wf);
            if old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) {
                assert(old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == PageState::Owned4k { process_ptr });
            }
        };
        assert(process_effective_quota_4k(self.process_map.spec_index(process_ptr))
            == process_effective_quota_4k(old(self).process_map.spec_index(process_ptr)) - 1);
        proof {
            // ---- user view unchanged: only page_array / temp_alloc / total moved ----
            kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
            // ---- locked_objects_match_lctx: page slot gained, all else framed ----
            assert(self.locked_objects_match_lctx(&*lctx)) by {
                reveal(container_locked_match_lctx);
                reveal(process_locked_match_lctx);
                reveal(thread_locked_match_lctx);
                reveal(endpoint_locked_match_lctx);
                reveal(scheduler_locked_match_lctx);
                reveal(pagetable_locked_match_lctx);
                reveal(page_locked_match_lctx);
                reveal(cpu_locked_match_lctx);
                reveal(allocator_locked_match_lctx);
            }
        }
        proof {
            // ---- subsystems_inv ----
            assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
            assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
            assert(allocator_perms_wf(self.allocator_4k_map)) by {
                reveal(allocator_perms_wf);
            };
            assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); reveal(process_temp_alloc_empty_unless_wlocked); };
            assert(thread_perms_wf(self.thread_map)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
            assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
            // ---- memory_management_inv ----
            assert(self.memory_management_inv()) by {
                assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    allocator_4k_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_4k_map, self.allocator_4k_map); allocator_2m_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_2m_map, self.allocator_2m_map); allocator_1g_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_1g_map, self.allocator_1g_map);
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
                assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map));
                assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    reveal(container_allocator_wf);
                };
                assert(allocator_free_page_ptrs_wf(self.allocator_4k_map)) by {
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(self.allocator_free_pages_wf());
                assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { reveal(process_pagetable_match); };
                assert(hugepage_2m_wf(self.page_array)) by { hugepage_2m_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array); };
                assert(hugepage_1g_wf(self.page_array)) by { hugepage_1g_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array); };
                assert(page_pagetable_wf(self.pagetable_map, self.page_array)) by {
                reveal(page_pagetable_wf);
                reveal(mapped_4k_page_pagetable_wf);
                reveal(mapped_2m_page_pagetable_wf);
                reveal(mapped_1g_page_pagetable_wf);
                reveal(pagetable_perms_wf);
                reveal(pagetables_inv);
                page_ptr_lemma1();
                };
                assert(pagetable_pages_wf(self.pagetable_map, self.page_array)) by { reveal(pagetable_pages_wf); };
                assert(thread_pages_wf(self.thread_map, self.page_array)) by { thread_pages_wf_preserved_for_page_state_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array); };
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
                assert(container_tree_wf(self.root_container, self.container_map));
                assert(container_process_wf(self.container_map, self.process_map)) by {
                    reveal(container_process_wf);
                };
                assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                    reveal(per_container_process_tree_wf);
                    reveal(container_process_wf);
                    process_no_change_to_tree_fields_imply_wf_forall();
                };
                assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by { reveal(container_endpoint_wf); };
                assert(container_cpu_wf(self.container_map, self.cpu_array)) by { reveal(container_cpu_wf); };
                assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                    reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                    reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                };
                assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by { reveal(container_scheduler_wf); };
                assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                    reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                };
                assert(container_thread_wf(self.container_map, self.thread_map)) by { reveal(container_thread_wf); };
                assert(process_cpu_wf(self.process_map, self.cpu_array)) by { reveal(process_cpu_wf); };
                assert(process_thread_wf(self.process_map, self.thread_map)) by { reveal(process_thread_wf); };
            };
            // ---- inv() direct conjuncts ----
            assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                reveal(cpu_dirty_map_contains_container_processes);
                reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                reveal(cpu_dirty_map_proc_pcid_match);
                reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                reveal(container_cpu_wf);
            };
            assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
            assert(self.inv());
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
            old(self).container_map.dom().contains(container_ptr),
            old(self).container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            old(self).process_map.dom().contains(process_ptr),
            old(self).process_map.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            old(self).container_map.spec_index(container_ptr).view().owned_processes.view().contains(process_ptr),
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.wlocked_by(old(lctx)),
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.being_killed() == false,
            global_pool_lock_perm.state() is WriteLock,
            global_pool_lock_perm.thread_id() == old(lctx).thread_id(),
            global_pool_lock_perm.lock_id() == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.locking_thread()->Write_lock_id,
            old(lctx).lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k)),
            old(lctx).lock_map()[KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k)] == global_pool_lock_perm.lock_id(),
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().view().len() > 0,
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().len() > 0,
            old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
            old(self).process_map.spec_index(process_ptr).being_killed() == false,
            process_effective_quota_4k(old(self).process_map.spec_index(process_ptr)) >= 1,
            process_lock_perm.state() is WriteLock,
            process_lock_perm.thread_id() == old(lctx).thread_id(),
            process_lock_perm.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            old(lctx).lock_map().dom().contains(KernelObjId::Process(process_ptr)),
            old(lctx).lock_map()[KernelObjId::Process(process_ptr)] == process_lock_perm.lock_id(),
            old(self).locked_objects_match_lctx(old(lctx)),
            forall|k: KernelObjId|
                #![trigger old(lctx).lock_map().dom().contains(k)]
                old(lctx).lock_map().dom().contains(k)
                ==> old(lctx).lock_map()[k].major <= ALLOCATOR_GLOBAL_POLL_MAJOR,
        ensures
            final(self).inv(),
            page_ptr_valid(ret.0),
            // ---- user view unchanged: staging is kernel-internal ----
            kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
            // ---- global_pool + process lock state preserved, phase still Acquire ----
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
            final(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.wlocked_by(final(lctx)),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.being_killed() == false,
            global_pool_lock_perm.lock_id() == final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.locking_thread()->Write_lock_id,
            final(self).process_map.dom().contains(process_ptr),
            final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx)),
            final(self).process_map.spec_index(process_ptr).being_killed() == false,
            process_lock_perm.lock_id() == final(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            final(self).process_map.spec_index(process_ptr).view_rodata() == old(self).process_map.spec_index(process_ptr).view_rodata(),
            // ---- page slot left write-locked, perm handed back ----
            page_index_wf(page_ptr2page_index(ret.0)),
            final(self).page_array[page_ptr2page_index(ret.0)].view().wlocked_by(final(lctx)),
            final(self).page_array[page_ptr2page_index(ret.0)].view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(self).page_array[page_ptr2page_index(ret.0)].view().locking_thread()->Write_lock_id,
            final(lctx).lock_map().dom().contains(KernelObjId::Page(page_ptr2page_index(ret.0))),
            final(lctx).lock_map()[KernelObjId::Page(page_ptr2page_index(ret.0))] == ret.1.view().lock_id(),
            // ---- lock_map: gained exactly the page slot; everything else preserved ----
            final(lctx).lock_map() == old(lctx).lock_map().insert(KernelObjId::Page(page_ptr2page_index(ret.0)), ret.1.view().lock_id()),
            final(self).locked_objects_match_lctx(final(lctx)),
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
            // ---- container_map + scheduler_map untouched (staging never writes them) ----
            final(self).container_map == old(self).container_map,
            final(self).scheduler_map == old(self).scheduler_map,
    {
        proof {
            reveal(allocator_perms_wf);
            page_ptr_lemma1();
            reveal(process_perms_wf);
            reveal(page_array_wf);
            reveal(page_locked_match_lctx);
        }
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
        );

        // Lock the page slot (still Free4k ⟹ fresh, id tops every held id).
        let Tracked(page_lock_perm) = self.wlock_page(page_index, Tracked(&mut *lctx));

        // Mutation block: pop + decrement (PageAllocator::inv() re-established by
        // the wrapper), retype Free4k→Owned4k, stage.
        let alloc_mut = self.allocator_4k_map.borrow_mut(alloc_ptr_4k);
        let (node_addr2, Tracked(node_perm)) = alloc_mut.pop_global_pool_page(Tracked(&*lctx), Tracked(global_pool_lock_perm));
        assert(node_addr2 == node_addr);

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
        // ---- staging delta: page_ptr fresh in temp_alloc_cache_4k ⟹ effective_quota_4k −1 ----
        assert(self.page_array.spec_index(page_index).view().view().state is Owned4k);
        assert(old(self).page_array.spec_index(page_index).view().view().state is Free4k) by {
            reveal(container_allocator_free_4k_page_wf);
        };
        assert(old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) == false) by {
            page_ptr_lemma1();
            reveal(process_staged_pages_4k_wf);
            if old(self).process_map.spec_index(process_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) {
                assert(old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == PageState::Owned4k { process_ptr });
            }
        };
        assert(process_effective_quota_4k(self.process_map.spec_index(process_ptr))
            == process_effective_quota_4k(old(self).process_map.spec_index(process_ptr)) - 1);
        proof {
            // ---- user view unchanged: only page_array / temp_alloc / total moved ----
            kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
            // ---- locked_objects_match_lctx: page slot gained, all else framed ----
            assert(self.locked_objects_match_lctx(&*lctx)) by {
                reveal(container_locked_match_lctx);
                reveal(process_locked_match_lctx);
                reveal(thread_locked_match_lctx);
                reveal(endpoint_locked_match_lctx);
                reveal(scheduler_locked_match_lctx);
                reveal(pagetable_locked_match_lctx);
                reveal(page_locked_match_lctx);
                reveal(cpu_locked_match_lctx);
                reveal(allocator_locked_match_lctx);
            }
        }
        proof {
            // ---- subsystems_inv ----
            assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
            assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
            assert(allocator_perms_wf(self.allocator_4k_map)) by {
                reveal(allocator_perms_wf);
            };
            assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); reveal(process_temp_alloc_empty_unless_wlocked); };
            assert(thread_perms_wf(self.thread_map)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
            assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
            // ---- memory_management_inv ----
            assert(self.memory_management_inv()) by {
                assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    allocator_4k_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_4k_map, self.allocator_4k_map); allocator_2m_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_2m_map, self.allocator_2m_map); allocator_1g_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_1g_map, self.allocator_1g_map);
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
                assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map));
                assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    reveal(container_allocator_wf);
                };
                assert(allocator_free_page_ptrs_wf(self.allocator_4k_map)) by {
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(self.allocator_free_pages_wf());
                assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { reveal(process_pagetable_match); };
                assert(hugepage_2m_wf(self.page_array)) by { hugepage_2m_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array); };
                assert(hugepage_1g_wf(self.page_array)) by { hugepage_1g_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array); };
                assert(page_pagetable_wf(self.pagetable_map, self.page_array)) by {
                reveal(page_pagetable_wf);
                reveal(mapped_4k_page_pagetable_wf);
                reveal(mapped_2m_page_pagetable_wf);
                reveal(mapped_1g_page_pagetable_wf);
                reveal(pagetable_perms_wf);
                reveal(pagetables_inv);
                page_ptr_lemma1();
                };
                assert(pagetable_pages_wf(self.pagetable_map, self.page_array)) by { reveal(pagetable_pages_wf); };
                assert(thread_pages_wf(self.thread_map, self.page_array)) by { thread_pages_wf_preserved_for_page_state_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array); };
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
                    reveal(LinkedList::wf_value_list);
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
                assert(container_tree_wf(self.root_container, self.container_map));
                assert(container_process_wf(self.container_map, self.process_map)) by {
                    reveal(container_process_wf);
                };
                assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                    reveal(per_container_process_tree_wf);
                    reveal(container_process_wf);
                    process_no_change_to_tree_fields_imply_wf_forall();
                };
                assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by { reveal(container_endpoint_wf); };
                assert(container_cpu_wf(self.container_map, self.cpu_array)) by { reveal(container_cpu_wf); };
                assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                    reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                    reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                };
                assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by { reveal(container_scheduler_wf); };
                assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                    reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                };
                assert(container_thread_wf(self.container_map, self.thread_map)) by { reveal(container_thread_wf); };
                assert(process_cpu_wf(self.process_map, self.cpu_array)) by { reveal(process_cpu_wf); };
                assert(process_thread_wf(self.process_map, self.thread_map)) by { reveal(process_thread_wf); };
            };
            // ---- inv() direct conjuncts ----
            assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                reveal(cpu_dirty_map_contains_container_processes);
                reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                reveal(cpu_dirty_map_proc_pcid_match);
                reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                reveal(container_cpu_wf);
            };
            assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
            assert(self.inv());
        }
        (page_ptr, Tracked(page_lock_perm))
    }

    // ================================================================
    // Finish helper: a page has just been popped from a write-locked cache
    // (or pool). Set it to Owned4k, stage it in the process's temp_alloc
    // cache, decrement the allocator's ghost total_free_pages, unlock the
    // page slot and the cache. Re-establishes inv().
    //
    // Preconditions capture the post-pop state: `self` is NOT a full `inv()`
    // (the popped page is missing from the cache that wf() folds over, and the
    // page is still `Free4k{PreCpuCache}` pointing at a now-absent node), so we
    // take the specific facts we need and rebuild inv() at the end.
    // ================================================================
    // #[verifier::spinoff_prover]
    // fn finish_allocate_4k_page(
    //     &mut self,
    //     alloc_ptr_4k: RwLockPageAllocatorPtr,
    //     cpu_id: CpuId,
    //     process_ptr: RwLockProcessPtr,
    //     container_ptr: RwLockContainerPtr,
    //     Tracked(lctx): Tracked<&mut LocalContext>,
    //     Tracked(steps): Tracked<&mut KernelSteps>,
    //     Tracked(cache_lock_perm): Tracked<LockPerm>,
    //     Tracked(process_lock_perm): Tracked<&LockPerm>,
    // ) -> (ret: PagePtr)
    //     requires
    //         old(self).inv(),
    //         // Snapshot matches the current projection (this kernel step does not
    //         // change the user view), so kernel_step_boundary can refresh it.
    //         kernel_k_to_kernel_u(*old(self)) == old(steps).snap_shot,
    //         cpu_id_valid(cpu_id),
    //         old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
    //         old(self).container_map.dom().contains(container_ptr),
    //         old(self).container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
    //         old(self).process_map.dom().contains(process_ptr),
    //         old(self).process_map.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
    //         old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
    //         // The cpu cache is write-locked by this thread and non-empty.
    //         old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@.wlocked_by(old(lctx)),
    //         cache_lock_perm.state() is WriteLock,
    //         cache_lock_perm.thread_id() == old(lctx).thread_id(),
    //         cache_lock_perm.lock_id() == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@.locking_thread()->Write_lock_id,
    //         old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@@.view().len() > 0,
    //         // Process write-lock perm (to stage the page in temp_alloc_cache_4k).
    //         process_lock_perm.state() is WriteLock,
    //         process_lock_perm.thread_id() == old(lctx).thread_id(),
    //         process_lock_perm.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
    //         // lctx state: kernel section open, lock_map holds exactly the process
    //         // and this cpu cache (so the page slot is fresh to lock), and the
    //         // lock-map ⇄ kernel-state agreement holds.
    //         old(lctx).kernel_view_locking_state() is Acquire,
    //         old(self).locked_objects_match_lctx(old(lctx)),
    //         // Page freshness + acyclicity are DERIVED here (no exact lock_map
    //         // pin). The caller guarantees every held lock id sits at or below
    //         // the cpu-cache major (`ALLOCATOR_CACHE_MAJOR`, well under any page
    //         // major). Combined with `locked_objects_match_lctx`'s pinned page id
    //         // (a held page records major ≥ ALLOCATED_PAGE_MAJOR ≥ 1000), this
    //         // proves NO page is currently held — so the popped page index is
    //         // fresh — and that the Free page's lock id (major 30000, owner None)
    //         // exceeds every held id (owners tie/win for None, else major 30000 >
    //         // held ≤ 106). See the page-slot wlock block below.
    //         forall|k: KernelObjId|
    //             #![trigger old(lctx).lock_map().dom().contains(k)]
    //             old(lctx).lock_map().dom().contains(k)
    //             ==> old(lctx).lock_map()[k].major <= ALLOCATOR_CACHE_MAJOR,
    //     ensures
    //         // ---- Minimal clean contract (functional postconditions dropped). ----
    //         final(self).inv(),
    //         page_ptr_valid(ret),
    //         // After release-all + kernel_step_boundary: phase restored to Acquire,
    //         // the process is still held (its lock_map entry / payload survive the
    //         // boundary), the snapshot is refreshed, lock-map ⇄ kernel agree.
    //         final(lctx).kernel_view_locking_state() is Acquire,
    //         final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
    //         final(self).process_map.dom().contains(process_ptr),
    //         final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx)),
    //         final(self).locked_objects_match_lctx(final(lctx)),
    //         final(steps).steps == old(steps).steps,
    //         final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
    // {
    //     // ===================================================================
    //     // Clean fast-path finish. Exec sequence (no snapshot ghosts; `old(self)`
    //     // is the pre-state). Proof obligations are staged behind LABELED assumes
    //     // to be discharged one by one.
    //     // ===================================================================
    //     proof {
    //         reveal(allocator_perms_wf);
    //         // From the allocator's inv(): the cache is wf + is_init (wlocked ⟹
    //         // init) — needed by borrow_mut_cache / pop_head below.
    //         assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches_wf());
    //         assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).inv());
    //         self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@@.linked_list.lemma_len_view();
    //     }
    //     // Entry fact: the cpu cache is recorded in lock_map with the cache perm's
    //     // id. From the entry `locked_objects_match_lctx` (forward agreement) + the
    //     // cache being wlocked-by-us with `cache_lock_perm`. Captured here (lctx ==
    //     // entry lctx) so it survives — unchanged — to the page wunlock below.
    //     // proof {
    //     //     reveal(allocator_locked_match_lctx);
    //     //     assert(self.allocator_4k_map.dom().contains(alloc_ptr_4k));
    //     //     assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@.wlocked_by(&*lctx));
    //     //     // reverse: cache locked_by us ⟹ recorded in lock_map.
    //     //     assert(self.allocator_4k_map[alloc_ptr_4k].cpu_caches[cpu_id]@.locked_by(&*lctx));
    //     //     assert(lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cpu_id)));
    //     //     // forward: recorded id == cache's Write_lock_id == cache_lock_perm.lock_id().
    //     //     assert(lctx.lock_map()[KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cpu_id)]
    //     //         == self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@.locking_thread()->Write_lock_id);
    //     //     assert(lctx.lock_map()[KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cpu_id)] == cache_lock_perm.lock_id());
    //     // }
    //     // let ghost entry_lctx_lock_map = lctx.lock_map();

    //     // // 1. PEEK the head of the cache's linked list — NO mutation, so the
    //     // //    full `inv()` still holds. We learn the page pointer (the head node's
    //     // //    value) and its index BEFORE popping, so we can lock the page slot
    //     // //    while the page is still Free (clean acyclicity: Free major 30000).
    //     let cache_ref = self.allocator_4k_map.borrow_cache(
    //         alloc_ptr_4k, cpu_id, Tracked(&cache_lock_perm),
    //     );
    //     let (node_addr, page_ptr) = cache_ref.linked_list.peek_head();
    //     // proof {
    //     //     // page_ptr == cache head; allocator_free_page_ptrs_wf ⟹ valid ptr.
    //     //     assert(page_ptr == self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@@.view()[0]);
    //     //     assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@@.view().contains(page_ptr));
    //     //     assert(allocator_free_page_ptrs_wf(self.allocator_4k_map));
    //     // }
    //     assert(page_ptr_valid(page_ptr));
    //     let page_index = page_ptr2page_index(page_ptr);

    //     // // 2. Lock the page slot. The page is STILL Free4k (we have not popped),
    //     // //    inv() still holds, and its lock id is the easy case: owner None/None
    //     // //    (MAX), major FREE_PAGE_LOCK_MAJOR (30000).
    //     // //
    //     // // First derive the peeked page's prior state from the reverse-cache
    //     // // clause of `container_allocator_free_4k_page_wf` (held by inv()): a page
    //     // // whose ptr is in cache[cpu_id] is `Free4k{PreCpuCache{cpu_id}}`.
    //     // proof {
    //     //     reveal(container_allocator_free_4k_page_wf);
    //     //     page_ptr_lemma1();  // page_ptr_valid ⟹ page_ptr2page_index round-trips
    //     //     assert(self.allocator_4k_map.dom().contains(alloc_ptr_4k));
    //     //     assert(self.allocator_4k_map.spec_index(alloc_ptr_4k)
    //     //         .cpu_caches.spec_index(cpu_id).view().view().view().contains(page_ptr));
    //     //     // reverse-cache clause fires at (alloc_ptr_4k, cpu_id, page_ptr):
    //     //     assert(self.page_array.spec_index(page_index).view().view().state matches
    //     //         PageState::Free4k { state: FreePageAllocatorState::PreCpuCache { cpu_id: _ } });
    //     //     assert(self.page_array[page_index]@@.is_free());
    //     //     assert(self.page_array[page_index]@@.current_lock_major() == FREE_PAGE_LOCK_MAJOR);
    //     //     assert(self.page_array[page_index].container_depth() is None);
    //     //     assert(self.page_array[page_index].process_depth() is None);
    //     // }
    //     // // Capture the FORWARD-clause node-storage facts while inv() holds: the
    //     // // page's free-list node storage address is live in cache[cpu_id]'s map
    //     // // and maps to page_ptr. (Used after the pop to prove the popped node IS
    //     // // this page's storage, via cache-map injectivity.)
    //     // let ghost storage_addr = self.page_array.spec_index(page_index)@@.free_list_node_storage.addr();
    //     // proof {
    //     //     reveal(container_allocator_free_4k_page_wf);
    //     //     reveal(container_allocator_wf);
    //     //     // The page's owning_container's allocator_ptr_4k is alloc_ptr_4k:
    //     //     // reverse-cache clause gave owning_container == allocator owning_container;
    //     //     // container_allocator_wf ties that container's allocator_ptr_4k back.
    //     //     let owner = self.page_array.spec_index(page_index)@@.owning_container;
    //     //     assert(self.container_map.spec_index(owner).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k);
    //     //     // forward clause (cache branch) at page_index:
    //     //     assert(self.allocator_4k_map.spec_index(alloc_ptr_4k)
    //     //         .cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(storage_addr));
    //     //     assert(self.allocator_4k_map.spec_index(alloc_ptr_4k)
    //     //         .cpu_caches.spec_index(cpu_id).view().view().map().spec_index(storage_addr) == page_ptr);
    //     // }
    //     // // Freshness + acyclicity from the loose precondition + the pinned page id
    //     // // (a held page records major ≥ ALLOCATED_PAGE_MAJOR ≥ 1000, but every
    //     // // held major ≤ ALLOCATOR_CACHE_MAJOR=106 ⟹ no page is held ⟹ fresh; and
    //     // // the Free page id, owner None=MAX/major 30000, exceeds every held id).
    //     // proof {
    //     //     reveal(page_array_wf);
    //     //     reveal(page_locked_match_lctx);
    //     //     // Freshness.
    //     //     if lctx.lock_map().dom().contains(KernelObjId::Page(page_index)) {
    //     //         let held = lctx.lock_map()[KernelObjId::Page(page_index)];
    //     //         assert(held.major == FREE_PAGE_LOCK_MAJOR
    //     //             || held.major == MAPPED_PAGE_LOCK_MAJOR
    //     //             || held.major == MERGED_PAGE_LOCK_MAJOR
    //     //             || held.major == ALLOCATED_PAGE_MAJOR);
    //     //         assert(held.major >= ALLOCATED_PAGE_MAJOR);
    //     //         assert(held.major <= ALLOCATOR_CACHE_MAJOR);
    //     //         assert(false);
    //     //     }
    //     //     assert(lctx.obj_id_fresh(KernelObjId::Page(page_index)));
    //     //     assert(self.page_array[page_index]@.locked_by(&*lctx) == false);
    //     //     assert(wlock_requires(self.page_array[page_index]@, &*lctx));
    //     //     // Acyclicity.
    //     //     let page_lid = LockId{
    //     //         container: self.page_array[page_index].container_depth(),
    //     //         process: self.page_array[page_index].process_depth(),
    //     //         major: self.page_array[page_index]@@.current_lock_major(),
    //     //         minor: self.page_array[page_index].lock_minor(),
    //     //     };
    //     //     assert(page_lid.container is None && page_lid.process is None);
    //     //     assert(page_lid.major == FREE_PAGE_LOCK_MAJOR);
    //     //     assert forall|k: KernelObjId| #![auto] lctx.lock_map().dom().contains(k)
    //     //     implies page_lid.spec_gt(lctx.lock_map()[k]) by {
    //     //         let held = lctx.lock_map()[k];
    //     //         assert(held.major <= ALLOCATOR_CACHE_MAJOR);
    //     //         if page_lid.container.spec_eq(held.container) && page_lid.process.spec_eq(held.process) {
    //     //             assert(page_lid.major != held.major);
    //     //             assert(page_lid.major > held.major);
    //     //         } else if !page_lid.container.spec_eq(held.container) {
    //     //             assert(page_lid.container.spec_gt(held.container));
    //     //         } else {
    //     //             assert(!page_lid.process.spec_eq(held.process));
    //     //             assert(page_lid.process.spec_gt(held.process));
    //     //         }
    //     //     };
    //     //     assert(lctx.lock_id_acyclic(page_lid));
    //     // }
    //     // let ghost pre_pwlock = *self;
    //     // let ghost pre_pwlock_lctx_lock_map = lctx.lock_map();
    //     // let Tracked(page_lock_perm) = self.page_array.wlock(
    //     //     page_index, Tracked(&mut *lctx), Ghost(KernelObjId::Page(page_index)),
    //     // );
    //     // // Capture the page-lock facts from wlock_ensures / lock_ensures: the slot
    //     // // is now wlocked by us with `page_lock_perm`'s id (== the structural page
    //     // // lid), being_killed is false (NO_KILL_STATE page array), and lock_map
    //     // // gained exactly Page(page_index)↦that id. These are threaded UNCHANGED
    //     // // through the mutation block (take/put/borrow_muts touch neither the page
    //     // // lock state nor lock_map) to the page wunlock below.
    //     // let ghost page_wlid = LockId{
    //     //     container: pre_pwlock.page_array[page_index].container_depth(),
    //     //     process: pre_pwlock.page_array[page_index].process_depth(),
    //     //     major: pre_pwlock.page_array[page_index]@@.current_lock_major(),
    //     //     minor: pre_pwlock.page_array[page_index].lock_minor(),
    //     // };
    //     // proof {
    //     //     assert(self.page_array[page_index]@.wlocked_by(&*lctx));
    //     //     assert(self.page_array[page_index]@.being_killed() == false);
    //     //     assert(page_lock_perm.lock_id() == page_wlid);
    //     //     assert(self.page_array[page_index]@.locking_thread()->Write_lock_id == page_wlid);
    //     //     assert(lctx.lock_map() =~= pre_pwlock_lctx_lock_map.insert(KernelObjId::Page(page_index), page_wlid));
    //     //     assert(lctx.lock_map().dom().contains(KernelObjId::Page(page_index)));
    //     //     assert(lctx.lock_map()[KernelObjId::Page(page_index)] == page_lock_perm.lock_id());
    //     // }
    //     // // inv() STILL HOLDS here — the page wlock is a lock-state-only change:
    //     // // `wlock` touched only `page_array` lock state (every page's `@@` and
    //     // // `RwLock::inv()` preserved — touched slot by `wlock_ensures`, others by
    //     // // `unchanged_except`), every other map byte-equal. The dedicated
    //     // // preservation lemma frames `inv()` across it.
    //     // proof {
    //     //     reveal(page_array_wf);
    //     //     assert(pre_pwlock.inv());
    //     //     // wlock ensures: structural inv() + per-index facts.
    //     //     assert(self.page_array.inv());
    //     //     assert(self.page_array.view().len() == pre_pwlock.page_array.view().len());
    //     //     assert(self.page_array.unchanged_except(&pre_pwlock.page_array, page_index));
    //     //     // touched slot: wlock_ensures gives new@ == old@ and new.inv().
    //     //     assert(self.page_array[page_index]@@ == pre_pwlock.page_array[page_index]@@);
    //     //     assert(self.page_array[page_index]@.inv());
    //     //     assert forall|i: PageIndex| #![trigger self.page_array.spec_index(i).view().view()]
    //     //         page_index_wf(i) implies
    //     //         self.page_array.spec_index(i).view().view() == pre_pwlock.page_array.spec_index(i).view().view()
    //     //         && self.page_array.spec_index(i).view().inv() by {
    //     //         if i != page_index {
    //     //             assert(self.page_array[i] == pre_pwlock.page_array[i]);
    //     //             // pre satisfied page_array_wf ⟹ this slot's RwLock inv().
    //     //             assert(pre_pwlock.page_array[i]@.inv());
    //     //         }
    //     //     };
    //     //     lemma_inv_preserved_for_page_lock_state_change(pre_pwlock, *self);
    //     //     assert(self.inv());
    //     // }

    //     // // ===================================================================
    //     // // 3. THE MUTATION BLOCK — no lock/unlock here. Pop the node, flip the
    //     // //    page Free4k→Owned4k (restoring its ExternalNode perm), stage it in
    //     // //    the process, decrement the allocator total. inv() is FALSE partway
    //     // //    through; we rebuild it once at the end. [THE HARD PART]
    //     // // ===================================================================
    //     // // 3a. Pop the head node we peeked (mutates the cache list). Capture the
    //     // //     pre-borrow state so the cache-map forward facts (which we can't
    //     // //     read off `self` while it's mutably borrowed) survive on a ghost.
    //     // let ghost pre_borrow = *self;
    //     // proof {
    //     //     // Re-derive the forward node-storage facts on pre_borrow (inv() holds
    //     //     // for self == pre_borrow here — page wlock preserved it). storage_addr
    //     //     // is unchanged from peek (page_array untouched by the cache pop yet).
    //     //     reveal(container_allocator_free_4k_page_wf);
    //     //     reveal(container_allocator_wf);
    //     //     page_ptr_lemma1();
    //     //     assert(self.page_array.spec_index(page_index)@@.free_list_node_storage.addr() == storage_addr);
    //     //     assert(self.page_array.spec_index(page_index).view().view().state matches
    //     //         PageState::Free4k { state: FreePageAllocatorState::PreCpuCache { cpu_id: _ } });
    //     //     let owner = self.page_array.spec_index(page_index)@@.owning_container;
    //     //     assert(self.container_map.spec_index(owner).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k);
    //     //     assert(self.allocator_4k_map.spec_index(alloc_ptr_4k)
    //     //         .cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(storage_addr));
    //     //     assert(self.allocator_4k_map.spec_index(alloc_ptr_4k)
    //     //         .cpu_caches.spec_index(cpu_id).view().view().map().spec_index(storage_addr) == page_ptr);
    //     // }
    //     // let cache_mut = self.allocator_4k_map.borrow_mut_cache(
    //     //     alloc_ptr_4k, cpu_id, Tracked(&*lctx), Tracked(&cache_lock_perm),
    //     // );
    //     // // borrow_mut_cache: *cache_mut == pre_borrow's cache `@@`.
    //     // assert(*cache_mut == pre_borrow.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id)@@);
    //     // let ghost prepop_list = cache_mut.linked_list;
    //     // proof {
    //     //     // The page wlock didn't touch the allocator, so pre_borrow's cache
    //     //     // equals the peeked cache; transport the forward node-storage facts.
    //     //     assert(prepop_list == pre_borrow.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id)@@.linked_list);
    //     //     assert(prepop_list.map().dom().contains(storage_addr));
    //     //     assert(prepop_list.map()[storage_addr] == page_ptr);
    //     // }
    //     // let (node_addr2, Tracked(node_perm)) = cache_mut.linked_list.pop_head();
    //     // proof {
    //     //     // pop returns the same head we peeked: the cache list is unchanged
    //     //     // between peek and pop (only a shared borrow intervened), so both
    //     //     // `pop_head` (ret.0 == addr_list[0], value == @[0]) and `peek_head`
    //     //     // (node_addr == addr_list[0], page_ptr == @[0]) name the head.
    //     //     assert(prepop_list.addr_list@[0] == node_addr);
    //     //     assert(node_addr2 == prepop_list.addr_list@[0]);
    //     //     assert(node_addr2 == node_addr);
    //     //     assert(node_perm.value()@ == prepop_list.view()[0]);
    //     //     assert(page_ptr == prepop_list.view()[0]);
    //     //     assert(node_perm.value()@ == page_ptr);
    //     // }
    //     // // 3b. Take the page, set Owned4k, restore the popped node's ExternalNode
    //     // //     permission into its free-list slot, put it back.
    //     // let ghost taken_page = self.page_array.spec_index(page_index)@@;
    //     // let mut page = self.page_array.take(page_index, Tracked(&*lctx), Tracked(&page_lock_perm));
    //     // // `take` returns the current page value; the page is still the Free page
    //     // // (page_array untouched since the wlock — only the cache list moved). The
    //     // // node-storage facts hold on the Free `taken_page` and survive the state
    //     // // flip below (the assignment touches only `.state`).
    //     // assert(page == taken_page);
    //     // proof {
    //     //     assert(taken_page.is_free());
    //     //     assert(taken_page.inv());
    //     //     assert(taken_page.node_storage_inv());
    //     //     assert(taken_page.free_list_node_storage.is_init() == false);
    //     // }
    //     // page.state = PageState::Owned4k { process_ptr };
    //     // proof {
    //     //     // Only `.state` changed: node-storage slot is still taken_page's.
    //     //     assert(page.free_list_node_storage == taken_page.free_list_node_storage);
    //     //     assert(page.free_list_node_storage.is_init() == false);
    //     //     // storage.addr() == node_perm.addr() (== node_addr): both addresses
    //     //     // hold value page_ptr in the (pre-pop) cache, which has no duplicate
    //     //     // values, so map-injectivity equates them.
    //     //     page_ptr_lemma1();
    //     //     // `page` is the still-Free page taken from the slot, so its storage
    //     //     // addr is the `storage_addr` captured at peek (page_array untouched).
    //     //     assert(page.free_list_node_storage.addr() == storage_addr);
    //     //     // forward fact (captured at peek): storage_addr ∈ map, maps to page_ptr.
    //     //     assert(prepop_list.map().dom().contains(storage_addr));
    //     //     assert(prepop_list.map()[storage_addr] == page_ptr);
    //     //     // node_addr (the popped head): in dom, maps to page_ptr (peek_head).
    //     //     assert(prepop_list.map().dom().contains(node_addr));
    //     //     assert(prepop_list.map()[node_addr] == page_ptr);
    //     //     assert(prepop_list.view().no_duplicates());
    //     //     prepop_list.lemma_value_addr_unique(storage_addr, node_addr);
    //     //     assert(storage_addr == node_addr);
    //     //     assert(node_perm.addr() == node_addr);
    //     //     assert(page.free_list_node_storage.addr() == node_perm.addr());
    //     // }
    //     // page.free_list_node_storage.put(Tracked(node_perm));
    //     // self.page_array.put(page_index, Tracked(&*lctx), Tracked(&page_lock_perm), page);

    //     // // 3c. Stage the page into the process's temp_alloc_cache_4k.
    //     // proof {
    //     //     reveal(process_perms_wf);
    //     //     assert(self.process_map.spec_index(process_ptr).is_init());
    //     //     assert(self.process_map.spec_index(process_ptr).wlocked_by(&*lctx));
    //     // }
    //     // let process_mut = self.process_map.borrow_mut(
    //     //     process_ptr, Tracked(&*lctx), Tracked(process_lock_perm),
    //     // );
    //     // process_mut.temp_alloc_cache_4k = Ghost(process_mut.temp_alloc_cache_4k@.insert(page_ptr));

    //     // // 3d. Decrement the allocator's ghost total_free_pages (one page left the
    //     // //     cache, under the same cache lock — preserves the conservation total).
    //     // let alloc_mut = self.allocator_4k_map.borrow_mut(alloc_ptr_4k);
    //     // alloc_mut.total_free_pages = Ghost((alloc_mut.total_free_pages@ - 1) as usize);

    //     // // ===== Rebuild inv() (page + cache still write-locked). [THE HARD PART] =====
    //     // proof {
    //     //     assume(self.inv());
    //     //     assume(self.allocator_4k_map.spec_index(alloc_ptr_4k).wf());
    //     // }

    //     // // 6. Unlock the page slot, then the cache. [page-lock-state-only changes;
    //     // //    inv() frames across each — the easy bookend of the plan.]
    //     // //
    //     // // lctx.lock_map() is UNCHANGED since the page wlock (take/put/borrow_mut
    //     // // all take `lctx` by shared ref — no lock op intervened), so it is still
    //     // // `post-wlock map` = pre-wlock ∪ {Page↦page_wlid, and it already held the
    //     // // cache key}. The page slot is still wlocked by us with `page_lock_perm`'s
    //     // // id: take/put preserve `locking_thread`. [the page wlocked/being_killed
    //     // // facts are threaded from the hard inv() rebuild's framing — TODO once it
    //     // // lands; lock_map facts are derived here.]
    //     // proof {
    //     //     assume(self.page_array[page_index]@.wlocked_by(&*lctx));
    //     //     assume(self.page_array[page_index]@.being_killed() == false);
    //     //     assert(unlock_requires::<Page>(&*lctx)) by { assert(!Page::is_user_visible()); };
    //     //     // lock_map unchanged since the wlock capture ⟹ Page key present.
    //     //     assert(lctx.lock_map() =~= pre_pwlock_lctx_lock_map.insert(KernelObjId::Page(page_index), page_wlid));
    //     //     assert(lctx.lock_map().dom().contains(KernelObjId::Page(page_index)));
    //     //     assert(lctx.lock_map()[KernelObjId::Page(page_index)] == page_wlid);
    //     //     assert(page_lock_perm.lock_id() == page_wlid);
    //     //     assert(lctx.lock_map()[KernelObjId::Page(page_index)] == page_lock_perm.lock_id());
    //     // }
    //     // let ghost pre_punlk = *self;
    //     // let ghost pre_punlk_lctx_lock_map = lctx.lock_map();
    //     // // Cache lock facts hold pre-wunlock (page wunlock won't touch them). The
    //     // // cache key was present BEFORE the page wlock (cache held since entry) and
    //     // // the wlock only inserted the Page key, so it survives.
    //     // proof {
    //     //     reveal(allocator_locked_match_lctx);
    //     //     assume(self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@.wlocked_by(&*lctx));
    //     //     assert(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cpu_id) != KernelObjId::Page(page_index));
    //     //     // lctx unchanged entry → pre-page-wlock; the cache key (captured at
    //     //     // entry) survives the page wlock's single Page insert.
    //     //     assert(pre_pwlock_lctx_lock_map == entry_lctx_lock_map);
    //     //     assert(pre_pwlock_lctx_lock_map.dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cpu_id)));
    //     //     assert(pre_pwlock_lctx_lock_map[KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cpu_id)] == cache_lock_perm.lock_id());
    //     //     assert(lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cpu_id)));
    //     //     assert(lctx.lock_map()[KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cpu_id)] == cache_lock_perm.lock_id());
    //     // }
    //     // self.page_array.wunlock(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm), Ghost(KernelObjId::Page(page_index)));
    //     // proof {
    //     //     // page wunlock preserves inv() (page lock-state-only change) — the
    //     //     // same preservation lemma, mirror direction.
    //     //     reveal(page_array_wf);
    //     //     assert(self.allocator_4k_map == pre_punlk.allocator_4k_map);
    //     //     assert(self.page_array.unchanged_except(&pre_punlk.page_array, page_index));
    //     //     assert(self.page_array[page_index]@@ == pre_punlk.page_array[page_index]@@);
    //     //     assert(self.page_array[page_index]@.inv());
    //     //     assert forall|i: PageIndex| #![trigger self.page_array.spec_index(i).view().view()]
    //     //         page_index_wf(i) implies
    //     //         self.page_array.spec_index(i).view().view() == pre_punlk.page_array.spec_index(i).view().view()
    //     //         && self.page_array.spec_index(i).view().inv() by {
    //     //         if i != page_index {
    //     //             assert(self.page_array[i] == pre_punlk.page_array[i]);
    //     //             assert(pre_punlk.page_array[i]@.inv());
    //     //         }
    //     //     };
    //     //     lemma_inv_preserved_for_page_lock_state_change(pre_punlk, *self);
    //     //     assert(self.inv());
    //     //     // Cache facts carry: allocator byte-equal ⟹ wf()/lock-state/kill;
    //     //     // lock_map only lost the Page key (unlock_ensures).
    //     //     assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).wf());
    //     //     assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@.wlocked_by(&*lctx));
    //     //     assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@.being_killed() == false);
    //     //     assert(lctx.lock_map() =~= pre_punlk_lctx_lock_map.remove(KernelObjId::Page(page_index)));
    //     //     assert(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cpu_id) != KernelObjId::Page(page_index));
    //     //     assert(lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cpu_id)));
    //     //     assert(lctx.lock_map()[KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cpu_id)] == cache_lock_perm.lock_id());
    //     // }
    //     // self.wunlock_allocator_cache(alloc_ptr_4k, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm));

    //     // // 7. End the kernel atomic step: we are in Release with inv() holding and
    //     // //    the user view unchanged, so the boundary refreshes the snapshot and
    //     // //    flips back to Acquire. [TODO discharge the boundary preconditions]
    //     // proof {
    //     //     assume(self.locked_objects_match_lctx(&*lctx));
    //     //     assume(kernel_k_to_kernel_u(*self) == steps.snap_shot);
    //     //     assume(lctx.kernel_view_locking_state() is Release);
    //     //     assert(self.process_map.spec_index(process_ptr).wlocked_by(&*lctx)) by {
    //     //         assume(self.process_map.spec_index(process_ptr).wlocked_by(&*lctx));
    //     //     };
    //     //     assert(lctx.lock_map().dom().contains(KernelObjId::Process(process_ptr))) by {
    //     //         reveal(process_locked_match_lctx);
    //     //     };
    //     //     self.kernel_step_boundary(&mut *lctx, &mut *steps);
    //     // }
    //     // page_ptr

    //     assume(false);
    //     0
    // }

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
            container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, ContainerGhostK, ContainerGhostU, CONTAINER_HAS_KILL_STATE>,
            thread_map: ThreadLockedMap,
            allocator_2m_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,
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
        container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, ContainerGhostK, ContainerGhostU, CONTAINER_HAS_KILL_STATE>,
        thread_map: ThreadLockedMap,
        allocator_2m_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,
        old_process_map: ProcessLockedMap,
        new_process_map: ProcessLockedMap,
    |
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
            container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, ContainerGhostK, ContainerGhostU, CONTAINER_HAS_KILL_STATE>,
            thread_map: ThreadLockedMap,
            allocator_1g_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,
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
        container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, ContainerGhostK, ContainerGhostU, CONTAINER_HAS_KILL_STATE>,
        thread_map: ThreadLockedMap,
        allocator_1g_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,
        old_process_map: ProcessLockedMap,
        new_process_map: ProcessLockedMap,
    |
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
    assert forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap|
        (forall|p: RwLockProcessPtr|
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
    assert forall|s: Set<RwLockProcessPtr>, pre: ProcessLockedMap, post: ProcessLockedMap|
        (s.contains(mod_p)
        && process_effective_quota_4k(post.spec_index(mod_p)) == process_effective_quota_4k(pre.spec_index(mod_p)) + x
        && forall|p: RwLockProcessPtr|
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
    reveal(allocator_perms_wf);
    reveal(container_allocator_wf);
    reveal(container_process_wf);
    reveal(container_process_allocator_quota_4k_wf);
    reveal(process_perms_wf);
    let owned = k.container_map.spec_index(container_ptr).view().owned_processes.view();
    let caches = k.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches;
    assert forall|j: int| #![trigger caches.view()[j]] 0 <= j < caches.view().len()
        implies caches.view()[j].view().linked_list.view().len() == 0 by {
        assert(caches.view()[j] == caches.spec_index(j as usize).value);
    };
    lemma_cache_len_fold_all_zero(caches.view());
    assert forall|p: RwLockProcessPtr|
        #![trigger process_effective_quota_4k(k.process_map.spec_index(p))]
        owned.contains(p)
        implies process_effective_quota_4k(k.process_map.spec_index(p)) >= 0 by {
        assert(k.process_map.spec_index(p).view().quota_4k >= k.process_map.spec_index(p).view().temp_alloc_cache_4k.view().len());
    };
    lemma_process_effective_quota_4k_fold_ge_member(owned, k.process_map, process_ptr);
    lemma_thread_direct_pending_4k_fold_nonneg(k.container_map.spec_index(container_ptr).view_user_ghost().owned_threads.view(), k.thread_map);
    lemma_thread_indirect_pending_4k_fold_nonneg(k.container_map.spec_index(container_ptr).view_kernel_ghost().owned_indirect_threads.view(), k.thread_map, k.container_map.spec_index(container_ptr).view_rodata().view().depth as int);
}

/// The container conservation law forces `total_free_pages >= 1` whenever the
/// held process has `effective_quota_4k >= 1`: the total equals the sum of
/// every owned process's effective quota plus both thread-pending folds plus
/// the allocator quota, and every summand other than the held process's (which
/// is `>= 1`) is non-negative. Unlike `lemma_scan_fail_pool_nonempty`, this
/// needs no caches-empty hypothesis — it bounds `total_free_pages`, the LHS of
/// `allocate_free_4k_page`'s entry precondition, directly.
pub proof fn lemma_effective_quota_ge_1_imply_total_free_pages_pos(
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
    ensures
        k.allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages.view() > 0,
{
    reveal(container_allocator_wf);
    reveal(container_process_wf);
    reveal(container_process_allocator_quota_4k_wf);
    reveal(process_perms_wf);
    let owned = k.container_map.spec_index(container_ptr).view().owned_processes.view();
    assert forall|p: RwLockProcessPtr|
        #![trigger process_effective_quota_4k(k.process_map.spec_index(p))]
        owned.contains(p)
        implies process_effective_quota_4k(k.process_map.spec_index(p)) >= 0 by {
        assert(k.process_map.spec_index(p).view().quota_4k >= k.process_map.spec_index(p).view().temp_alloc_cache_4k.view().len());
    };
    lemma_process_effective_quota_4k_fold_ge_member(owned, k.process_map, process_ptr);
    lemma_thread_direct_pending_4k_fold_nonneg(k.container_map.spec_index(container_ptr).view_user_ghost().owned_threads.view(), k.thread_map);
    lemma_thread_indirect_pending_4k_fold_nonneg(k.container_map.spec_index(container_ptr).view_kernel_ghost().owned_indirect_threads.view(), k.thread_map, k.container_map.spec_index(container_ptr).view_rodata().view().depth as int);
}

/// A scheduler write-locked before `allocate_free_4k_page` is still write-locked
/// after, with its `scheduler_map` entry + `lock_map` key intact. This is what
/// lets a caller (e.g. `syscall_new_thread`) keep the scheduler it acquired
/// before the allocation and use it in the retype/commit that follows.
///
/// Sound because: `allocate_free_4k_page` never creates/destroys a scheduler and
/// every one of its sub-steps frames `scheduler_map == old` off the held object;
/// the internal `kernel_step_boundary`s preserve held schedulers (a scheduler in
/// `lock_map` rides the interleaving byte-for-byte). Mechanically it's the same
/// per-boundary + per-loop `lock_map`-key bookkeeping the other three alloc exits
/// discharge inline; the Case-3 scan-found exit needs it through
/// `wunlock_all_caches`'s removal loop, which resists the inline chain.
///
//@Xiangdong PENDING PROOF (external_body stub, matching the len-bound lemmas):
// prove `wunlock_all_caches` preserves held non-cache keys (a "non-cache key
// survives" ensure + its loop-maintenance), then this closes inline like the
// pool-stage exit already does.
#[verifier::external_body]
pub proof fn lemma_alloc_preserves_held_scheduler(
    pre: &KernelK,
    post: &KernelK,
    pre_lctx: &LocalContext,
    post_lctx: &LocalContext,
    scheduler_ptr: RwLockSchedulerPtr,
)
    requires
        pre_lctx.lock_map().dom().contains(KernelObjId::Scheduler(scheduler_ptr)),
        pre.scheduler_map.dom() == post.scheduler_map.dom(),
    ensures
        post_lctx.lock_map().dom().contains(KernelObjId::Scheduler(scheduler_ptr)),
        post_lctx.lock_map()[KernelObjId::Scheduler(scheduler_ptr)]
            == pre_lctx.lock_map()[KernelObjId::Scheduler(scheduler_ptr)],
        post.scheduler_map.spec_index(scheduler_ptr) == pre.scheduler_map.spec_index(scheduler_ptr),
{
}

/// A cpu write-locked before `allocate_free_4k_page` is still write-locked after,
/// with its `cpu_array` slot view + `lock_map` key intact. Twin of
/// `lemma_alloc_preserves_held_scheduler` for the running cpu the caller holds.
///
/// Sound because: `allocate_free_4k_page` never touches `cpu_array` and the
/// internal `kernel_step_boundary`s preserve held cpus (a cpu in `lock_map` rides
/// the interleaving byte-for-byte). Same per-boundary + per-loop `lock_map`-key
/// bookkeeping the other alloc exits discharge inline; stubbed to match the
/// scheduler twin.
///
//@Xiangdong PENDING PROOF (external_body stub, matching lemma_alloc_preserves_held_scheduler).
#[verifier::external_body]
pub proof fn lemma_alloc_preserves_held_cpu(
    pre: &KernelK,
    post: &KernelK,
    pre_lctx: &LocalContext,
    post_lctx: &LocalContext,
    cpu_id: CpuId,
)
    requires
        cpu_id_valid(cpu_id),
        pre_lctx.lock_map().dom().contains(KernelObjId::Cpu(cpu_id)),
    ensures
        post_lctx.lock_map().dom().contains(KernelObjId::Cpu(cpu_id)),
        post_lctx.lock_map()[KernelObjId::Cpu(cpu_id)]
            == pre_lctx.lock_map()[KernelObjId::Cpu(cpu_id)],
        post.cpu_array.spec_index(cpu_id).view() == pre.cpu_array.spec_index(cpu_id).view(),
{
}

}
