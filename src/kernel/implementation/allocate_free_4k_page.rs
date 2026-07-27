use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;

verus! {

impl KernelK {

    // ================================================================
    // Case 3: scan all caches + global pool after an internal boundary.
    // ================================================================

    fn alloc_4k_scan_all_caches_and_pool(
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        process_ptr: RwLockProcessPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(process_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(self).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(self).locked_objects_match_lctx(old(lctx)),
            old(self).process_map.spec_index(process_ptr).being_killed() == false,
            process_lock_perm.state() is WriteLock,
            process_lock_perm.thread_id() == old(lctx).thread_id(),
            process_lock_perm.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            old(lctx).lock_map().dom().contains(KernelObjId::Process(process_ptr)),
            lock_id_aligned(old(self), old(lctx)),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
            process_effective_quota_4k(old(self).process_map.spec_index(process_ptr)) >= 1,
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
            final(self).process_map.spec_index(process_ptr).being_killed() == false,
            process_lock_perm.lock_id() == final(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            final(self).process_map.spec_index(process_ptr).view_rodata()
                == old(self).process_map.spec_index(process_ptr).view_rodata(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
            final(self).locked_objects_match_lctx(final(lctx)),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            page_ptr_valid(ret.0),
            page_index_wf(page_ptr2page_index(ret.0)),
            final(self).page_array[page_ptr2page_index(ret.0)].view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(self).page_array[page_ptr2page_index(ret.0)].view().locking_thread()->Write_lock_id,
            final(lctx).lock_map().dom().contains(KernelObjId::Page(page_ptr2page_index(ret.0))),
            final(lctx).lock_map()[KernelObjId::Page(page_ptr2page_index(ret.0))] == final(self).page_array.lock_id_by_index(page_ptr2page_index(ret.0)),
            forall|s: RwLockSchedulerPtr|
                #![trigger old(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))]
                old(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))
                ==> final(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))
                    && final(lctx).lock_map()[KernelObjId::Scheduler(s)]
                        == old(lctx).lock_map()[KernelObjId::Scheduler(s)]
                    && final(self).scheduler_map.spec_index(s)
                        == old(self).scheduler_map.spec_index(s),
            forall|c: CpuId|
                #![trigger old(lctx).lock_map().dom().contains(KernelObjId::Cpu(c))]
                cpu_id_valid(c) && old(lctx).lock_map().dom().contains(KernelObjId::Cpu(c))
                ==> final(lctx).lock_map().dom().contains(KernelObjId::Cpu(c))
                    && final(lctx).lock_map()[KernelObjId::Cpu(c)]
                        == old(lctx).lock_map()[KernelObjId::Cpu(c)]
                    && final(self).cpu_array[c]@
                        == old(self).cpu_array[c]@,
            old(lctx).lock_map().dom().contains(KernelObjId::Process(process_ptr))
            ==> final(lctx).lock_map().dom().contains(KernelObjId::Process(process_ptr))
                && final(lctx).lock_map()[KernelObjId::Process(process_ptr)]
                    == old(lctx).lock_map()[KernelObjId::Process(process_ptr)],
            final(self).container_map.spec_index(
                final(self).process_map.spec_index(process_ptr).view_rodata().view().owning_container
            ).view_rodata()
                == old(self).container_map.spec_index(
                    old(self).process_map.spec_index(process_ptr).view_rodata().view().owning_container
                ).view_rodata(),
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
        let ghost post_first_boundary = *self;
        let ghost post_first_boundary_lctx = *lctx;

        // Post-boundary: the world has run, but the held process is preserved in
        // full. Re-derive the allocator pointer from the process's container (its
        // rodata is lock-free readable), so the scan targets the current map.
        assert(self.process_map.dom().contains(process_ptr)) by {
            reveal(process_locked_match_lctx);
        };
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
        let tracked cache_perms_ref = cache_perms.borrow();
        assert(Self::cache_perms_match_lctx(
            self.allocator_4k_map, recov_alloc, &*lctx, cache_perms_ref)) by {
            reveal(KernelK::cache_perms_match_lctx);
        };
        let (found, slot) = self.scan_caches_and_alloc(
            recov_alloc, process_ptr, recov_container,
            Tracked(&mut *lctx), Tracked(cache_perms_ref), Tracked(process_lock_perm),
        );

        if found {
            // A cache held a free page: it is popped + staged, page slot held.
            // Release the page, every cache, then the pool, and close the step.
            let (_scan_cpu, page_ptr, Tracked(page_lock_perm)) = slot.unwrap();
            let page_index = page_ptr2page_index(page_ptr);
            let ghost pre_unlock = *self;

            // Keep the page slot write-locked so it rides across the boundary as
            // a held object (its state is pinned); release the caches + pool.
            let ghost pool_lid = self.allocator_4k_map.spec_index(recov_alloc).global_pool.lock_id();
            self.wunlock_all_caches(recov_alloc, Tracked(&mut *lctx), Tracked(cache_perms.get()));
            assert(
                lctx.lock_map()[KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, recov_alloc)]
                    == pool_lid
            ) by {
                reveal(allocator_locked_match_lctx);
            };
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
                self.update_lock_id_preserving_locked_match(
                    &mut *lctx,
                    KernelObjId::Page(page_index),
                    self.page_array.lock_id_by_index(page_index),
                );
                assert(lctx.lock_map() =~= post_first_boundary_lctx.lock_map().insert(
                    KernelObjId::Page(page_index),
                    self.page_array.lock_id_by_index(page_index),
                ));
                page_lock_id_aligned_after_refresh(
                    post_first_boundary.page_array, self.page_array,
                    &post_first_boundary_lctx, &*lctx,
                    page_index, self.page_array.lock_id_by_index(page_index),
                );
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                }
                let ghost pre_boundary = *self;
                let ghost pre_boundary_lctx = *lctx;
                assert(pre_boundary_lctx.lock_map().dom().contains(
                    KernelObjId::Page(page_index)));
                self.kernel_step_boundary(&mut *lctx, &mut *steps);
                assert(self.process_map.spec_index(process_ptr)
                    == pre_boundary.process_map.spec_index(process_ptr)) by {
                    reveal(boundary_processes_preserved);
                };
                assert(self.container_map.dom().contains(recov_container)) by {
                    reveal(container_process_wf);
                };
                assert(self.container_map.spec_index(recov_container).view_rodata()
                    == pre_boundary.container_map.spec_index(recov_container).view_rodata()) by {
                    reveal(boundary_containers_preserved);
                };
                held_page_aligned_after_boundary(
                    &pre_boundary, self, &pre_boundary_lctx, &*lctx, page_index);
                assert(page_lock_perm.lock_id()
                    == self.page_array[page_index].view().locking_thread()->Write_lock_id);
                assert(self.page_array[page_index].view().view().state
                    == PageState::Owned4k { process_ptr });
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

        let ghost pre_pool_stage = *self;
        let (page_ptr, Tracked(page_lock_perm)) = self.pop_stage_global_4k_page(
            recov_alloc, process_ptr, recov_container,
            Tracked(&mut *lctx), Tracked(pool_perm.borrow()), Tracked(process_lock_perm),
        );
        let page_index = page_ptr2page_index(page_ptr);
        let ghost pre_unlock = *self;

        // Keep the page slot write-locked so it rides across the boundary as a
        // held object (its state is pinned); release the caches + pool.
        let tracked cache_perms_ref = cache_perms.borrow();
        assert(Self::cache_perms_match_lctx(
            self.allocator_4k_map, recov_alloc, &*lctx, cache_perms_ref)) by {
            reveal(KernelK::cache_perms_match_lctx);
            reveal(allocator_locked_match_lctx);
        };
        let ghost pool_lid = self.allocator_4k_map.spec_index(recov_alloc).global_pool.lock_id();
        self.wunlock_all_caches(recov_alloc, Tracked(&mut *lctx), Tracked(cache_perms.get()));
        assert(
            lctx.lock_map()[KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, recov_alloc)]
                == pool_lid
        ) by {
            reveal(allocator_locked_match_lctx);
        };
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
            self.update_lock_id_preserving_locked_match(
                &mut *lctx,
                KernelObjId::Page(page_index),
                self.page_array.lock_id_by_index(page_index),
            );
            assert(lctx.lock_map() =~= post_first_boundary_lctx.lock_map().insert(
                KernelObjId::Page(page_index),
                self.page_array.lock_id_by_index(page_index),
            ));
            page_lock_id_aligned_after_refresh(
                post_first_boundary.page_array, self.page_array,
                &post_first_boundary_lctx, &*lctx,
                page_index, self.page_array.lock_id_by_index(page_index),
            );
            assert(lock_id_aligned(self, &*lctx)) by {
                reveal(lock_id_aligned);
            }
            let ghost pre_boundary = *self;
            let ghost pre_boundary_lctx = *lctx;
            assert(pre_boundary_lctx.lock_map().dom().contains(
                KernelObjId::Page(page_index)));
            self.kernel_step_boundary(&mut *lctx, &mut *steps);
            assert(self.process_map.spec_index(process_ptr)
                == pre_boundary.process_map.spec_index(process_ptr)) by {
                reveal(boundary_processes_preserved);
            };
            assert(self.container_map.dom().contains(recov_container)) by {
                reveal(container_process_wf);
            };
            assert(self.container_map.spec_index(recov_container).view_rodata()
                == pre_boundary.container_map.spec_index(recov_container).view_rodata()) by {
                reveal(boundary_containers_preserved);
            };
            held_page_aligned_after_boundary(
                &pre_boundary, self, &pre_boundary_lctx, &*lctx, page_index);
            assert(page_lock_perm.lock_id()
                == self.page_array[page_index].view().locking_thread()->Write_lock_id);
            assert(self.page_array[page_index].view().view().state
                == PageState::Owned4k { process_ptr });
        }
        (page_ptr, Tracked(page_lock_perm))
    }

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
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(process_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(self).inv(),
            cpu_id_valid(cpu_id),
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
            // old(lctx).lock_id_acyclic(old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id].lock_id()),
            old(lctx).lock_map().dom().contains(KernelObjId::Process(process_ptr)),
            old(lctx).lock_map()[KernelObjId::Process(process_ptr)] == old(self).process_map.lock_id_by_key(process_ptr),
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),

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
            // ---- held process: not killed, perm still matches (process held throughout) ----
            final(self).process_map.spec_index(process_ptr).being_killed() == false,
            process_lock_perm.lock_id() == final(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            final(self).process_map.spec_index(process_ptr).view_rodata() == old(self).process_map.spec_index(process_ptr).view_rodata(),
            final(self).container_map.spec_index(final(self).process_map.spec_index(process_ptr).view_rodata().view().owning_container).view_rodata()
                == old(self).container_map.spec_index(old(self).process_map.spec_index(process_ptr).view_rodata().view().owning_container).view_rodata(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
            final(self).locked_objects_match_lctx(final(lctx)),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            page_ptr_valid(ret.0),
            // ---- page slot left write-locked, perm handed back (rides across the boundary as a held object) ----
            page_index_wf(page_ptr2page_index(ret.0)),
            final(self).page_array[page_ptr2page_index(ret.0)].view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(self).page_array[page_ptr2page_index(ret.0)].view().locking_thread()->Write_lock_id,
            final(lctx).lock_map().dom().contains(KernelObjId::Page(page_ptr2page_index(ret.0))),
            final(lctx).lock_map()[KernelObjId::Page(page_ptr2page_index(ret.0))] == final(self).page_array.lock_id_by_index(page_ptr2page_index(ret.0)),
            // ---- a held scheduler survives: its dom + lock state carry across ----
            forall|s: RwLockSchedulerPtr|
                #![trigger old(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))]
                #![trigger final(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))]
                #![trigger old(self).scheduler_map.spec_index(s).locked_by(old(lctx))]
                #![trigger final(self).scheduler_map.spec_index(s).locked_by(final(lctx))]
                old(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))
                ==> final(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))
                    && final(lctx).lock_map()[KernelObjId::Scheduler(s)] == old(lctx).lock_map()[KernelObjId::Scheduler(s)]
                    && final(self).scheduler_map.spec_index(s) == old(self).scheduler_map.spec_index(s),
            // ---- a held cpu survives ----
            forall|c: CpuId|
                #![trigger old(lctx).lock_map().dom().contains(KernelObjId::Cpu(c))]
                #![trigger final(lctx).lock_map().dom().contains(KernelObjId::Cpu(c))]
                #![trigger old(self).cpu_array[c]@.locked_by(old(lctx))]
                #![trigger final(self).cpu_array[c]@.locked_by(final(lctx))]
                cpu_id_valid(c) && old(lctx).lock_map().dom().contains(KernelObjId::Cpu(c))
                ==> final(lctx).lock_map().dom().contains(KernelObjId::Cpu(c))
                    && final(lctx).lock_map()[KernelObjId::Cpu(c)] == old(lctx).lock_map()[KernelObjId::Cpu(c)]
                    && final(self).cpu_array[c]@ == old(self).cpu_array[c]@,
            // ---- the held process survives ----
            old(lctx).lock_map().dom().contains(KernelObjId::Process(process_ptr))
            ==> final(lctx).lock_map().dom().contains(KernelObjId::Process(process_ptr))
                && final(lctx).lock_map()[KernelObjId::Process(process_ptr)] == old(lctx).lock_map()[KernelObjId::Process(process_ptr)],
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
        proof {
            reveal(allocator_perms_wf);
            reveal(container_process_wf);
            reveal(container_allocator_wf);
            reveal(process_locked_match_lctx);
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
        proof {
            assert(lock_id_aligned(self, &*lctx)) by {
                reveal(lock_id_aligned);
                reveal(page_lock_id_aligned);
            }
        }

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
                self.update_lock_id_preserving_locked_match(
                    &mut *lctx,
                    KernelObjId::Page(page_index),
                    self.page_array.lock_id_by_index(page_index),
                );
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                }
                let ghost pre_boundary = *self;
                let ghost pre_boundary_lctx = *lctx;
                assert(pre_boundary_lctx.lock_map().dom().contains(
                    KernelObjId::Page(page_index)));
                self.kernel_step_boundary(&mut *lctx, &mut *steps);
                held_page_aligned_after_boundary(
                    &pre_boundary, self, &pre_boundary_lctx, &*lctx, page_index);
                assert(page_lock_perm.lock_id()
                    == self.page_array[page_index].view().locking_thread()->Write_lock_id);
                assert(self.page_array[page_index].view().view().state
                    == PageState::Owned4k { process_ptr });
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
        proof {
            assert(lock_id_aligned(self, &*lctx)) by {
                reveal(lock_id_aligned);
                reveal(page_lock_id_aligned);
            }
        }

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
                        assert(lctx.lock_map()[k] == self.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.lock_id());
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
                self.update_lock_id_preserving_locked_match(
                    &mut *lctx,
                    KernelObjId::Page(page_index),
                    self.page_array.lock_id_by_index(page_index),
                );
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                }
                let ghost pre_boundary = *self;
                let ghost pre_boundary_lctx = *lctx;
                assert(pre_boundary_lctx.lock_map().dom().contains(
                    KernelObjId::Page(page_index)));
                self.kernel_step_boundary(&mut *lctx, &mut *steps);
                held_page_aligned_after_boundary(
                    &pre_boundary, self, &pre_boundary_lctx, &*lctx, page_index);
                assert(page_lock_perm.lock_id()
                    == self.page_array[page_index].view().locking_thread()->Write_lock_id);
                assert(self.page_array[page_index].view().view().state
                    == PageState::Owned4k { process_ptr });
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
            kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
            assert(lctx.lock_map().dom().contains(KernelObjId::Process(process_ptr))) by {
                reveal(process_locked_match_lctx);
            };
            // No payload changed on this path: the cache and pool were only
            // acquired and released.  Their ids were removed from lock_map,
            // and every remaining entry therefore retains the alignment from
            // this routine's precondition.
            assert(lock_id_aligned(self, &*lctx)) by {
                reveal(lock_id_aligned);
                reveal(page_lock_id_aligned);
            }
            let ghost pre_boundary = *self;
            let ghost pre_boundary_lctx = *lctx;
            self.kernel_step_boundary(&mut *lctx, &mut *steps);
            assert forall|i: PageIndex|
                #![trigger pre_boundary_lctx.lock_map().dom().contains(KernelObjId::Page(i))]
                pre_boundary_lctx.lock_map().dom().contains(KernelObjId::Page(i))
                ==> page_index_wf(i) && self.page_array[i]@ == pre_boundary.page_array[i]@ by {
                if pre_boundary_lctx.lock_map().dom().contains(KernelObjId::Page(i)) {
                    assert(page_index_wf(i)) by {
                        reveal(lock_id_aligned);
                        reveal(page_lock_id_aligned);
                    };
                    assert(self.page_array[i]@ == pre_boundary.page_array[i]@) by {
                        reveal(boundary_pages_preserved);
                    };
                }
            };
            page_lock_id_aligned_after_boundary(
                pre_boundary.page_array,
                self.page_array,
                &pre_boundary_lctx,
                &*lctx,
            );
            assert(lock_id_aligned(self, &*lctx)) by {
                reveal(lock_id_aligned);
            }
            assert forall|s: RwLockSchedulerPtr|
                #![trigger old(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))]
                old(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))
                implies self.scheduler_map.spec_index(s) == old(self).scheduler_map.spec_index(s) by {
                reveal(boundary_schedulers_preserved);
            };
            assert forall|s: RwLockSchedulerPtr|
                #![trigger old(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))]
                old(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))
                ==> lctx.lock_map().dom().contains(KernelObjId::Scheduler(s))
                    && lctx.lock_map()[KernelObjId::Scheduler(s)]
                        == old(lctx).lock_map()[KernelObjId::Scheduler(s)] by {
            };
        }
        assert forall|c: CpuId| #![auto]
            cpu_id_valid(c) && old(lctx).lock_map().dom().contains(KernelObjId::Cpu(c))
            implies lctx.lock_map().dom().contains(KernelObjId::Cpu(c))
                && lctx.lock_map()[KernelObjId::Cpu(c)] == old(lctx).lock_map()[KernelObjId::Cpu(c)]
                && self.cpu_array[c]@ == old(self).cpu_array[c]@ by {
                    reveal(boundary_cpus_preserved);
        };
        let result = self.alloc_4k_scan_all_caches_and_pool(
            alloc_ptr_4k, process_ptr,
            Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(process_lock_perm),
        );
        proof {
            assert forall|s: RwLockSchedulerPtr|
                #![trigger old(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))]
                old(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))
                implies lctx.lock_map().dom().contains(KernelObjId::Scheduler(s))
                    && lctx.lock_map()[KernelObjId::Scheduler(s)] == old(lctx).lock_map()[KernelObjId::Scheduler(s)]
                    && self.scheduler_map.spec_index(s) == old(self).scheduler_map.spec_index(s) by {}
        }
        result
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
            lock_id_aligned(old(self), old(lctx)),
            forall|k: KernelObjId|
                #![trigger old(lctx).lock_map().dom().contains(k)]
                old(lctx).lock_map().dom().contains(k)
                ==> old(lctx).lock_map()[k].major <= PROCESS_LOCK_MAJOR,
        ensures
            final(self).inv(),
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
            lock_id_aligned(final(self), final(lctx)),
            // ---- every cache + the pool is write-locked by us, perm recorded ----
            Self::cache_perms_match_lctx(
                final(self).allocator_4k_map, alloc_ptr_4k,
                final(lctx), &ret.0.view()),
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.locking_thread()->Write_lock_id,
            final(lctx).lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k)),
            final(lctx).lock_map()[KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k)] == final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.lock_id(),
            // ---- pre-existing lock_map entries preserved (only caches + pool + page added) ----
            forall|k: KernelObjId|
                #![trigger old(lctx).lock_map().dom().contains(k)]
                #![trigger final(lctx).lock_map().dom().contains(k)]
                old(lctx).lock_map().dom().contains(k)
                ==> final(lctx).lock_map().dom().contains(k) && final(lctx).lock_map()[k] == old(lctx).lock_map()[k],
            forall|k: KernelObjId|
                #![trigger final(lctx).lock_map().dom().contains(k)]
                final(lctx).lock_map().dom().contains(k)
                ==> old(lctx).lock_map().dom().contains(k)
                    || k == KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k)
                    || (k is AllocatorCache
                        && k->AllocatorCache_0 == PageSize::SZ4k
                        && k->AllocatorCache_1 == alloc_ptr_4k
                        && cpu_id_valid(k->AllocatorCache_2)),
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
                lock_id_aligned(self, &*lctx),
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
                        &&& cache_perms.spec_index(c).state() is WriteLock
                        &&& cache_perms.spec_index(c).thread_id() == lctx.thread_id()
                        &&& cache_perms.spec_index(c).lock_id() == self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().locking_thread()->Write_lock_id
                        &&& lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c))
                        &&& lctx.lock_map()[KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c)] == self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].lock_id()
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
                forall|k: KernelObjId|
                    #![trigger lctx.lock_map().dom().contains(k)]
                    lctx.lock_map().dom().contains(k)
                    ==> old(lctx).lock_map().dom().contains(k)
                        || (k is AllocatorCache
                            && k->AllocatorCache_0 == PageSize::SZ4k
                            && k->AllocatorCache_1 == alloc_ptr_4k
                            && cpu_id_valid(k->AllocatorCache_2)
                            && k->AllocatorCache_2 < cpu),
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
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                }
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
            assert(lock_id_aligned(self, &*lctx)) by {
                reveal(lock_id_aligned);
                reveal(page_lock_id_aligned);
            }
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
            assert(Self::cache_perms_match_lctx(
                self.allocator_4k_map, alloc_ptr_4k, &*lctx, &cache_perms)) by {
                reveal(KernelK::cache_perms_match_lctx);
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
            Self::cache_perms_match_lctx(
                old(self).allocator_4k_map, alloc_ptr_4k, old(lctx), &cache_perms),
        ensures
            final(self).inv(),
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
                #![trigger old(lctx).lock_map().dom().contains(k)]
                #![trigger final(lctx).lock_map().dom().contains(k)]
                old(lctx).lock_map().dom().contains(k)
                    && !(k is AllocatorCache && k->AllocatorCache_1 == alloc_ptr_4k)
                ==> final(lctx).lock_map().dom().contains(k)
                    && final(lctx).lock_map()[k] == old(lctx).lock_map()[k],
            forall|k: KernelObjId|
                #![trigger final(lctx).lock_map().dom().contains(k)]
                final(lctx).lock_map().dom().contains(k)
                ==> old(lctx).lock_map().dom().contains(k) && final(lctx).lock_map()[k] == old(lctx).lock_map()[k],
    {
        let tracked mut perms = cache_perms;
        proof {
            reveal(allocator_locked_match_lctx);
            reveal(allocator_perms_wf);
            assert forall|c: CpuId|
                #![trigger perms.spec_index(c)]
                #![trigger perms.dom().contains(c)]
                cpu_id_valid(c)
                ==> {
                    &&& perms.dom().contains(c)
                    &&& perms.spec_index(c).state() is WriteLock
                    &&& perms.spec_index(c).thread_id() == lctx.thread_id()
                    &&& perms.spec_index(c).lock_id()
                        == self.allocator_4k_map.spec_index(alloc_ptr_4k)
                            .cpu_caches[c].view().locking_thread()->Write_lock_id
                    &&& lctx.lock_map().dom().contains(
                        KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c))
                    &&& lctx.lock_map()[KernelObjId::AllocatorCache(
                        PageSize::SZ4k, alloc_ptr_4k, c)]
                        == self.allocator_4k_map.spec_index(alloc_ptr_4k)
                            .cpu_caches[c].lock_id()
                } by {
                reveal(KernelK::cache_perms_match_lctx);
            };
        }
        let mut cpu: CpuId = 0;
        while cpu < NUM_CPUS
            invariant
                self.inv(),
                self.locked_objects_match_lctx(&*lctx),
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
                        &&& perms.spec_index(c).state() is WriteLock
                        &&& perms.spec_index(c).thread_id() == lctx.thread_id()
                        &&& perms.spec_index(c).lock_id() == self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].view().locking_thread()->Write_lock_id
                        &&& lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c))
                        &&& lctx.lock_map()[KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c)] == self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[c].lock_id()
                    },
                forall|c: CpuId|
                    #![trigger lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c))]
                    cpu_id_valid(c) && c < cpu
                    ==> lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c)) == false,
                forall|k: KernelObjId|
                    #![trigger lctx.lock_map().dom().contains(k)]
                    lctx.lock_map().dom().contains(k)
                    ==> old(lctx).lock_map().dom().contains(k) && lctx.lock_map()[k] == old(lctx).lock_map()[k],
                forall|k: KernelObjId|
                    #![trigger old(lctx).lock_map().dom().contains(k)]
                    old(lctx).lock_map().dom().contains(k)
                        && !(k is AllocatorCache && k->AllocatorCache_1 == alloc_ptr_4k && k->AllocatorCache_2 < cpu)
                    ==> lctx.lock_map().dom().contains(k)
                        && lctx.lock_map()[k] == old(lctx).lock_map()[k],
            decreases NUM_CPUS - cpu,
        {
            proof {
                assert(perms.spec_index(cpu).state() is WriteLock);
                assert(self.allocator_4k_map.dom().contains(alloc_ptr_4k)) by {
                    reveal(allocator_locked_match_lctx);
                };
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
                &&& lctx.lock_map().dom().contains(
                    KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c))
                &&& lctx.lock_map()[KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, c)]
                    == alloc_map.spec_index(alloc_ptr_4k).cpu_caches[c].lock_id()
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
            old(self).container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(self).process_map.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            old(self).process_map.spec_index(process_ptr).being_killed() == false,
            process_effective_quota_4k(old(self).process_map.spec_index(process_ptr)) >= 1,
            process_lock_perm.state() is WriteLock,
            process_lock_perm.thread_id() == old(lctx).thread_id(),
            process_lock_perm.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            old(lctx).lock_map().dom().contains(KernelObjId::Process(process_ptr)),
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            Self::cache_perms_match_lctx(
                old(self).allocator_4k_map, alloc_ptr_4k, old(lctx), cache_perms),
            forall|k: KernelObjId|
                #![trigger old(lctx).lock_map().dom().contains(k)]
                old(lctx).lock_map().dom().contains(k)
                ==> old(lctx).lock_map()[k].major <= ALLOCATOR_GLOBAL_POLL_MAJOR,
        ensures
            final(self).inv(),
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
                &&& lock_id_aligned(final(self), final(lctx))
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
                &&& final(self).page_array.unchanged_except(
                    &old(self).page_array, page_ptr2page_index(ret.1.unwrap().1))
                &&& final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool
                    == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool
                &&& final(self).page_array[page_ptr2page_index(ret.1.unwrap().1)].view().being_killed() == false
                &&& ret.1.unwrap().2.view().state() is WriteLock
                &&& ret.1.unwrap().2.view().thread_id() == final(lctx).thread_id()
                &&& ret.1.unwrap().2.view().lock_id() == final(self).page_array[page_ptr2page_index(ret.1.unwrap().1)].view().locking_thread()->Write_lock_id
                &&& final(lctx).lock_map() == old(lctx).lock_map().insert(
                    KernelObjId::Page(page_ptr2page_index(ret.1.unwrap().1)),
                    old(self).page_array.lock_id_by_index(page_ptr2page_index(ret.1.unwrap().1)))
                &&& Self::cache_perms_match_lctx(
                    final(self).allocator_4k_map, alloc_ptr_4k, final(lctx), cache_perms)
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
                &&& final(self).cpu_array == old(self).cpu_array
            },
    {
        proof {
            reveal(container_process_wf);
            reveal(container_allocator_wf);
            reveal(process_locked_match_lctx);
            reveal(allocator_locked_match_lctx);
        }
        let mut cpu: CpuId = 0;
        while cpu < NUM_CPUS
            invariant
                *self == *old(self),
                self.inv(),
                self.locked_objects_match_lctx(&*lctx),
                lock_id_aligned(self, &*lctx),
                lctx.lock_map() == old(lctx).lock_map(),
                lctx.thread_id() == old(lctx).thread_id(),
                lctx.kernel_view_locking_state() is Acquire,
                lctx.user_view_locking_state() == old(lctx).user_view_locking_state(),
                0 <= cpu <= NUM_CPUS,
                self.container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
                self.process_map.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
                self.process_map.spec_index(process_ptr).being_killed() == false,
                process_effective_quota_4k(self.process_map.spec_index(process_ptr)) >= 1,
                process_lock_perm.state() is WriteLock,
                process_lock_perm.thread_id() == lctx.thread_id(),
                process_lock_perm.lock_id() == self.process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                lctx.lock_map().dom().contains(KernelObjId::Process(process_ptr)),
                Self::cache_perms_match_lctx(
                    self.allocator_4k_map, alloc_ptr_4k, &*lctx, cache_perms),
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
                reveal(allocator_locked_match_lctx);
                reveal(KernelK::cache_perms_match_lctx);
                assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu].view().write_lock_perm_match(&cache_perms.spec_index(cpu)));
                assert(self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches[cpu].view().being_killed() == false);
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
                let tracked selected_cache_perm = cache_perms.tracked_borrow(cpu);
                let (page_ptr, Tracked(page_lock_perm)) = self.pop_stage_4k_page(
                    alloc_ptr_4k, cpu, process_ptr, container_ptr,
                    Tracked(&mut *lctx), Tracked(selected_cache_perm), Tracked(process_lock_perm),
                );
                assert(Self::cache_perms_match_lctx(
                    self.allocator_4k_map, alloc_ptr_4k, &*lctx, cache_perms)) by {
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
            old(lctx).lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cpu_id)),
            old(lctx).lock_map()[KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cpu_id)] == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id].lock_id(),
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@@.view().len() > 0,
            old(self).process_map.spec_index(process_ptr).being_killed() == false,
            process_effective_quota_4k(old(self).process_map.spec_index(process_ptr)) >= 1,
            process_lock_perm.state() is WriteLock,
            process_lock_perm.thread_id() == old(lctx).thread_id(),
            process_lock_perm.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            old(lctx).lock_map().dom().contains(KernelObjId::Process(process_ptr)),
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            forall|k: KernelObjId|
                #![trigger old(lctx).lock_map().dom().contains(k)]
                old(lctx).lock_map().dom().contains(k)
                ==> old(lctx).lock_map()[k].major <= ALLOCATOR_GLOBAL_POLL_MAJOR,
        ensures
            final(self).inv(),
            page_ptr_valid(ret.0),
            final(self).page_array.unchanged_except(
                &old(self).page_array, page_ptr2page_index(ret.0)),
            // ---- user view unchanged: staging is kernel-internal ----
            kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
            // ---- cache + process lock state preserved, phase still Acquire ----
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
            cache_lock_perm.lock_id() == final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id].view().locking_thread()->Write_lock_id,
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id].lock_id()
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id].lock_id(),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.unchanged_except(
                &old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches, cpu_id),
            final(self).process_map.spec_index(process_ptr).being_killed() == false,
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
            final(lctx).lock_map() == old(lctx).lock_map().insert(KernelObjId::Page(page_ptr2page_index(ret.0)), old(self).page_array.lock_id_by_index(page_ptr2page_index(ret.0))),
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
            final(self).process_map.spec_index(process_ptr).view().owned_threads
                == old(self).process_map.spec_index(process_ptr).view().owned_threads,
            // ---- container_map + scheduler_map untouched (staging never writes them) ----
            final(self).container_map == old(self).container_map,
            final(self).scheduler_map == old(self).scheduler_map,
            final(self).cpu_array == old(self).cpu_array,
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
    {
        proof {
            reveal(allocator_perms_wf);
            page_ptr_lemma1();
            reveal(process_perms_wf);
            reveal(page_array_wf);
            reveal(page_locked_match_lctx);
            reveal(allocator_locked_match_lctx);
            reveal(process_locked_match_lctx);
            reveal(container_process_wf);
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
        assert(self.page_array.spec_index(page_index).view().view().state is Free4k) by {
            reveal(container_allocator_free_4k_page_wf);
        };
        assert(lctx.lock_map().dom().contains(KernelObjId::Page(page_index)) == false) by {
            if lctx.lock_map().dom().contains(KernelObjId::Page(page_index)) {
                assert(lctx.lock_map()[KernelObjId::Page(page_index)]
                    == self.page_array.lock_id_by_index(page_index)) by {
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                };
                assert(self.page_array.lock_id_by_index(page_index).major == FREE_PAGE_LOCK_MAJOR) by {
                    reveal(Page::is_free);
                };
                assert(lctx.lock_map()[KernelObjId::Page(page_index)].major
                    <= ALLOCATOR_GLOBAL_POLL_MAJOR);
                assert(false);
            }
        };
        assert(self.page_array[page_index]@.locked_by(&*lctx) == false) by {
            reveal(page_locked_match_lctx);
        };

        // Lock the page slot (still Free4k ⟹ fresh, id tops every held id).
        proof {
            assert(lctx.lock_id_acyclic(self.page_array.lock_id_by_index(page_index))) by {
                assert forall|k: KernelObjId|
                    #![trigger lctx.lock_map().dom().contains(k)]
                    lctx.lock_map().dom().contains(k)
                    ==> self.page_array.lock_id_by_index(page_index).spec_gt(lctx.lock_map()[k]) by {
                    reveal(LockId::spec_gt);
                    reveal(LockOwnerId::spec_eq);
                    reveal(LockOwnerId::spec_gt);
                };
            }
        }
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
            old(self).container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(self).process_map.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            global_pool_lock_perm.state() is WriteLock,
            global_pool_lock_perm.thread_id() == old(lctx).thread_id(),
            global_pool_lock_perm.lock_id() == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.locking_thread()->Write_lock_id,
            old(lctx).lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k)),
            old(lctx).lock_map()[KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k)] == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.lock_id(),
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().view().len() > 0,
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().len() > 0,
            old(self).process_map.spec_index(process_ptr).being_killed() == false,
            process_effective_quota_4k(old(self).process_map.spec_index(process_ptr)) >= 1,
            process_lock_perm.state() is WriteLock,
            process_lock_perm.thread_id() == old(lctx).thread_id(),
            process_lock_perm.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            old(lctx).lock_map().dom().contains(KernelObjId::Process(process_ptr)),
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            forall|k: KernelObjId|
                #![trigger old(lctx).lock_map().dom().contains(k)]
                old(lctx).lock_map().dom().contains(k)
                ==> old(lctx).lock_map()[k].major <= ALLOCATOR_GLOBAL_POLL_MAJOR,
        ensures
            final(self).inv(),
            page_ptr_valid(ret.0),
            final(self).page_array.unchanged_except(
                &old(self).page_array, page_ptr2page_index(ret.0)),
            // ---- user view unchanged: staging is kernel-internal ----
            kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
            // ---- global_pool + process lock state preserved, phase still Acquire ----
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
            global_pool_lock_perm.lock_id() == final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.locking_thread()->Write_lock_id,
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.lock_id()
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.lock_id(),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches,
            final(self).process_map.spec_index(process_ptr).being_killed() == false,
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
            final(lctx).lock_map() == old(lctx).lock_map().insert(KernelObjId::Page(page_ptr2page_index(ret.0)), old(self).page_array.lock_id_by_index(page_ptr2page_index(ret.0))),
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
            final(self).process_map.spec_index(process_ptr).view().owned_threads
                == old(self).process_map.spec_index(process_ptr).view().owned_threads,
            // ---- container_map + scheduler_map untouched (staging never writes them) ----
            final(self).container_map == old(self).container_map,
            final(self).scheduler_map == old(self).scheduler_map,
            final(self).cpu_array == old(self).cpu_array,
    {
        proof {
            reveal(allocator_perms_wf);
            page_ptr_lemma1();
            reveal(process_perms_wf);
            reveal(page_array_wf);
            reveal(page_locked_match_lctx);
            reveal(allocator_locked_match_lctx);
            reveal(process_locked_match_lctx);
            reveal(container_process_wf);
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
        assert(self.page_array.spec_index(page_index).view().view().state is Free4k) by {
            reveal(container_allocator_free_4k_page_wf);
        };
        assert(lctx.lock_map().dom().contains(KernelObjId::Page(page_index)) == false) by {
            if lctx.lock_map().dom().contains(KernelObjId::Page(page_index)) {
                assert(lctx.lock_map()[KernelObjId::Page(page_index)]
                    == self.page_array.lock_id_by_index(page_index)) by {
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                };
                assert(self.page_array.lock_id_by_index(page_index).major == FREE_PAGE_LOCK_MAJOR) by {
                    reveal(Page::is_free);
                };
                assert(lctx.lock_map()[KernelObjId::Page(page_index)].major
                    <= ALLOCATOR_GLOBAL_POLL_MAJOR);
                assert(false);
            }
        };
        assert(self.page_array[page_index]@.locked_by(&*lctx) == false) by {
            reveal(page_locked_match_lctx);
        };

        // Lock the page slot (still Free4k ⟹ fresh, id tops every held id).
        proof {
            assert(lctx.lock_id_acyclic(self.page_array.lock_id_by_index(page_index))) by {
                assert forall|k: KernelObjId|
                    #![trigger lctx.lock_map().dom().contains(k)]
                    lctx.lock_map().dom().contains(k)
                    ==> self.page_array.lock_id_by_index(page_index).spec_gt(lctx.lock_map()[k]) by {
                    reveal(LockId::spec_gt);
                    reveal(LockOwnerId::spec_eq);
                    reveal(LockOwnerId::spec_gt);
                };
            }
        }
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

}
