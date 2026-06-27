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
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(process_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: PagePtr)
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
            // Process write-lock perm, needed to mutate the process payload
            // (insert the freshly-allocated page into `temp_alloc_cache_4k`).
            process_lock_perm.state() is WriteLock,
            process_lock_perm.thread_id() == old(lctx).thread_id(),
            process_lock_perm.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
            process_effective_quota_4k(old(self).process_map.spec_index(process_ptr)) >= 1,
            // Deadlock-freedom (replaces the old `lock_map == {Process}` pin):
            // every lock currently held is ordered strictly below the cpu
            // free-page cache we are about to lock — i.e. the cache's lock id is
            // greater than every held id under the (wildcard-aware) `spec_gt`.
            // The caller may hold ANY set of locks, as long as all sit below the
            // cache. Because the cache id has `container=process=NotApp` and
            // `major == ALLOCATOR_CACHE_MAJOR (< FREE_PAGE_LOCK_MAJOR)`, this one
            // clause discharges BOTH the cache wlock's acyclicity AND (since
            // every held major is then `< FREE_PAGE_LOCK_MAJOR`, and a Free page
            // carries the MAX owner-id `None`) the page-slot wlock's acyclicity.
            old(lctx).lock_id_acyclic(LockId{
                container: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id].container_depth(),
                process: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id].process_depth(),
                major: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@@.current_lock_major(),
                minor: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id].lock_minor(),
            }),
            // The process this thread holds is recorded in the lock map (still
            // needed: the syscall returns with the process write-locked, and the
            // step boundary / post-conditions reason about that held entry).
            old(lctx).lock_map().dom().contains(KernelObjId::Process(process_ptr)),
            old(lctx).lock_map()[KernelObjId::Process(process_ptr)] == (LockId{
                container: old(self).process_map@[process_ptr].container_depth(),
                process: old(self).process_map@[process_ptr].process_depth(),
                major: old(self).process_map@[process_ptr].value()@.current_lock_major(),
                minor: process_ptr,
            }),
            old(self).locked_objects_match_lctx(old(lctx)),
        ensures
            // ---- Minimal "clean fast path" contract (functional postconditions
            // intentionally dropped — see the AskUserQuestion choice). We keep:
            //   * the kernel invariant,
            //   * the caller discipline needed to KEEP USING the held process
            //     and to take a later step (process still write-locked, phase
            //     back to Acquire, lock-map ⇄ kernel agreement, snapshot
            //     refreshed), and
            //   * the fact that this whole syscall does NOT change the user
            //     view (the page-allocation bookkeeping — Free4k→Owned4k, temp
            //     staging, the allocator ghost total — is all kernel-internal;
            //     `KernelU`/`ProcessU` project none of it).
            final(self).inv(),
            final(self).process_map.dom().contains(process_ptr),
            final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx)),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            final(self).locked_objects_match_lctx(final(lctx)),
            page_ptr_valid(ret),
    {
        proof {
            reveal(allocator_perms_wf);
        }

        // ---- Case 1: Fast path — pop from running cpu's cache ----
        //
        // Lock the running cpu's cache. Both obligations come from the
        // precondition (no manual per-held-id loop, no `lock_map=={Process}`
        // pin):
        //   * acyclicity: the precondition IS `lock_id_acyclic(<cache id>)`.
        //   * freshness (cache ∉ lock_map): if it were held, the bidirectional
        //     agreement (`allocator_locked_match_lctx`, forward, with the pinned
        //     recorded id) would record its id as `<cache id>` itself, and
        //     acyclicity would then demand `<cache id>.spec_gt(<cache id>)` —
        //     false. Hence not held ⟹ fresh.
        let ghost cache_lock_id = LockId{
            container: self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id].container_depth(),
            process: self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id].process_depth(),
            major: self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@@.current_lock_major(),
            minor: self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id].lock_minor(),
        };
        proof {
            reveal(allocator_locked_match_lctx);
            // The cache's structural lock id is exactly the pinned shape: NotApp
            // owners, major ALLOCATOR_CACHE_MAJOR, minor cpu_id.
            assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id].container_depth() == LockOwnerId::NotApp);
            assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id].process_depth() == LockOwnerId::NotApp);
            assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@@.current_lock_major() == ALLOCATOR_CACHE_MAJOR);
            assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id].lock_minor() == cpu_id);
            // Freshness by contradiction with acyclicity.
            if lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cpu_id)) {
                // forward agreement pins the recorded id == cache_lock_id.
                assert(lctx.lock_map()[KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cpu_id)] == cache_lock_id);
                // acyclicity ⟹ cache_lock_id.spec_gt(cache_lock_id), impossible.
                assert(cache_lock_id.spec_gt(cache_lock_id));
                assert(cache_lock_id.container.spec_eq(cache_lock_id.container));
                assert(cache_lock_id.process.spec_eq(cache_lock_id.process));
                assert(false);
            }
            assert(lctx.obj_id_fresh(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cpu_id)));
            // not-already-held ⟹ wlock_requires' `locked_by == false`.
            assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@.locked_by(&*lctx) == false);
        }

        let Tracked(cache_lock_perm) = self.wlock_allocator_cache(
            alloc_ptr_4k, cpu_id, Tracked(&mut *lctx),
        );

        // Read the cache length via a SHARED borrow so `self`'s `wf()` (which
        // now folds over live cache lengths) is preserved for the slow path.
        let cache_ref = self.allocator_4k_map.borrow_cache(
            alloc_ptr_4k, cpu_id, Tracked(&cache_lock_perm),
        );
        let cache_len = cache_ref.linked_list.len();
        // borrow_cache ensures *cache_ref == cache[cpu_id]@@. len() returns the
        // list's `length`; lemma_len_view (needs the list's wf(), from the
        // allocator's cpu_caches_wf) gives view().len() == length, so cache_len
        // equals the spec view length the finish helper requires.
        proof {
            reveal(allocator_perms_wf);
            assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches_wf());
            assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@@.wf());
            cache_ref.linked_list.lemma_len_view();
            assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cpu_id]@@.view().len()
                == cache_len);
        }

        if cache_len > 0 {
            // Fast path: the cache is write-locked and non-empty. The finish
            // helper pops a page, sets it Owned4k, stages it in the process,
            // decrements the ghost total, unlocks the page slot and the cache,
            // and re-establishes inv().
            //
            // The cache wlock is kernel-internal — `wlock_allocator_cache`
            // preserved process_map / cpu_array / pagetable_map verbatim, and
            // `kernel_k_to_kernel_u` projects ONLY those. So the user view (hence
            // the snapshot) is unchanged since entry.
            proof {
                // cpu_array structural inv() (needed by the lemma): both states
                // satisfy KernelK::inv() ⟹ cpu_array_wf ⟹ cpu_array.inv().
                reveal(cpu_array_wf);
                assert(old(self).cpu_array.inv());
                assert(self.cpu_array.inv());
                // lemma_release_with_process_preserves_user_view(*old(self), *self, cpu_id);
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self)));
            }
            // Every held lock id sits at or below the cache major — needed by the
            // finish helper to derive page freshness. The cache acquire only ADDED
            // the cache id (major ALLOCATOR_CACHE_MAJOR); every pre-existing held
            // id was ≤ that by the entry precondition (`lock_id_acyclic(cache_id)`
            // ⟹ cache.spec_gt(held), and with the cache's NotApp owners that means
            // held major < cache major).
            proof {
                assert forall|k: KernelObjId|
                    #![trigger lctx.lock_map().dom().contains(k)]
                    lctx.lock_map().dom().contains(k)
                    implies lctx.lock_map()[k].major <= ALLOCATOR_CACHE_MAJOR by {
                    if k == KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cpu_id) {
                        // the freshly-added cache id has exactly this major.
                        assert(lctx.lock_map()[k] == cache_lock_id);
                        assert(cache_lock_id.major == ALLOCATOR_CACHE_MAJOR);
                    } else {
                        // pre-existing held id: in old(lctx).lock_map (lock_ensures
                        // only inserted the cache key), so the entry acyclicity
                        // `cache_lock_id.spec_gt(old held)` applies.
                        assert(old(lctx).lock_map().dom().contains(k));
                        assert(old(lctx).lock_map()[k] == lctx.lock_map()[k]);
                        assert(cache_lock_id.spec_gt(old(lctx).lock_map()[k]));
                        let held = old(lctx).lock_map()[k];
                        // cache owners are NotApp ⟹ spec_eq with held owners ⟹
                        // spec_gt decided by major ⟹ cache.major > held.major.
                        assert(cache_lock_id.container.spec_eq(held.container));
                        assert(cache_lock_id.process.spec_eq(held.process));
                        assert(cache_lock_id.major != held.major ==> cache_lock_id.major > held.major);
                        assert(held.major <= ALLOCATOR_CACHE_MAJOR);
                    }
                };
            }
            // let page_ptr = self.finish_allocate_4k_page(
            //     alloc_ptr_4k, cpu_id, process_ptr, container_ptr,
            //     Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(cache_lock_perm),
            //     Tracked(process_lock_perm),
            // );
            return page_ptr;
        }

        // // ---- Case 2: Slow path — lock global poll while holding cache ----
        // proof {
        //     // After wlock_allocator_cache, lock_map has Process + AllocatorCache.
        //     assert(lctx.lock_map().dom().contains(KernelObjId::Process(process_ptr)));
        //     assert(lctx.lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cpu_id)));
        //     assert(!lctx.lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k)));
        //     reveal(allocator_locked_match_lctx);
        //     assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).global_poll.locked_by(&*lctx) == false);
        //     assert(lctx.kernel_view_locking_state() is Acquire);
        //     let gp_lock_id = LockId{
        //         container: self.allocator_4k_map.spec_index(alloc_ptr_4k).global_poll@.container_depth(),
        //         process: self.allocator_4k_map.spec_index(alloc_ptr_4k).global_poll@.process_depth(),
        //         major: self.allocator_4k_map.spec_index(alloc_ptr_4k).global_poll@.current_lock_major(),
        //         minor: self.allocator_4k_map.spec_index(alloc_ptr_4k).global_poll@.lock_minor(),
        //     };
        //     assert forall|k: KernelObjId| #![auto] lctx.lock_map().dom().contains(k)
        //     implies gp_lock_id.spec_gt(lctx.lock_map()[k]) by {
        //         let held_lid = lctx.lock_map()[k];
        //         assert(gp_lock_id.container.spec_eq(held_lid.container));
        //         assert(gp_lock_id.process.spec_eq(held_lid.process));
        //         assert(gp_lock_id.major != held_lid.major);
        //         assert(gp_lock_id.major > held_lid.major);
        //     };
        // }

        // let Tracked(gp_lock_perm) = self.wlock_allocator_global_poll(
        //     alloc_ptr_4k, Tracked(&mut *lctx),
        // );

        // // TODO: borrow global_poll, check len, pop if non-empty
        // // TODO: if empty → case 3 (lock-all path)

        // // ---- Case 3: Lock-all path ----
        // // Unlock global_poll + cache, kernel_step_boundary, then lock all.
        // // Each wrapper re-establishes inv() internally (wrapper-per-lock-op).
        // self.wunlock_allocator_global_poll(
        //     alloc_ptr_4k, Tracked(&mut *lctx), Tracked(gp_lock_perm),
        // );
        // self.wunlock_allocator_cache(
        //     alloc_ptr_4k, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm),
        // );

        // proof {
        //     assume(self.locked_objects_match_lctx(&*lctx));
        //     assume(kernel_k_to_kernel_u(*self) == steps.snap_shot);
        // }

        // proof { self.kernel_step_boundary(&mut *lctx, &mut *steps); }

        // // After boundary: process still held, allocator still has pages.
        // proof {
        //     assert(self.process_map.dom().contains(process_ptr));
        //     assert(self.process_map.spec_index(process_ptr).wlocked_by(&*lctx));
        //     assume(self.allocator_4k_map.dom().contains(alloc_ptr_4k));
        //     assume(self.allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages.view() > 0);
        // }

        // // Lock caches one by one. After locking each cache, try to allocate a
        // // free page from it: if the cache is non-empty, pop a page and finish
        // // (every lock stays held for the finish/unlock-all). If the cache is
        // // empty, KEEP it locked (do not unlock) and move on to the next cpu.
        // let mut scan_cpu: CpuId = 0;
        // while scan_cpu < NUM_CPUS
        //     invariant
        //         self.inv(),
        //         self.allocator_4k_map.dom().contains(alloc_ptr_4k),
        //         self.allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
        //         self.allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages.view() > 0,
        //         self.process_map.dom().contains(process_ptr),
        //         self.process_map.spec_index(process_ptr).wlocked_by(&*lctx),
        //         lctx.kernel_view_locking_state() is Acquire,
        //         0 <= scan_cpu <= NUM_CPUS,
        //         forall|i: CpuId| #![auto]
        //             cpu_id_valid(i) && i < scan_cpu ==>
        //             self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[i]@.wlocked_by(&*lctx),
        //     decreases NUM_CPUS - scan_cpu,
        // {
        //     proof {
        //         // Lock ordering: cache[scan_cpu] has same major as earlier caches
        //         // but higher minor (= scan_cpu > earlier cpu ids).
        //         assume(
        //             wlock_requires(self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[scan_cpu]@, &*lctx)
        //             && lctx.lock_id_acyclic(LockId{
        //                 container: self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[scan_cpu].container_depth(),
        //                 process: self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[scan_cpu].process_depth(),
        //                 major: self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[scan_cpu]@@.current_lock_major(),
        //                 minor: self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[scan_cpu].lock_minor(),
        //             })
        //             && lctx.obj_id_fresh(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, scan_cpu))
        //         );
        //     }
        //     let ghost pre_caches = self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches;
        //     let Tracked(cache_perm) = self.wlock_allocator_cache(
        //         alloc_ptr_4k, scan_cpu, Tracked(&mut *lctx),
        //     );
        //     // Earlier caches (< scan_cpu) are preserved by unchanged_except.
        //     proof {
        //         assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.unchanged_except(&pre_caches, scan_cpu));
        //         assert forall|i: CpuId| #![auto] cpu_id_valid(i) && i < scan_cpu
        //         implies self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[i]@.wlocked_by(&*lctx)
        //         by {
        //             assert(i != scan_cpu);
        //             assert(self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[i] == pre_caches[i]);
        //         };
        //     }

        //     // Try to allocate from this freshly-locked cache (shared borrow so
        //     // wf() — which folds over live cache lengths — is preserved).
        //     proof { reveal(allocator_perms_wf); }
        //     let cache_ref = self.allocator_4k_map.borrow_cache(
        //         alloc_ptr_4k, scan_cpu, Tracked(&cache_perm),
        //     );
        //     let cache_len = cache_ref.linked_list.len();
        //     if cache_len > 0 {
        //         // Found a free page: pop it. All caches [0, scan_cpu] stay
        //         // write-locked for the finish/unlock-all path below.
        //         let cache_mut = self.allocator_4k_map.borrow_mut_cache(
        //             alloc_ptr_4k, scan_cpu, Tracked(&*lctx), Tracked(&cache_perm),
        //         );
        //         let (page_ptr, _node_perm) = cache_mut.linked_list.pop_head();
        //         // TODO finish: page state → Owned4k, temp_alloc insert,
        //         // total_free_pages decrement, unlock all locked caches, inv().
        //         // (unlock-all needs the per-cpu perms collected — see below.)
        //         proof { assume(false); }
        //         return page_ptr;
        //     }
        //     // Cache empty → keep it locked, move on to the next cpu.
        //     // TODO: collect `cache_perm` into a tracked per-cpu map so the
        //     // finish path can unlock every cache it locked.
        //     scan_cpu = scan_cpu + 1;
        // }

        // // All caches locked. Lock global poll.
        // proof {
        //     assume(
        //         wlock_requires(self.allocator_4k_map.spec_index(alloc_ptr_4k).global_poll, &*lctx)
        //         && lctx.lock_id_acyclic(LockId{
        //             container: self.allocator_4k_map.spec_index(alloc_ptr_4k).global_poll@.container_depth(),
        //             process: self.allocator_4k_map.spec_index(alloc_ptr_4k).global_poll@.process_depth(),
        //             major: self.allocator_4k_map.spec_index(alloc_ptr_4k).global_poll@.current_lock_major(),
        //             minor: self.allocator_4k_map.spec_index(alloc_ptr_4k).global_poll@.lock_minor(),
        //         })
        //         && lctx.obj_id_fresh(KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k))
        //     );
        // }
        // let Tracked(_gp_perm) = self.wlock_allocator_global_poll(
        //     alloc_ptr_4k, Tracked(&mut *lctx),
        // );

        // // By leak-free spec: total_free_pages > 0 ∧ all locked ⟹
        // // ∃ i. cache[i].len() > 0 ∨ global_poll.len() > 0.
        // // Scan for non-empty, pop, update page state, unlock all.
        // // TODO: scan + pop + page state + temp_alloc + unlock all + inv()
        // proof { assume(false); }
        // return 0;
        assume(false);
        0
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

    // ================================================================
    // KernelK-level wrappers: wlock/wunlock for cpu cache and global poll.
    // Each re-establishes inv() after the UnLockedMap call.
    // ================================================================

    // #[verifier::spinoff_prover]
    // fn wlock_allocator_cache(
    //     &mut self,
    //     alloc_ptr_4k: RwLockPageAllocatorPtr,
    //     cache_cpu: CpuId,
    //     Tracked(lctx): Tracked<&mut LocalContext>,
    // ) -> (ret: Tracked<LockPerm>)
    //     requires
    //         old(self).inv(),
    //         old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
    //         old(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
    //         cpu_id_valid(cache_cpu),
    //         wlock_requires(old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@, old(lctx)),
    //         old(lctx).lock_id_acyclic(LockId{
    //             container: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu].container_depth(),
    //             process: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu].process_depth(),
    //             major: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@@.current_lock_major(),
    //             minor: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu].lock_minor(),
    //         }),
    //         old(lctx).obj_id_fresh(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cache_cpu)),
    //     ensures
    //         final(self).inv(),
    //         final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
    //         final(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
    //         final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@.wlocked_by(final(lctx)),
    //         final(self).process_map == old(self).process_map,
    //         final(self).thread_map == old(self).thread_map,
    //         final(self).container_map == old(self).container_map,
    //         final(self).page_array == old(self).page_array,
    //         final(self).cpu_array == old(self).cpu_array,
    //         final(self).pagetable_map == old(self).pagetable_map,
    //         final(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages,
    //         final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll,
    //         final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.unchanged_except(&old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches, cache_cpu),
    //         final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
    //         final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
    //         final(lctx).thread_id() == old(lctx).thread_id(),
    //         wlock_ensures(
    //             old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@,
    //             final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@,
    //             LockId{
    //                 container: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu].container_depth(),
    //                 process: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu].process_depth(),
    //                 major: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@@.current_lock_major(),
    //                 minor: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu].lock_minor(),
    //             },
    //             final(lctx).thread_id(),
    //             ret@,
    //         ),
    //         lock_ensures(
    //             old(lctx), final(lctx),
    //             final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@@,
    //             LockId{
    //                 container: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu].container_depth(),
    //                 process: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu].process_depth(),
    //                 major: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@@.current_lock_major(),
    //                 minor: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu].lock_minor(),
    //             },
    //             KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cache_cpu),
    //         ),
    //         // Lock-map ⇄ kernel-state agreement is preserved (one cache added to
    //         // both lock_map and the locked set, consistently).
    //         old(self).locked_objects_match_lctx(old(lctx))
    //             ==> final(self).locked_objects_match_lctx(final(lctx)),
    // {
    //     proof {
    //         reveal(cpu_array_wf);
    //         reveal(container_perms_wf);
    //         reveal(allocator_perms_wf);
    //         reveal(process_perms_wf);
    //     }
    //     let ghost pre_match = self.locked_objects_match_lctx(&*lctx);
    //     let ret = self.allocator_4k_map.wlock_cache(alloc_ptr_4k, cache_cpu, Tracked(&mut *lctx), Ghost(PageSize::SZ4k));
    //     proof {
    //         assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
    //         assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    //         assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
    //         assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); reveal(process_temp_alloc_empty_unless_wlocked); };
    //         assert(self.thread_perms_wf()) by { reveal(KernelK::thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
    //         assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    //         assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
    //             reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
    //         };
    //         assert(container_page_owner_wf(self.container_map, self.page_array)) by { reveal(container_page_owner_wf); };
    //         assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
    //             reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
    //             reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
    //         };
    //         assert(self.container_pages_wf()) by { reveal(KernelK::container_pages_wf); };
    //         assert(self.process_pages_wf()) by { reveal(KernelK::process_pages_wf); };
    //         assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
    //             lemma_container_process_allocator_quota_wf_preserved_for_process_lock_op(*old(self), *self);
    //         };
    //         assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by { reveal(container_allocator_wf); };
    //         assert(self.allocator_free_pages_wf());
    //         assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { reveal(process_pagetable_match); };
    //         assert(process_staged_pages_wf(self.process_map, self.page_array)) by {
    //             reveal(process_staged_pages_wf); reveal(process_staged_pages_4k_wf);
    //             reveal(process_staged_pages_2m_wf); reveal(process_staged_pages_1g_wf);
    //         };
    //         lemma_container_allocator_free_pages_wf_preserved_for_lock_op(*old(self), *self);
    //         assert(self.memory_management_inv());
    //         assert(container_tree_wf(self.root_container, self.container_map));
    //         assert(container_process_wf(self.container_map, self.process_map)) by { reveal(container_process_wf); };
    //         assert(per_container_process_tree_wf(self.container_map, self.process_map)) by { reveal(container_process_wf); reveal(per_container_process_tree_wf); };
    //         assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by { reveal(container_endpoint_wf); };
    //         assert(container_cpu_wf(self.container_map, self.cpu_array)) by { reveal(container_cpu_wf); };
    //         assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
    //             reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
    //             reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
    //         };
    //         assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by { reveal(container_scheduler_wf); };
    //         assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
    //             reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
    //         };
    //         assert(container_thread_wf(self.container_map, self.thread_map)) by { reveal(container_thread_wf); };
    //         assert(process_cpu_wf(self.process_map, self.cpu_array)) by { reveal(process_cpu_wf); };
    //         assert(process_thread_wf(self.process_map, self.thread_map)) by { reveal(process_thread_wf); };
    //         assert(self.process_management_inv());
    //         assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
    //             reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
    //             reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf);
    //         };
    //         assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
    //         assert(self.inv());
    //         // Lock-map ⇄ kernel-state agreement preserved: lock_map gained
    //         // exactly AllocatorCache(.., cache_cpu) (lock_ensures), and that
    //         // cache is now wlocked with the matching id; all other objects and
    //         // their lock_map entries are unchanged. Full per-object-kind proof
    //         // is TODO; the fact itself is sound (one consistent lock add).
    //         if pre_match {
    //             assume(self.locked_objects_match_lctx(&*lctx));
    //         }
    //     }
    //     ret
    // }

    // #[verifier::spinoff_prover]
    // fn wunlock_allocator_cache(
    //     &mut self,
    //     alloc_ptr_4k: RwLockPageAllocatorPtr,
    //     cache_cpu: CpuId,
    //     Tracked(lctx): Tracked<&mut LocalContext>,
    //     lock_perm: Tracked<LockPerm>,
    // )
    //     requires
    //         old(self).inv(),
    //         old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
    //         old(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
    //         cpu_id_valid(cache_cpu),
    //         old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@.wlocked_by(old(lctx)),
    //         old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@.being_killed() == false,
    //         lock_perm@.state() is WriteLock,
    //         lock_perm@.thread_id() == old(lctx).thread_id(),
    //         lock_perm@.lock_id() == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@.locking_thread()->Write_lock_id,
    //         old(lctx).lock_map().dom().contains(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cache_cpu)),
    //         old(lctx).lock_map()[KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cache_cpu)] == lock_perm@.lock_id(),
    //     ensures
    //         final(self).inv(),
    //         final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
    //         final(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
    //         final(self).process_map == old(self).process_map,
    //         final(self).thread_map == old(self).thread_map,
    //         final(self).container_map == old(self).container_map,
    //         final(self).page_array == old(self).page_array,
    //         final(self).cpu_array == old(self).cpu_array,
    //         final(self).pagetable_map == old(self).pagetable_map,
    //         final(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages,
    //         final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll,
    //         final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.unchanged_except(&old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches, cache_cpu),
    //         final(lctx).thread_id() == old(lctx).thread_id(),
    //         wunlock_ensures(
    //             old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@,
    //             final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@,
    //         ),
    //         unlock_ensures(
    //             old(lctx), final(lctx),
    //             final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@@,
    //             lock_perm@.lock_id(),
    //             KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cache_cpu),
    //         ),
    // {
    //     proof {
    //         reveal(cpu_array_wf);
    //         reveal(container_perms_wf);
    //         reveal(allocator_perms_wf);
    //         reveal(process_perms_wf);
    //     }
    //     self.allocator_4k_map.wunlock_cache(alloc_ptr_4k, cache_cpu, Tracked(&mut *lctx), lock_perm, Ghost(PageSize::SZ4k));
    //     proof {
    //         assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
    //         assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    //         assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
    //         assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); reveal(process_temp_alloc_empty_unless_wlocked); };
    //         assert(self.thread_perms_wf()) by { reveal(KernelK::thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
    //         assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    //         assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
    //             reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
    //         };
    //         assert(container_page_owner_wf(self.container_map, self.page_array)) by { reveal(container_page_owner_wf); };
    //         assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
    //             reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
    //             reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
    //         };
    //         assert(self.container_pages_wf()) by { reveal(KernelK::container_pages_wf); };
    //         assert(self.process_pages_wf()) by { reveal(KernelK::process_pages_wf); };
    //         assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
    //             lemma_container_process_allocator_quota_wf_preserved_for_process_lock_op(*old(self), *self);
    //         };
    //         assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by { reveal(container_allocator_wf); };
    //         assert(self.allocator_free_pages_wf());
    //         assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { reveal(process_pagetable_match); };
    //         assert(process_staged_pages_wf(self.process_map, self.page_array)) by {
    //             reveal(process_staged_pages_wf); reveal(process_staged_pages_4k_wf);
    //             reveal(process_staged_pages_2m_wf); reveal(process_staged_pages_1g_wf);
    //         };
    //         lemma_container_allocator_free_pages_wf_preserved_for_lock_op(*old(self), *self);
    //         assert(self.memory_management_inv());
    //         assert(container_tree_wf(self.root_container, self.container_map));
    //         assert(container_process_wf(self.container_map, self.process_map)) by { reveal(container_process_wf); };
    //         assert(per_container_process_tree_wf(self.container_map, self.process_map)) by { reveal(container_process_wf); reveal(per_container_process_tree_wf); };
    //         assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by { reveal(container_endpoint_wf); };
    //         assert(container_cpu_wf(self.container_map, self.cpu_array)) by { reveal(container_cpu_wf); };
    //         assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
    //             reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
    //             reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
    //         };
    //         assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by { reveal(container_scheduler_wf); };
    //         assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
    //             reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
    //         };
    //         assert(container_thread_wf(self.container_map, self.thread_map)) by { reveal(container_thread_wf); };
    //         assert(process_cpu_wf(self.process_map, self.cpu_array)) by { reveal(process_cpu_wf); };
    //         assert(process_thread_wf(self.process_map, self.thread_map)) by { reveal(process_thread_wf); };
    //         assert(self.process_management_inv());
    //         assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
    //             reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
    //             reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf);
    //         };
    //         assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
    //         assert(self.inv());
    //     }
    // }

    // #[verifier::spinoff_prover]
    // fn wlock_allocator_global_poll(
    //     &mut self,
    //     alloc_ptr_4k: RwLockPageAllocatorPtr,
    //     Tracked(lctx): Tracked<&mut LocalContext>,
    // ) -> (ret: Tracked<LockPerm>)
    //     requires
    //         old(self).inv(),
    //         old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
    //         old(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
    //         wlock_requires(old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll, old(lctx)),
    //         old(lctx).lock_id_acyclic(LockId{
    //             container: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll@.container_depth(),
    //             process: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll@.process_depth(),
    //             major: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll@.current_lock_major(),
    //             minor: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll@.lock_minor(),
    //         }),
    //         old(lctx).obj_id_fresh(KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k)),
    //     ensures
    //         final(self).inv(),
    //         final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
    //         final(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
    //         final(self).process_map == old(self).process_map,
    //         final(self).thread_map == old(self).thread_map,
    //         final(self).container_map == old(self).container_map,
    //         final(self).page_array == old(self).page_array,
    //         final(self).cpu_array == old(self).cpu_array,
    //         final(self).pagetable_map == old(self).pagetable_map,
    //         final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches,
    //         final(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages,
    //         final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
    //         final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
    //         final(lctx).thread_id() == old(lctx).thread_id(),
    //         wlock_ensures(
    //             old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll,
    //             final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll,
    //             LockId{
    //                 container: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll@.container_depth(),
    //                 process: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll@.process_depth(),
    //                 major: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll@.current_lock_major(),
    //                 minor: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll@.lock_minor(),
    //             },
    //             final(lctx).thread_id(),
    //             ret@,
    //         ),
    //         lock_ensures(
    //             old(lctx), final(lctx),
    //             final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll.view(),
    //             LockId{
    //                 container: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll@.container_depth(),
    //                 process: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll@.process_depth(),
    //                 major: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll@.current_lock_major(),
    //                 minor: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll@.lock_minor(),
    //             },
    //             KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k),
    //         ),
    // {
    //     proof {
    //         reveal(cpu_array_wf);
    //         reveal(container_perms_wf);
    //         reveal(allocator_perms_wf);
    //         reveal(process_perms_wf);
    //     }
    //     let ret = self.allocator_4k_map.wlock_global_poll(alloc_ptr_4k, Tracked(&mut *lctx), Ghost(PageSize::SZ4k));
    //     proof {
    //         assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
    //         assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    //         assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
    //         assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); reveal(process_temp_alloc_empty_unless_wlocked); };
    //         assert(self.thread_perms_wf()) by { reveal(KernelK::thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
    //         assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    //         assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
    //             reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
    //         };
    //         assert(container_page_owner_wf(self.container_map, self.page_array)) by { reveal(container_page_owner_wf); };
    //         assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
    //             reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
    //             reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
    //         };
    //         assert(self.container_pages_wf()) by { reveal(KernelK::container_pages_wf); };
    //         assert(self.process_pages_wf()) by { reveal(KernelK::process_pages_wf); };
    //         assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
    //             lemma_container_process_allocator_quota_wf_preserved_for_process_lock_op(*old(self), *self);
    //         };
    //         assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by { reveal(container_allocator_wf); };
    //         assert(self.allocator_free_pages_wf());
    //         assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { reveal(process_pagetable_match); };
    //         assert(process_staged_pages_wf(self.process_map, self.page_array)) by {
    //             reveal(process_staged_pages_wf); reveal(process_staged_pages_4k_wf);
    //             reveal(process_staged_pages_2m_wf); reveal(process_staged_pages_1g_wf);
    //         };
    //         lemma_container_allocator_free_pages_wf_preserved_for_lock_op(*old(self), *self);
    //         assert(self.memory_management_inv());
    //         assert(container_tree_wf(self.root_container, self.container_map));
    //         assert(container_process_wf(self.container_map, self.process_map)) by { reveal(container_process_wf); };
    //         assert(per_container_process_tree_wf(self.container_map, self.process_map)) by { reveal(container_process_wf); reveal(per_container_process_tree_wf); };
    //         assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by { reveal(container_endpoint_wf); };
    //         assert(container_cpu_wf(self.container_map, self.cpu_array)) by { reveal(container_cpu_wf); };
    //         assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
    //             reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
    //             reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
    //         };
    //         assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by { reveal(container_scheduler_wf); };
    //         assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
    //             reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
    //         };
    //         assert(container_thread_wf(self.container_map, self.thread_map)) by { reveal(container_thread_wf); };
    //         assert(process_cpu_wf(self.process_map, self.cpu_array)) by { reveal(process_cpu_wf); };
    //         assert(process_thread_wf(self.process_map, self.thread_map)) by { reveal(process_thread_wf); };
    //         assert(self.process_management_inv());
    //         assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
    //             reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
    //             reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf);
    //         };
    //         assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
    //         assert(self.inv());
    //     }
    //     ret
    // }

    // #[verifier::spinoff_prover]
    // fn wunlock_allocator_global_poll(
    //     &mut self,
    //     alloc_ptr_4k: RwLockPageAllocatorPtr,
    //     Tracked(lctx): Tracked<&mut LocalContext>,
    //     lock_perm: Tracked<LockPerm>,
    // )
    //     requires
    //         old(self).inv(),
    //         old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
    //         old(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
    //         old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll.wlocked_by(old(lctx)),
    //         old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll.inv(),
    //         unlock_requires::<crate::linkedlist::spec_impl::LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>>(old(lctx)),
    //         lock_perm@.state() is WriteLock,
    //         lock_perm@.thread_id() == old(lctx).thread_id(),
    //         lock_perm@.lock_id() == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll.locking_thread()->Write_lock_id,
    //         old(lctx).lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k)),
    //         old(lctx).lock_map()[KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k)] == lock_perm@.lock_id(),
    //     ensures
    //         final(self).inv(),
    //         final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
    //         final(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
    //         final(self).process_map == old(self).process_map,
    //         final(self).thread_map == old(self).thread_map,
    //         final(self).container_map == old(self).container_map,
    //         final(self).page_array == old(self).page_array,
    //         final(self).cpu_array == old(self).cpu_array,
    //         final(self).pagetable_map == old(self).pagetable_map,
    //         final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches,
    //         final(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages,
    //         final(lctx).thread_id() == old(lctx).thread_id(),
    //         wunlock_ensures(
    //             old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll,
    //             final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll,
    //         ),
    //         unlock_ensures(
    //             old(lctx), final(lctx),
    //             final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll.view(),
    //             lock_perm@.lock_id(),
    //             KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k),
    //         ),
    // {
    //     proof {
    //         reveal(cpu_array_wf);
    //         reveal(container_perms_wf);
    //         reveal(allocator_perms_wf);
    //         reveal(process_perms_wf);
    //     }
    //     self.allocator_4k_map.wunlock_global_poll(alloc_ptr_4k, Tracked(&mut *lctx), lock_perm, Ghost(PageSize::SZ4k));
    //     proof {
    //         assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
    //         assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    //         assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
    //         assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); reveal(process_temp_alloc_empty_unless_wlocked); };
    //         assert(self.thread_perms_wf()) by { reveal(KernelK::thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
    //         assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    //         assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
    //             reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
    //         };
    //         assert(container_page_owner_wf(self.container_map, self.page_array)) by { reveal(container_page_owner_wf); };
    //         assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
    //             reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
    //             reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
    //         };
    //         assert(self.container_pages_wf()) by { reveal(KernelK::container_pages_wf); };
    //         assert(self.process_pages_wf()) by { reveal(KernelK::process_pages_wf); };
    //         assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
    //             lemma_container_process_allocator_quota_wf_preserved_for_process_lock_op(*old(self), *self);
    //         };
    //         assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by { reveal(container_allocator_wf); };
    //         assert(self.allocator_free_pages_wf());
    //         assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { reveal(process_pagetable_match); };
    //         assert(process_staged_pages_wf(self.process_map, self.page_array)) by {
    //             reveal(process_staged_pages_wf); reveal(process_staged_pages_4k_wf);
    //             reveal(process_staged_pages_2m_wf); reveal(process_staged_pages_1g_wf);
    //         };
    //         lemma_container_allocator_free_pages_wf_preserved_for_lock_op(*old(self), *self);
    //         assert(self.memory_management_inv());
    //         assert(container_tree_wf(self.root_container, self.container_map));
    //         assert(container_process_wf(self.container_map, self.process_map)) by { reveal(container_process_wf); };
    //         assert(per_container_process_tree_wf(self.container_map, self.process_map)) by { reveal(container_process_wf); reveal(per_container_process_tree_wf); };
    //         assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by { reveal(container_endpoint_wf); };
    //         assert(container_cpu_wf(self.container_map, self.cpu_array)) by { reveal(container_cpu_wf); };
    //         assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
    //             reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
    //             reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
    //         };
    //         assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by { reveal(container_scheduler_wf); };
    //         assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
    //             reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
    //         };
    //         assert(container_thread_wf(self.container_map, self.thread_map)) by { reveal(container_thread_wf); };
    //         assert(process_cpu_wf(self.process_map, self.cpu_array)) by { reveal(process_cpu_wf); };
    //         assert(process_thread_wf(self.process_map, self.thread_map)) by { reveal(process_thread_wf); };
    //         assert(self.process_management_inv());
    //         assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
    //             reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
    //             reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf);
    //         };
    //         assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
    //         assert(self.inv());
    //     }
    // }
}

}
