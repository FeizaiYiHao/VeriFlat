use vstd::prelude::*;
use vstd::simple_pptr::*;
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
        krnl: &mut KernelK,
        thread_ptr: RwLockThreadPtr,
        container_ptr: RwLockContainerPtr,
        cpu_id: CpuId,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(krnl).inv(),
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            // Thread write-lock perm, needed to mutate the thread payload
            // (insert the freshly-allocated page into `temp_alloc_cache_4k`).
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
            thread_effective_quota_4k(old(krnl).thr_mp.spec_index(thread_ptr)) >= 1,
            old(krnl).thr_mp.spec_index(thread_ptr).wlocked_by(old(lctx)),
            page_objects_unlocked(old(krnl).pg_arr, old(lctx).thread_id()),
            allocator_objects_unlocked(old(krnl).allc_4k_mp, old(lctx).thread_id()),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        ensures
            final(krnl).inv(),
            // ---- held thread: not killed, perm still matches ----
            final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc,
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container,
            final(krnl).thr_mp.spec_index(thread_ptr).view().stable_allocation_root_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view()),
            final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr,
            thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            final(krnl).thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(ret.0)), TypedHeldLock {
                lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(ret.0)),
                mode: TypedLockMode::Write,
            }),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            final(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
            forall|t: RwLockThreadPtr|
                #![trigger old(krnl).thr_mp.spec_index(t)
                    .locked_by_thread(old(lctx).thread_id())]
                #![trigger final(krnl).thr_mp.spec_index(t)
                    .locked_by_thread(final(lctx).thread_id())]
                (old(krnl).thr_mp.dom().contains(t)
                    && old(krnl).thr_mp.spec_index(t)
                        .locked_by_thread(old(lctx).thread_id()))
                == (final(krnl).thr_mp.dom().contains(t)
                    && final(krnl).thr_mp.spec_index(t)
                        .locked_by_thread(final(lctx).thread_id())),
            forall|t: RwLockThreadPtr|
                #![trigger old(krnl).thr_mp.spec_index(t)]
                #![trigger final(krnl).thr_mp.spec_index(t)]
                t != thread_ptr
                    && old(krnl).thr_mp.dom().contains(t)
                    && old(krnl).thr_mp.spec_index(t)
                        .locked_by_thread(old(lctx).thread_id())
                ==> final(krnl).thr_mp.dom().contains(t)
                    && final(krnl).thr_mp.spec_index(t)
                        == old(krnl).thr_mp.spec_index(t)
                    && final(krnl).thr_mp.lock_id_by_key(t)
                        == old(krnl).thr_mp.lock_id_by_key(t),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
            page_ptr_valid(ret.0),
            // ---- page slot left write-locked, perm handed back (rides across the boundary as a held object) ----
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().locking_thread()->Write_lock_id,
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().wlocked_by(final(lctx)),
            page_objects_unlocked_except(final(krnl).pg_arr, final(lctx).thread_id(), set![page_ptr2page_index(ret.0)]),
            final(krnl).thr_mp.dom().contains(thread_ptr),
            final(krnl).thr_mp.spec_index(thread_ptr).wlocked_by(final(lctx)),
            held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
            final(krnl).ctn_mp.dom().contains(container_ptr),
            final(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata(),
            held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
            held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
            held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
            allocator_objects_unlocked(old(krnl).allc_2m_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(final(krnl).allc_2m_mp, final(lctx).thread_id()),
            allocator_objects_unlocked(old(krnl).allc_1g_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(final(krnl).allc_1g_mp, final(lctx).thread_id()),
            allocator_objects_unlocked(final(krnl).allc_4k_mp, final(lctx).thread_id()),
            // ---- staging: ret staged Owned4k; 4k cache gained exactly ret, 2m/1g caches + nominal quota untouched ----
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() =~= old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().insert(ret.0),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().state == (PageState::Owned4k{ thread_ptr }),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container == container_ptr,
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m,
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k,
            final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_fields_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view()),
            final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors == old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors,
    {
        assert({
            &&& krnl.ctn_mp.dom().contains(container_ptr)
            &&& krnl.ctn_mp.view().spec_index(container_ptr).is_init()
            &&& krnl.ctn_mp.view().spec_index(container_ptr).addr()
                == container_ptr
        }) by { reveal(container_perms_wf); reveal(container_thread_wf); };
        let alloc_ptr_4k = krnl.ctn_mp
            .borrow_rodata(container_ptr).borrow().allocator_ptr_4k;
        assert(
            krnl.allc_4k_mp.dom().contains(alloc_ptr_4k)
            && krnl.allc_4k_mp.spec_index(alloc_ptr_4k).wf()
        ) by { reveal(container_allocator_wf); reveal(allocator_perms_wf); };
        proof {
            assert(!lctx.allocator_cache_4k_lock_map().dom().contains((alloc_ptr_4k, cpu_id))) by { reveal(LocalContext::holds_no_allocator_locks); };
            assert(!lctx.allocator_global_pool_4k_lock_map().dom().contains(alloc_ptr_4k)) by { reveal(LocalContext::holds_no_allocator_locks); };
        }
        // Fast path: lock the running cpu's cache.
        let Tracked(cache_lock_perm) = krnl.wlock_allocator_cache(alloc_ptr_4k, cpu_id, Tracked(&mut *lctx));

        // Read the cache length via a shared borrow (preserves wf() for the slow path).
        let cache_ref = krnl.allc_4k_mp.borrow_cache(alloc_ptr_4k, cpu_id, Tracked(&cache_lock_perm));
        let cache_len = cache_ref.linked_list.len();

        if cache_len > 0 {
            let (page_ptr, Tracked(page_lock_perm)) = pop_stage_4k_page(krnl, alloc_ptr_4k, cpu_id, thread_ptr, container_ptr, Tracked(&mut *lctx), Tracked(&cache_lock_perm), Tracked(thread_lock_perm));
            krnl.wunlock_allocator_cache(alloc_ptr_4k, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm));
            proof {
                krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
                assert(typed_lock_maps_inserted(old(lctx), lctx, KernelObjId::Page(page_ptr2page_index(page_ptr)), TypedHeldLock {
                    lock_id: krnl.pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write,
                })) by {
                    map_insert_remove_absent_lemma(old(lctx).allocator_cache_4k_lock_map(), (alloc_ptr_4k, cpu_id), TypedHeldLock {
                        lock_id: allocator_cache_lock_id(cpu_id), mode: TypedLockMode::Write,
                    });
                };
                assert(krnl.ctn_mp.dom().contains(container_ptr)) by { reveal(container_thread_wf); };
            }
            return (page_ptr, Tracked(page_lock_perm));
        }

        let Tracked(gp_lock_perm) = krnl.wlock_allocator_global_pool(alloc_ptr_4k, Tracked(&mut *lctx));
        assert(krnl.allc_4k_mp.perms_wf()) by { reveal(allocator_perms_wf); };
        let pool_ref = krnl.allc_4k_mp.borrow_global_pool(alloc_ptr_4k, Tracked(&gp_lock_perm));
        let pool_len = pool_ref.len();

        if pool_len > 0 {
            let (page_ptr, Tracked(page_lock_perm)) = pop_stage_global_4k_page(krnl, alloc_ptr_4k, thread_ptr, container_ptr, Tracked(&mut *lctx), Tracked(&gp_lock_perm), Tracked(thread_lock_perm));
            krnl.wunlock_allocator_global_pool(alloc_ptr_4k, Tracked(&mut *lctx), Tracked(gp_lock_perm));
            krnl.wunlock_allocator_cache(alloc_ptr_4k, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm));
            proof {
                krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
                assert(typed_lock_maps_inserted(old(lctx), lctx, KernelObjId::Page(page_ptr2page_index(page_ptr)), TypedHeldLock {
                    lock_id: krnl.pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write,
                })) by {
                    map_insert_remove_absent_lemma(old(lctx).allocator_cache_4k_lock_map(), (alloc_ptr_4k, cpu_id), TypedHeldLock {
                        lock_id: allocator_cache_lock_id(cpu_id), mode: TypedLockMode::Write,
                    });
                    map_insert_remove_absent_lemma(old(lctx).allocator_global_pool_4k_lock_map(), alloc_ptr_4k, TypedHeldLock {
                        lock_id: old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.lock_id(), mode: TypedLockMode::Write,
                    });
                };
                assert(krnl.ctn_mp.dom().contains(container_ptr)) by { reveal(container_thread_wf); };
            }
            return (page_ptr, Tracked(page_lock_perm));
        }

        krnl.wunlock_allocator_global_pool(alloc_ptr_4k, Tracked(&mut *lctx), Tracked(gp_lock_perm));
        krnl.wunlock_allocator_cache(alloc_ptr_4k, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm));
            proof {
                assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
                krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
                assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
                    map_insert_remove_absent_lemma(old(lctx).allocator_cache_4k_lock_map(), (alloc_ptr_4k, cpu_id), TypedHeldLock {
                        lock_id: allocator_cache_lock_id(cpu_id), mode: TypedLockMode::Write,
                    });
                    map_insert_remove_absent_lemma(old(lctx).allocator_global_pool_4k_lock_map(), alloc_ptr_4k, TypedHeldLock {
                        lock_id: old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.lock_id(), mode: TypedLockMode::Write,
                    });
                };
                assert(lctx.holds_no_allocator_locks(PageSize::SZ4k)) by { reveal(LocalContext::holds_no_allocator_locks); };
                assert(krnl.ctn_mp.dom().contains(container_ptr)) by { reveal(container_thread_wf); };
        }
        alloc_4k_scan_all_caches_and_pool(krnl, thread_ptr, container_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm))
    }

    // ================================================================
    // Case 3: scan all caches + global pool after an internal boundary.
    // ================================================================

    fn alloc_4k_scan_all_caches_and_pool(
        krnl: &mut KernelK,
        thread_ptr: RwLockThreadPtr,
        container_ptr: RwLockContainerPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).thr_mp.spec_index(thread_ptr).wlocked_by(old(lctx)),
            page_objects_unlocked(old(krnl).pg_arr, old(lctx).thread_id()),
            allocator_objects_unlocked(old(krnl).allc_4k_mp, old(lctx).thread_id()),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
            thread_effective_quota_4k(old(krnl).thr_mp.spec_index(thread_ptr)) >= 1,
            old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        ensures
            final(krnl).inv(),
            final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc,
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container,
            final(krnl).thr_mp.spec_index(thread_ptr).view().stable_allocation_root_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view()),
            final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr,
            thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            final(krnl).thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(ret.0)), TypedHeldLock {
                lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(ret.0)), mode: TypedLockMode::Write,
            }),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            final(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
            forall|t: RwLockThreadPtr|
                #![trigger old(krnl).thr_mp.spec_index(t)
                    .locked_by_thread(old(lctx).thread_id())]
                #![trigger final(krnl).thr_mp.spec_index(t)
                    .locked_by_thread(final(lctx).thread_id())]
                (old(krnl).thr_mp.dom().contains(t)
                    && old(krnl).thr_mp.spec_index(t)
                        .locked_by_thread(old(lctx).thread_id()))
                == (final(krnl).thr_mp.dom().contains(t)
                    && final(krnl).thr_mp.spec_index(t)
                        .locked_by_thread(final(lctx).thread_id())),
            forall|t: RwLockThreadPtr|
                #![trigger old(krnl).thr_mp.spec_index(t)]
                #![trigger final(krnl).thr_mp.spec_index(t)]
                t != thread_ptr
                    && old(krnl).thr_mp.dom().contains(t)
                    && old(krnl).thr_mp.spec_index(t)
                        .locked_by_thread(old(lctx).thread_id())
                ==> final(krnl).thr_mp.dom().contains(t)
                    && final(krnl).thr_mp.spec_index(t)
                        == old(krnl).thr_mp.spec_index(t)
                    && final(krnl).thr_mp.lock_id_by_key(t)
                        == old(krnl).thr_mp.lock_id_by_key(t),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
            page_ptr_valid(ret.0),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().locking_thread()->Write_lock_id,
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().wlocked_by(final(lctx)),
            page_objects_unlocked_except(final(krnl).pg_arr, final(lctx).thread_id(), set![page_ptr2page_index(ret.0)]),
            final(krnl).thr_mp.dom().contains(thread_ptr),
            final(krnl).thr_mp.spec_index(thread_ptr).wlocked_by(final(lctx)),
            held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
            final(krnl).ctn_mp.dom().contains(container_ptr),
            final(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata(),
            held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
            held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
            held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
            allocator_objects_unlocked(old(krnl).allc_2m_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(final(krnl).allc_2m_mp, final(lctx).thread_id()),
            allocator_objects_unlocked(old(krnl).allc_1g_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(final(krnl).allc_1g_mp, final(lctx).thread_id()),
            allocator_objects_unlocked(final(krnl).allc_4k_mp, final(lctx).thread_id()),
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() =~= old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().insert(ret.0),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().state == (PageState::Owned4k{ thread_ptr }),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container == container_ptr,
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m,
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k,
            final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_fields_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view()),
            final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors == old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors,
    {
        assert({
            &&& krnl.ctn_mp.dom().contains(container_ptr)
            &&& krnl.ctn_mp.view().spec_index(container_ptr).is_init()
            &&& krnl.ctn_mp.view().spec_index(container_ptr).addr()
                == container_ptr
        }) by { reveal(container_perms_wf); reveal(container_thread_wf); };
        let alloc_ptr_4k = krnl.ctn_mp
            .borrow_rodata(container_ptr).borrow().allocator_ptr_4k;
        assert(krnl.allc_4k_mp.dom().contains(alloc_ptr_4k)) by { reveal(container_allocator_wf); };
        proof {
            assert(old(lctx).allocator_cache_4k_lock_map().dom().is_empty()) by { reveal(LocalContext::holds_no_allocator_locks); };
            assert(!old(lctx).allocator_global_pool_4k_lock_map().dom().contains(alloc_ptr_4k)) by { reveal(LocalContext::holds_no_allocator_locks); };
        }
        let (cache_perms, pool_perm) = wlock_all_caches_and_global_pool(krnl, alloc_ptr_4k, thread_ptr, Tracked(&mut *lctx));

        let tracked cache_perms_ref = cache_perms.borrow();
        let (found, slot) = scan_caches_and_alloc(krnl, alloc_ptr_4k, thread_ptr, container_ptr, Tracked(&mut *lctx), Tracked(cache_perms_ref), Tracked(thread_lock_perm));

        let (page_ptr, Tracked(page_lock_perm)) = if found {
            let (_scan_cpu, page_ptr, Tracked(page_lock_perm)) = slot.unwrap();
            (page_ptr, Tracked(page_lock_perm))
        } else {
            // Every cache was empty. By conservation the free pages must sit in the
            // global pool: total_free_pages == pool.len() + Σ cache.len(), the caches
            // are all empty, and the held thread still has effective_quota_4k >= 1,
            // so total_free_pages >= 1 and hence pool.len() >= 1.
            assert(krnl.allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.view().len() > 0) by {
                assert(krnl.ctn_mp.spec_index(container_ptr).view_user_ghost().owned_threads.view().contains(thread_ptr)) by { reveal(container_thread_wf); };
                lemma_scan_fail_pool_nonempty(krnl, container_ptr, alloc_ptr_4k, thread_ptr);
                reveal(allocator_perms_wf);
                krnl.allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.view().lemma_len_view();
            };
            pop_stage_global_4k_page(krnl, alloc_ptr_4k, thread_ptr, container_ptr, Tracked(&mut *lctx), Tracked(pool_perm.borrow()), Tracked(thread_lock_perm))
        };
        // Keep the page slot write-locked so it rides across the boundary as a
        // held object (its state is pinned); release the caches + pool.
        let tracked cache_perms_ref = cache_perms.borrow();
        assert(cache_perms_match_lctx(krnl.allc_4k_mp, alloc_ptr_4k, &*lctx, cache_perms_ref)) by { reveal(cache_perms_match_lctx); };
        wunlock_all_caches(krnl, alloc_ptr_4k, thread_ptr, page_ptr2page_index(page_ptr), Tracked(&mut *lctx), Tracked(cache_perms.get()));
        krnl.wunlock_allocator_global_pool(alloc_ptr_4k, Tracked(&mut *lctx), Tracked(pool_perm.get()));

        proof {
            assert(allocator_objects_unlocked(krnl.allc_4k_mp, lctx.thread_id())) by { reveal(allocator_caches_unlocked); };
            krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
            assert(lctx.holds_no_allocator_locks(PageSize::SZ4k)) by {
                reveal(LocalContext::holds_no_allocator_locks);
                vstd::set_lib::lemma_set_disjoint(old(lctx).allocator_cache_4k_lock_map().dom(), allocator_cache_key_prefix(alloc_ptr_4k, NUM_CPUS));
                map_union_remove_right_domain_disjoint_lemma(old(lctx).allocator_cache_4k_lock_map(), Map::new(
                    allocator_cache_key_prefix(alloc_ptr_4k, NUM_CPUS),
                    |key: (RwLockPageAllocatorPtr, CpuId)| TypedHeldLock { lock_id: allocator_cache_lock_id(key.1), mode: TypedLockMode::Write },
                ));
                map_insert_remove_absent_lemma(old(lctx).allocator_global_pool_4k_lock_map(), alloc_ptr_4k, TypedHeldLock {
                    lock_id: old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.lock_id(), mode: TypedLockMode::Write,
                });
            };
            assert({
                &&& lctx.allocator_cache_4k_lock_map() == old(lctx).allocator_cache_4k_lock_map()
                &&& lctx.allocator_global_pool_4k_lock_map() == old(lctx).allocator_global_pool_4k_lock_map()
            }) by { reveal(LocalContext::holds_no_allocator_locks); };
            assert(typed_lock_maps_inserted(old(lctx), lctx, KernelObjId::Page(page_ptr2page_index(page_ptr)), TypedHeldLock {
                lock_id: krnl.pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write,
            })) by {
                reveal(LocalContext::holds_no_allocator_locks);
            };
            assert(krnl.pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)).major == OWNED_PAGE_LOCK_MAJOR) by { reveal(page_array_wf); };
            assert(!old(lctx).page_lock_map().dom().contains(page_ptr2page_index(page_ptr))) by { reveal(typed_lock_maps_aligned); reveal(LockedArray::typed_lock_map_aligned); reveal(page_objects_unlocked); };
            assert(lctx.lock_id_set() =~= old(lctx).lock_id_set().insert((krnl.pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), KernelObjId::Page(page_ptr2page_index(page_ptr))))) by { reveal(lock_id_set_aligned); reveal(typed_lock_maps_inserted); vstd::set::axiom_set_ext_equal(lctx.lock_id_set(), old(lctx).lock_id_set().insert((krnl.pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), KernelObjId::Page(page_ptr2page_index(page_ptr))))); };
            assert(lctx.held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR)) by { reveal(LocalContext::held_lock_majors_lt); assert(OWNED_PAGE_LOCK_MAJOR < ALLOCATOR_CACHE_MAJOR) by (compute); broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; };
            assert(krnl.ctn_mp.dom().contains(container_ptr)) by { reveal(container_thread_wf); };
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

    spec fn allocator_cache_key_prefix_seq(
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        upper: CpuId,
    ) -> Seq<(RwLockPageAllocatorPtr, CpuId)> {
        Seq::new(upper as nat, |i: int| (alloc_ptr_4k, i as CpuId))
    }

    pub(crate) closed spec fn allocator_cache_key_prefix(
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        upper: CpuId,
    ) -> Set<(RwLockPageAllocatorPtr, CpuId)> {
        allocator_cache_key_prefix_seq(alloc_ptr_4k, upper).to_set()
    }

    #[verifier::opaque]
    spec fn allocator_cache_keys_absent_from(
        lctx: &LocalContext,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        first_cpu: CpuId,
    ) -> bool {
        forall|c: CpuId|
            #![trigger lctx.allocator_cache_4k_lock_map().dom().contains((alloc_ptr_4k, c))]
            index_valid(NUM_CPUS, c) && c >= first_cpu
            ==> !lctx.allocator_cache_4k_lock_map().dom().contains((alloc_ptr_4k, c))
    }

    pub(crate) fn wlock_all_caches_and_global_pool(
        krnl: &mut KernelK,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
    ) -> (ret: (Tracked<Map<CpuId, LockPerm>>, Tracked<LockPerm>))
        requires
            old(krnl).inv(),
            old(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).locked_by_thread(old(lctx).thread_id()),
            old(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
            allocator_objects_unlocked(old(krnl).allc_4k_mp, old(lctx).thread_id()),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        ensures
            final(krnl).inv(),
            final(krnl).thr_mp.spec_index(thread_ptr).locked_by_thread(final(lctx).thread_id()),
            kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
            // ---- only allocator_4k_map lock state moves; every other field byte-equal ----
            final(krnl).pt_mp     == old(krnl).pt_mp,
            final(krnl).it_mp     == old(krnl).it_mp,
            final(krnl).irt     == old(krnl).irt,
            final(krnl).pg_arr        == old(krnl).pg_arr,
            final(krnl).cpu_arr         == old(krnl).cpu_arr,
            final(krnl).cpu_tlb           == old(krnl).cpu_tlb,
            final(krnl).iommu_tlb           == old(krnl).iommu_tlb,
            final(krnl).rt_ctn    == old(krnl).rt_ctn,
            final(krnl).ctn_mp     == old(krnl).ctn_mp,
            final(krnl).sched_mp     == old(krnl).sched_mp,
            final(krnl).pcid_allc_mp == old(krnl).pcid_allc_mp,
            final(krnl).prc_mp       == old(krnl).prc_mp,
            final(krnl).thr_mp        == old(krnl).thr_mp,
            final(krnl).ep_mp      == old(krnl).ep_mp,
            final(krnl).allc_2m_mp  == old(krnl).allc_2m_mp,
            final(krnl).allc_1g_mp  == old(krnl).allc_1g_mp,
            final(krnl).dflt_pt == old(krnl).dflt_pt,
            final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
            final(krnl).allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, alloc_ptr_4k),
            final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).quota == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).quota,
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).allocator_cache_4k_lock_map() =~= old(lctx).allocator_cache_4k_lock_map().union_prefer_right(Map::new(
                allocator_cache_key_prefix(alloc_ptr_4k, NUM_CPUS),
                |key: (RwLockPageAllocatorPtr, CpuId)| TypedHeldLock { lock_id: allocator_cache_lock_id(key.1), mode: TypedLockMode::Write },
            )),
            final(lctx).allocator_global_pool_4k_lock_map() == old(lctx).allocator_global_pool_4k_lock_map().insert(alloc_ptr_4k, TypedHeldLock {
                lock_id: final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.lock_id(), mode: TypedLockMode::Write,
            }),
            final(lctx).allocator_quota_4k_lock_map() == old(lctx).allocator_quota_4k_lock_map(),
            final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            final(lctx).page_lock_map() == old(lctx).page_lock_map(),
            final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
            final(lctx).container_lock_map() == old(lctx).container_lock_map(),
            final(lctx).process_lock_map() == old(lctx).process_lock_map(),
            final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
            final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            // ---- every cache + the pool is write-locked by us, perm recorded ----
            cache_perms_match_lctx(final(krnl).allc_4k_mp, alloc_ptr_4k, final(lctx), &ret.0.view()),
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.locking_thread()->Write_lock_id,
            final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.wlocked_by(final(lctx)),
            // ---- every held id ≤ pool major (caches 106, pool 107, pre-entry ≤ 105) ----
            final(lctx).held_lock_majors_le(ALLOCATOR_GLOBAL_POLL_MAJOR),
            allocator_objects_unlocked_except_cache_pool(final(krnl).allc_4k_mp, alloc_ptr_4k, final(lctx).thread_id()),
    {
        let tracked mut cache_perms: Map<CpuId, LockPerm> = Map::tracked_empty();

        proof {
            assert(!lctx.allocator_global_pool_4k_lock_map().dom().contains(alloc_ptr_4k)) by { reveal(LocalContext::holds_no_allocator_locks); };
            assert(allocator_cache_keys_absent_from(&*lctx, alloc_ptr_4k, 0)) by { reveal(LocalContext::holds_no_allocator_locks); reveal(allocator_cache_keys_absent_from); };
        }

        let mut cpu: CpuId = 0;
        while cpu < NUM_CPUS
            invariant
                krnl.inv(),
                krnl.thr_mp.dom().contains(thread_ptr),
                krnl.thr_mp.spec_index(thread_ptr)
                    .locked_by_thread(lctx.thread_id()),
                typed_lock_maps_aligned(krnl, &*lctx),
                lock_id_set_aligned(&*lctx),
                krnl.allc_4k_mp.dom().contains(alloc_ptr_4k),
                krnl.pt_mp     == old(krnl).pt_mp,
                krnl.it_mp     == old(krnl).it_mp,
                krnl.irt     == old(krnl).irt,
                krnl.pg_arr        == old(krnl).pg_arr,
                krnl.cpu_arr         == old(krnl).cpu_arr,
                krnl.cpu_tlb           == old(krnl).cpu_tlb,
                krnl.iommu_tlb           == old(krnl).iommu_tlb,
                krnl.rt_ctn    == old(krnl).rt_ctn,
                krnl.ctn_mp     == old(krnl).ctn_mp,
                krnl.sched_mp     == old(krnl).sched_mp,
                krnl.pcid_allc_mp == old(krnl).pcid_allc_mp,
                krnl.prc_mp       == old(krnl).prc_mp,
                krnl.thr_mp        == old(krnl).thr_mp,
                krnl.ep_mp      == old(krnl).ep_mp,
                krnl.allc_2m_mp  == old(krnl).allc_2m_mp,
                krnl.allc_1g_mp  == old(krnl).allc_1g_mp,
                krnl.dflt_pt == old(krnl).dflt_pt,
                krnl.allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
                krnl.allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, alloc_ptr_4k),
                krnl.allc_4k_mp.spec_index(alloc_ptr_4k).quota
                    == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).quota,
                lctx.thread_id() == old(lctx).thread_id(),
                lctx.kernel_view_locking_state() is Acquire,
                0 <= cpu <= NUM_CPUS,
                lctx.allocator_cache_4k_lock_map() =~= old(lctx).allocator_cache_4k_lock_map().union_prefer_right(Map::new(
                    allocator_cache_key_prefix(alloc_ptr_4k, cpu),
                    |key: (RwLockPageAllocatorPtr, CpuId)| TypedHeldLock { lock_id: allocator_cache_lock_id(key.1), mode: TypedLockMode::Write },
                )),
                lctx.allocator_global_pool_4k_lock_map() == old(lctx).allocator_global_pool_4k_lock_map(),
                lctx.allocator_quota_4k_lock_map() == old(lctx).allocator_quota_4k_lock_map(),
                lctx.allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
                lctx.allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
                lctx.page_lock_map() == old(lctx).page_lock_map(),
                lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
                lctx.container_lock_map() == old(lctx).container_lock_map(),
                lctx.process_lock_map() == old(lctx).process_lock_map(),
                lctx.thread_lock_map() == old(lctx).thread_lock_map(),
                lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
                lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
                lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
                lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
                lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
                allocator_cache_keys_absent_from(&*lctx, alloc_ptr_4k, cpu),
                !lctx.allocator_global_pool_4k_lock_map().dom().contains(alloc_ptr_4k),
                !krnl.allc_4k_mp.spec_index(alloc_ptr_4k)
                    .global_pool.wlocked_by(&*lctx),
                forall|c: CpuId|
                    #![trigger krnl.allc_4k_mp.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(c)]
                    index_valid(NUM_CPUS, c) && c >= cpu
                    ==> !krnl.allc_4k_mp.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(c).view().wlocked_by(&*lctx),
                // Caches [0, cpu) are locked, perm collected; [cpu, NUM_CPUS) untouched.
                forall|c: CpuId|
                    #![trigger cache_perms.spec_index(c)]
                    index_valid(NUM_CPUS, c) && c < cpu
                    ==> {
                        &&& cache_perms.dom().contains(c)
                        &&& cache_perms.spec_index(c).state() is WriteLock
                        &&& cache_perms.spec_index(c).thread_id() == lctx.thread_id()
                        &&& cache_perms.spec_index(c).lock_id() == krnl.allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(c).view().locking_thread()->Write_lock_id
                        &&& cache_perms.spec_index(c).ordering_lock_id()
                            == allocator_cache_lock_id(c)
                        &&& krnl.allc_4k_mp.spec_index(alloc_ptr_4k)
                            .cpu_caches.spec_index(c).view().wlocked_by(&*lctx)
                    },
                // Every held id is a pre-entry id (major ≤ 105) or a cache we just
                // took (major 106, minor < cpu) — so cache[cpu] (minor = cpu) tops all.
                lctx.lock_id_acyclic(allocator_cache_lock_id(cpu)),
            decreases NUM_CPUS - cpu,
        {
            proof {
                assert(krnl.allc_4k_mp.spec_index(alloc_ptr_4k).wf()) by { reveal(allocator_perms_wf); };
                assert(!lctx.allocator_cache_4k_lock_map().dom().contains((alloc_ptr_4k, cpu))) by { reveal(allocator_cache_keys_absent_from); };
            }
            let Tracked(cache_perm) = krnl.wlock_allocator_cache(alloc_ptr_4k, cpu, Tracked(&mut *lctx));
            proof {
                assert(krnl.allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.lock_id_by_index(cpu) == allocator_cache_lock_id(cpu)) by { reveal(allocator_perms_wf); reveal(allocator_cache_lock_id); };
                assert(allocator_cache_key_prefix_seq(alloc_ptr_4k, (cpu + 1) as CpuId) =~= allocator_cache_key_prefix_seq(alloc_ptr_4k, cpu).push((alloc_ptr_4k, cpu))) by { reveal(allocator_cache_key_prefix_seq); };
                assert(allocator_cache_key_prefix(alloc_ptr_4k, (cpu + 1) as CpuId) =~= allocator_cache_key_prefix(alloc_ptr_4k, cpu).insert((alloc_ptr_4k, cpu))) by {
                    allocator_cache_key_prefix_seq(alloc_ptr_4k, cpu).lemma_push_to_set_commute((alloc_ptr_4k, cpu));
                    reveal(allocator_cache_key_prefix_seq); reveal(allocator_cache_key_prefix);
                };
                assert(lctx.allocator_cache_4k_lock_map() =~= old(lctx).allocator_cache_4k_lock_map().union_prefer_right(Map::new(
                    allocator_cache_key_prefix(alloc_ptr_4k, (cpu + 1) as CpuId),
                    |key: (RwLockPageAllocatorPtr, CpuId)| TypedHeldLock { lock_id: allocator_cache_lock_id(key.1), mode: TypedLockMode::Write },
                ))) by { reveal(allocator_cache_key_prefix_seq); reveal(allocator_cache_key_prefix); };
                assert(allocator_cache_keys_absent_from(&*lctx, alloc_ptr_4k, (cpu + 1) as CpuId)) by { reveal(allocator_cache_keys_absent_from); };
                cache_perms.tracked_insert(cpu, cache_perm);
            }
            cpu = cpu + 1;
        }

        // After the loop: all caches held (major 106), pool (major 107) tops them.
        proof {
            assert(krnl.allc_4k_mp.spec_index(alloc_ptr_4k).wf()) by { reveal(allocator_perms_wf); };
        }
        let Tracked(pool_perm) = krnl.wlock_allocator_global_pool(alloc_ptr_4k, Tracked(&mut *lctx));
        proof {
            assert(cache_perms_match_lctx(krnl.allc_4k_mp, alloc_ptr_4k, &*lctx, &cache_perms)) by { reveal(cache_perms_match_lctx); };
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
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
        krnl: &mut KernelK,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        page_index: PageIndex,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(cache_perms): Tracked<Map<CpuId, LockPerm>>,
    )
        requires
            old(krnl).inv(),
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).locked_by_thread(old(lctx).thread_id()),
            index_valid(NUM_PAGES, page_index),
            old(krnl).pg_arr.spec_index(page_index).view().locked_by_thread(old(lctx).thread_id()),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
            allocator_objects_unlocked_except_cache_pool(old(krnl).allc_4k_mp, alloc_ptr_4k, old(lctx).thread_id()),
            cache_perms_match_lctx(old(krnl).allc_4k_mp, alloc_ptr_4k, old(lctx), &cache_perms),
            old(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.wlocked_by(old(lctx)),
        ensures
            final(krnl).inv(),
            final(krnl).thr_mp.dom().contains(thread_ptr),
            final(krnl).thr_mp.spec_index(thread_ptr).locked_by_thread(final(lctx).thread_id()),
            final(krnl).pg_arr.spec_index(page_index).view().locked_by_thread(final(lctx).thread_id()),
            kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).allocator_cache_4k_lock_map() =~= old(lctx).allocator_cache_4k_lock_map().remove_keys(allocator_cache_key_prefix(alloc_ptr_4k, NUM_CPUS)),
            final(lctx).allocator_global_pool_4k_lock_map() == old(lctx).allocator_global_pool_4k_lock_map(),
            final(lctx).allocator_quota_4k_lock_map() == old(lctx).allocator_quota_4k_lock_map(),
            final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            final(lctx).page_lock_map() == old(lctx).page_lock_map(),
            final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
            final(lctx).container_lock_map() == old(lctx).container_lock_map(),
            final(lctx).process_lock_map() == old(lctx).process_lock_map(),
            final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
            final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            // ---- only allocator_4k_map cache lock state moves; every other field byte-equal ----
            final(krnl).pt_mp     == old(krnl).pt_mp,
            final(krnl).it_mp     == old(krnl).it_mp,
            final(krnl).irt     == old(krnl).irt,
            final(krnl).pg_arr        == old(krnl).pg_arr,
            final(krnl).cpu_arr         == old(krnl).cpu_arr,
            final(krnl).cpu_tlb           == old(krnl).cpu_tlb,
            final(krnl).iommu_tlb           == old(krnl).iommu_tlb,
            final(krnl).rt_ctn    == old(krnl).rt_ctn,
            final(krnl).ctn_mp     == old(krnl).ctn_mp,
            final(krnl).sched_mp     == old(krnl).sched_mp,
            final(krnl).pcid_allc_mp == old(krnl).pcid_allc_mp,
            final(krnl).prc_mp       == old(krnl).prc_mp,
            final(krnl).thr_mp        == old(krnl).thr_mp,
            final(krnl).ep_mp      == old(krnl).ep_mp,
            final(krnl).allc_2m_mp  == old(krnl).allc_2m_mp,
            final(krnl).allc_1g_mp  == old(krnl).allc_1g_mp,
            final(krnl).dflt_pt == old(krnl).dflt_pt,
            final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
            final(krnl).allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, alloc_ptr_4k),
            final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).quota == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).quota,
            final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool,
            final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.wlocked_by(final(lctx)),
            allocator_caches_unlocked(final(krnl).allc_4k_mp, alloc_ptr_4k),
            allocator_objects_unlocked_except_cache_pool(final(krnl).allc_4k_mp, alloc_ptr_4k, final(lctx).thread_id()),
    {
        let tracked mut perms = cache_perms;
        assert(cache_perms_match_lctx_from(krnl.allc_4k_mp, alloc_ptr_4k, &*lctx, &perms, 0)) by { reveal(cache_perms_match_lctx); reveal(cache_perms_match_lctx_from); };
        let mut cpu: CpuId = 0;
        while cpu < NUM_CPUS
            invariant
                krnl.inv(),
                krnl.thr_mp.dom().contains(thread_ptr),
                krnl.thr_mp.spec_index(thread_ptr)
                    .locked_by_thread(lctx.thread_id()),
                index_valid(NUM_PAGES, page_index),
                krnl.pg_arr.spec_index(page_index).view()
                    .locked_by_thread(lctx.thread_id()),
                typed_lock_maps_aligned(krnl, &*lctx),
                lock_id_set_aligned(&*lctx),
                krnl.pt_mp     == old(krnl).pt_mp,
                krnl.it_mp     == old(krnl).it_mp,
                krnl.irt     == old(krnl).irt,
                krnl.pg_arr        == old(krnl).pg_arr,
                krnl.cpu_arr         == old(krnl).cpu_arr,
                krnl.cpu_tlb           == old(krnl).cpu_tlb,
                krnl.iommu_tlb           == old(krnl).iommu_tlb,
                krnl.rt_ctn    == old(krnl).rt_ctn,
                krnl.ctn_mp     == old(krnl).ctn_mp,
                krnl.sched_mp     == old(krnl).sched_mp,
                krnl.pcid_allc_mp == old(krnl).pcid_allc_mp,
                krnl.prc_mp       == old(krnl).prc_mp,
                krnl.thr_mp        == old(krnl).thr_mp,
                krnl.ep_mp      == old(krnl).ep_mp,
                krnl.allc_2m_mp  == old(krnl).allc_2m_mp,
                krnl.allc_1g_mp  == old(krnl).allc_1g_mp,
                krnl.dflt_pt == old(krnl).dflt_pt,
                krnl.allc_4k_mp.dom().contains(alloc_ptr_4k),
                krnl.allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
                krnl.allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, alloc_ptr_4k),
                krnl.allc_4k_mp.spec_index(alloc_ptr_4k).quota
                    == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).quota,
                krnl.allc_4k_mp.spec_index(alloc_ptr_4k).global_pool == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool,
                lctx.thread_id() == old(lctx).thread_id(),
                0 <= cpu <= NUM_CPUS,
                lctx.allocator_cache_4k_lock_map() =~= old(lctx).allocator_cache_4k_lock_map().remove_keys(allocator_cache_key_prefix(alloc_ptr_4k, cpu)),
                lctx.allocator_global_pool_4k_lock_map() == old(lctx).allocator_global_pool_4k_lock_map(),
                lctx.allocator_quota_4k_lock_map() == old(lctx).allocator_quota_4k_lock_map(),
                lctx.allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
                lctx.allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
                lctx.page_lock_map() == old(lctx).page_lock_map(),
                lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
                lctx.container_lock_map() == old(lctx).container_lock_map(),
                lctx.process_lock_map() == old(lctx).process_lock_map(),
                lctx.thread_lock_map() == old(lctx).thread_lock_map(),
                lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
                lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
                lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
                lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
                lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
                krnl.allc_4k_mp.spec_index(alloc_ptr_4k)
                    .global_pool.wlocked_by(&*lctx),
                forall|c: CpuId|
                    #![trigger krnl.allc_4k_mp.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(c).view().locked()]
                    index_valid(NUM_CPUS, c) && c < cpu
                    ==> krnl.allc_4k_mp.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(c).view().locked() == false,
                forall|c: CpuId|
                    #![trigger krnl.allc_4k_mp.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(c)]
                    index_valid(NUM_CPUS, c) && c < cpu
                    ==> !krnl.allc_4k_mp.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(c).view()
                        .wlocked_by_thread(lctx.thread_id()),
                cache_perms_match_lctx_from(krnl.allc_4k_mp, alloc_ptr_4k, &*lctx, &perms, cpu),
            decreases NUM_CPUS - cpu,
        {
            proof {
                assert({
                    &&& perms.dom().contains(cpu)
                    && perms.spec_index(cpu).state() is WriteLock
                    && perms.spec_index(cpu).thread_id() == lctx.thread_id()
                    && perms.spec_index(cpu).lock_id()
                        == krnl.allc_4k_mp.spec_index(alloc_ptr_4k)
                            .cpu_caches.spec_index(cpu).view().locking_thread()->Write_lock_id
                    && perms.spec_index(cpu).ordering_lock_id()
                        == allocator_cache_lock_id(cpu)
                    && krnl.allc_4k_mp.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(cpu).view().wlocked_by(&*lctx)
                    &&& krnl.allc_4k_mp.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(cpu).view().being_killed() == false
                    &&& krnl.allc_4k_mp.spec_index(alloc_ptr_4k)
                        .cpu_caches.lock_id_by_index(cpu)
                        == allocator_cache_lock_id(cpu)
                }) by { reveal(cache_perms_match_lctx_from); reveal(allocator_perms_wf); reveal(allocator_cache_lock_id); };
                assert(typed_lock_map_contains_mode(lctx.allocator_cache_4k_lock_map(), (alloc_ptr_4k, cpu), TypedLockMode::Write)) by { reveal(UnLockedMap::typed_cache_lock_map_aligned); };
            }
            let tracked cache_perm = perms.tracked_remove(cpu);
            krnl.wunlock_allocator_cache(alloc_ptr_4k, cpu, Tracked(&mut *lctx), Tracked(cache_perm));
            proof {
                assert(allocator_cache_key_prefix_seq(alloc_ptr_4k, (cpu + 1) as CpuId) =~= allocator_cache_key_prefix_seq(alloc_ptr_4k, cpu).push((alloc_ptr_4k, cpu))) by { reveal(allocator_cache_key_prefix_seq); };
                assert(allocator_cache_key_prefix(alloc_ptr_4k, (cpu + 1) as CpuId) =~= allocator_cache_key_prefix(alloc_ptr_4k, cpu).insert((alloc_ptr_4k, cpu))) by {
                    allocator_cache_key_prefix_seq(alloc_ptr_4k, cpu).lemma_push_to_set_commute((alloc_ptr_4k, cpu));
                    reveal(allocator_cache_key_prefix_seq); reveal(allocator_cache_key_prefix);
                };
                assert(lctx.allocator_cache_4k_lock_map() =~= old(lctx).allocator_cache_4k_lock_map().remove_keys(allocator_cache_key_prefix(alloc_ptr_4k, (cpu + 1) as CpuId))) by { reveal(allocator_cache_key_prefix_seq); reveal(allocator_cache_key_prefix); };
                assert(cache_perms_match_lctx_from(krnl.allc_4k_mp, alloc_ptr_4k, &*lctx, &perms, (cpu + 1) as CpuId)) by { reveal(cache_perms_match_lctx_from); reveal(allocator_perms_wf); };
            }
            cpu = cpu + 1;
        }
        proof {
            assert(allocator_caches_unlocked(krnl.allc_4k_mp, alloc_ptr_4k)) by { reveal(allocator_caches_unlocked); };
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
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
        krnl: &mut KernelK,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        container_ptr: RwLockContainerPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(cache_perms): Tracked<&Map<CpuId, LockPerm>>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (bool, Option<(CpuId, PagePtr, Tracked<LockPerm>)>))
        requires
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(krnl).ctn_mp.dom().contains(container_ptr),
            old(krnl).thr_mp.dom().contains(thread_ptr),
            page_objects_unlocked(old(krnl).pg_arr, old(lctx).thread_id()),
            old(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            allocator_objects_unlocked_except_cache_pool(old(krnl).allc_4k_mp, alloc_ptr_4k, old(lctx).thread_id()),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            thread_effective_quota_4k(old(krnl).thr_mp.spec_index(thread_ptr)) >= 1,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).thr_mp.spec_index(thread_ptr).wlocked_by(old(lctx)),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
            cache_perms_match_lctx(old(krnl).allc_4k_mp, alloc_ptr_4k, old(lctx), cache_perms),
            old(lctx).held_lock_majors_lt(FREE_PAGE_LOCK_MAJOR),
        ensures
            final(krnl).inv(),
            final(krnl).thr_mp.spec_index(thread_ptr).locked_by_thread(final(lctx).thread_id()),
            final(krnl).prc_mp == old(krnl).prc_mp,
            final(krnl).pt_mp == old(krnl).pt_mp,
            final(krnl).ctn_mp == old(krnl).ctn_mp,
            final(krnl).sched_mp == old(krnl).sched_mp,
            final(krnl).pcid_allc_mp == old(krnl).pcid_allc_mp,
            final(krnl).ep_mp == old(krnl).ep_mp,
            final(krnl).irt == old(krnl).irt,
            final(krnl).it_mp == old(krnl).it_mp,
            final(krnl).iommu_tlb == old(krnl).iommu_tlb,
            final(krnl).cpu_arr == old(krnl).cpu_arr,
            final(krnl).allc_2m_mp == old(krnl).allc_2m_mp,
            final(krnl).allc_1g_mp == old(krnl).allc_1g_mp,
            final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, thread_ptr),
            forall|t: RwLockThreadPtr|
                #![trigger old(krnl).thr_mp.spec_index(t)
                    .locked_by_thread(old(lctx).thread_id())]
                #![trigger final(krnl).thr_mp.spec_index(t)
                    .locked_by_thread(final(lctx).thread_id())]
                t != thread_ptr
                    && old(krnl).thr_mp.dom().contains(t)
                    && old(krnl).thr_mp.spec_index(t)
                        .locked_by_thread(old(lctx).thread_id())
                ==> final(krnl).thr_mp.dom().contains(t)
                    && final(krnl).thr_mp.spec_index(t)
                        == old(krnl).thr_mp.spec_index(t)
                    && final(krnl).thr_mp.lock_id_by_key(t)
                        == old(krnl).thr_mp.lock_id_by_key(t),
            allocator_objects_unlocked_except_cache_pool(final(krnl).allc_4k_mp, alloc_ptr_4k, final(lctx).thread_id()),
            final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
            final(krnl).allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, alloc_ptr_4k),
            final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).quota == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).quota,
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(krnl).thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            // ---- user view unchanged: staging is krnl-internal ----
            kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
            // ---- failure: every cache was empty; complete no-op ----
            ret.0 == false ==> { &&& ret.1 is None &&&*final(krnl) == *old(krnl) &&&*final(lctx) == *old(lctx) &&& final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.view().fold_left(0int, |sum: int, cache: RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>| { sum + cache.view().linked_list.len() }) == 0 },
            // ---- success: popped + staged a page from cache `cpu`, page slot held ----
            ret.0 == true ==> {
                &&& ret.1 is Some
                &&& final(lctx).kernel_view_locking_state() is Release
                &&& index_valid(NUM_CPUS, ret.1.unwrap().0)
                &&& page_ptr_valid(ret.1.unwrap().1)
                &&& old(krnl).pg_arr.spec_index(page_ptr2page_index(ret.1.unwrap().1)).view().view().state is Free4k
                &&& !old(krnl).thr_mp.spec_index(thread_ptr).view()
                    .temp_alloc_cache_4k.view().contains(ret.1.unwrap().1)
                &&& index_valid(NUM_PAGES, page_ptr2page_index(ret.1.unwrap().1))
                &&& final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(ret.1.unwrap().1))
                &&& final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool
                    == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool
                &&& final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.1.unwrap().1)).view().being_killed() == false
                &&& ret.1.unwrap().2.view().state() is WriteLock
                &&& ret.1.unwrap().2.view().thread_id() == final(lctx).thread_id()
                &&& ret.1.unwrap().2.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.1.unwrap().1)).view().locking_thread()->Write_lock_id
                &&& final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.1.unwrap().1)).view()
                    .wlocked_by(final(lctx))
                &&& final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.1.unwrap().1)).view()
                    .locked_by_thread(final(lctx).thread_id())
                &&& page_objects_unlocked_except(final(krnl).pg_arr, final(lctx).thread_id(), set![page_ptr2page_index(ret.1.unwrap().1)])
                &&& final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(ret.1.unwrap().1)), KernelObjId::Page(page_ptr2page_index(ret.1.unwrap().1))))
                &&& typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(ret.1.unwrap().1)), TypedHeldLock {
                    lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(ret.1.unwrap().1)), mode: TypedLockMode::Write,
                })
                &&& cache_perms_match_lctx(final(krnl).allc_4k_mp, alloc_ptr_4k, final(lctx), cache_perms)
                &&& final(krnl).thr_mp.spec_index(thread_ptr)
                    .wlocked_by(final(lctx))
                &&& final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false
                &&& final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc
                    == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc
                &&& final(krnl).thr_mp.spec_index(thread_ptr).view().owning_container
                    == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container
                &&& final(krnl).thr_mp.spec_index(thread_ptr).view()
                    .stable_allocation_root_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view())
                &&& final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr
                    == old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr
                &&& thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id
                &&& final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
                    =~= old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().insert(ret.1.unwrap().1)
                &&& final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.1.unwrap().1)).view().view().state == (PageState::Owned4k{ thread_ptr })
                &&& final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.1.unwrap().1)).view().view().owning_container
                    == container_ptr
                &&& final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m
                    == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m
                &&& final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g
                    == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g
                &&& final(krnl).thr_mp.spec_index(thread_ptr).view()
                    .free_quota_pending_fields_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view())
                &&& final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k
                    == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k
                &&& final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors
                    == old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors
            },
    {
        let mut cpu: CpuId = 0;
        while cpu < NUM_CPUS
            invariant
                *krnl == *old(krnl),
                *lctx == *old(lctx),
                krnl.inv(),
                typed_lock_maps_aligned(krnl, &*lctx),
                lock_id_set_aligned(&*lctx),
                lctx.kernel_view_locking_state() is Acquire,
                0 <= cpu <= NUM_CPUS,
                krnl.ctn_mp.dom().contains(container_ptr),
                krnl.allc_4k_mp.dom().contains(alloc_ptr_4k),
                allocator_objects_unlocked_except_cache_pool(krnl.allc_4k_mp, alloc_ptr_4k, lctx.thread_id()),
                krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
                krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
                krnl.thr_mp.spec_index(thread_ptr).being_killed() == false,
                thread_effective_quota_4k(krnl.thr_mp.spec_index(thread_ptr)) >= 1,
                thread_lock_perm.state() is WriteLock,
                thread_lock_perm.thread_id() == lctx.thread_id(),
                thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
                krnl.thr_mp.dom().contains(thread_ptr),
                krnl.thr_mp.spec_index(thread_ptr).wlocked_by(&*lctx),
                krnl.thr_mp.spec_index(thread_ptr)
                    .locked_by_thread(lctx.thread_id()),
                page_objects_unlocked(krnl.pg_arr, lctx.thread_id()),
                cache_perms_match_lctx(krnl.allc_4k_mp, alloc_ptr_4k, &*lctx, cache_perms),
                lctx.held_lock_majors_lt(FREE_PAGE_LOCK_MAJOR),
                krnl.allc_4k_mp.spec_index(alloc_ptr_4k)
                    .cpu_caches.view().take(cpu as int).fold_left(
                        0int,
                        |sum: int, cache: RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>| {
                            sum + cache.view().linked_list.len()
                        },
                    ) == 0,
            decreases NUM_CPUS - cpu,
        {
            proof {
                assert(
                    krnl.allc_4k_mp.perms_wf()
                    && krnl.allc_4k_mp.dom().contains(alloc_ptr_4k)
                    && krnl.allc_4k_mp.spec_index(alloc_ptr_4k).wf()
                    && krnl.allc_4k_mp.spec_index(alloc_ptr_4k)
                        .cpu_caches.inv()
                    && krnl.allc_4k_mp.spec_index(alloc_ptr_4k)
                        .cpu_caches_wf()
                    && cache_perms.dom().contains(cpu)
                    && cache_perms.spec_index(cpu).state() is WriteLock
                    && cache_perms.spec_index(cpu).thread_id() == lctx.thread_id()
                    && cache_perms.spec_index(cpu).lock_id()
                        == krnl.allc_4k_mp.spec_index(alloc_ptr_4k)
                            .cpu_caches.spec_index(cpu).view().locking_thread()->Write_lock_id
                    && krnl.allc_4k_mp.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(cpu).view()
                        .write_lock_perm_match(&cache_perms.spec_index(cpu))
                    && krnl.allc_4k_mp.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(cpu).view().being_killed() == false
                ) by { reveal(allocator_perms_wf); reveal(cache_perms_match_lctx); };
            }
            let cache_ref = krnl.allc_4k_mp.borrow_cache(alloc_ptr_4k, cpu, Tracked(cache_perms.tracked_borrow(cpu)));
            assert(cache_ref.linked_list.wf()) by {
                assert(
                    index_valid(NUM_CPUS, cpu)
                    && krnl.allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches_wf()
                ) by { reveal(allocator_perms_wf); };
            };
            let cache_len = cache_ref.linked_list.len();
            assert(cache_len == krnl.allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu).view().view().view().len()) by { cache_ref.linked_list.lemma_len_view(); };
            if cache_len > 0 {
                let tracked selected_cache_perm = cache_perms.tracked_borrow(cpu);
                let (page_ptr, Tracked(page_lock_perm)) = pop_stage_4k_page(krnl, alloc_ptr_4k, cpu, thread_ptr, container_ptr, Tracked(&mut *lctx), Tracked(selected_cache_perm), Tracked(thread_lock_perm));
                assert(cache_perms_match_lctx(krnl.allc_4k_mp, alloc_ptr_4k, &*lctx, cache_perms)) by { reveal(cache_perms_match_lctx); };
                return (true, Some((cpu, page_ptr, Tracked(page_lock_perm))));
            }
            assert(
                krnl.allc_4k_mp.spec_index(alloc_ptr_4k)
                    .cpu_caches.view().take(cpu as int + 1).fold_left(
                        0int,
                        |sum: int, cache: RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>| {
                            sum + cache.view().linked_list.len()
                        },
                    ) == 0
            ) by {
                let caches = krnl.allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches;
                let cache_seq = caches.view();
                let cache_len_sum =
                    |sum: int, cache: RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>| {
                        sum + cache.view().linked_list.len()
                    };
                assert(cache_seq.spec_index(cpu as int).view().linked_list.len() == 0) by { caches.lemma_view_index(cpu); };
                assert(cache_seq.take(cpu as int + 1).fold_left(0int, cache_len_sum) == cache_len_sum(cache_seq.take(cpu as int).fold_left(0int, cache_len_sum), cache_seq.spec_index(cpu as int))) by {
                    assert(
                        cache_seq.take(cpu as int + 1).drop_last() =~=
                            cache_seq.take(cpu as int)
                        && cache_seq.take(cpu as int + 1).last() ==
                            cache_seq.spec_index(cpu as int)
                    ) by { cache_seq.lemma_take_succ_push(cpu as int); };
                };
            };
            cpu = cpu + 1;
        }
        assert(
            krnl.allc_4k_mp.spec_index(alloc_ptr_4k)
                .cpu_caches.view().fold_left(
                    0int,
                    |sum: int, cache: RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>| {
                        sum + cache.view().linked_list.len()
                    },
                ) == 0
        ) by {
            reveal(allocator_perms_wf);
            krnl.allc_4k_mp.spec_index(alloc_ptr_4k)
                .cpu_caches.view().lemma_take_len();
        };
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
        k.ctn_mp.dom().contains(container_ptr),
        k.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
        k.ctn_mp.spec_index(container_ptr).view_user_ghost().owned_threads.view().contains(thread_ptr),
        thread_effective_quota_4k(k.thr_mp.spec_index(thread_ptr)) >= 1,
        k.allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.view().fold_left(0int, |sum: int, cache: RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>| { sum + cache.view().linked_list.len() }) == 0,
    ensures
        k.allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.view().view().len() > 0,
{
    let owned_processes = k.ctn_mp.spec_index(container_ptr).view().owned_processes.view();
    let owned_threads = k.ctn_mp.spec_index(container_ptr).view_user_ghost().owned_threads.view();
    assert(k.allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.view().view().len() > 0) by {
        reveal(allocator_perms_wf); reveal(container_allocator_wf); reveal(container_process_wf); reveal(container_thread_wf); reveal(container_process_allocator_quota_4k_wf); reveal(process_perms_wf); reveal(thread_perms_wf);
        lemma_process_effective_quota_4k_fold_nonneg(owned_processes, k.prc_mp);
        lemma_thread_effective_quota_4k_fold_ge_member(owned_threads, k.thr_mp, thread_ptr);
        lemma_thread_direct_pending_4k_fold_nonneg(k.ctn_mp.spec_index(container_ptr).view_user_ghost().owned_threads.view(), k.thr_mp);
        lemma_thread_indirect_pending_4k_fold_nonneg(k.ctn_mp.spec_index(container_ptr).view_kernel_ghost().owned_indirect_threads.view(), k.thr_mp, k.ctn_mp.spec_index(container_ptr).view_rodata().view().depth as int);
    };
}

}
