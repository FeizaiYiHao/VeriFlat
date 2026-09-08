use super::super::allocator_cache_spec::*;
use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;
use super::allocate_free_2m_page_pop_impl::{pop_stage_2m_page, pop_stage_global_2m_page};

verus! {
    /// Allocate a single 2m page from the container's allocator.
    /// Caller holds the allocating thread's write-lock.
    #[verifier::spinoff_prover]
    pub fn allocate_free_2m_page(
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
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
            thread_effective_quota_2m(old(krnl).thr_mp.spec_index(thread_ptr)) >= 1,
            old(krnl).thr_mp.spec_index(thread_ptr).wlocked_by(old(lctx)),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        ensures
            final(krnl).inv(),
            final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc,
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container,
            final(krnl).thr_mp.spec_index(thread_ptr).view().stable_allocation_root_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view()),
            final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr,
            final(krnl).thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
            thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(ret.0)), TypedHeldLock {
                lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(ret.0)),
                mode: TypedLockMode::Write,
            }),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            final(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
            held_threads_unchanged_except(
                old(krnl).thr_mp, final(krnl).thr_mp, old(lctx),
                set![thread_ptr],
            ),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
            page_ptr_valid(ret.0),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().locking_thread()->Write_lock_id,
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().wlocked_by(final(lctx)),
            !old(lctx).page_lock_map().dom().contains(page_ptr2page_index(ret.0)),
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
            held_pages_unchanged_except(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx), set![page_ptr2page_index(ret.0)]),
            held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
            final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            !old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().contains(ret.0),
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view() =~= old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().insert(ret.0),
            thread_effective_quota_2m(final(krnl).thr_mp.spec_index(thread_ptr)) == thread_effective_quota_2m(old(krnl).thr_mp.spec_index(thread_ptr)) - 1,
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().state == (PageState::Owned2m{ thread_ptr }),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container == container_ptr,
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k,
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_2m == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_2m,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_1g == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_1g,
            final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_fields_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view()),
            final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors == old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors,
    {
        proof {
            assert(page_objects_unlocked_except(krnl.pg_arr, lctx.thread_id(), lctx.page_lock_map().dom())) by {
                reveal(page_objects_unlocked_except);
                reveal(typed_lock_maps_aligned);
                reveal(LockedArray::typed_lock_map_aligned);
            };
            assert(allocator_objects_unlocked(krnl.allc_2m_mp, lctx.thread_id())) by {
                reveal(allocator_objects_unlocked);
                reveal(LocalContext::holds_no_allocator_locks);
                reveal(typed_lock_maps_aligned);
                reveal(UnLockedMap::typed_quota_lock_map_aligned);
                reveal(UnLockedMap::typed_cache_lock_map_aligned);
                reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
            };
        }
        assert({
            &&& krnl.ctn_mp.dom().contains(container_ptr)
            &&& krnl.ctn_mp.view().spec_index(container_ptr).is_init()
            &&& krnl.ctn_mp.view().spec_index(container_ptr).addr()
                == container_ptr
        }) by { reveal(container_perms_wf); reveal(container_thread_wf); };
        let alloc_ptr_2m = krnl.ctn_mp
            .borrow_rodata(container_ptr).borrow().allocator_ptr_2m;
        assert(
            krnl.allc_2m_mp.dom().contains(alloc_ptr_2m)
            && krnl.allc_2m_mp.spec_index(alloc_ptr_2m).wf()
        ) by { reveal(container_allocator_wf); reveal(allocator_perms_wf); };
        proof {
            assert(!lctx.allocator_cache_2m_lock_map().dom().contains((alloc_ptr_2m, cpu_id))) by { reveal(LocalContext::holds_no_allocator_locks); };
            assert(!lctx.allocator_global_pool_2m_lock_map().dom().contains(alloc_ptr_2m)) by { reveal(LocalContext::holds_no_allocator_locks); };
        }
        let Tracked(cache_lock_perm) = krnl.wlock_allocator_cache_2m(alloc_ptr_2m, cpu_id, Tracked(&mut *lctx));

        let cache_ref = krnl.allc_2m_mp.borrow_cache(alloc_ptr_2m, cpu_id, Tracked(&cache_lock_perm));
        let cache_len = cache_ref.linked_list.len();

        if cache_len > 0 {
            let (page_ptr, Tracked(page_lock_perm)) = pop_stage_2m_page(krnl, alloc_ptr_2m, cpu_id, thread_ptr, container_ptr, Tracked(&mut *lctx), Tracked(&cache_lock_perm), Tracked(thread_lock_perm));
            krnl.wunlock_allocator_cache_2m(alloc_ptr_2m, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm));
            proof {
                assert(lctx.thread_lock_map().dom().contains(thread_ptr)) by {
                    reveal(LockedMap::typed_lock_map_aligned);
                };
                krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
                assert(typed_lock_maps_inserted(old(lctx), lctx, KernelObjId::Page(page_ptr2page_index(page_ptr)), TypedHeldLock {
                    lock_id: krnl.pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write,
                })) by {
                    map_insert_remove_absent_lemma(old(lctx).allocator_cache_2m_lock_map(), (alloc_ptr_2m, cpu_id), TypedHeldLock {
                        lock_id: allocator_cache_lock_id(cpu_id), mode: TypedLockMode::Write,
                    });
                };
                assert({
                    &&& lctx.holds_no_allocator_locks(PageSize::SZ2m)
                    &&& krnl.ctn_mp.dom().contains(container_ptr)
                    &&& krnl.thr_mp.spec_index(thread_ptr).view().state
                        == old(krnl).thr_mp.spec_index(thread_ptr).view().state
                }) by {
                    reveal(LocalContext::holds_no_allocator_locks);
                    reveal(container_thread_wf);
                    reveal(Thread::stable_allocation_root_equal);
                };
            }
            return (page_ptr, Tracked(page_lock_perm));
        }

        let Tracked(gp_lock_perm) = krnl.wlock_allocator_global_pool_2m(alloc_ptr_2m, Tracked(&mut *lctx));
        assert(krnl.allc_2m_mp.perms_wf()) by { reveal(allocator_perms_wf); };
        let pool_ref = krnl.allc_2m_mp.borrow_global_pool(alloc_ptr_2m, Tracked(&gp_lock_perm));
        let pool_len = pool_ref.len();

        if pool_len > 0 {
            let (page_ptr, Tracked(page_lock_perm)) = pop_stage_global_2m_page(krnl, alloc_ptr_2m, thread_ptr, container_ptr, Tracked(&mut *lctx), Tracked(&gp_lock_perm), Tracked(thread_lock_perm));
            krnl.wunlock_allocator_global_pool_2m(alloc_ptr_2m, Tracked(&mut *lctx), Tracked(gp_lock_perm));
            krnl.wunlock_allocator_cache_2m(alloc_ptr_2m, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm));
            proof {
                assert(lctx.thread_lock_map().dom().contains(thread_ptr)) by {
                    reveal(LockedMap::typed_lock_map_aligned);
                };
                krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
                assert(typed_lock_maps_inserted(old(lctx), lctx, KernelObjId::Page(page_ptr2page_index(page_ptr)), TypedHeldLock {
                    lock_id: krnl.pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write,
                })) by {
                    map_insert_remove_absent_lemma(old(lctx).allocator_cache_2m_lock_map(), (alloc_ptr_2m, cpu_id), TypedHeldLock {
                        lock_id: allocator_cache_lock_id(cpu_id), mode: TypedLockMode::Write,
                    });
                    map_insert_remove_absent_lemma(old(lctx).allocator_global_pool_2m_lock_map(), alloc_ptr_2m, TypedHeldLock {
                        lock_id: old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.lock_id(), mode: TypedLockMode::Write,
                    });
                };
                assert({
                    &&& lctx.holds_no_allocator_locks(PageSize::SZ2m)
                    &&& krnl.ctn_mp.dom().contains(container_ptr)
                    &&& krnl.thr_mp.spec_index(thread_ptr).view().state
                        == old(krnl).thr_mp.spec_index(thread_ptr).view().state
                }) by {
                    reveal(LocalContext::holds_no_allocator_locks);
                    reveal(container_thread_wf);
                    reveal(Thread::stable_allocation_root_equal);
                };
            }
            return (page_ptr, Tracked(page_lock_perm));
        }

        krnl.wunlock_allocator_global_pool_2m(alloc_ptr_2m, Tracked(&mut *lctx), Tracked(gp_lock_perm));
        krnl.wunlock_allocator_cache_2m(alloc_ptr_2m, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm));
        proof {
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
            assert(lctx.thread_lock_map().dom().contains(thread_ptr)) by {
                reveal(LockedMap::typed_lock_map_aligned);
            };
            krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
            assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
                map_insert_remove_absent_lemma(old(lctx).allocator_cache_2m_lock_map(), (alloc_ptr_2m, cpu_id), TypedHeldLock {
                    lock_id: allocator_cache_lock_id(cpu_id), mode: TypedLockMode::Write,
                });
                map_insert_remove_absent_lemma(old(lctx).allocator_global_pool_2m_lock_map(), alloc_ptr_2m, TypedHeldLock {
                    lock_id: old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.lock_id(), mode: TypedLockMode::Write,
                });
            };
            assert({
                &&& lctx.holds_no_allocator_locks(PageSize::SZ2m)
                &&& krnl.ctn_mp.dom().contains(container_ptr)
            }) by {
                reveal(LocalContext::holds_no_allocator_locks);
                reveal(container_thread_wf);
            };
        }
        let ret = alloc_2m_scan_all_caches_and_pool(
            krnl, thread_ptr, container_ptr, Tracked(&mut *lctx),
            Tracked(&mut *steps), Tracked(thread_lock_perm),
        );
        ret
    }

    fn alloc_2m_scan_all_caches_and_pool(
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
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
            thread_effective_quota_2m(old(krnl).thr_mp.spec_index(thread_ptr)) >= 1,
            old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        ensures
            final(krnl).inv(),
            final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc,
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container,
            final(krnl).thr_mp.spec_index(thread_ptr).view().stable_allocation_root_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view()),
            final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr,
            final(krnl).thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
            thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(ret.0)), TypedHeldLock {
                lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(ret.0)), mode: TypedLockMode::Write,
            }),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            final(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
            held_threads_unchanged_except(
                old(krnl).thr_mp, final(krnl).thr_mp, old(lctx),
                set![thread_ptr],
            ),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
            page_ptr_valid(ret.0),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().locking_thread()->Write_lock_id,
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().wlocked_by(final(lctx)),
            !old(lctx).page_lock_map().dom().contains(page_ptr2page_index(ret.0)),
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
            held_pages_unchanged_except(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx), set![page_ptr2page_index(ret.0)]),
            held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
            final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view() =~= old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().insert(ret.0),
            !old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().contains(ret.0),
            thread_effective_quota_2m(final(krnl).thr_mp.spec_index(thread_ptr)) == thread_effective_quota_2m(old(krnl).thr_mp.spec_index(thread_ptr)) - 1,
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().state == (PageState::Owned2m{ thread_ptr }),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container == container_ptr,
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k,
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_2m == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_2m,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_1g == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_1g,
            final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_fields_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view()),
            final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors == old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors,
    {
        assert({
            &&& krnl.ctn_mp.dom().contains(container_ptr)
            &&& krnl.ctn_mp.view().spec_index(container_ptr).is_init()
            &&& krnl.ctn_mp.view().spec_index(container_ptr).addr()
                == container_ptr
        }) by { reveal(container_perms_wf); reveal(container_thread_wf); };
        let alloc_ptr_2m = krnl.ctn_mp
            .borrow_rodata(container_ptr).borrow().allocator_ptr_2m;
        assert(krnl.allc_2m_mp.dom().contains(alloc_ptr_2m)) by { reveal(container_allocator_wf); };
        proof {
            assert(old(lctx).allocator_cache_2m_lock_map().dom().is_empty()) by { reveal(LocalContext::holds_no_allocator_locks); };
            assert(!old(lctx).allocator_global_pool_2m_lock_map().dom().contains(alloc_ptr_2m)) by { reveal(LocalContext::holds_no_allocator_locks); };
            assert(lctx.thread_lock_map().dom().contains(thread_ptr)) by {
                reveal(LockedMap::typed_lock_map_aligned);
            };
            assert(allocator_objects_unlocked(
                krnl.allc_2m_mp, lctx.thread_id(),
            )) by {
                reveal(allocator_objects_unlocked);
                reveal(LocalContext::holds_no_allocator_locks);
                reveal(typed_lock_maps_aligned);
                reveal(UnLockedMap::typed_quota_lock_map_aligned);
                reveal(UnLockedMap::typed_cache_lock_map_aligned);
                reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
            };
        }
        let (cache_perms, pool_perm) = wlock_all_caches_and_global_pool(krnl, alloc_ptr_2m, Tracked(&mut *lctx));

        let tracked cache_perms_ref = cache_perms.borrow();
        proof {
            assert({
                &&& lctx.allocator_quota_2m_lock_map().dom().is_empty()
                &&& lctx.allocator_cache_2m_lock_map().dom()
                    =~= allocator_cache_key_prefix(alloc_ptr_2m, NUM_CPUS)
                &&& lctx.allocator_global_pool_2m_lock_map().dom()
                    =~= set![alloc_ptr_2m]
            }) by {
                reveal(LocalContext::holds_no_allocator_locks);
            };
        }
        let slot = scan_caches_and_alloc(krnl, alloc_ptr_2m, thread_ptr, container_ptr, Tracked(&mut *lctx), Tracked(cache_perms_ref), Tracked(thread_lock_perm));

        let (page_ptr, Tracked(page_lock_perm)) = if let Some(page) = slot {
            page
        } else {
            // Every cache was empty. By conservation the free pages must sit in the
            // global pool: total_free_pages == pool.len() + Σ cache.len(), the caches
            // are all empty, and the held thread still has effective_quota_2m >= 1,
            // so total_free_pages >= 1 and hence pool.len() >= 1.
            assert(krnl.allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.view().len() > 0) by {
                assert(krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().contains(thread_ptr)) by { reveal(container_thread_wf); };
                lemma_scan_fail_pool_nonempty(krnl, container_ptr, alloc_ptr_2m, thread_ptr);
                reveal(allocator_perms_wf);
                krnl.allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.view().lemma_len_view();
            };
            proof {
                assert(page_objects_unlocked_except(
                    krnl.pg_arr, lctx.thread_id(), lctx.page_lock_map().dom(),
                )) by {
                    reveal(page_objects_unlocked_except);
                    reveal(typed_lock_maps_aligned);
                    reveal(LockedArray::typed_lock_map_aligned);
                };
                assert(allocator_objects_unlocked_except_cache_pool(
                    krnl.allc_2m_mp, alloc_ptr_2m, lctx.thread_id(),
                )) by {
                    reveal(typed_lock_maps_aligned);
                    reveal(UnLockedMap::typed_quota_lock_map_aligned);
                    reveal(UnLockedMap::typed_cache_lock_map_aligned);
                    reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
                };
            }
            pop_stage_global_2m_page(krnl, alloc_ptr_2m, thread_ptr, container_ptr, Tracked(&mut *lctx), Tracked(pool_perm.borrow()), Tracked(thread_lock_perm))
        };
        // Keep the page slot write-locked so it rides across the boundary as a
        // held object (its state is pinned); release the caches + pool.
        let tracked cache_perms_ref = cache_perms.borrow();
        assert(cache_perms_match_lctx(krnl.allc_2m_mp, alloc_ptr_2m, &*lctx, cache_perms_ref)) by { reveal(cache_perms_match_lctx); };
        assert(allocator_objects_unlocked_except_cache_pool(
            krnl.allc_2m_mp, alloc_ptr_2m, lctx.thread_id(),
        )) by {
            reveal(typed_lock_maps_aligned);
            reveal(UnLockedMap::typed_quota_lock_map_aligned);
            reveal(UnLockedMap::typed_cache_lock_map_aligned);
            reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
        };
        wunlock_all_caches(krnl, alloc_ptr_2m, Tracked(&mut *lctx), Tracked(cache_perms.get()));
        krnl.wunlock_allocator_global_pool_2m(alloc_ptr_2m, Tracked(&mut *lctx), Tracked(pool_perm.get()));

        proof {
            assert(lctx.holds_no_allocator_locks(PageSize::SZ2m)) by {
                reveal(LocalContext::holds_no_allocator_locks);
                vstd::set_lib::lemma_set_disjoint(old(lctx).allocator_cache_2m_lock_map().dom(), allocator_cache_key_prefix(alloc_ptr_2m, NUM_CPUS));
                map_union_remove_right_domain_disjoint_lemma(old(lctx).allocator_cache_2m_lock_map(), Map::new(
                    allocator_cache_key_prefix(alloc_ptr_2m, NUM_CPUS),
                    |key: (RwLockPageAllocatorPtr, CpuId)| TypedHeldLock { lock_id: allocator_cache_lock_id(key.1), mode: TypedLockMode::Write },
                ));
                map_insert_remove_absent_lemma(old(lctx).allocator_global_pool_2m_lock_map(), alloc_ptr_2m, TypedHeldLock {
                    lock_id: old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.lock_id(), mode: TypedLockMode::Write,
                });
            };
            assert({
                &&& lctx.allocator_cache_2m_lock_map() == old(lctx).allocator_cache_2m_lock_map()
                &&& lctx.allocator_global_pool_2m_lock_map() == old(lctx).allocator_global_pool_2m_lock_map()
            }) by { reveal(LocalContext::holds_no_allocator_locks); };
            assert(typed_lock_maps_inserted(old(lctx), lctx, KernelObjId::Page(page_ptr2page_index(page_ptr)), TypedHeldLock {
                lock_id: krnl.pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write,
            })) by {
                reveal(LocalContext::holds_no_allocator_locks);
            };
            assert(krnl.pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)).major == OWNED_PAGE_LOCK_MAJOR) by { reveal(page_array_wf); };
            held_lock_majors_lt_preserved_for_fresh_typed_insert(
                old(lctx), lctx,
                KernelObjId::Page(page_ptr2page_index(page_ptr)),
                TypedHeldLock {
                    lock_id: krnl.pg_arr.lock_id_by_index(
                        page_ptr2page_index(page_ptr),
                    ),
                    mode: TypedLockMode::Write,
                },
                ALLOCATOR_CACHE_MAJOR,
            );
        }
        proof {
            assert(held_pages_unchanged_except(
                old(krnl).pg_arr, krnl.pg_arr, old(lctx),
                set![page_ptr2page_index(page_ptr)],
            )) by {
                held_pages_unchanged_except_for_entries_unchanged_except(
                    old(krnl).pg_arr, krnl.pg_arr, old(lctx),
                    page_ptr2page_index(page_ptr),
                );
            };
            assert(
                old(lctx).page_lock_map().dom().subset_of(
                    lctx.page_lock_map().dom(),
                )
            ) by {
                broadcast use vstd::map::lemma_map_insert_domain;
            };
            assert(lctx.thread_lock_map().dom().contains(thread_ptr)) by {
                reveal(LockedMap::typed_lock_map_aligned);
            };
            krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
            assert(held_pages_unchanged_except(
                old(krnl).pg_arr, krnl.pg_arr, old(lctx),
                set![page_ptr2page_index(page_ptr)],
            )) by {
                broadcast use group_held_objects_unchanged_transitive;
            };
            assert(krnl.ctn_mp.dom().contains(container_ptr)) by { reveal(container_thread_wf); };
            assert({
                &&& krnl.thr_mp.spec_index(thread_ptr).view().state
                    == old(krnl).thr_mp.spec_index(thread_ptr).view().state
                &&& krnl.thr_mp.spec_index(thread_ptr).view().quota_4k
                    == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k
                &&& krnl.thr_mp.spec_index(thread_ptr).view().quota_1g
                    == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_1g
            }) by {
                reveal(Thread::stable_allocation_root_equal);
                reveal(held_threads_unchanged);
            };
        }
        (page_ptr, Tracked(page_lock_perm))
    }

    #[verifier::opaque]
    spec fn allocator_cache_keys_absent_from(
        lctx: &LocalContext,
        alloc_ptr_2m: RwLockPageAllocatorPtr,
        first_cpu: CpuId,
    ) -> bool {
        forall|c: CpuId|
            #![trigger lctx.allocator_cache_2m_lock_map().dom().contains((alloc_ptr_2m, c))]
            index_valid(NUM_CPUS, c) && c >= first_cpu
            ==> !lctx.allocator_cache_2m_lock_map().dom().contains((alloc_ptr_2m, c))
    }

    pub(crate) fn wlock_all_caches_and_global_pool(krnl: &mut KernelK, alloc_ptr_2m: RwLockPageAllocatorPtr, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: (Tracked<Map<CpuId, LockPerm>>, Tracked<LockPerm>))
        requires
            old(krnl).inv(),
            old(krnl).allc_2m_mp.dom().contains(alloc_ptr_2m),
            old(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
            allocator_objects_unlocked(old(krnl).allc_2m_mp, old(lctx).thread_id()),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        ensures
            final(krnl).inv(),
            kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
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
            final(krnl).allc_4k_mp  == old(krnl).allc_4k_mp,
            final(krnl).allc_1g_mp  == old(krnl).allc_1g_mp,
            final(krnl).dflt_pt == old(krnl).dflt_pt,
            final(krnl).allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom(),
            final(krnl).allc_2m_mp.unchanged_except(&old(krnl).allc_2m_mp, alloc_ptr_2m),
            final(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).quota == old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).quota,
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).allocator_cache_2m_lock_map() =~= old(lctx).allocator_cache_2m_lock_map().union_prefer_right(Map::new(
                allocator_cache_key_prefix(alloc_ptr_2m, NUM_CPUS),
                |key: (RwLockPageAllocatorPtr, CpuId)| TypedHeldLock { lock_id: allocator_cache_lock_id(key.1), mode: TypedLockMode::Write },
            )),
            final(lctx).allocator_global_pool_2m_lock_map() == old(lctx).allocator_global_pool_2m_lock_map().insert(alloc_ptr_2m, TypedHeldLock {
                lock_id: final(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.lock_id(), mode: TypedLockMode::Write,
            }),
            final(lctx).allocator_quota_2m_lock_map() == old(lctx).allocator_quota_2m_lock_map(),
            final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
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
            cache_perms_match_lctx(final(krnl).allc_2m_mp, alloc_ptr_2m, final(lctx), &ret.0.view()),
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.locking_thread()->Write_lock_id,
            final(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.wlocked_by(final(lctx)),
            final(lctx).held_lock_majors_le(ALLOCATOR_GLOBAL_POLL_MAJOR),
            allocator_objects_unlocked_except_cache_pool(final(krnl).allc_2m_mp, alloc_ptr_2m, final(lctx).thread_id()),
    {
        let tracked mut cache_perms: Map<CpuId, LockPerm> = Map::tracked_empty();

        proof {
            assert(!lctx.allocator_global_pool_2m_lock_map().dom().contains(alloc_ptr_2m)) by { reveal(LocalContext::holds_no_allocator_locks); };
            assert(allocator_cache_keys_absent_from(&*lctx, alloc_ptr_2m, 0)) by { reveal(LocalContext::holds_no_allocator_locks); reveal(allocator_cache_keys_absent_from); };
        }

        let mut cpu: CpuId = 0;
        while cpu < NUM_CPUS
            invariant
                krnl.inv(),
                typed_lock_maps_aligned(krnl, &*lctx),
                lock_id_set_aligned(&*lctx),
                krnl.allc_2m_mp.dom().contains(alloc_ptr_2m),
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
                krnl.allc_4k_mp  == old(krnl).allc_4k_mp,
                krnl.allc_1g_mp  == old(krnl).allc_1g_mp,
                krnl.dflt_pt == old(krnl).dflt_pt,
                krnl.allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom(),
                krnl.allc_2m_mp.unchanged_except(&old(krnl).allc_2m_mp, alloc_ptr_2m),
                krnl.allc_2m_mp.spec_index(alloc_ptr_2m).quota == old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).quota,
                lctx.thread_id() == old(lctx).thread_id(),
                lctx.kernel_view_locking_state() is Acquire,
                0 <= cpu <= NUM_CPUS,
                lctx.allocator_cache_2m_lock_map() =~= old(lctx).allocator_cache_2m_lock_map().union_prefer_right(Map::new(
                    allocator_cache_key_prefix(alloc_ptr_2m, cpu),
                    |key: (RwLockPageAllocatorPtr, CpuId)| TypedHeldLock { lock_id: allocator_cache_lock_id(key.1), mode: TypedLockMode::Write },
                )),
                lctx.allocator_global_pool_2m_lock_map() == old(lctx).allocator_global_pool_2m_lock_map(),
                lctx.allocator_quota_2m_lock_map() == old(lctx).allocator_quota_2m_lock_map(),
                lctx.allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
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
                allocator_cache_keys_absent_from(&*lctx, alloc_ptr_2m, cpu),
                !lctx.allocator_global_pool_2m_lock_map().dom().contains(alloc_ptr_2m),
                !krnl.allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.wlocked_by(&*lctx),
                forall|c: CpuId|
                    #![trigger krnl.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(c)]
                    index_valid(NUM_CPUS, c) && c >= cpu ==> !krnl.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(c).view().wlocked_by(&*lctx),
                forall|c: CpuId|
                    #![trigger cache_perms.spec_index(c)]
                    index_valid(NUM_CPUS, c) && c < cpu ==> {
                        &&& cache_perms.dom().contains(c)
                        &&& cache_perms.spec_index(c).state() is WriteLock
                        &&& cache_perms.spec_index(c).thread_id() == lctx.thread_id()
                        &&& cache_perms.spec_index(c).lock_id() == krnl.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(c).view().locking_thread()->Write_lock_id
                        &&& cache_perms.spec_index(c).ordering_lock_id() == allocator_cache_lock_id(c)
                        &&& krnl.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(c).view().wlocked_by(&*lctx)
                    },
                lctx.lock_id_acyclic(allocator_cache_lock_id(cpu)),
            decreases NUM_CPUS - cpu,
        {
            proof {
                assert(krnl.allc_2m_mp.spec_index(alloc_ptr_2m).wf()) by { reveal(allocator_perms_wf); };
                assert(!lctx.allocator_cache_2m_lock_map().dom().contains((alloc_ptr_2m, cpu))) by { reveal(allocator_cache_keys_absent_from); };
            }
            let Tracked(cache_perm) = krnl.wlock_allocator_cache_2m(alloc_ptr_2m, cpu, Tracked(&mut *lctx));
            proof {
                assert(krnl.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.lock_id_by_index(cpu) == allocator_cache_lock_id(cpu)) by { reveal(allocator_perms_wf); };

                assert(allocator_cache_key_prefix(alloc_ptr_2m, (cpu + 1) as CpuId) =~= allocator_cache_key_prefix(alloc_ptr_2m, cpu).insert((alloc_ptr_2m, cpu))) by {
                    vstd::assert_seqs_equal!(allocator_cache_key_prefix_seq(alloc_ptr_2m, (cpu + 1) as CpuId), allocator_cache_key_prefix_seq(alloc_ptr_2m, cpu).push((alloc_ptr_2m, cpu)));
                    allocator_cache_key_prefix_seq(alloc_ptr_2m, cpu).lemma_push_to_set_commute((alloc_ptr_2m, cpu));
                };

                assert(allocator_cache_keys_absent_from(&*lctx, alloc_ptr_2m, (cpu + 1) as CpuId)) by { reveal(allocator_cache_keys_absent_from); };
                cache_perms.tracked_insert(cpu, cache_perm);
            }
            cpu = cpu + 1;
        }

        proof {
            assert(krnl.allc_2m_mp.spec_index(alloc_ptr_2m).wf()) by { reveal(allocator_perms_wf); };
        }
        let Tracked(pool_perm) = krnl.wlock_allocator_global_pool_2m(alloc_ptr_2m, Tracked(&mut *lctx));
        proof {
            assert(cache_perms_match_lctx(krnl.allc_2m_mp, alloc_ptr_2m, &*lctx, &cache_perms)) by { reveal(cache_perms_match_lctx); };
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
        }
        (Tracked(cache_perms), Tracked(pool_perm))
    }

    pub(crate) fn wunlock_all_caches(krnl: &mut KernelK, alloc_ptr_2m: RwLockPageAllocatorPtr, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(cache_perms): Tracked<Map<CpuId, LockPerm>>)
        requires
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
            allocator_objects_unlocked_except_cache_pool(old(krnl).allc_2m_mp, alloc_ptr_2m, old(lctx).thread_id()),
            cache_perms_match_lctx(old(krnl).allc_2m_mp, alloc_ptr_2m, old(lctx), &cache_perms),
            old(krnl).allc_2m_mp.dom().contains(alloc_ptr_2m),
            old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.wlocked_by(old(lctx)),
        ensures
            final(krnl).inv(),
            kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).allocator_cache_2m_lock_map() =~= old(lctx).allocator_cache_2m_lock_map().remove_keys(allocator_cache_key_prefix(alloc_ptr_2m, NUM_CPUS)),
            final(lctx).allocator_global_pool_2m_lock_map() == old(lctx).allocator_global_pool_2m_lock_map(),
            final(lctx).allocator_quota_2m_lock_map() == old(lctx).allocator_quota_2m_lock_map(),
            final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
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
            final(krnl).allc_4k_mp  == old(krnl).allc_4k_mp,
            final(krnl).allc_1g_mp  == old(krnl).allc_1g_mp,
            final(krnl).dflt_pt == old(krnl).dflt_pt,
            final(krnl).allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom(),
            final(krnl).allc_2m_mp.unchanged_except(&old(krnl).allc_2m_mp, alloc_ptr_2m),
            final(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).quota == old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).quota,
            final(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool == old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool,
            final(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.wlocked_by(final(lctx)),
            allocator_caches_unlocked(final(krnl).allc_2m_mp, alloc_ptr_2m),
            allocator_objects_unlocked_except_cache_pool(final(krnl).allc_2m_mp, alloc_ptr_2m, final(lctx).thread_id()),
    {
        let tracked mut perms = cache_perms;
        assert(cache_perms_match_lctx_from(krnl.allc_2m_mp, alloc_ptr_2m, &*lctx, &perms, 0)) by { reveal(cache_perms_match_lctx); reveal(cache_perms_match_lctx_from); };
        let mut cpu: CpuId = 0;
        while cpu < NUM_CPUS
            invariant
                krnl.inv(),
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
                krnl.allc_4k_mp  == old(krnl).allc_4k_mp,
                krnl.allc_1g_mp  == old(krnl).allc_1g_mp,
                krnl.dflt_pt == old(krnl).dflt_pt,
                krnl.allc_2m_mp.dom().contains(alloc_ptr_2m),
                krnl.allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom(),
                krnl.allc_2m_mp.unchanged_except(&old(krnl).allc_2m_mp, alloc_ptr_2m),
                krnl.allc_2m_mp.spec_index(alloc_ptr_2m).quota == old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).quota,
                krnl.allc_2m_mp.spec_index(alloc_ptr_2m).global_pool == old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool,
                lctx.thread_id() == old(lctx).thread_id(),
                0 <= cpu <= NUM_CPUS,
                lctx.allocator_cache_2m_lock_map() =~= old(lctx).allocator_cache_2m_lock_map().remove_keys(allocator_cache_key_prefix(alloc_ptr_2m, cpu)),
                lctx.allocator_global_pool_2m_lock_map() == old(lctx).allocator_global_pool_2m_lock_map(),
                lctx.allocator_quota_2m_lock_map() == old(lctx).allocator_quota_2m_lock_map(),
                lctx.allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
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
                krnl.allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.wlocked_by(&*lctx),
                forall|c: CpuId|
                    #![trigger krnl.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(c).view().locked()]
                    index_valid(NUM_CPUS, c) && c < cpu ==> krnl.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(c).view().locked() == false,
                forall|c: CpuId|
                    #![trigger krnl.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(c)]
                    index_valid(NUM_CPUS, c) && c < cpu ==> !krnl.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(c).view().wlocked_by_thread(lctx.thread_id()),
                cache_perms_match_lctx_from(krnl.allc_2m_mp, alloc_ptr_2m, &*lctx, &perms, cpu),
            decreases NUM_CPUS - cpu,
        {
            proof {
                assert({
                    &&& perms.dom().contains(cpu)
                    && perms.spec_index(cpu).state() is WriteLock
                    && perms.spec_index(cpu).thread_id() == lctx.thread_id()
                    && perms.spec_index(cpu).lock_id() == krnl.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cpu).view().locking_thread()->Write_lock_id
                    && perms.spec_index(cpu).ordering_lock_id() == allocator_cache_lock_id(cpu)
                    && krnl.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cpu).view().wlocked_by(&*lctx)
                    &&& krnl.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cpu).view().being_killed() == false
                    &&& krnl.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.lock_id_by_index(cpu) == allocator_cache_lock_id(cpu)
                }) by { reveal(cache_perms_match_lctx_from); reveal(allocator_perms_wf); };
                assert(typed_lock_map_contains_mode(lctx.allocator_cache_2m_lock_map(), (alloc_ptr_2m, cpu), TypedLockMode::Write)) by { reveal(UnLockedMap::typed_cache_lock_map_aligned); };
            }
            let tracked cache_perm = perms.tracked_remove(cpu);
            krnl.wunlock_allocator_cache_2m(alloc_ptr_2m, cpu, Tracked(&mut *lctx), Tracked(cache_perm));
            proof {
                assert(allocator_cache_key_prefix(alloc_ptr_2m, (cpu + 1) as CpuId) =~= allocator_cache_key_prefix(alloc_ptr_2m, cpu).insert((alloc_ptr_2m, cpu))) by {
                    vstd::assert_seqs_equal!(allocator_cache_key_prefix_seq(alloc_ptr_2m, (cpu + 1) as CpuId), allocator_cache_key_prefix_seq(alloc_ptr_2m, cpu).push((alloc_ptr_2m, cpu)));
                    allocator_cache_key_prefix_seq(alloc_ptr_2m, cpu).lemma_push_to_set_commute((alloc_ptr_2m, cpu));
                };

                assert(cache_perms_match_lctx_from(krnl.allc_2m_mp, alloc_ptr_2m, &*lctx, &perms, (cpu + 1) as CpuId)) by { reveal(cache_perms_match_lctx_from); reveal(allocator_perms_wf); };
            }
            cpu = cpu + 1;
        }
        proof {
            assert(allocator_caches_unlocked(krnl.allc_2m_mp, alloc_ptr_2m)) by { reveal(allocator_caches_unlocked); };
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
        }
    }

    #[verifier::opaque]
    spec fn cache_perms_match_lctx_from(
        alloc_map: PageAllocatorUnLockedMap,
        alloc_ptr_2m: RwLockPageAllocatorPtr,
        lctx: &LocalContext,
        cache_perms: &Map<CpuId, LockPerm>,
        first_cpu: CpuId,
    ) -> bool {
        &&& alloc_map.dom().contains(alloc_ptr_2m)
        &&& forall|c: CpuId|
                #![trigger cache_perms.spec_index(c)]
                index_valid(NUM_CPUS, c) && c >= first_cpu
                ==> {
                    &&& cache_perms.dom().contains(c)
                    &&& cache_perms.spec_index(c).state() is WriteLock
                    &&& cache_perms.spec_index(c).thread_id() == lctx.thread_id()
                    &&& cache_perms.spec_index(c).lock_id()
                        == alloc_map.spec_index(alloc_ptr_2m)
                            .cpu_caches.spec_index(c).view().locking_thread()->Write_lock_id
                    &&& cache_perms.spec_index(c).ordering_lock_id()
                        == allocator_cache_lock_id(c)
                    &&& alloc_map.spec_index(alloc_ptr_2m)
                        .cpu_caches.spec_index(c).view().wlocked_by(lctx)
                }
    }

    #[verifier::opaque]
    pub(crate) open spec fn cache_perms_match_lctx(
        alloc_map: PageAllocatorUnLockedMap,
        alloc_ptr_2m: RwLockPageAllocatorPtr,
        lctx: &LocalContext,
        cache_perms: &Map<CpuId, LockPerm>,
    ) -> bool {
        &&& alloc_map.dom().contains(alloc_ptr_2m)
        &&& forall|c: CpuId|
                #![trigger cache_perms.spec_index(c)]
                index_valid(NUM_CPUS, c)
                ==> {
                    &&& cache_perms.dom().contains(c)
                    &&& cache_perms.spec_index(c).state() is WriteLock
                    &&& cache_perms.spec_index(c).thread_id() == lctx.thread_id()
                    &&& cache_perms.spec_index(c).lock_id()
                        == alloc_map.spec_index(alloc_ptr_2m).cpu_caches.spec_index(c).view().locking_thread()->Write_lock_id
                    &&& cache_perms.spec_index(c).ordering_lock_id()
                        == allocator_cache_lock_id(c)
                    &&& alloc_map.spec_index(alloc_ptr_2m)
                        .cpu_caches.spec_index(c).view().wlocked_by(lctx)
                }
    }

    fn scan_caches_and_alloc(
        krnl: &mut KernelK,
        alloc_ptr_2m: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        container_ptr: RwLockContainerPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(cache_perms): Tracked<&Map<CpuId, LockPerm>>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: Option<(PagePtr, Tracked<LockPerm>)>)
        requires
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(krnl).ctn_mp.dom().contains(container_ptr),
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).allc_2m_mp.dom().contains(alloc_ptr_2m),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m == alloc_ptr_2m,
            old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            thread_effective_quota_2m(old(krnl).thr_mp.spec_index(thread_ptr)) >= 1,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).thr_mp.spec_index(thread_ptr).wlocked_by(old(lctx)),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
            old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_2m_lock_map().dom()
                =~= allocator_cache_key_prefix(alloc_ptr_2m, NUM_CPUS),
            old(lctx).allocator_global_pool_2m_lock_map().dom()
                =~= set![alloc_ptr_2m],
            cache_perms_match_lctx(old(krnl).allc_2m_mp, alloc_ptr_2m, old(lctx), cache_perms),
            old(lctx).held_lock_majors_lt(FREE_PAGE_LOCK_MAJOR),
        ensures
            final(krnl).inv(),
            final(lctx).thread_lock_map().dom().contains(thread_ptr),
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
            final(krnl).allc_4k_mp == old(krnl).allc_4k_mp,
            final(krnl).allc_1g_mp == old(krnl).allc_1g_mp,
            final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, thread_ptr),
            held_threads_unchanged_except(
                old(krnl).thr_mp, final(krnl).thr_mp, old(lctx),
                set![thread_ptr],
            ),
            final(lctx).allocator_2m_lock_maps()
                == old(lctx).allocator_2m_lock_maps(),
            final(krnl).allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom(),
            final(krnl).allc_2m_mp.unchanged_except(&old(krnl).allc_2m_mp, alloc_ptr_2m),
            final(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).quota == old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).quota,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
            ret is None ==> { &&&*final(krnl) == *old(krnl) &&&*final(lctx) == *old(lctx) &&& final(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.view().fold_left(0int, |sum: int, cache: RwLock<AllocatorCache, (), (), NO_KILL_STATE>| { sum + cache.view().linked_list.len() }) == 0 },
            ret is Some ==> {
                &&& final(lctx).kernel_view_locking_state() is Release
                &&& page_ptr_valid(ret.unwrap().0)
                &&& old(krnl).pg_arr.spec_index(page_ptr2page_index(ret.unwrap().0)).view().view().state is Free2m
                &&& !old(krnl).thr_mp.spec_index(thread_ptr).view()
                    .temp_alloc_cache_2m.view().contains(ret.unwrap().0)
                &&& thread_effective_quota_2m(final(krnl).thr_mp.spec_index(thread_ptr)) == thread_effective_quota_2m(old(krnl).thr_mp.spec_index(thread_ptr)) - 1
                &&& index_valid(NUM_PAGES, page_ptr2page_index(ret.unwrap().0))
                &&& final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(ret.unwrap().0))
                &&& final(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool
                    == old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool
                &&& final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.unwrap().0)).view().being_killed() == false
                &&& ret.unwrap().1.view().state() is WriteLock
                &&& ret.unwrap().1.view().thread_id() == final(lctx).thread_id()
                &&& ret.unwrap().1.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.unwrap().0)).view().locking_thread()->Write_lock_id
                &&& final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.unwrap().0)).view()
                    .wlocked_by(final(lctx))
                &&& !old(lctx).page_lock_map().dom().contains(page_ptr2page_index(ret.unwrap().0))
                &&& final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(ret.unwrap().0)), KernelObjId::Page(page_ptr2page_index(ret.unwrap().0))))
                &&& typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(ret.unwrap().0)), TypedHeldLock {
                    lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(ret.unwrap().0)), mode: TypedLockMode::Write,
                })
                &&& cache_perms_match_lctx(final(krnl).allc_2m_mp, alloc_ptr_2m, final(lctx), cache_perms)
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
                &&& final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view()
                    =~= old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().insert(ret.unwrap().0)
                &&& final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.unwrap().0)).view().view().state == (PageState::Owned2m{ thread_ptr })
                &&& final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.unwrap().0)).view().view().owning_container
                    == container_ptr
                &&& final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k
                    == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k
                &&& final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g
                    == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g
                &&& final(krnl).thr_mp.spec_index(thread_ptr).view()
                    .free_quota_pending_fields_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view())
                &&& final(krnl).thr_mp.spec_index(thread_ptr).view().quota_2m
                    == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_2m
                &&& final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k
                    == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k
                &&& final(krnl).thr_mp.spec_index(thread_ptr).view().quota_1g
                    == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_1g
                &&& final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors
                    == old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors
            },
    {
        let mut cpu: CpuId = 0;
        proof {
            assert(lctx.thread_lock_map().dom().contains(thread_ptr)) by {
                reveal(LockedMap::typed_lock_map_aligned);
            };
        }
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
                krnl.allc_2m_mp.dom().contains(alloc_ptr_2m),
                krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m == alloc_ptr_2m,
                krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
                krnl.thr_mp.spec_index(thread_ptr).being_killed() == false,
                thread_effective_quota_2m(krnl.thr_mp.spec_index(thread_ptr)) >= 1,
                thread_lock_perm.state() is WriteLock,
                thread_lock_perm.thread_id() == lctx.thread_id(),
                thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
                krnl.thr_mp.spec_index(thread_ptr).wlocked_by(&*lctx),
                lctx.thread_lock_map().dom().contains(thread_ptr),
                lctx.allocator_quota_2m_lock_map().dom().is_empty(),
                lctx.allocator_cache_2m_lock_map().dom()
                    =~= allocator_cache_key_prefix(alloc_ptr_2m, NUM_CPUS),
                lctx.allocator_global_pool_2m_lock_map().dom()
                    =~= set![alloc_ptr_2m],
                cache_perms_match_lctx(krnl.allc_2m_mp, alloc_ptr_2m, &*lctx, cache_perms),
                lctx.held_lock_majors_lt(FREE_PAGE_LOCK_MAJOR),
                krnl.allc_2m_mp.spec_index(alloc_ptr_2m)
                    .cpu_caches.view().take(cpu as int).fold_left(
                        0int,
                        |sum: int, cache: RwLock<AllocatorCache, (), (), NO_KILL_STATE>| {
                            sum + cache.view().linked_list.len()
                        },
                    ) == 0,
            decreases NUM_CPUS - cpu,
        {
            proof {
                assert(
                    krnl.allc_2m_mp.perms_wf()
                    && krnl.allc_2m_mp.dom().contains(alloc_ptr_2m)
                    && krnl.allc_2m_mp.spec_index(alloc_ptr_2m).wf()
                    && krnl.allc_2m_mp.spec_index(alloc_ptr_2m)
                        .cpu_caches.inv()
                    && krnl.allc_2m_mp.spec_index(alloc_ptr_2m)
                        .cpu_caches_wf()
                    && cache_perms.dom().contains(cpu)
                    && cache_perms.spec_index(cpu).state() is WriteLock
                    && cache_perms.spec_index(cpu).thread_id() == lctx.thread_id()
                    && cache_perms.spec_index(cpu).lock_id()
                        == krnl.allc_2m_mp.spec_index(alloc_ptr_2m)
                            .cpu_caches.spec_index(cpu).view().locking_thread()->Write_lock_id
                    && krnl.allc_2m_mp.spec_index(alloc_ptr_2m)
                        .cpu_caches.spec_index(cpu).view()
                        .write_lock_perm_match(&cache_perms.spec_index(cpu))
                    && krnl.allc_2m_mp.spec_index(alloc_ptr_2m)
                        .cpu_caches.spec_index(cpu).view().being_killed() == false
                ) by { reveal(allocator_perms_wf); reveal(cache_perms_match_lctx); };
            }
            let cache_ref = krnl.allc_2m_mp.borrow_cache(alloc_ptr_2m, cpu, Tracked(cache_perms.tracked_borrow(cpu)));
            assert(cache_ref.linked_list.wf()) by {
                assert(
                    index_valid(NUM_CPUS, cpu)
                    && krnl.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches_wf()
                ) by { reveal(allocator_perms_wf); };
            };
            let cache_len = cache_ref.linked_list.len();
            assert(cache_len == krnl.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cpu).view().view().view().len()) by { cache_ref.linked_list.lemma_len_view(); };
            if cache_len > 0 {
                let tracked selected_cache_perm = cache_perms.tracked_borrow(cpu);
                proof {
                    assert(krnl.thr_mp.dom().contains(thread_ptr)) by {
                        reveal(LockedMap::typed_lock_map_aligned);
                    };
                    assert(page_objects_unlocked_except(
                        krnl.pg_arr, lctx.thread_id(),
                        lctx.page_lock_map().dom(),
                    )) by {
                        reveal(page_objects_unlocked_except);
                        reveal(typed_lock_maps_aligned);
                        reveal(LockedArray::typed_lock_map_aligned);
                    };
                    assert(allocator_objects_unlocked_except_cache_pool(
                        krnl.allc_2m_mp, alloc_ptr_2m, lctx.thread_id(),
                    )) by {
                        reveal(typed_lock_maps_aligned);
                        reveal(UnLockedMap::typed_quota_lock_map_aligned);
                        reveal(UnLockedMap::typed_cache_lock_map_aligned);
                        reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
                    };
                }
                let (page_ptr, Tracked(page_lock_perm)) = pop_stage_2m_page(krnl, alloc_ptr_2m, cpu, thread_ptr, container_ptr, Tracked(&mut *lctx), Tracked(selected_cache_perm), Tracked(thread_lock_perm));
                assert(cache_perms_match_lctx(krnl.allc_2m_mp, alloc_ptr_2m, &*lctx, cache_perms)) by { reveal(cache_perms_match_lctx); };
                return Some((page_ptr, Tracked(page_lock_perm)));
            }
            assert(
                krnl.allc_2m_mp.spec_index(alloc_ptr_2m)
                    .cpu_caches.view().take(cpu as int + 1).fold_left(
                        0int,
                        |sum: int, cache: RwLock<AllocatorCache, (), (), NO_KILL_STATE>| {
                            sum + cache.view().linked_list.len()
                        },
                    ) == 0
            ) by {
                let caches = krnl.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches;
                let cache_seq = caches.view();
                let cache_len_sum = |sum: int, cache: RwLock<AllocatorCache, (), (), NO_KILL_STATE>| {
                        sum + cache.view().linked_list.len()
                    };
                assert(cache_seq.spec_index(cpu as int).view().linked_list.len() == 0) by { caches.lemma_view_index(cpu); };
                assert(cache_seq.take(cpu as int + 1).fold_left(0int, cache_len_sum) == cache_len_sum(cache_seq.take(cpu as int).fold_left(0int, cache_len_sum), cache_seq.spec_index(cpu as int))) by {
                    assert(
                        cache_seq.take(cpu as int + 1).drop_last() =~= cache_seq.take(cpu as int)
                        && cache_seq.take(cpu as int + 1).last() ==
                            cache_seq.spec_index(cpu as int)
                    ) by { cache_seq.lemma_take_succ_push(cpu as int); };
                };
            };
            cpu = cpu + 1;
        }
        assert(
            krnl.allc_2m_mp.spec_index(alloc_ptr_2m)
                .cpu_caches.view().fold_left(
                    0int,
                    |sum: int, cache: RwLock<AllocatorCache, (), (), NO_KILL_STATE>| {
                        sum + cache.view().linked_list.len()
                    },
                ) == 0
        ) by {
            reveal(allocator_perms_wf);
            krnl.allc_2m_mp.spec_index(alloc_ptr_2m)
                .cpu_caches.view().lemma_take_len();
        };
        proof {
            held_threads_unchanged_except_for_unchanged_except(
                old(krnl).thr_mp, krnl.thr_mp, old(lctx), thread_ptr,
            );
        }
        None
    }

} // verus!

verus! {
/// After a failed cache scan (every cpu cache of `alloc_ptr_2m` empty), the
/// container conservation law forces the global pool to be non-empty: the
/// total free-page count equals the pool length (all cache summands are zero),
/// and that total is at least the held thread's `effective_quota_2m >= 1`
/// because every other conservation summand is non-negative.
pub proof fn lemma_scan_fail_pool_nonempty(
    k: &KernelK,
    container_ptr: RwLockContainerPtr,
    alloc_ptr_2m: RwLockPageAllocatorPtr,
    thread_ptr: RwLockThreadPtr,
)
    requires
        k.inv(),
        k.ctn_mp.dom().contains(container_ptr),
        k.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m == alloc_ptr_2m,
        k.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().contains(thread_ptr),
        thread_effective_quota_2m(k.thr_mp.spec_index(thread_ptr)) >= 1,
        k.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.view().fold_left(0int, |sum: int, cache: RwLock<AllocatorCache, (), (), NO_KILL_STATE>| { sum + cache.view().linked_list.len() }) == 0,
    ensures
        k.allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.view().view().len() > 0,
{
    let owned_processes = k.ctn_mp.spec_index(container_ptr).view().owned_processes.view();
    let owned_threads = k.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view();
    assert(k.allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.view().view().len() > 0) by {
        reveal(allocator_perms_wf); reveal(container_allocator_wf); reveal(container_process_wf); reveal(container_thread_wf); reveal(container_process_allocator_quota_2m_wf); reveal(process_perms_wf); reveal(thread_perms_wf);
        lemma_process_effective_quota_2m_fold_nonneg(owned_processes, k.prc_mp);
        lemma_thread_effective_quota_2m_fold_ge_member(owned_threads, k.thr_mp, thread_ptr);
        lemma_thread_direct_pending_2m_fold_nonneg(k.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view(), k.thr_mp);
        lemma_thread_indirect_pending_2m_fold_nonneg(k.ctn_mp.spec_index(container_ptr).view_ghost().owned_indirect_threads.view(), k.thr_mp, k.ctn_mp.spec_index(container_ptr).view_rodata().view().depth as int);
    };
}

}
