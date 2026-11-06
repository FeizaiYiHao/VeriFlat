use vstd::prelude::*;
use crate::*;
use super::allocate_free_1g_page_pop::pop_stage_1g_page;
#[cfg(verus_keep_ghost)]
use super::allocate_free_1g_page_lemmas::thread_effective_quota_1g_positive_implies_global_pool_1g_nonempty;

verus! {
    /// Allocate a single 1G page from the global pool of the container's 1G allocator (1G pages never enter a CPU cache). Caller holds the allocating thread's write-lock.
    pub fn allocate_free_1g_page(
        krnl: &mut KernelK, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>, Tracked(thread_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(krnl).inv(),
            old(krnl).thrd_mp.dom().contains(thrd_ptr),
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
            old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == false,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            old(lctx).kernel_view_locking_state() is Acquire,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
            old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            thread_effective_quota_1g(old(krnl).thrd_mp.spec_index(thrd_ptr)) >= 1,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
            old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(krnl))),
            old(steps).snapshot_k() == *old(krnl) ==> final(steps).view() == old(steps).view(),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] == old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int],
            final(krnl).inv(),
            final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == false,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().upper_container_seq == old(krnl).thrd_mp.spec_index(thrd_ptr).view().upper_container_seq,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().state == old(krnl).thrd_mp.spec_index(thrd_ptr).view().state,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress == old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { temp_alloc_cache_1g: final(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().blocking_endpoint_ptr == old(krnl).thrd_mp.spec_index(thrd_ptr).view().blocking_endpoint_ptr,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr,
            thread_lock_perm.lock_id() == final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(ret.0)), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(ret.0)), mode: TypedLockMode::Write }),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            held_threads_unchanged_except(old(krnl).thrd_mp, final(krnl).thrd_mp, old(lctx), set![thrd_ptr]),
            final(steps).snapshot_k() == *final(krnl),
            page_ptr_valid(ret.0),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(ret.0), TypedLockMode::Write),
            !old(lctx).page_lock_map().dom().contains(page_ptr2page_index(ret.0)),
            final(krnl).thrd_mp.dom().contains(thrd_ptr),
            typed_lock_map_contains_mode(final(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
            final(krnl).ctn_mp.dom().contains(ctn_ptr),
            final(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata(),
            held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
            held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
            held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
            held_pagetable_windows_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), final(krnl).pt_mp, final(krnl).pt_lower.view(), old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
            held_pages_unchanged_except(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx), set![page_ptr2page_index(ret.0)]),
            held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
            !old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view().contains(ret.0),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view() =~= old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view().insert(ret.0),
            thread_effective_quota_1g(final(krnl).thrd_mp.spec_index(thrd_ptr)) == thread_effective_quota_1g(old(krnl).thrd_mp.spec_index(thrd_ptr)) - 1,
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().state == (PageState::Owned1g { thread_ptr: thrd_ptr }),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container == ctn_ptr,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k == old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_2m == old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_2m,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k == old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_1g == old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_1g,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_2m == old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_2m,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_fields_unchanged(&old(krnl).thrd_mp.spec_index(thrd_ptr).view()),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors == old(krnl).thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors,
    {
        assert({
            &&& krnl.ctn_mp.dom().contains(ctn_ptr)
            &&& krnl.ctn_mp.view().spec_index(ctn_ptr).is_init()
            &&& krnl.ctn_mp.view().spec_index(ctn_ptr).addr() == ctn_ptr
            &&& krnl.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_threads.view().contains(thrd_ptr)
        }) by { container_thread_wf_thread_at(krnl.ctn_mp, krnl.thrd_mp, thrd_ptr); container_perms_wf_at(krnl.ctn_mp, ctn_ptr); };
        let alloc_ptr_1g = krnl.ctn_mp.borrow_rodata(ctn_ptr).borrow().allocator_ptr_1g;
        assert(krnl.allc_1g_mp.dom().contains(alloc_ptr_1g) && krnl.allc_1g_mp.spec_index(alloc_ptr_1g).global_pool.view().len() > 0) by {
            container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, ctn_ptr);
            thread_effective_quota_1g_positive_implies_global_pool_1g_nonempty(&*krnl, ctn_ptr, alloc_ptr_1g, thrd_ptr);
        };
        let Tracked(pool_lock_perm) = krnl.wlock_allocator_global_pool_1g_ordered(alloc_ptr_1g, Tracked(&mut *lctx));
        let ghost pool_krnl = *krnl;
        let ghost pool_lctx = *lctx;
        let (pg_ptr, Tracked(page_lock_perm)) = pop_stage_1g_page(krnl, alloc_ptr_1g, thrd_ptr, ctn_ptr, Tracked(&mut *lctx), Tracked(&pool_lock_perm), Tracked(thread_lock_perm));
        krnl.wunlock_allocator_global_pool_1g(alloc_ptr_1g, Tracked(&mut *lctx), Tracked(pool_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by {
                broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_container_nonlock_fields_and_quotas_unchanged_transitive;
                kernel_thread_write_held_section_implies_u_eq(old(krnl), &*krnl, old(lctx), &*lctx, thrd_ptr);
            };
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
            assert(typed_lock_maps_inserted(old(lctx), lctx, KernelObjId::Page(page_ptr2page_index(pg_ptr)), TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_ptr2page_index(pg_ptr)), mode: TypedLockMode::Write })
                && old(lctx).page_lock_map().dom().subset_of(lctx.page_lock_map().dom())) by {
                map_insert_remove_absent_lemma(old(lctx).allocator_global_pool_1g_lock_map(), alloc_ptr_1g, TypedHeldLock { lock_id: old(krnl).allc_1g_mp.spec_index(alloc_ptr_1g).global_pool.lock_id(), mode: TypedLockMode::Write });
            };
            assert({
                &&& krnl.ctn_mp.dom().contains(ctn_ptr)
                &&& krnl.thrd_mp.spec_index(thrd_ptr).view().state == old(krnl).thrd_mp.spec_index(thrd_ptr).view().state
                &&& krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress == old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress
            }) by { container_thread_wf_thread_at(krnl.ctn_mp, krnl.thrd_mp, thrd_ptr); };
        }
        (pg_ptr, Tracked(page_lock_perm))
    }
} // verus!
