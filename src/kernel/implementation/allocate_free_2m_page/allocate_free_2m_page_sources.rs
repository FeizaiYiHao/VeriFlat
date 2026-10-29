use super::super::allocator_cache_spec::*;
use vstd::prelude::*;
use crate::*;
use super::allocate_free_2m_page_pop_impl::pop_stage_2m_page;
use super::allocate_free_2m_impl_base::alloc_2m_scan_all_caches_and_pool;

verus! {
    /// Pops the head 2m page of the write-locked CPU cache, releases the cache, and crosses the step boundary.
    pub(super) fn allocate_free_2m_page_from_cache(
        krnl: &mut KernelK, alloc_ptr_2m: RwLockPageAllocatorPtr, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
        Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Tracked(cache_lock_perm): Tracked<LockPerm>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>, Ghost(entry_krnl): Ghost<KernelK>, Ghost(entry_lctx): Ghost<LocalContext>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            index_valid(NUM_CPUS, cpu_id),
            entry_krnl.thr_mp.dom().contains(thread_ptr),
            entry_krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            entry_krnl.thr_mp.spec_index(thread_ptr).being_killed() == false,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == entry_lctx.thread_id(),
            thread_lock_perm.lock_id() == entry_krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            entry_lctx.kernel_view_locking_state() is Acquire,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), &entry_krnl),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, entry_krnl.ep_mp),
            entry_krnl.irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
            entry_krnl.irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
            entry_krnl.cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            entry_krnl.iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), &entry_krnl),
            thread_effective_quota_2m(entry_krnl.thr_mp.spec_index(thread_ptr)) >= 1,
            typed_lock_map_contains_mode(entry_lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
            typed_lock_maps_aligned(&entry_krnl, &entry_lctx),
            index_valid(NUM_CPUS, entry_lctx.cpu_id()) ==> entry_krnl.cpu_op.view().view()[entry_lctx.cpu_id() as int] is InStep,
            entry_lctx.cpu_lock_map().dom().contains(entry_lctx.cpu_id()),
            held_locks_order_below(&entry_krnl, &entry_lctx, ALLOCATOR_CACHE_4K_MAJOR),
            old(lctx).cpu_id() == entry_lctx.cpu_id(),
            old(krnl).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&entry_krnl, old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(entry_krnl.ep_mp, old(krnl).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&entry_krnl, old(krnl)),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            *old(krnl) == (KernelK { allc_2m_mp: old(krnl).allc_2m_mp, ..entry_krnl }),
            old(lctx).thread_id() == entry_lctx.thread_id(),
            old(lctx).kernel_view_locking_state() == entry_lctx.kernel_view_locking_state(),
            wlock_ensures(entry_krnl.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cpu_id).view(), old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cpu_id).view(),
                entry_krnl.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.lock_id_by_index(cpu_id), old(lctx), cache_lock_perm),
            typed_lock_maps_inserted(&entry_lctx, old(lctx), KernelObjId::AllocatorCache(PageSize::SZ2m, alloc_ptr_2m, cpu_id), TypedHeldLock { lock_id: old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.lock_id_by_index(cpu_id), mode: TypedLockMode::Write }),
            old(krnl).ctn_mp.dom().contains(container_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m == alloc_ptr_2m,
            old(krnl).allc_2m_mp.dom().contains(alloc_ptr_2m),
            old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cpu_id).view().view().view().len() > 0,
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(entry_krnl)),
            old(steps).snapshot_k() == entry_krnl ==> final(steps).view() == old(steps).view(),
            final(lctx).cpu_id() == entry_lctx.cpu_id(),
            index_valid(NUM_CPUS, entry_lctx.cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[entry_lctx.cpu_id() as int].view() == entry_krnl.cpu_hw_cr3_pcid[entry_lctx.cpu_id() as int].view(),
            index_valid(NUM_CPUS, entry_lctx.cpu_id()) ==> final(krnl).cpu_op.view().view()[entry_lctx.cpu_id() as int] == entry_krnl.cpu_op.view().view()[entry_lctx.cpu_id() as int],
            final(krnl).inv(),
            final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == entry_krnl.thr_mp.spec_index(thread_ptr).view().owning_proc,
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == entry_krnl.thr_mp.spec_index(thread_ptr).view().owning_container,
            final(krnl).thr_mp.spec_index(thread_ptr).view().upper_container_seq == entry_krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq,
            final(krnl).thr_mp.spec_index(thread_ptr).view().state == entry_krnl.thr_mp.spec_index(thread_ptr).view().state,
            final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == entry_krnl.thr_mp.spec_index(thread_ptr).view_ghost(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress == entry_krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress,
            final(krnl).thr_mp.spec_index(thread_ptr).view().blocking_endpoint_ptr == entry_krnl.thr_mp.spec_index(thread_ptr).view().blocking_endpoint_ptr,
            final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == entry_krnl.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr,
            thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            final(lctx).thread_id() == entry_lctx.thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_inserted(&entry_lctx, final(lctx), KernelObjId::Page(page_ptr2page_index(ret.0)), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(ret.0)), mode: TypedLockMode::Write }),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            held_threads_unchanged_except(entry_krnl.thr_mp, final(krnl).thr_mp, &entry_lctx, set![thread_ptr]),
            final(steps).snapshot_k() == *final(krnl),
            page_ptr_valid(ret.0),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(ret.0), TypedLockMode::Write),
            !entry_lctx.page_lock_map().dom().contains(page_ptr2page_index(ret.0)),
            final(krnl).thr_mp.dom().contains(thread_ptr),
            typed_lock_map_contains_mode(final(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            held_containers_unchanged(entry_krnl.ctn_mp, final(krnl).ctn_mp, &entry_lctx),
            final(krnl).ctn_mp.dom().contains(container_ptr),
            final(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == entry_krnl.ctn_mp.spec_index(container_ptr).view_rodata(),
            held_processes_unchanged(entry_krnl.prc_mp, final(krnl).prc_mp, &entry_lctx),
            held_endpoints_unchanged(entry_krnl.ep_mp, final(krnl).ep_mp, &entry_lctx),
            held_schedulers_unchanged(entry_krnl.sched_mp, final(krnl).sched_mp, &entry_lctx),
            held_pcid_allocators_unchanged(entry_krnl.pcid_allc_mp, final(krnl).pcid_allc_mp, &entry_lctx),
            held_cpu_sets_unchanged(entry_krnl.cpu_set_mp, final(krnl).cpu_set_mp, &entry_lctx),
            held_pagetables_unchanged(entry_krnl.pt_mp, final(krnl).pt_mp, &entry_lctx),
            held_pagetable_windows_unchanged(entry_krnl.pt_mp, entry_krnl.pt_lower.view(), final(krnl).pt_mp, final(krnl).pt_lower.view(), &entry_lctx),
            held_iommu_tables_unchanged(entry_krnl.it_mp, final(krnl).it_mp, &entry_lctx),
            held_pages_unchanged_except(entry_krnl.pg_arr, final(krnl).pg_arr, &entry_lctx, set![page_ptr2page_index(ret.0)]),
            held_cpus_unchanged(entry_krnl.cpu_arr, final(krnl).cpu_arr, &entry_lctx),
            !entry_krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().contains(ret.0),
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view() =~= entry_krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().insert(ret.0),
            thread_effective_quota_2m(final(krnl).thr_mp.spec_index(thread_ptr)) == thread_effective_quota_2m(entry_krnl.thr_mp.spec_index(thread_ptr)) - 1,
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().state == (PageState::Owned2m { thread_ptr }),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container == container_ptr,
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k == entry_krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k,
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g == entry_krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k == entry_krnl.thr_mp.spec_index(thread_ptr).view().quota_4k,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_2m == entry_krnl.thr_mp.spec_index(thread_ptr).view().quota_2m,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_1g == entry_krnl.thr_mp.spec_index(thread_ptr).view().quota_1g,
            final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_fields_unchanged(&entry_krnl.thr_mp.spec_index(thread_ptr).view()),
            final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors == entry_krnl.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors,
    {
        let (page_ptr, Tracked(page_lock_perm)) = pop_stage_2m_page(krnl, alloc_ptr_2m, Some(cpu_id), thread_ptr, container_ptr, Tracked(&mut *lctx), Tracked(&cache_lock_perm), Tracked(thread_lock_perm));
        krnl.wunlock_allocator_cache_2m(alloc_ptr_2m, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(entry_krnl)) by {
                broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_container_nonlock_fields_and_quotas_unchanged_transitive;
                kernel_thread_write_held_section_implies_u_eq(&entry_krnl, &*krnl, &entry_lctx, &*lctx, thread_ptr);
            };
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
            assert(typed_lock_maps_inserted(&entry_lctx, lctx, KernelObjId::Page(page_ptr2page_index(page_ptr)), TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write })
                && entry_lctx.page_lock_map().dom().subset_of(lctx.page_lock_map().dom())) by {
                map_insert_remove_absent_lemma(entry_lctx.allocator_cache_2m_lock_map(), (alloc_ptr_2m, cpu_id), TypedHeldLock { lock_id: allocator_cache_lock_id(ALLOCATOR_SIZE_2M, cpu_id), mode: TypedLockMode::Write });
            };
            assert({
                &&& krnl.ctn_mp.dom().contains(container_ptr)
                &&& krnl.thr_mp.spec_index(thread_ptr).view().state == entry_krnl.thr_mp.spec_index(thread_ptr).view().state
                &&& krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress == entry_krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress
            }) by { container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr); };
        }
        (page_ptr, Tracked(page_lock_perm))
    }

    /// The CPU cache is empty: allocates from the global pool, or scans every cache and the pool when the pool is empty too.
    pub(super) fn allocate_free_2m_page_from_pool(
        krnl: &mut KernelK, alloc_ptr_2m: RwLockPageAllocatorPtr, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
        Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Tracked(cache_lock_perm): Tracked<LockPerm>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>, Ghost(entry_krnl): Ghost<KernelK>, Ghost(entry_lctx): Ghost<LocalContext>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            index_valid(NUM_CPUS, cpu_id),
            entry_krnl.thr_mp.dom().contains(thread_ptr),
            entry_krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            entry_krnl.thr_mp.spec_index(thread_ptr).being_killed() == false,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == entry_lctx.thread_id(),
            thread_lock_perm.lock_id() == entry_krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            entry_lctx.kernel_view_locking_state() is Acquire,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), &entry_krnl),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, entry_krnl.ep_mp),
            entry_krnl.irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
            entry_krnl.irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
            entry_krnl.cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            entry_krnl.iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), &entry_krnl),
            thread_effective_quota_2m(entry_krnl.thr_mp.spec_index(thread_ptr)) >= 1,
            typed_lock_map_contains_mode(entry_lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
            typed_lock_maps_aligned(&entry_krnl, &entry_lctx),
            index_valid(NUM_CPUS, entry_lctx.cpu_id()) ==> entry_krnl.cpu_op.view().view()[entry_lctx.cpu_id() as int] is InStep,
            entry_lctx.cpu_lock_map().dom().contains(entry_lctx.cpu_id()),
            held_locks_order_below(&entry_krnl, &entry_lctx, ALLOCATOR_CACHE_4K_MAJOR),
            old(lctx).cpu_id() == entry_lctx.cpu_id(),
            old(krnl).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&entry_krnl, old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(entry_krnl.ep_mp, old(krnl).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&entry_krnl, old(krnl)),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            *old(krnl) == (KernelK { allc_2m_mp: old(krnl).allc_2m_mp, ..entry_krnl }),
            old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool == entry_krnl.allc_2m_mp.spec_index(alloc_ptr_2m).global_pool,
            old(lctx).thread_id() == entry_lctx.thread_id(),
            old(lctx).kernel_view_locking_state() == entry_lctx.kernel_view_locking_state(),
            wlock_ensures(entry_krnl.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cpu_id).view(), old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cpu_id).view(),
                entry_krnl.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.lock_id_by_index(cpu_id), old(lctx), cache_lock_perm),
            typed_lock_maps_inserted(&entry_lctx, old(lctx), KernelObjId::AllocatorCache(PageSize::SZ2m, alloc_ptr_2m, cpu_id), TypedHeldLock { lock_id: old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.lock_id_by_index(cpu_id), mode: TypedLockMode::Write }),
            old(krnl).ctn_mp.dom().contains(container_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m == alloc_ptr_2m,
            old(krnl).allc_2m_mp.dom().contains(alloc_ptr_2m),
            old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cpu_id).view().view().view().len() == 0,
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(entry_krnl)),
            old(steps).snapshot_k() == entry_krnl ==> final(steps).view() == old(steps).view(),
            final(lctx).cpu_id() == entry_lctx.cpu_id(),
            index_valid(NUM_CPUS, entry_lctx.cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[entry_lctx.cpu_id() as int].view() == entry_krnl.cpu_hw_cr3_pcid[entry_lctx.cpu_id() as int].view(),
            index_valid(NUM_CPUS, entry_lctx.cpu_id()) ==> final(krnl).cpu_op.view().view()[entry_lctx.cpu_id() as int] == entry_krnl.cpu_op.view().view()[entry_lctx.cpu_id() as int],
            final(krnl).inv(),
            final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == entry_krnl.thr_mp.spec_index(thread_ptr).view().owning_proc,
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == entry_krnl.thr_mp.spec_index(thread_ptr).view().owning_container,
            final(krnl).thr_mp.spec_index(thread_ptr).view().upper_container_seq == entry_krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq,
            final(krnl).thr_mp.spec_index(thread_ptr).view().state == entry_krnl.thr_mp.spec_index(thread_ptr).view().state,
            final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == entry_krnl.thr_mp.spec_index(thread_ptr).view_ghost(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress == entry_krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress,
            final(krnl).thr_mp.spec_index(thread_ptr).view().blocking_endpoint_ptr == entry_krnl.thr_mp.spec_index(thread_ptr).view().blocking_endpoint_ptr,
            final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == entry_krnl.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr,
            thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            final(lctx).thread_id() == entry_lctx.thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_inserted(&entry_lctx, final(lctx), KernelObjId::Page(page_ptr2page_index(ret.0)), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(ret.0)), mode: TypedLockMode::Write }),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            held_threads_unchanged_except(entry_krnl.thr_mp, final(krnl).thr_mp, &entry_lctx, set![thread_ptr]),
            final(steps).snapshot_k() == *final(krnl),
            page_ptr_valid(ret.0),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(ret.0), TypedLockMode::Write),
            !entry_lctx.page_lock_map().dom().contains(page_ptr2page_index(ret.0)),
            final(krnl).thr_mp.dom().contains(thread_ptr),
            typed_lock_map_contains_mode(final(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            held_containers_unchanged(entry_krnl.ctn_mp, final(krnl).ctn_mp, &entry_lctx),
            final(krnl).ctn_mp.dom().contains(container_ptr),
            final(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == entry_krnl.ctn_mp.spec_index(container_ptr).view_rodata(),
            held_processes_unchanged(entry_krnl.prc_mp, final(krnl).prc_mp, &entry_lctx),
            held_endpoints_unchanged(entry_krnl.ep_mp, final(krnl).ep_mp, &entry_lctx),
            held_schedulers_unchanged(entry_krnl.sched_mp, final(krnl).sched_mp, &entry_lctx),
            held_pcid_allocators_unchanged(entry_krnl.pcid_allc_mp, final(krnl).pcid_allc_mp, &entry_lctx),
            held_cpu_sets_unchanged(entry_krnl.cpu_set_mp, final(krnl).cpu_set_mp, &entry_lctx),
            held_pagetables_unchanged(entry_krnl.pt_mp, final(krnl).pt_mp, &entry_lctx),
            held_pagetable_windows_unchanged(entry_krnl.pt_mp, entry_krnl.pt_lower.view(), final(krnl).pt_mp, final(krnl).pt_lower.view(), &entry_lctx),
            held_iommu_tables_unchanged(entry_krnl.it_mp, final(krnl).it_mp, &entry_lctx),
            held_pages_unchanged_except(entry_krnl.pg_arr, final(krnl).pg_arr, &entry_lctx, set![page_ptr2page_index(ret.0)]),
            held_cpus_unchanged(entry_krnl.cpu_arr, final(krnl).cpu_arr, &entry_lctx),
            !entry_krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().contains(ret.0),
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view() =~= entry_krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().insert(ret.0),
            thread_effective_quota_2m(final(krnl).thr_mp.spec_index(thread_ptr)) == thread_effective_quota_2m(entry_krnl.thr_mp.spec_index(thread_ptr)) - 1,
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().state == (PageState::Owned2m { thread_ptr }),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container == container_ptr,
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k == entry_krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k,
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g == entry_krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k == entry_krnl.thr_mp.spec_index(thread_ptr).view().quota_4k,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_2m == entry_krnl.thr_mp.spec_index(thread_ptr).view().quota_2m,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_1g == entry_krnl.thr_mp.spec_index(thread_ptr).view().quota_1g,
            final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_fields_unchanged(&entry_krnl.thr_mp.spec_index(thread_ptr).view()),
            final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors == entry_krnl.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors,
    {
        let Tracked(gp_lock_perm) = krnl.wlock_allocator_global_pool_2m(alloc_ptr_2m, Tracked(&mut *lctx));
        let pool_ref = krnl.allc_2m_mp.borrow_global_pool_typed(alloc_ptr_2m, Ghost(lctx.allocator_global_pool_2m_lock_map()), Tracked(&*lctx), Tracked(&gp_lock_perm));
        let pool_len = pool_ref.len();

        if pool_len > 0 {
            let (page_ptr, Tracked(page_lock_perm)) = pop_stage_2m_page(krnl, alloc_ptr_2m, None, thread_ptr, container_ptr, Tracked(&mut *lctx), Tracked(&gp_lock_perm), Tracked(thread_lock_perm));
            krnl.wunlock_allocator_global_pool_2m(alloc_ptr_2m, Tracked(&mut *lctx), Tracked(gp_lock_perm));
            krnl.wunlock_allocator_cache_2m(alloc_ptr_2m, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm));
            proof {
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(entry_krnl)) by {
                    broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_container_nonlock_fields_and_quotas_unchanged_transitive;
                    kernel_thread_write_held_section_implies_u_eq(&entry_krnl, &*krnl, &entry_lctx, &*lctx, thread_ptr);
                };
                krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
                assert(typed_lock_maps_inserted(&entry_lctx, lctx, KernelObjId::Page(page_ptr2page_index(page_ptr)), TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write })
                    && entry_lctx.page_lock_map().dom().subset_of(lctx.page_lock_map().dom())) by {
                    map_insert_remove_absent_lemma(entry_lctx.allocator_cache_2m_lock_map(), (alloc_ptr_2m, cpu_id), TypedHeldLock { lock_id: allocator_cache_lock_id(ALLOCATOR_SIZE_2M, cpu_id), mode: TypedLockMode::Write });
                    map_insert_remove_absent_lemma(entry_lctx.allocator_global_pool_2m_lock_map(), alloc_ptr_2m, TypedHeldLock { lock_id: entry_krnl.allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.lock_id(), mode: TypedLockMode::Write });
                };
                assert({
                    &&& krnl.ctn_mp.dom().contains(container_ptr)
                    &&& krnl.thr_mp.spec_index(thread_ptr).view().state == entry_krnl.thr_mp.spec_index(thread_ptr).view().state
                    &&& krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress == entry_krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress
                }) by { container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr); };
            }
            return (page_ptr, Tracked(page_lock_perm));
        }

        krnl.wunlock_allocator_global_pool_2m(alloc_ptr_2m, Tracked(&mut *lctx), Tracked(gp_lock_perm));
        krnl.wunlock_allocator_cache_2m(alloc_ptr_2m, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(entry_krnl)) by {
                broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_container_nonlock_fields_and_quotas_unchanged_transitive;
                kernel_thread_write_held_section_implies_u_eq(&entry_krnl, &*krnl, &entry_lctx, &*lctx, thread_ptr);
            };
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
            assert(typed_lock_maps_unchanged(&entry_lctx, lctx)) by {
                map_insert_remove_absent_lemma(entry_lctx.allocator_cache_2m_lock_map(), (alloc_ptr_2m, cpu_id), TypedHeldLock { lock_id: allocator_cache_lock_id(ALLOCATOR_SIZE_2M, cpu_id), mode: TypedLockMode::Write });
                map_insert_remove_absent_lemma(entry_lctx.allocator_global_pool_2m_lock_map(), alloc_ptr_2m, TypedHeldLock { lock_id: entry_krnl.allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.lock_id(), mode: TypedLockMode::Write });
            };
            assert(krnl.ctn_mp.dom().contains(container_ptr)) by { container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr); };
        }
        let ret = alloc_2m_scan_all_caches_and_pool(krnl, thread_ptr, container_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm));
        ret
    }
}
