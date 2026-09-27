use vstd::prelude::*;
use crate::*;
use super::allocate_free_4k_impl_base::allocate_free_4k_page_k;

verus! {
    #[inline(always)]
    pub fn allocate_free_4k_page(
        krnl: &mut KernelK, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, cpu_id: CpuId,
        Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
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
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
            old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            thread_effective_quota_4k(old(krnl).thr_mp.spec_index(thread_ptr)) >= 1,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_MAJOR),
        ensures
            forall|pt: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(pt)]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread {
                temp_alloc_cache_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k,
                ..old(krnl).thr_mp.spec_index(thread_ptr).view()
            }),
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc,
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container,
            final(krnl).thr_mp.spec_index(thread_ptr).view().upper_container_seq == old(krnl).thr_mp.spec_index(thread_ptr).view().upper_container_seq,
            final(krnl).thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
            final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress == old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress,
            final(krnl).thr_mp.spec_index(thread_ptr).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().blocking_endpoint_ptr,
            final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr,
            thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(ret.0)), TypedHeldLock {
                lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(ret.0)),
                mode: TypedLockMode::Write,
            }),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![thread_ptr]),
            final(steps).nonlock_view() == old(steps).nonlock_view(),
            old(steps).snapshot_k() == *old(krnl) ==> final(steps).view() == old(steps).view(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            page_ptr_valid(ret.0),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(ret.0), TypedLockMode::Write),
            !old(lctx).page_lock_map().dom().contains(page_ptr2page_index(ret.0)),
            final(krnl).thr_mp.dom().contains(thread_ptr),
            typed_lock_map_contains_mode(final(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
            final(krnl).ctn_mp.dom().contains(container_ptr),
            final(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata(),
            held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
            held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
            held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
            held_pages_unchanged_except(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx), set![page_ptr2page_index(ret.0)]),
            held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            !old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(ret.0),
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() =~= old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().insert(ret.0),
            thread_effective_quota_4k(final(krnl).thr_mp.spec_index(thread_ptr)) == thread_effective_quota_4k(old(krnl).thr_mp.spec_index(thread_ptr)) - 1,
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().state == (PageState::Owned4k{ thread_ptr }),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container == container_ptr,
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m,
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_2m == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_2m,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_1g == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_1g,
            final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_fields_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view()),
            final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors == old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors,
    {
        proof { use_type_invariant(&*steps); }
        allocate_free_4k_page_k(krnl, thread_ptr, container_ptr, cpu_id,
            Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm))
    }
}
