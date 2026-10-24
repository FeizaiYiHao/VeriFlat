use vstd::prelude::*;
use crate::*;

verus! {
/// Write-locks the owner allocator's 4K cache on `cpu_id` and, when the cache is full, drains one batch into the global pool under its own step boundary, so that the cache has room
/// for the reclaimed page. The cache lock stays held.
pub fn reclaim_last_lock_4k_cache_with_room(krnl: &mut KernelK, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>) -> (ret: Tracked<LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        *old(krnl) == (KernelK { pg_arr: old(krnl).pg_arr, ..old(steps).snapshot_k() }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).allc_4k_mp.dom().contains(allocator_ptr),
    ensures
        final(steps).view() == old(steps).view(),
        final(steps).nonlock_view() == old(steps).nonlock_view(),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, allc_4k_mp: final(krnl).allc_4k_mp, ..final(steps).snapshot_k() }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::AllocatorCache(PageSize::SZ4k, allocator_ptr, cpu_id), final(lctx).allocator_cache_4k_lock_map().spec_index((allocator_ptr, cpu_id))),
        typed_lock_map_contains_mode(final(lctx).allocator_cache_4k_lock_map(), (allocator_ptr, cpu_id), TypedLockMode::Write),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).allc_4k_mp.dom().contains(allocator_ptr),
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() < ALLOCATOR_MAX_WATERMARK,
        ret.view().state() is WriteLock,
        ret.view().thread_id() == old(lctx).thread_id(),
        ret.view().lock_id() == final(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_threads_unchanged(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        held_pagetable_windows_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), final(krnl).pt_mp, final(krnl).pt_lower.view(), old(lctx)),
        forall|p: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(p)] #![trigger final(krnl).pg_arr.spec_index(p)] old(lctx).page_lock_map().dom().contains(p)
            ==> final(krnl).ctn_mp.spec_index(old(krnl).pg_arr.spec_index(p).view().view().owning_container).view_rodata() == old(krnl).ctn_mp.spec_index(old(krnl).pg_arr.spec_index(p).view().view().owning_container).view_rodata(),
{
    proof {
        assert(held_containers_unchanged(krnl.ctn_mp, krnl.ctn_mp, lctx) && held_processes_unchanged(krnl.prc_mp, krnl.prc_mp, lctx) && held_threads_unchanged(krnl.thr_mp, krnl.thr_mp, lctx)
            && held_pagetables_unchanged(krnl.pt_mp, krnl.pt_mp, lctx) && held_iommu_tables_unchanged(krnl.it_mp, krnl.it_mp, lctx) && held_pages_unchanged(krnl.pg_arr, krnl.pg_arr, lctx)
            && held_cpus_unchanged(krnl.cpu_arr, krnl.cpu_arr, lctx)) by { held_kernel_objects_unchanged_reflexive(krnl, lctx); };
    }
    let Tracked(cache_perm) = krnl.wlock_allocator_cache_4k(allocator_ptr, cpu_id, Tracked(&mut *lctx));
    let cache = krnl.allc_4k_mp.borrow_cache_typed(allocator_ptr, cpu_id, Ghost(lctx.allocator_cache_4k_lock_map()), Tracked(&*lctx), Tracked(&cache_perm));
    if cache.linked_list.len() == ALLOCATOR_MAX_WATERMARK {
        let Tracked(pool_perm) = krnl.wlock_allocator_global_pool_4k(allocator_ptr, Tracked(&mut *lctx));
        proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
        proof { assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; }; }
        proof { kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl); }
        drain_4k_cache_batch(krnl, allocator_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&cache_perm), Tracked(&pool_perm));
        krnl.wunlock_allocator_global_pool_4k(allocator_ptr, Tracked(&mut *lctx), Tracked(pool_perm));
        proof {
            kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
            assert(lctx.allocator_global_pool_4k_lock_map() =~= old(lctx).allocator_global_pool_4k_lock_map());
        }
    }
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    Tracked(cache_perm)
}
}
