use vstd::prelude::*;
use crate::*;

verus! {
/// Write-hold the 4K and then the 2M global pools of the marked container `container_ptr`'s allocators `a4` and `a2`
/// and of the killer's container `owner_ptr`'s allocators `o4` and `o2`, each pair in container order.
pub(crate) fn kill_container_wlock_pool_pairs(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, container_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, a4: RwLockPageAllocatorPtr,
    o4: RwLockPageAllocatorPtr, a2: RwLockPageAllocatorPtr, o2: RwLockPageAllocatorPtr, Tracked(pools_4k): Tracked<&mut Map<RwLockPageAllocatorPtr, LockPerm>>,
    Tracked(pools_2m): Tracked<&mut Map<RwLockPageAllocatorPtr, LockPerm>>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        forall|p: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(p)] old(lctx).page_lock_map().dom().contains(p) ==> old(krnl).pg_arr.spec_index(p).view().view().orders_below_allocator_locks(),
        forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)] old(lctx).thread_lock_map().dom().contains(held_thread) ==> !(old(krnl).thr_mp.spec_index(held_thread).view().state is SCHEDULED),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty() && old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty() && old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty() && old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        container_ptr != owner_ptr,
        old(krnl).allc_4k_mp.dom().contains(a4) && old(krnl).allc_4k_mp.dom().contains(o4) && old(krnl).allc_2m_mp.dom().contains(a2) && old(krnl).allc_2m_mp.dom().contains(o2),
        old(krnl).allc_4k_mp.spec_index(a4).owning_container == container_ptr && old(krnl).allc_4k_mp.spec_index(o4).owning_container == owner_ptr,
        old(krnl).allc_2m_mp.spec_index(a2).owning_container == container_ptr && old(krnl).allc_2m_mp.spec_index(o2).owning_container == owner_ptr,
        old(pools_4k).dom().is_empty() && old(pools_2m).dom().is_empty(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        *final(krnl) == (KernelK { allc_4k_mp: final(krnl).allc_4k_mp, allc_2m_mp: final(krnl).allc_2m_mp, ..*old(krnl) }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_cache_4k_lock_map() == old(lctx).allocator_cache_4k_lock_map(),
        final(lctx).allocator_cache_2m_lock_map() == old(lctx).allocator_cache_2m_lock_map(),
        final(lctx).allocator_cache_1g_lock_map() == old(lctx).allocator_cache_1g_lock_map(),
        final(lctx).allocator_quota_4k_lock_map() == old(lctx).allocator_quota_4k_lock_map(),
        final(lctx).allocator_quota_2m_lock_map() == old(lctx).allocator_quota_2m_lock_map(),
        final(lctx).allocator_quota_1g_lock_map() == old(lctx).allocator_quota_1g_lock_map(),
        final(lctx).allocator_global_pool_1g_lock_map() == old(lctx).allocator_global_pool_1g_lock_map(),
        final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
        final(krnl).allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom(),
        forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_4k_mp.spec_index(a)] final(krnl).allc_4k_mp.dom().contains(a) ==> {
            &&& final(krnl).allc_4k_mp.spec_index(a).cpu_caches == old(krnl).allc_4k_mp.spec_index(a).cpu_caches
            &&& final(krnl).allc_4k_mp.spec_index(a).quota == old(krnl).allc_4k_mp.spec_index(a).quota
            &&& final(krnl).allc_4k_mp.spec_index(a).owning_container == old(krnl).allc_4k_mp.spec_index(a).owning_container
        },
        forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_2m_mp.spec_index(a)] final(krnl).allc_2m_mp.dom().contains(a) ==> {
            &&& final(krnl).allc_2m_mp.spec_index(a).cpu_caches == old(krnl).allc_2m_mp.spec_index(a).cpu_caches
            &&& final(krnl).allc_2m_mp.spec_index(a).quota == old(krnl).allc_2m_mp.spec_index(a).quota
            &&& final(krnl).allc_2m_mp.spec_index(a).owning_container == old(krnl).allc_2m_mp.spec_index(a).owning_container
        },
        final(lctx).allocator_global_pool_4k_lock_map().dom() == set![a4, o4],
        final(pools_4k).dom() == set![a4, o4],
        typed_lock_map_contains_mode(final(lctx).allocator_global_pool_4k_lock_map(), a4, TypedLockMode::Write) && typed_lock_map_contains_mode(final(lctx).allocator_global_pool_4k_lock_map(), o4, TypedLockMode::Write),
        final(pools_4k)[a4].state() is WriteLock && final(pools_4k)[a4].thread_id() == final(lctx).thread_id(),
        final(pools_4k)[a4].lock_id() == final(krnl).allc_4k_mp.spec_index(a4).global_pool.locking_thread()->Write_lock_id,
        final(pools_4k)[o4].state() is WriteLock && final(pools_4k)[o4].thread_id() == final(lctx).thread_id(),
        final(pools_4k)[o4].lock_id() == final(krnl).allc_4k_mp.spec_index(o4).global_pool.locking_thread()->Write_lock_id,
        final(lctx).allocator_global_pool_2m_lock_map().dom() == set![a2, o2],
        final(pools_2m).dom() == set![a2, o2],
        typed_lock_map_contains_mode(final(lctx).allocator_global_pool_2m_lock_map(), a2, TypedLockMode::Write) && typed_lock_map_contains_mode(final(lctx).allocator_global_pool_2m_lock_map(), o2, TypedLockMode::Write),
        final(pools_2m)[a2].state() is WriteLock && final(pools_2m)[a2].thread_id() == final(lctx).thread_id(),
        final(pools_2m)[a2].lock_id() == final(krnl).allc_2m_mp.spec_index(a2).global_pool.locking_thread()->Write_lock_id,
        final(pools_2m)[o2].state() is WriteLock && final(pools_2m)[o2].thread_id() == final(lctx).thread_id(),
        final(pools_2m)[o2].lock_id() == final(krnl).allc_2m_mp.spec_index(o2).global_pool.locking_thread()->Write_lock_id,
{
    if container_ptr < owner_ptr {
        let Tracked(perm) = krnl.wlock_allocator_global_pool_4k_ordered(a4, Tracked(&mut *lctx));
        proof { pools_4k.tracked_insert(a4, perm); }
        let Tracked(perm) = krnl.wlock_allocator_global_pool_4k_ordered(o4, Tracked(&mut *lctx));
        proof { pools_4k.tracked_insert(o4, perm); }
        let Tracked(perm) = krnl.wlock_allocator_global_pool_2m_ordered(a2, Tracked(&mut *lctx));
        proof { pools_2m.tracked_insert(a2, perm); }
        let Tracked(perm) = krnl.wlock_allocator_global_pool_2m_ordered(o2, Tracked(&mut *lctx));
        proof { pools_2m.tracked_insert(o2, perm); }
    } else {
        let Tracked(perm) = krnl.wlock_allocator_global_pool_4k_ordered(o4, Tracked(&mut *lctx));
        proof { pools_4k.tracked_insert(o4, perm); }
        let Tracked(perm) = krnl.wlock_allocator_global_pool_4k_ordered(a4, Tracked(&mut *lctx));
        proof { pools_4k.tracked_insert(a4, perm); }
        let Tracked(perm) = krnl.wlock_allocator_global_pool_2m_ordered(o2, Tracked(&mut *lctx));
        proof { pools_2m.tracked_insert(o2, perm); }
        let Tracked(perm) = krnl.wlock_allocator_global_pool_2m_ordered(a2, Tracked(&mut *lctx));
        proof { pools_2m.tracked_insert(a2, perm); }
    }
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        assert(lctx.allocator_global_pool_4k_lock_map().dom() =~= set![a4, o4] && pools_4k.dom() =~= set![a4, o4]);
        assert(lctx.allocator_global_pool_2m_lock_map().dom() =~= set![a2, o2] && pools_2m.dom() =~= set![a2, o2]);
    }
}

/// Write-hold the 4K and then the 2M quotas of the marked container `container_ptr`'s allocators `a4` and `a2` and of
/// the killer's container `owner_ptr`'s allocators `o4` and `o2`, each pair in container order.
pub(crate) fn kill_container_wlock_quota_pairs(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, container_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, a4: RwLockPageAllocatorPtr,
    o4: RwLockPageAllocatorPtr, a2: RwLockPageAllocatorPtr, o2: RwLockPageAllocatorPtr, Tracked(quotas_4k): Tracked<&mut Map<RwLockPageAllocatorPtr, LockPerm>>,
    Tracked(quotas_2m): Tracked<&mut Map<RwLockPageAllocatorPtr, LockPerm>>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        forall|p: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(p)] old(lctx).page_lock_map().dom().contains(p) ==> old(krnl).pg_arr.spec_index(p).view().view().orders_below_allocator_locks(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty() && old(lctx).allocator_quota_2m_lock_map().dom().is_empty() && old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        container_ptr != owner_ptr,
        old(krnl).allc_4k_mp.dom().contains(a4) && old(krnl).allc_4k_mp.dom().contains(o4) && old(krnl).allc_2m_mp.dom().contains(a2) && old(krnl).allc_2m_mp.dom().contains(o2),
        old(krnl).allc_4k_mp.spec_index(a4).owning_container == container_ptr && old(krnl).allc_4k_mp.spec_index(o4).owning_container == owner_ptr,
        old(krnl).allc_2m_mp.spec_index(a2).owning_container == container_ptr && old(krnl).allc_2m_mp.spec_index(o2).owning_container == owner_ptr,
        old(quotas_4k).dom().is_empty() && old(quotas_2m).dom().is_empty(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        *final(krnl) == (KernelK { allc_4k_mp: final(krnl).allc_4k_mp, allc_2m_mp: final(krnl).allc_2m_mp, ..*old(krnl) }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_cache_4k_lock_map() == old(lctx).allocator_cache_4k_lock_map(),
        final(lctx).allocator_cache_2m_lock_map() == old(lctx).allocator_cache_2m_lock_map(),
        final(lctx).allocator_cache_1g_lock_map() == old(lctx).allocator_cache_1g_lock_map(),
        final(lctx).allocator_global_pool_4k_lock_map() == old(lctx).allocator_global_pool_4k_lock_map(),
        final(lctx).allocator_global_pool_2m_lock_map() == old(lctx).allocator_global_pool_2m_lock_map(),
        final(lctx).allocator_global_pool_1g_lock_map() == old(lctx).allocator_global_pool_1g_lock_map(),
        final(lctx).allocator_quota_1g_lock_map() == old(lctx).allocator_quota_1g_lock_map(),
        final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
        final(krnl).allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom(),
        forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_4k_mp.spec_index(a)] final(krnl).allc_4k_mp.dom().contains(a) ==> {
            &&& final(krnl).allc_4k_mp.spec_index(a).cpu_caches == old(krnl).allc_4k_mp.spec_index(a).cpu_caches
            &&& final(krnl).allc_4k_mp.spec_index(a).global_pool == old(krnl).allc_4k_mp.spec_index(a).global_pool
            &&& final(krnl).allc_4k_mp.spec_index(a).quota.view() == old(krnl).allc_4k_mp.spec_index(a).quota.view()
            &&& final(krnl).allc_4k_mp.spec_index(a).owning_container == old(krnl).allc_4k_mp.spec_index(a).owning_container
        },
        forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_2m_mp.spec_index(a)] final(krnl).allc_2m_mp.dom().contains(a) ==> {
            &&& final(krnl).allc_2m_mp.spec_index(a).cpu_caches == old(krnl).allc_2m_mp.spec_index(a).cpu_caches
            &&& final(krnl).allc_2m_mp.spec_index(a).global_pool == old(krnl).allc_2m_mp.spec_index(a).global_pool
            &&& final(krnl).allc_2m_mp.spec_index(a).quota.view() == old(krnl).allc_2m_mp.spec_index(a).quota.view()
            &&& final(krnl).allc_2m_mp.spec_index(a).owning_container == old(krnl).allc_2m_mp.spec_index(a).owning_container
        },
        final(lctx).allocator_quota_4k_lock_map().dom() == set![a4, o4],
        final(quotas_4k).dom() == set![a4, o4],
        typed_lock_map_contains_mode(final(lctx).allocator_quota_4k_lock_map(), a4, TypedLockMode::Write) && typed_lock_map_contains_mode(final(lctx).allocator_quota_4k_lock_map(), o4, TypedLockMode::Write),
        final(quotas_4k)[a4].state() is WriteLock && final(quotas_4k)[a4].thread_id() == final(lctx).thread_id(),
        final(quotas_4k)[a4].lock_id() == final(krnl).allc_4k_mp.spec_index(a4).quota.locking_thread()->Write_lock_id,
        final(quotas_4k)[o4].state() is WriteLock && final(quotas_4k)[o4].thread_id() == final(lctx).thread_id(),
        final(quotas_4k)[o4].lock_id() == final(krnl).allc_4k_mp.spec_index(o4).quota.locking_thread()->Write_lock_id,
        final(lctx).allocator_quota_2m_lock_map().dom() == set![a2, o2],
        final(quotas_2m).dom() == set![a2, o2],
        typed_lock_map_contains_mode(final(lctx).allocator_quota_2m_lock_map(), a2, TypedLockMode::Write) && typed_lock_map_contains_mode(final(lctx).allocator_quota_2m_lock_map(), o2, TypedLockMode::Write),
        final(quotas_2m)[a2].state() is WriteLock && final(quotas_2m)[a2].thread_id() == final(lctx).thread_id(),
        final(quotas_2m)[a2].lock_id() == final(krnl).allc_2m_mp.spec_index(a2).quota.locking_thread()->Write_lock_id,
        final(quotas_2m)[o2].state() is WriteLock && final(quotas_2m)[o2].thread_id() == final(lctx).thread_id(),
        final(quotas_2m)[o2].lock_id() == final(krnl).allc_2m_mp.spec_index(o2).quota.locking_thread()->Write_lock_id,
{
    if container_ptr < owner_ptr {
        let Tracked(perm) = krnl.wlock_allocator_quota_4k_ordered(a4, Tracked(&mut *lctx));
        proof { quotas_4k.tracked_insert(a4, perm); }
        let Tracked(perm) = krnl.wlock_allocator_quota_4k_ordered(o4, Tracked(&mut *lctx));
        proof { quotas_4k.tracked_insert(o4, perm); }
        let Tracked(perm) = krnl.wlock_allocator_quota_2m_ordered(a2, Tracked(&mut *lctx));
        proof { quotas_2m.tracked_insert(a2, perm); }
        let Tracked(perm) = krnl.wlock_allocator_quota_2m_ordered(o2, Tracked(&mut *lctx));
        proof { quotas_2m.tracked_insert(o2, perm); }
    } else {
        let Tracked(perm) = krnl.wlock_allocator_quota_4k_ordered(o4, Tracked(&mut *lctx));
        proof { quotas_4k.tracked_insert(o4, perm); }
        let Tracked(perm) = krnl.wlock_allocator_quota_4k_ordered(a4, Tracked(&mut *lctx));
        proof { quotas_4k.tracked_insert(a4, perm); }
        let Tracked(perm) = krnl.wlock_allocator_quota_2m_ordered(o2, Tracked(&mut *lctx));
        proof { quotas_2m.tracked_insert(o2, perm); }
        let Tracked(perm) = krnl.wlock_allocator_quota_2m_ordered(a2, Tracked(&mut *lctx));
        proof { quotas_2m.tracked_insert(a2, perm); }
    }
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        assert(lctx.allocator_quota_4k_lock_map().dom() =~= set![a4, o4] && quotas_4k.dom() =~= set![a4, o4]);
        assert(lctx.allocator_quota_2m_lock_map().dom() =~= set![a2, o2] && quotas_2m.dom() =~= set![a2, o2]);
    }
}
} // verus!
