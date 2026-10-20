use vstd::prelude::*;
use vstd::simple_pptr::PointsTo;
use crate::*;

verus! {
/// In a released view, retire the scheduler `scheduler_ptr`, whose run queues are empty and whose every shard the caller
/// write-holds through `shard_perms`: it leaves its map and its shard locks leave `lctx`.
pub(crate) fn kill_container_retire_scheduler_object(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, scheduler_ptr: RwLockSchedulerPtr, Tracked(shard_perms): Tracked<Map<CpuId, LockPerm>>,
) -> (ret: Tracked<PagePerm4k>)
    requires
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        old(krnl).sched_mp.perms_wf(),
        old(krnl).sched_mp.dom().contains(scheduler_ptr),
        forall|i: CpuId| #![trigger shard_perms.dom().contains(i)] index_valid(NUM_CPUS, i) ==> {
            &&& shard_perms.dom().contains(i)
            &&& shard_perms[i].state() is WriteLock
            &&& shard_perms[i].thread_id() == old(lctx).thread_id()
            &&& old(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(i).view().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: shard_perms[i].lock_id() })
            &&& old(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(i).view().view().queue.view().len() == 0
            &&& typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (scheduler_ptr, i), TypedLockMode::Write)
        },
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map().remove_keys(old(lctx).scheduler_lock_map().dom().filter(|k: (RwLockSchedulerPtr, CpuId)| k.0 == scheduler_ptr)),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        *final(krnl) == (KernelK { sched_mp: final(krnl).sched_mp, ..*old(krnl) }),
        final(krnl).sched_mp.perms_wf(),
        final(krnl).sched_mp.dom() =~= old(krnl).sched_mp.dom().remove(scheduler_ptr),
        forall|s: RwLockSchedulerPtr| #![trigger final(krnl).sched_mp.spec_index(s)] final(krnl).sched_mp.dom().contains(s) ==> final(krnl).sched_mp.spec_index(s) == old(krnl).sched_mp.spec_index(s),
        ret.view().is_init(),
        ret.view().addr() == scheduler_ptr,
{
    proof { reveal(UnLockedMap::typed_shard_lock_map_aligned); }
    let Tracked(scheduler_perm) = krnl.sched_mp.remove_with_perm(scheduler_ptr);
    let ret = retype_scheduler_to_4k_page_perm(scheduler_ptr, Tracked(scheduler_perm), Tracked(shard_perms), Tracked(&mut *lctx));
    proof { assert(typed_lock_maps_aligned(krnl, &*lctx)) by { reveal(UnLockedMap::typed_shard_lock_map_aligned); }; }
    ret
}

/// In a released view, retire the marked cpu set `cpu_set_ptr`, write-held through `lock_perm`: it leaves its map and
/// its lock leaves `lctx`.
pub(crate) fn kill_container_retire_cpu_set_object(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_set_ptr: RwLockCpuSetPtr, Tracked(lock_perm): Tracked<LockPerm>)
    -> (ret: Tracked<PagePerm4k>)
    requires
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        old(krnl).cpu_set_mp.perms_wf(),
        old(krnl).cpu_set_mp.dom().contains(cpu_set_ptr),
        old(krnl).cpu_set_mp.spec_index(cpu_set_ptr).is_init(),
        old(krnl).cpu_set_mp.spec_index(cpu_set_ptr).being_killed(),
        typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), cpu_set_ptr, TypedLockMode::Write),
        lock_perm.state() is WriteLock,
        lock_perm.thread_id() == old(lctx).thread_id(),
        lock_perm.lock_id() == old(krnl).cpu_set_mp.spec_index(cpu_set_ptr).locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::CpuSet(cpu_set_ptr)),
        *final(krnl) == (KernelK { cpu_set_mp: final(krnl).cpu_set_mp, ..*old(krnl) }),
        final(krnl).cpu_set_mp.perms_wf(),
        final(krnl).cpu_set_mp.dom() =~= old(krnl).cpu_set_mp.dom().remove(cpu_set_ptr),
        forall|s: RwLockCpuSetPtr| #![trigger final(krnl).cpu_set_mp.spec_index(s)] final(krnl).cpu_set_mp.dom().contains(s) ==> final(krnl).cpu_set_mp.spec_index(s) == old(krnl).cpu_set_mp.spec_index(s),
        forall|s: RwLockCpuSetPtr| #![trigger final(krnl).cpu_set_mp.lock_id_by_key(s)] final(krnl).cpu_set_mp.dom().contains(s) ==> final(krnl).cpu_set_mp.lock_id_by_key(s) == old(krnl).cpu_set_mp.lock_id_by_key(s),
        ret.view().is_init(),
        ret.view().addr() == cpu_set_ptr,
{
    proof { krnl.cpu_set_mp.typed_lock_map_aligned_write_at(lctx.cpu_set_lock_map(), lctx.thread_id(), cpu_set_ptr); }
    let Tracked(cpu_set_perm) = krnl.cpu_set_mp.remove_with_perm(cpu_set_ptr);
    let ret = retype_cpu_set_rwlock_to_4k_page_perm(cpu_set_ptr, Tracked(cpu_set_perm), Tracked(lock_perm), Tracked(&mut *lctx));
    proof { assert(typed_lock_maps_aligned(krnl, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); }; }
    ret
}

/// In a released view, retire the PCID allocator `allocator_ptr`, write-held through `lock_perm`: it leaves its map and
/// its lock leaves `lctx`.
pub(crate) fn kill_container_retire_pcid_allocator_object(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, allocator_ptr: RwLockPcidAllocatorPtr, Tracked(lock_perm): Tracked<LockPerm>,
) -> (ret: Tracked<PagePerm2m>)
    requires
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        old(krnl).pcid_allc_mp.perms_wf(),
        old(krnl).pcid_allc_mp.dom().contains(allocator_ptr),
        old(krnl).pcid_allc_mp.spec_index(allocator_ptr).is_init(),
        typed_lock_map_contains_mode(old(lctx).pcid_allocator_lock_map(), allocator_ptr, TypedLockMode::Write),
        lock_perm.state() is WriteLock,
        lock_perm.thread_id() == old(lctx).thread_id(),
        lock_perm.lock_id() == old(krnl).pcid_allc_mp.spec_index(allocator_ptr).locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::PcidAllocator(allocator_ptr)),
        *final(krnl) == (KernelK { pcid_allc_mp: final(krnl).pcid_allc_mp, ..*old(krnl) }),
        final(krnl).pcid_allc_mp.perms_wf(),
        final(krnl).pcid_allc_mp.dom() =~= old(krnl).pcid_allc_mp.dom().remove(allocator_ptr),
        forall|a: RwLockPcidAllocatorPtr| #![trigger final(krnl).pcid_allc_mp.spec_index(a)]
            final(krnl).pcid_allc_mp.dom().contains(a) ==> final(krnl).pcid_allc_mp.spec_index(a) == old(krnl).pcid_allc_mp.spec_index(a),
        ret.view().is_init(),
        ret.view().addr() == allocator_ptr,
{
    proof { krnl.pcid_allc_mp.typed_lock_map_aligned_write_at(lctx.pcid_allocator_lock_map(), lctx.thread_id(), allocator_ptr); }
    let Tracked(allocator_perm) = krnl.pcid_allc_mp.remove_with_perm(allocator_ptr);
    let ret = retype_pcid_allocator_rwlock_to_2m_page_perm(allocator_ptr, Tracked(allocator_perm), Tracked(lock_perm), Tracked(&mut *lctx));
    proof { assert(typed_lock_maps_aligned(krnl, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); }; }
    ret
}

/// In a released view, retire the 4K allocator `allocator_ptr`, whose caches and global pool are empty and whose every
/// cache shard, pool, and quota the caller write-holds: it leaves its map and its locks leave `lctx`.
pub(crate) fn kill_container_retire_allocator_4k_object(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, allocator_ptr: RwLockPageAllocatorPtr, Tracked(cache_perms): Tracked<Map<CpuId, LockPerm>>,
    Tracked(pool_perm): Tracked<LockPerm>, Tracked(quota_perm): Tracked<LockPerm>,
) -> (ret: Tracked<PagePerm4k>)
    requires
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        old(krnl).allc_4k_mp.perms_wf(),
        old(krnl).allc_4k_mp.dom().contains(allocator_ptr),
        forall|i: CpuId| #![trigger cache_perms.dom().contains(i)] index_valid(NUM_CPUS, i) ==> {
            &&& cache_perms.dom().contains(i)
            &&& cache_perms[i].state() is WriteLock
            &&& cache_perms[i].thread_id() == old(lctx).thread_id()
            &&& old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(i).view().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cache_perms[i].lock_id() })
            &&& old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(i).view().view().linked_list.view().len() == 0
            &&& typed_lock_map_contains_mode(old(lctx).allocator_cache_4k_lock_map(), (allocator_ptr, i), TypedLockMode::Write)
        },
        old(krnl).allc_4k_mp.spec_index(allocator_ptr).global_pool.view().view().len() == 0,
        typed_lock_map_contains_mode(old(lctx).allocator_global_pool_4k_lock_map(), allocator_ptr, TypedLockMode::Write),
        pool_perm.state() is WriteLock,
        pool_perm.thread_id() == old(lctx).thread_id(),
        pool_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).global_pool.locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_quota_4k_lock_map(), allocator_ptr, TypedLockMode::Write),
        quota_perm.state() is WriteLock,
        quota_perm.thread_id() == old(lctx).thread_id(),
        quota_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
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
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).allocator_4k_lock_maps() == (AllocatorLockMaps { quota: old(lctx).allocator_quota_4k_lock_map().remove(allocator_ptr),
            cache: old(lctx).allocator_cache_4k_lock_map().remove_keys(old(lctx).allocator_cache_4k_lock_map().dom().filter(|k: (RwLockPageAllocatorPtr, CpuId)| k.0 == allocator_ptr)),
            global_pool: old(lctx).allocator_global_pool_4k_lock_map().remove(allocator_ptr) }),
        *final(krnl) == (KernelK { allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }),
        final(krnl).allc_4k_mp.perms_wf(),
        final(krnl).allc_4k_mp.dom() =~= old(krnl).allc_4k_mp.dom().remove(allocator_ptr),
        forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_4k_mp.spec_index(a)]
            final(krnl).allc_4k_mp.dom().contains(a) ==> final(krnl).allc_4k_mp.spec_index(a) == old(krnl).allc_4k_mp.spec_index(a),
        ret.view().is_init(),
        ret.view().addr() == allocator_ptr,
{
    proof { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); }
    let Tracked(allocator_perm) = krnl.allc_4k_mp.remove_with_perm(allocator_ptr);
    let ret = retype_allocator_to_4k_page_perm::<ALLOCATOR_SIZE_4K>(PageSize::SZ4k, allocator_ptr, Tracked(allocator_perm), Tracked(cache_perms), Tracked(pool_perm), Tracked(quota_perm),
        Tracked(&mut *lctx));
    proof {
        assert(typed_lock_maps_aligned(krnl, &*lctx)) by {
            reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
        };
    }
    ret
}

/// In a released view, retire the 2M allocator `allocator_ptr`, whose caches and global pool are empty and whose every
/// cache shard, pool, and quota the caller write-holds: it leaves its map and its locks leave `lctx`.
pub(crate) fn kill_container_retire_allocator_2m_object(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, allocator_ptr: RwLockPageAllocatorPtr, Tracked(cache_perms): Tracked<Map<CpuId, LockPerm>>,
    Tracked(pool_perm): Tracked<LockPerm>, Tracked(quota_perm): Tracked<LockPerm>,
) -> (ret: Tracked<PagePerm4k>)
    requires
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        old(krnl).allc_2m_mp.perms_wf(),
        old(krnl).allc_2m_mp.dom().contains(allocator_ptr),
        forall|i: CpuId| #![trigger cache_perms.dom().contains(i)] index_valid(NUM_CPUS, i) ==> {
            &&& cache_perms.dom().contains(i)
            &&& cache_perms[i].state() is WriteLock
            &&& cache_perms[i].thread_id() == old(lctx).thread_id()
            &&& old(krnl).allc_2m_mp.spec_index(allocator_ptr).cpu_caches.spec_index(i).view().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cache_perms[i].lock_id() })
            &&& old(krnl).allc_2m_mp.spec_index(allocator_ptr).cpu_caches.spec_index(i).view().view().linked_list.view().len() == 0
            &&& typed_lock_map_contains_mode(old(lctx).allocator_cache_2m_lock_map(), (allocator_ptr, i), TypedLockMode::Write)
        },
        old(krnl).allc_2m_mp.spec_index(allocator_ptr).global_pool.view().view().len() == 0,
        typed_lock_map_contains_mode(old(lctx).allocator_global_pool_2m_lock_map(), allocator_ptr, TypedLockMode::Write),
        pool_perm.state() is WriteLock,
        pool_perm.thread_id() == old(lctx).thread_id(),
        pool_perm.lock_id() == old(krnl).allc_2m_mp.spec_index(allocator_ptr).global_pool.locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_quota_2m_lock_map(), allocator_ptr, TypedLockMode::Write),
        quota_perm.state() is WriteLock,
        quota_perm.thread_id() == old(lctx).thread_id(),
        quota_perm.lock_id() == old(krnl).allc_2m_mp.spec_index(allocator_ptr).quota.locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
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
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == (AllocatorLockMaps { quota: old(lctx).allocator_quota_2m_lock_map().remove(allocator_ptr),
            cache: old(lctx).allocator_cache_2m_lock_map().remove_keys(old(lctx).allocator_cache_2m_lock_map().dom().filter(|k: (RwLockPageAllocatorPtr, CpuId)| k.0 == allocator_ptr)),
            global_pool: old(lctx).allocator_global_pool_2m_lock_map().remove(allocator_ptr) }),
        *final(krnl) == (KernelK { allc_2m_mp: final(krnl).allc_2m_mp, ..*old(krnl) }),
        final(krnl).allc_2m_mp.perms_wf(),
        final(krnl).allc_2m_mp.dom() =~= old(krnl).allc_2m_mp.dom().remove(allocator_ptr),
        forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_2m_mp.spec_index(a)]
            final(krnl).allc_2m_mp.dom().contains(a) ==> final(krnl).allc_2m_mp.spec_index(a) == old(krnl).allc_2m_mp.spec_index(a),
        ret.view().is_init(),
        ret.view().addr() == allocator_ptr,
{
    proof { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); }
    let Tracked(allocator_perm) = krnl.allc_2m_mp.remove_with_perm(allocator_ptr);
    let ret = retype_allocator_to_4k_page_perm::<ALLOCATOR_SIZE_2M>(PageSize::SZ2m, allocator_ptr, Tracked(allocator_perm), Tracked(cache_perms), Tracked(pool_perm), Tracked(quota_perm),
        Tracked(&mut *lctx));
    proof {
        assert(typed_lock_maps_aligned(krnl, &*lctx)) by {
            reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
        };
    }
    ret
}

/// In a released view, retire the 1G allocator `allocator_ptr`, whose caches and global pool are empty and whose every
/// cache shard, pool, and quota the caller write-holds: it leaves its map and its locks leave `lctx`.
pub(crate) fn kill_container_retire_allocator_1g_object(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, allocator_ptr: RwLockPageAllocatorPtr, Tracked(cache_perms): Tracked<Map<CpuId, LockPerm>>,
    Tracked(pool_perm): Tracked<LockPerm>, Tracked(quota_perm): Tracked<LockPerm>,
) -> (ret: Tracked<PagePerm4k>)
    requires
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        old(krnl).allc_1g_mp.perms_wf(),
        old(krnl).allc_1g_mp.dom().contains(allocator_ptr),
        forall|i: CpuId| #![trigger cache_perms.dom().contains(i)] index_valid(NUM_CPUS, i) ==> {
            &&& cache_perms.dom().contains(i)
            &&& cache_perms[i].state() is WriteLock
            &&& cache_perms[i].thread_id() == old(lctx).thread_id()
            &&& old(krnl).allc_1g_mp.spec_index(allocator_ptr).cpu_caches.spec_index(i).view().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cache_perms[i].lock_id() })
            &&& old(krnl).allc_1g_mp.spec_index(allocator_ptr).cpu_caches.spec_index(i).view().view().linked_list.view().len() == 0
            &&& typed_lock_map_contains_mode(old(lctx).allocator_cache_1g_lock_map(), (allocator_ptr, i), TypedLockMode::Write)
        },
        old(krnl).allc_1g_mp.spec_index(allocator_ptr).global_pool.view().view().len() == 0,
        typed_lock_map_contains_mode(old(lctx).allocator_global_pool_1g_lock_map(), allocator_ptr, TypedLockMode::Write),
        pool_perm.state() is WriteLock,
        pool_perm.thread_id() == old(lctx).thread_id(),
        pool_perm.lock_id() == old(krnl).allc_1g_mp.spec_index(allocator_ptr).global_pool.locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_quota_1g_lock_map(), allocator_ptr, TypedLockMode::Write),
        quota_perm.state() is WriteLock,
        quota_perm.thread_id() == old(lctx).thread_id(),
        quota_perm.lock_id() == old(krnl).allc_1g_mp.spec_index(allocator_ptr).quota.locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
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
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == (AllocatorLockMaps { quota: old(lctx).allocator_quota_1g_lock_map().remove(allocator_ptr),
            cache: old(lctx).allocator_cache_1g_lock_map().remove_keys(old(lctx).allocator_cache_1g_lock_map().dom().filter(|k: (RwLockPageAllocatorPtr, CpuId)| k.0 == allocator_ptr)),
            global_pool: old(lctx).allocator_global_pool_1g_lock_map().remove(allocator_ptr) }),
        *final(krnl) == (KernelK { allc_1g_mp: final(krnl).allc_1g_mp, ..*old(krnl) }),
        final(krnl).allc_1g_mp.perms_wf(),
        final(krnl).allc_1g_mp.dom() =~= old(krnl).allc_1g_mp.dom().remove(allocator_ptr),
        forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_1g_mp.spec_index(a)]
            final(krnl).allc_1g_mp.dom().contains(a) ==> final(krnl).allc_1g_mp.spec_index(a) == old(krnl).allc_1g_mp.spec_index(a),
        ret.view().is_init(),
        ret.view().addr() == allocator_ptr,
{
    proof { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); }
    let Tracked(allocator_perm) = krnl.allc_1g_mp.remove_with_perm(allocator_ptr);
    let ret = retype_allocator_to_4k_page_perm::<ALLOCATOR_SIZE_1G>(PageSize::SZ1g, allocator_ptr, Tracked(allocator_perm), Tracked(cache_perms), Tracked(pool_perm), Tracked(quota_perm),
        Tracked(&mut *lctx));
    proof {
        assert(typed_lock_maps_aligned(krnl, &*lctx)) by {
            reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
        };
    }
    ret
}

/// In a released view, retire the marked childless container `container_ptr` with its offline request table, whose
/// parent list node `parent_node_perm` its parent returned and whose lock and every request cell the caller write-holds:
/// both leave their maps and their locks leave `lctx`.
pub(crate) fn kill_container_retire_container_object(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, container_ptr: RwLockContainerPtr, Tracked(parent_node_perm): Tracked<PointsTo<Node<RwLockContainerPtr>>>,
    Tracked(lock_perm): Tracked<LockPerm>, Tracked(flag_perms): Tracked<Map<CpuId, LockPerm>>,
) -> (ret: Tracked<PagePerm2m>)
    requires
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        container_ptr + 4096 <= usize::MAX,
        old(krnl).ctn_mp.perms_wf(),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).is_init(),
        old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(container_ptr).view().children.view().len() == 0,
        parent_node_perm.is_init(),
        parent_node_perm.addr() == old(krnl).ctn_mp.spec_index(container_ptr).view().parent_linkedlist_node.addr(),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        lock_perm.state() is WriteLock,
        lock_perm.thread_id() == old(lctx).thread_id(),
        lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        old(krnl).cpu_offline_mp.perms_wf(),
        old(krnl).cpu_offline_mp.dom().contains(cpu_offline_flags_ptr(container_ptr)),
        forall|i: CpuId|
            #![trigger flag_perms.dom().contains(i)]
            #![trigger flag_perms[i]]
            #![trigger typed_lock_map_contains_mode(old(lctx).cpu_offline_flag_lock_map(), (cpu_offline_flags_ptr(container_ptr), i), TypedLockMode::Write)]
            index_valid(NUM_CPUS, i) ==> {
            &&& flag_perms.dom().contains(i)
            &&& flag_perms[i].state() is WriteLock
            &&& flag_perms[i].thread_id() == old(lctx).thread_id()
            &&& flag_perms[i].lock_id() == old(krnl).cpu_offline_mp.spec_index(cpu_offline_flags_ptr(container_ptr)).flags.spec_index(i).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(old(lctx).cpu_offline_flag_lock_map(), (cpu_offline_flags_ptr(container_ptr), i), TypedLockMode::Write)
        },
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map().remove_keys(old(lctx).cpu_offline_flag_lock_map().dom().filter(
            |k: (RwLockCpuOfflineFlagsPtr, CpuId)| k.0 == cpu_offline_flags_ptr(container_ptr))),
        final(lctx).container_lock_map() == old(lctx).container_lock_map().remove(container_ptr),
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
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        *final(krnl) == (KernelK { ctn_mp: final(krnl).ctn_mp, cpu_offline_mp: final(krnl).cpu_offline_mp, ..*old(krnl) }),
        final(krnl).ctn_mp.perms_wf(),
        final(krnl).ctn_mp.dom() =~= old(krnl).ctn_mp.dom().remove(container_ptr),
        forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)] final(krnl).ctn_mp.dom().contains(c) ==> final(krnl).ctn_mp.spec_index(c) == old(krnl).ctn_mp.spec_index(c),
        forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.lock_id_by_key(c)] final(krnl).ctn_mp.dom().contains(c) ==> final(krnl).ctn_mp.lock_id_by_key(c) == old(krnl).ctn_mp.lock_id_by_key(c),
        final(krnl).cpu_offline_mp.perms_wf(),
        final(krnl).cpu_offline_mp.dom() =~= old(krnl).cpu_offline_mp.dom().remove(cpu_offline_flags_ptr(container_ptr)),
        forall|f: RwLockCpuOfflineFlagsPtr| #![trigger final(krnl).cpu_offline_mp.spec_index(f)]
            final(krnl).cpu_offline_mp.dom().contains(f) ==> final(krnl).cpu_offline_mp.spec_index(f) == old(krnl).cpu_offline_mp.spec_index(f),
        ret.view().is_init(),
        ret.view().addr() == container_ptr,
{
    proof { krnl.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), container_ptr); reveal(UnLockedMap::typed_flag_lock_map_aligned); }
    let Tracked(container_perm) = krnl.ctn_mp.remove_with_perm(container_ptr);
    let Tracked(flags_perm) = krnl.cpu_offline_mp.remove_with_perm(container_ptr + 4096);
    let ret = retype_container_rwlock_to_2m_page_perm(container_ptr, Tracked(container_perm), Tracked(flags_perm), Tracked(parent_node_perm), Tracked(lock_perm), Tracked(flag_perms),
        Tracked(&mut *lctx));
    proof { assert(typed_lock_maps_aligned(krnl, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); reveal(UnLockedMap::typed_flag_lock_map_aligned); }; }
    ret
}
} // verus!
