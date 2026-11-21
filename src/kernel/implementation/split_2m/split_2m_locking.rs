#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;

verus! {
pub tracked struct SplitSourceLocks {
    pub cache: Map<CpuId, LockPerm>,
    pub pool4k: LockPerm,
    pub pool2m: LockPerm,
}

pub fn freeze_split_2m_sources(krnl: &mut KernelK, allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<SplitSourceLocks>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).allc_2m_mp.dom().contains(allocator_2m),
        old(krnl).allc_4k_mp.dom().contains(allocator_4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        forall|cpu: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(cpu)] old(lctx).cpu_lock_map().dom().contains(cpu) ==> index_valid(NUM_CPUS, cpu) && !(old(krnl).cpu_arr.spec_index(cpu).view().view().view().state is Off),
        forall|thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(thread)] old(lctx).thread_lock_map().dom().contains(thread)
            ==> old(krnl).thrd_mp.dom().contains(thread) && !(old(krnl).thrd_mp.spec_index(thread).view().state is SCHEDULED),
    ensures
        forall|source: usize| #![trigger final(krnl).allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(source)] source <= NUM_CPUS ==>
            final(krnl).allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(source) == old(krnl).allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(source),
        final(krnl).allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom(),
        forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_2m_mp.spec_index(a)] old(krnl).allc_2m_mp.dom().contains(a) ==> final(krnl).allc_2m_mp.spec_index(a).quota == old(krnl).allc_2m_mp.spec_index(a).quota,
        final(krnl).allc_2m_mp.spec_index(allocator_2m).total_free_pages == old(krnl).allc_2m_mp.spec_index(allocator_2m).total_free_pages,
        final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
        forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_4k_mp.spec_index(a)] old(krnl).allc_4k_mp.dom().contains(a) ==> final(krnl).allc_4k_mp.spec_index(a).quota == old(krnl).allc_4k_mp.spec_index(a).quota,
        final(krnl).allc_4k_mp.spec_index(allocator_4k).total_free_pages == old(krnl).allc_4k_mp.spec_index(allocator_4k).total_free_pages,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        *final(krnl) == (KernelK { allc_2m_mp: final(krnl).allc_2m_mp, allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }),
        forall|held: (RwLockPageAllocatorPtr, CpuId)| #![trigger final(lctx).allocator_cache_2m_lock_map().dom().contains(held)] final(lctx).allocator_cache_2m_lock_map().dom().contains(held)
            <==> held.0 == allocator_2m && held.1 < NUM_CPUS,
        final(lctx).allocator_global_pool_2m_lock_map().dom() =~= set![allocator_2m],
        final(lctx).allocator_global_pool_4k_lock_map().dom() =~= set![allocator_4k],
        forall|cpu: CpuId| #![trigger ret.view().cache.dom().contains(cpu)] ret.view().cache.dom().contains(cpu) <==> cpu < NUM_CPUS,
        forall|cpu: CpuId| #![trigger ret.view().cache[cpu]] cpu < NUM_CPUS ==> {
            &&& typed_lock_map_contains_mode(final(lctx).allocator_cache_2m_lock_map(), (allocator_2m, cpu), TypedLockMode::Write)
            &&& ret.view().cache[cpu].state() is WriteLock
            &&& ret.view().cache[cpu].thread_id() == final(lctx).thread_id()
            &&& final(krnl).allc_2m_mp.spec_index(allocator_2m).cpu_caches.spec_index(cpu).view().locking_thread() is Write
            &&& ret.view().cache[cpu].lock_id() == final(krnl).allc_2m_mp.spec_index(allocator_2m).cpu_caches.spec_index(cpu).view().locking_thread()->Write_lock_id
        },
        typed_lock_map_contains_mode(final(lctx).allocator_global_pool_2m_lock_map(), allocator_2m, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).allocator_global_pool_4k_lock_map(), allocator_4k, TypedLockMode::Write),
        ret.view().pool2m.state() is WriteLock,
        ret.view().pool4k.state() is WriteLock,
        ret.view().pool2m.thread_id() == final(lctx).thread_id(),
        ret.view().pool4k.thread_id() == final(lctx).thread_id(),
        final(krnl).allc_2m_mp.spec_index(allocator_2m).global_pool.locking_thread() is Write,
        final(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread() is Write,
        ret.view().pool2m.lock_id() == final(krnl).allc_2m_mp.spec_index(allocator_2m).global_pool.locking_thread()->Write_lock_id,
        ret.view().pool4k.lock_id() == final(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread()->Write_lock_id,
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
        final(lctx).allocator_quota_2m_lock_map() == old(lctx).allocator_quota_2m_lock_map(),
        final(lctx).allocator_quota_4k_lock_map() == old(lctx).allocator_quota_4k_lock_map(),
        final(lctx).allocator_cache_4k_lock_map() == old(lctx).allocator_cache_4k_lock_map(),
        final(lctx).allocator_quota_1g_lock_map() == old(lctx).allocator_quota_1g_lock_map(),
        final(lctx).allocator_cache_1g_lock_map() == old(lctx).allocator_cache_1g_lock_map(),
        final(lctx).allocator_global_pool_1g_lock_map() == old(lctx).allocator_global_pool_1g_lock_map(),
{
    let tracked mut cache: Map<CpuId, LockPerm> = Map::tracked_empty();
    let mut cpu = 0usize;
    while cpu < NUM_CPUS
        invariant
            old(krnl).allc_2m_mp.dom().contains(allocator_2m),
            old(krnl).allc_4k_mp.dom().contains(allocator_4k),
            krnl.allc_4k_mp.dom().contains(allocator_4k),
            forall|source: usize| #![trigger krnl.allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(source)] source <= NUM_CPUS ==>
                krnl.allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(source) == old(krnl).allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(source),
            lctx.page_lock_map().dom().is_empty(),
            lctx.pcid_needflush_lock_map().dom().is_empty(),
            lctx.allocator_quota_2m_lock_map().dom().is_empty(),
            forall|held_cpu: CpuId| #![trigger lctx.cpu_lock_map().dom().contains(held_cpu)] lctx.cpu_lock_map().dom().contains(held_cpu)
                ==> index_valid(NUM_CPUS, held_cpu) && !(krnl.cpu_arr.spec_index(held_cpu).view().view().view().state is Off),
            forall|thread: RwLockThreadPtr| #![trigger lctx.thread_lock_map().dom().contains(thread)] lctx.thread_lock_map().dom().contains(thread)
                ==> krnl.thrd_mp.dom().contains(thread) && !(krnl.thrd_mp.spec_index(thread).view().state is SCHEDULED),
            cpu <= NUM_CPUS,
            krnl.allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom(),
            forall|a: RwLockPageAllocatorPtr| #![trigger krnl.allc_2m_mp.spec_index(a)] old(krnl).allc_2m_mp.dom().contains(a) ==> krnl.allc_2m_mp.spec_index(a).quota == old(krnl).allc_2m_mp.spec_index(a).quota,
            krnl.allc_2m_mp.spec_index(allocator_2m).total_free_pages == old(krnl).allc_2m_mp.spec_index(allocator_2m).total_free_pages,
            krnl.allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
            forall|a: RwLockPageAllocatorPtr| #![trigger krnl.allc_4k_mp.spec_index(a)] old(krnl).allc_4k_mp.dom().contains(a) ==> krnl.allc_4k_mp.spec_index(a).quota == old(krnl).allc_4k_mp.spec_index(a).quota,
            krnl.allc_4k_mp.spec_index(allocator_4k).total_free_pages == old(krnl).allc_4k_mp.spec_index(allocator_4k).total_free_pages,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.kernel_view_locking_state() is Acquire,
            *krnl == (KernelK { allc_2m_mp: krnl.allc_2m_mp, ..*old(krnl) }),
            krnl.allc_2m_mp.dom().contains(allocator_2m),
            krnl.allc_4k_mp.dom().contains(allocator_4k),
            lctx.holds_no_allocator_locks(PageSize::SZ4k),
            lctx.holds_no_allocator_locks(PageSize::SZ1g),
            lctx.allocator_global_pool_2m_lock_map().dom().is_empty(),
            forall|c: CpuId| #![trigger cache.dom().contains(c)] cache.dom().contains(c) <==> c < cpu,
            forall|held: (RwLockPageAllocatorPtr, CpuId)| #![trigger lctx.allocator_cache_2m_lock_map().dom().contains(held)] lctx.allocator_cache_2m_lock_map().dom().contains(held) <==> held.0 == allocator_2m && held.1 < cpu,
            forall|c: CpuId| #![trigger cache[c]] c < cpu ==> {
                &&& typed_lock_map_contains_mode(lctx.allocator_cache_2m_lock_map(), (allocator_2m, c), TypedLockMode::Write)
                &&& cache[c].state() is WriteLock
                &&& cache[c].thread_id() == lctx.thread_id()
                &&& krnl.allc_2m_mp.spec_index(allocator_2m).cpu_caches.spec_index(c).view().locking_thread() is Write
                &&& cache[c].lock_id() == krnl.allc_2m_mp.spec_index(allocator_2m).cpu_caches.spec_index(c).view().locking_thread()->Write_lock_id
            },
            lctx.page_lock_map() == old(lctx).page_lock_map(),
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
            lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            lctx.cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.process_lock_map() == old(lctx).process_lock_map(),
            lctx.thread_lock_map() == old(lctx).thread_lock_map(),
            lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            lctx.pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
            lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            lctx.iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
            lctx.allocator_quota_2m_lock_map() == old(lctx).allocator_quota_2m_lock_map(),
            lctx.allocator_quota_4k_lock_map() == old(lctx).allocator_quota_4k_lock_map(),
            lctx.allocator_cache_4k_lock_map() == old(lctx).allocator_cache_4k_lock_map(),
            lctx.allocator_quota_1g_lock_map() == old(lctx).allocator_quota_1g_lock_map(),
            lctx.allocator_cache_1g_lock_map() == old(lctx).allocator_cache_1g_lock_map(),
            lctx.allocator_global_pool_1g_lock_map() == old(lctx).allocator_global_pool_1g_lock_map(),
        decreases NUM_CPUS - cpu,
    {
        let Tracked(perm) = krnl.wlock_allocator_cache_2m(allocator_2m, cpu, Tracked(&mut *lctx));
        proof { cache.tracked_insert(cpu, perm); }

        cpu += 1;
    }
    let Tracked(pool4k) = krnl.wlock_allocator_global_pool_4k(allocator_4k, Tracked(&mut *lctx));
    let Tracked(pool2m) = krnl.wlock_allocator_global_pool_2m_ordered(allocator_2m, Tracked(&mut *lctx));

    Tracked(SplitSourceLocks { cache, pool2m, pool4k })
}

pub fn thaw_split_2m_sources(krnl: &mut KernelK, allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(locks): Tracked<SplitSourceLocks>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(krnl).allc_2m_mp.dom().contains(allocator_2m),
        old(krnl).allc_4k_mp.dom().contains(allocator_4k),
        forall|cpu: CpuId| #![trigger locks.cache.dom().contains(cpu)] locks.cache.dom().contains(cpu) <==> cpu < NUM_CPUS,
        forall|cpu: CpuId| #![trigger locks.cache[cpu]] cpu < NUM_CPUS ==> {
            &&& typed_lock_map_contains_mode(old(lctx).allocator_cache_2m_lock_map(), (allocator_2m, cpu), TypedLockMode::Write)
            &&& locks.cache[cpu].state() is WriteLock
            &&& locks.cache[cpu].thread_id() == old(lctx).thread_id()
            &&& old(krnl).allc_2m_mp.spec_index(allocator_2m).cpu_caches.spec_index(cpu).view().locking_thread() is Write
            &&& locks.cache[cpu].lock_id() == old(krnl).allc_2m_mp.spec_index(allocator_2m).cpu_caches.spec_index(cpu).view().locking_thread()->Write_lock_id
        },
        forall|held: (RwLockPageAllocatorPtr, CpuId)| #![trigger old(lctx).allocator_cache_2m_lock_map().dom().contains(held)] old(lctx).allocator_cache_2m_lock_map().dom().contains(held) <==> held.0 == allocator_2m && held.1 < NUM_CPUS,
        old(lctx).allocator_global_pool_2m_lock_map().dom() =~= set![allocator_2m],
        old(lctx).allocator_global_pool_4k_lock_map().dom() =~= set![allocator_4k],
        typed_lock_map_contains_mode(old(lctx).allocator_global_pool_2m_lock_map(), allocator_2m, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).allocator_global_pool_4k_lock_map(), allocator_4k, TypedLockMode::Write),
        locks.pool2m.state() is WriteLock,
        locks.pool4k.state() is WriteLock,
        locks.pool2m.thread_id() == old(lctx).thread_id(),
        locks.pool4k.thread_id() == old(lctx).thread_id(),
        old(krnl).allc_2m_mp.spec_index(allocator_2m).global_pool.locking_thread() is Write,
        old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread() is Write,
        locks.pool2m.lock_id() == old(krnl).allc_2m_mp.spec_index(allocator_2m).global_pool.locking_thread()->Write_lock_id,
        locks.pool4k.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread()->Write_lock_id,
    ensures
        forall|source: usize| #![trigger final(krnl).allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(source)] source <= NUM_CPUS ==>
            final(krnl).allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(source) == old(krnl).allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(source),
        final(krnl).allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom(),
        forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_2m_mp.spec_index(a)] old(krnl).allc_2m_mp.dom().contains(a) ==> final(krnl).allc_2m_mp.spec_index(a).quota == old(krnl).allc_2m_mp.spec_index(a).quota,
        final(krnl).allc_2m_mp.spec_index(allocator_2m).total_free_pages == old(krnl).allc_2m_mp.spec_index(allocator_2m).total_free_pages,
        final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
        forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_4k_mp.spec_index(a)] old(krnl).allc_4k_mp.dom().contains(a) ==> final(krnl).allc_4k_mp.spec_index(a).quota == old(krnl).allc_4k_mp.spec_index(a).quota,
        final(krnl).allc_4k_mp.spec_index(allocator_4k).total_free_pages == old(krnl).allc_4k_mp.spec_index(allocator_4k).total_free_pages,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        final(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        final(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        *final(krnl) == (KernelK { allc_2m_mp: final(krnl).allc_2m_mp, allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }),
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
        final(lctx).allocator_quota_2m_lock_map() == old(lctx).allocator_quota_2m_lock_map(),
        final(lctx).allocator_quota_4k_lock_map() == old(lctx).allocator_quota_4k_lock_map(),
        final(lctx).allocator_cache_4k_lock_map() == old(lctx).allocator_cache_4k_lock_map(),
        final(lctx).allocator_quota_1g_lock_map() == old(lctx).allocator_quota_1g_lock_map(),
        final(lctx).allocator_cache_1g_lock_map() == old(lctx).allocator_cache_1g_lock_map(),
        final(lctx).allocator_global_pool_1g_lock_map() == old(lctx).allocator_global_pool_1g_lock_map(),
{
    let tracked mut cache = locks.cache;
    krnl.wunlock_allocator_global_pool_2m(allocator_2m, Tracked(&mut *lctx), Tracked(locks.pool2m));
    krnl.wunlock_allocator_global_pool_4k(allocator_4k, Tracked(&mut *lctx), Tracked(locks.pool4k));
    let mut cpu = 0usize;
    while cpu < NUM_CPUS
        invariant
            old(krnl).allc_2m_mp.dom().contains(allocator_2m),
            old(krnl).allc_4k_mp.dom().contains(allocator_4k),
            krnl.allc_4k_mp.dom().contains(allocator_4k),
            forall|source: usize| #![trigger krnl.allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(source)] source <= NUM_CPUS ==>
                krnl.allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(source) == old(krnl).allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(source),
            cpu <= NUM_CPUS,
            krnl.allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom(),
            forall|a: RwLockPageAllocatorPtr| #![trigger krnl.allc_2m_mp.spec_index(a)] old(krnl).allc_2m_mp.dom().contains(a) ==> krnl.allc_2m_mp.spec_index(a).quota == old(krnl).allc_2m_mp.spec_index(a).quota,
            krnl.allc_2m_mp.spec_index(allocator_2m).total_free_pages == old(krnl).allc_2m_mp.spec_index(allocator_2m).total_free_pages,
            krnl.allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
            forall|a: RwLockPageAllocatorPtr| #![trigger krnl.allc_4k_mp.spec_index(a)] old(krnl).allc_4k_mp.dom().contains(a) ==> krnl.allc_4k_mp.spec_index(a).quota == old(krnl).allc_4k_mp.spec_index(a).quota,
            krnl.allc_4k_mp.spec_index(allocator_4k).total_free_pages == old(krnl).allc_4k_mp.spec_index(allocator_4k).total_free_pages,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.kernel_view_locking_state() is Release,
            krnl.allc_2m_mp.dom().contains(allocator_2m),
            lctx.allocator_global_pool_2m_lock_map().dom().is_empty(),
            lctx.allocator_global_pool_4k_lock_map().dom().is_empty(),
            *krnl == (KernelK { allc_2m_mp: krnl.allc_2m_mp, allc_4k_mp: krnl.allc_4k_mp, ..*old(krnl) }),
            forall|c: CpuId| #![trigger cache.dom().contains(c)] cache.dom().contains(c) <==> cpu <= c < NUM_CPUS,
            forall|held: (RwLockPageAllocatorPtr, CpuId)| #![trigger lctx.allocator_cache_2m_lock_map().dom().contains(held)] lctx.allocator_cache_2m_lock_map().dom().contains(held) <==> held.0 == allocator_2m && cpu <= held.1 < NUM_CPUS,
            forall|c: CpuId| #![trigger cache[c]] cpu <= c < NUM_CPUS ==> {
                &&& typed_lock_map_contains_mode(lctx.allocator_cache_2m_lock_map(), (allocator_2m, c), TypedLockMode::Write)
                &&& cache[c].state() is WriteLock
                &&& cache[c].thread_id() == lctx.thread_id()
                &&& krnl.allc_2m_mp.spec_index(allocator_2m).cpu_caches.spec_index(c).view().locking_thread() is Write
                &&& cache[c].lock_id() == krnl.allc_2m_mp.spec_index(allocator_2m).cpu_caches.spec_index(c).view().locking_thread()->Write_lock_id
            },
            lctx.page_lock_map() == old(lctx).page_lock_map(),
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
            lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            lctx.cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.process_lock_map() == old(lctx).process_lock_map(),
            lctx.thread_lock_map() == old(lctx).thread_lock_map(),
            lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            lctx.pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
            lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            lctx.iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
            lctx.allocator_quota_2m_lock_map() == old(lctx).allocator_quota_2m_lock_map(),
            lctx.allocator_quota_4k_lock_map() == old(lctx).allocator_quota_4k_lock_map(),
            lctx.allocator_cache_4k_lock_map() == old(lctx).allocator_cache_4k_lock_map(),
            lctx.allocator_quota_1g_lock_map() == old(lctx).allocator_quota_1g_lock_map(),
            lctx.allocator_cache_1g_lock_map() == old(lctx).allocator_cache_1g_lock_map(),
            lctx.allocator_global_pool_1g_lock_map() == old(lctx).allocator_global_pool_1g_lock_map(),
        decreases NUM_CPUS - cpu,
    {
        let tracked perm = cache.tracked_remove(cpu);
        krnl.wunlock_allocator_cache_2m(allocator_2m, cpu, Tracked(&mut *lctx), Tracked(perm));

        cpu += 1;
    }
}
}
