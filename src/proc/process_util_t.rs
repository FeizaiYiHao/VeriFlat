use vstd::prelude::*;
verus! {
use crate::*;
use vstd::simple_pptr::*;
use super::process_util_t_eof::*;

/// TCB: retire a write-locked, killed process object that has no child and no thread, and reclaim its 4k page as raw
/// memory.
///
/// This is the inverse of `retype_page_to_process_and_insert`. The object has already left `process_map`, the caller
/// exclusively write-holds its lock in the release phase, its parent's child list returned its in-page parent node, and
/// its own lists are empty, so it owns no other memory and no other thread can reach or wait on the lock. The held lock
/// disappears from `lctx` with the object.
/// TCB assumption: `ExternalNode::is_init()` means a slot holds the initialized node permission at `addr()`, and the address `requires` makes the parent node this page's own tail slot, so the passed node permission plus the lock object cover exactly the returned page.
#[verifier::external_body]
pub fn retype_process_rwlock_to_4k_page_perm(
    prc_ptr: RwLockProcessPtr, Tracked(process_perm): Tracked<PointsTo<ProcessRwLock>>, Tracked(parent_node_perm): Tracked<PointsTo<Node<RwLockProcessPtr>>>,
    Tracked(lock_perm): Tracked<LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>,
) -> (ret: Tracked<PagePerm4k>)
    requires
        process_perm.is_init(),
        process_perm.addr() == prc_ptr,
        process_perm.value().is_init(),
        process_perm.value().being_killed(),
        process_perm.value().view().children.view().len() == 0,
        process_perm.value().view().owned_threads.view().len() == 0,
        parent_node_perm.is_init(),
        process_perm.value().view().parent_linkedlist_node.addr() == process_parent_node_addr(prc_ptr),
        parent_node_perm.addr() == process_perm.value().view().parent_linkedlist_node.addr(),
        process_perm.value().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: lock_perm.lock_id() }),
        lock_perm.state() is WriteLock,
        lock_perm.thread_id() == old(lctx).thread_id(),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), prc_ptr, TypedLockMode::Write),
        old(lctx).kernel_view_locking_state() is Release,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Process(prc_ptr)),
        ret.view().is_init(),
        ret.view().addr() == prc_ptr,
{
    Tracked::assume_new()
}

/// TCB: retire the write-held, killed, childless container object at `ctn_ptr` together with the offline
/// request table in its second 4K and reclaim its 2M page as raw memory.
///
/// This is the inverse of `retype_container_page_perm_to_rwlock` plus `retype_container_page_tail_to_offline_flags`. The
/// container and its table have already left their maps, the caller exclusively holds the container lock and every
/// per-cpu lock of the table in the release phase, and its parent's child list returned the in-page parent node, so
/// no other thread can reach or wait on these locks. The held locks disappear from `lctx` with the objects.
/// TCB assumption: `ExternalNode::is_init()` means a slot holds the initialized node permission at `addr()`, and the address `requires` makes the parent node this 2M page's own tail slot, so the passed node permission, the offline table and the lock object cover exactly the returned page.
#[verifier::external_body]
pub fn retype_container_rwlock_to_2m_page_perm(
    ctn_ptr: RwLockContainerPtr, Tracked(container_perm): Tracked<LockObjPerm<Container, ReadOnlyNode<ContainerRO>, ContainerGhost, CONTAINER_HAS_KILL_STATE>>,
    Tracked(flags_perm): Tracked<PointsTo<CpuOfflineFlags>>, Tracked(parent_node_perm): Tracked<PointsTo<Node<RwLockContainerPtr>>>, Tracked(lock_perm): Tracked<LockPerm>,
    Tracked(flag_lock_perms): Tracked<Map<CpuId, LockPerm>>, Tracked(lctx): Tracked<&mut LocalContext>,
) -> (ret: Tracked<PagePerm2m>)
    requires
        container_perm.is_init(),
        container_perm.addr() == ctn_ptr,
        container_perm.value().is_init(),
        container_perm.value().being_killed(),
        container_perm.value().view().children.view().len() == 0,
        parent_node_perm.is_init(),
        container_perm.value().view().parent_linkedlist_node.addr() == container_parent_node_addr(ctn_ptr),
        parent_node_perm.addr() == container_perm.value().view().parent_linkedlist_node.addr(),
        container_perm.value().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: lock_perm.lock_id() }),
        lock_perm.state() is WriteLock,
        lock_perm.thread_id() == old(lctx).thread_id(),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), ctn_ptr, TypedLockMode::Write),
        flags_perm.is_init(),
        flags_perm.addr() == cpu_offline_flags_ptr(ctn_ptr),
        forall|i: CpuId| #![trigger flag_lock_perms.dom().contains(i)] index_valid(NUM_CPUS, i) ==> {
            &&& flag_lock_perms.dom().contains(i)
            &&& flag_lock_perms[i].state() is WriteLock
            &&& flag_lock_perms[i].thread_id() == old(lctx).thread_id()
            &&& flags_perm.value().flags.spec_index(i).view().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: flag_lock_perms[i].lock_id() })
            &&& typed_lock_map_contains_mode(old(lctx).cpu_offline_flag_lock_map(), (cpu_offline_flags_ptr(ctn_ptr), i), TypedLockMode::Write)
        },
        old(lctx).kernel_view_locking_state() is Release,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map().remove_keys(old(lctx).cpu_offline_flag_lock_map().dom().filter(|k: (RwLockCpuOfflineFlagsPtr, CpuId)| k.0 == cpu_offline_flags_ptr(ctn_ptr))),
        final(lctx).container_lock_map() == old(lctx).container_lock_map().remove(ctn_ptr),
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
        ret.view().is_init(),
        ret.view().addr() == ctn_ptr,
{
    Tracked::assume_new()
}

/// TCB: retire the write-held PCID allocator object at `allc_ptr` of a retired container and reclaim its 2M page
/// as raw memory.
///
/// This is the inverse of `retype_page_perm_2m_to_rwlock`. The object has already left its map and the caller
/// exclusively write-holds its lock in the release phase, so no other thread can reach or wait on the lock. The held
/// lock disappears from `lctx` with the object.
#[verifier::external_body]
pub fn retype_pcid_allocator_rwlock_to_2m_page_perm(
    allc_ptr: RwLockPcidAllocatorPtr, Tracked(allocator_perm): Tracked<LockObjPerm<PcidAllocator, (), (), PCID_ALLOCATOR_HAS_KILL_STATE>>,
    Tracked(lock_perm): Tracked<LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>,
) -> (ret: Tracked<PagePerm2m>)
    requires
        allocator_perm.is_init(),
        allocator_perm.addr() == allc_ptr,
        allocator_perm.value().is_init(),
        allocator_perm.value().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: lock_perm.lock_id() }),
        lock_perm.state() is WriteLock,
        lock_perm.thread_id() == old(lctx).thread_id(),
        typed_lock_map_contains_mode(old(lctx).pcid_allocator_lock_map(), allc_ptr, TypedLockMode::Write),
        old(lctx).kernel_view_locking_state() is Release,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::PcidAllocator(allc_ptr)),
        ret.view().is_init(),
        ret.view().addr() == allc_ptr,
{
    Tracked::assume_new()
}

/// TCB: retire the write-held, marked cpu set object at `cpu_set_ptr` of a retired container and reclaim its 4K page
/// as raw memory.
///
/// This is the inverse of `retype_page_perm_to_rwlock`. The object has already left its map and the caller exclusively
/// write-holds its lock in the release phase, so no other thread can reach or wait on the lock. The held lock
/// disappears from `lctx` with the object.
#[verifier::external_body]
pub fn retype_cpu_set_rwlock_to_4k_page_perm(
    cpu_set_ptr: RwLockCpuSetPtr, Tracked(cpu_set_perm): Tracked<LockObjPerm<CpuSet, (), (), CPU_SET_HAS_KILL_STATE, PerCpuReaderSlots>>, Tracked(lock_perm): Tracked<LockPerm>,
    Tracked(lctx): Tracked<&mut LocalContext>,
) -> (ret: Tracked<PagePerm4k>)
    requires
        cpu_set_perm.is_init(),
        cpu_set_perm.addr() == cpu_set_ptr,
        cpu_set_perm.value().is_init(),
        cpu_set_perm.value().being_killed(),
        cpu_set_perm.value().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: lock_perm.lock_id() }),
        lock_perm.state() is WriteLock,
        lock_perm.thread_id() == old(lctx).thread_id(),
        typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), cpu_set_ptr, TypedLockMode::Write),
        old(lctx).kernel_view_locking_state() is Release,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::CpuSet(cpu_set_ptr)),
        ret.view().is_init(),
        ret.view().addr() == cpu_set_ptr,
{
    Tracked::assume_new()
}

/// TCB: retire the scheduler object at `sched_ptr` of a retired container, whose run queues are empty and whose
/// every shard lock the caller holds, and reclaim its 4K page as raw memory.
///
/// This is the inverse of `retype_4k_page_perm_to_scheduler`. The object has already left its map in the release
/// phase, so no other thread can reach or wait on its shard locks. The held shard locks disappear from `lctx` with the
/// object.
#[verifier::external_body]
pub fn retype_scheduler_to_4k_page_perm(
    sched_ptr: RwLockSchedulerPtr, Tracked(scheduler_perm): Tracked<PointsTo<Scheduler>>, Tracked(shard_lock_perms): Tracked<Map<CpuId, LockPerm>>,
    Tracked(lctx): Tracked<&mut LocalContext>,
) -> (ret: Tracked<PagePerm4k>)
    requires
        scheduler_perm.is_init(),
        scheduler_perm.addr() == sched_ptr,
        forall|i: CpuId| #![trigger shard_lock_perms.dom().contains(i)] index_valid(NUM_CPUS, i) ==> {
            &&& shard_lock_perms.dom().contains(i)
            &&& shard_lock_perms[i].state() is WriteLock
            &&& shard_lock_perms[i].thread_id() == old(lctx).thread_id()
            &&& scheduler_perm.value().shards.spec_index(i).view().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: shard_lock_perms[i].lock_id() })
            &&& scheduler_perm.value().shards.spec_index(i).view().view().queue.view().len() == 0
            &&& typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (sched_ptr, i), TypedLockMode::Write)
        },
        old(lctx).kernel_view_locking_state() is Release,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map().remove_keys(old(lctx).scheduler_lock_map().dom().filter(|k: (RwLockSchedulerPtr, CpuId)| k.0 == sched_ptr)),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        ret.view().is_init(),
        ret.view().addr() == sched_ptr,
{
    Tracked::assume_new()
}

/// TCB: retire the page allocator object of `size` at `allc_ptr` of a retired container, whose caches and global
/// pool are empty and whose every cache shard, global pool, and quota lock the caller holds, and reclaim its 4K page
/// as raw memory.
///
/// This is the inverse of `retype_4k_page_perm_to_allocator`. The object has already left its map in the release
/// phase, so no other thread can reach or wait on its locks. The held locks disappear from `lctx` with the object.
#[verifier::external_body]
pub fn retype_allocator_to_4k_page_perm<const SIZE: usize>(
    size: PageSize, allc_ptr: RwLockPageAllocatorPtr, Tracked(allocator_perm): Tracked<PointsTo<PageAllocator<SIZE>>>, Tracked(cache_lock_perms): Tracked<Map<CpuId, LockPerm>>,
    Tracked(pool_lock_perm): Tracked<LockPerm>, Tracked(quota_lock_perm): Tracked<LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>,
) -> (ret: Tracked<PagePerm4k>)
    requires
        SIZE == match size { PageSize::SZ4k => ALLOCATOR_SIZE_4K, PageSize::SZ2m => ALLOCATOR_SIZE_2M, PageSize::SZ1g => ALLOCATOR_SIZE_1G },
        allocator_perm.is_init(),
        allocator_perm.addr() == allc_ptr,
        forall|i: CpuId| #![trigger cache_lock_perms.dom().contains(i)] index_valid(NUM_CPUS, i) ==> {
            &&& cache_lock_perms.dom().contains(i)
            &&& cache_lock_perms[i].state() is WriteLock
            &&& cache_lock_perms[i].thread_id() == old(lctx).thread_id()
            &&& allocator_perm.value().cpu_caches.spec_index(i).view().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cache_lock_perms[i].lock_id() })
            &&& allocator_perm.value().cpu_caches.spec_index(i).view().view().linked_list.view().len() == 0
            &&& typed_lock_map_contains_mode(match size {
                PageSize::SZ4k => old(lctx).allocator_cache_4k_lock_map(), PageSize::SZ2m => old(lctx).allocator_cache_2m_lock_map(), PageSize::SZ1g => old(lctx).allocator_cache_1g_lock_map(),
            }, (allc_ptr, i), TypedLockMode::Write)
        },
        allocator_perm.value().global_pool.view().view().len() == 0,
        allocator_perm.value().global_pool.locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: pool_lock_perm.lock_id() }),
        pool_lock_perm.state() is WriteLock,
        pool_lock_perm.thread_id() == old(lctx).thread_id(),
        typed_lock_map_contains_mode(match size {
            PageSize::SZ4k => old(lctx).allocator_global_pool_4k_lock_map(), PageSize::SZ2m => old(lctx).allocator_global_pool_2m_lock_map(),
            PageSize::SZ1g => old(lctx).allocator_global_pool_1g_lock_map(),
        }, allc_ptr, TypedLockMode::Write),
        allocator_perm.value().quota.locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: quota_lock_perm.lock_id() }),
        quota_lock_perm.state() is WriteLock,
        quota_lock_perm.thread_id() == old(lctx).thread_id(),
        typed_lock_map_contains_mode(match size {
            PageSize::SZ4k => old(lctx).allocator_quota_4k_lock_map(), PageSize::SZ2m => old(lctx).allocator_quota_2m_lock_map(), PageSize::SZ1g => old(lctx).allocator_quota_1g_lock_map(),
        }, allc_ptr, TypedLockMode::Write),
        old(lctx).kernel_view_locking_state() is Release,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
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
        final(lctx).allocator_4k_lock_maps() == if size is SZ4k {
            AllocatorLockMaps { quota: old(lctx).allocator_quota_4k_lock_map().remove(allc_ptr),
                cache: old(lctx).allocator_cache_4k_lock_map().remove_keys(old(lctx).allocator_cache_4k_lock_map().dom().filter(|k: (RwLockPageAllocatorPtr, CpuId)| k.0 == allc_ptr)),
                global_pool: old(lctx).allocator_global_pool_4k_lock_map().remove(allc_ptr) }
        } else { old(lctx).allocator_4k_lock_maps() },
        final(lctx).allocator_2m_lock_maps() == if size is SZ2m {
            AllocatorLockMaps { quota: old(lctx).allocator_quota_2m_lock_map().remove(allc_ptr),
                cache: old(lctx).allocator_cache_2m_lock_map().remove_keys(old(lctx).allocator_cache_2m_lock_map().dom().filter(|k: (RwLockPageAllocatorPtr, CpuId)| k.0 == allc_ptr)),
                global_pool: old(lctx).allocator_global_pool_2m_lock_map().remove(allc_ptr) }
        } else { old(lctx).allocator_2m_lock_maps() },
        final(lctx).allocator_1g_lock_maps() == if size is SZ1g {
            AllocatorLockMaps { quota: old(lctx).allocator_quota_1g_lock_map().remove(allc_ptr),
                cache: old(lctx).allocator_cache_1g_lock_map().remove_keys(old(lctx).allocator_cache_1g_lock_map().dom().filter(|k: (RwLockPageAllocatorPtr, CpuId)| k.0 == allc_ptr)),
                global_pool: old(lctx).allocator_global_pool_1g_lock_map().remove(allc_ptr) }
        } else { old(lctx).allocator_1g_lock_maps() },
        ret.view().is_init(),
        ret.view().addr() == allc_ptr,
{
    Tracked::assume_new()
}

impl KernelK {
    /// Remove the write-held, killed process `prc_ptr`, which has no child and no thread, from `prc_mp` and reclaim
    /// its page memory together with the parent node its parent's child list returned.
    pub fn remove_process_and_reclaim_4k_page_perm(
        &mut self, prc_ptr: RwLockProcessPtr, Tracked(parent_node_perm): Tracked<PointsTo<Node<RwLockProcessPtr>>>,
        Tracked(lock_perm): Tracked<LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>,
    ) -> (ret: Tracked<PagePerm4k>)
        requires
            old(self).prc_mp.perms_wf(),
            old(self).prc_mp.dom().contains(prc_ptr),
            old(self).prc_mp.spec_index(prc_ptr).is_init(),
            old(self).prc_mp.spec_index(prc_ptr).being_killed(),
            old(self).prc_mp.spec_index(prc_ptr).view_rodata().view().parent is None ==> typed_lock_map_contains_mode(old(lctx).container_lock_map(), old(self).prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container, TypedLockMode::Write),
            old(self).prc_mp.spec_index(prc_ptr).view().children.view().len() == 0,
            old(self).prc_mp.spec_index(prc_ptr).view().owned_threads.view().len() == 0,
            parent_node_perm.is_init(),
            old(self).prc_mp.spec_index(prc_ptr).view().parent_linkedlist_node.addr() == process_parent_node_addr(prc_ptr),
            parent_node_perm.addr() == old(self).prc_mp.spec_index(prc_ptr).view().parent_linkedlist_node.addr(),
            lock_perm.state() is WriteLock,
            lock_perm.thread_id() == old(lctx).thread_id(),
            lock_perm.lock_id() == old(self).prc_mp.spec_index(prc_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), prc_ptr, TypedLockMode::Write),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Process(prc_ptr)),
            *final(self) == (KernelK { prc_mp: final(self).prc_mp, ..*old(self) }),
            final(self).prc_mp.perms_wf(),
            process_perms_wf(old(self).prc_mp) ==> process_perms_wf(final(self).prc_mp),
            final(self).prc_mp.dom() =~= old(self).prc_mp.dom().remove(prc_ptr),
            forall|p: RwLockProcessPtr| #![trigger final(self).prc_mp.spec_index(p)] final(self).prc_mp.dom().contains(p) ==> final(self).prc_mp.spec_index(p) == old(self).prc_mp.spec_index(p),
            forall|p: RwLockProcessPtr| #![trigger final(self).prc_mp.lock_id_by_key(p)] final(self).prc_mp.dom().contains(p) ==> final(self).prc_mp.lock_id_by_key(p) == old(self).prc_mp.lock_id_by_key(p),
            typed_lock_maps_aligned(final(self), final(lctx)),
            ret.view().is_init(),
            ret.view().addr() == prc_ptr,
    {
        proof { self.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), prc_ptr); }
        let Tracked(process_perm) = self.prc_mp.remove_with_perm(prc_ptr);
        let ret = retype_process_rwlock_to_4k_page_perm(prc_ptr, Tracked(process_perm), Tracked(parent_node_perm), Tracked(lock_perm), Tracked(&mut *lctx));
        proof {
            remove_process_and_reclaim_4k_page_perm_eof(old(self).prc_mp, self.prc_mp, prc_ptr);
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
        }
        ret
    }
}
} // verus!
