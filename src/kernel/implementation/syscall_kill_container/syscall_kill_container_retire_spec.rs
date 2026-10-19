use vstd::prelude::*;
use crate::*;

verus! {
/// The five 4K object pages of a container with read-only data `ro`: its scheduler, cpu set, and 4K, 2M, and 1G
/// allocators.
pub open spec fn kill_container_retire_pages_4k(ro: ContainerRO) -> Seq<PageIndex> {
    seq![page_ptr2page_index(ro.scheduler), page_ptr2page_index(ro.cpu_set), page_ptr2page_index(ro.allocator_ptr_4k), page_ptr2page_index(ro.allocator_ptr_2m),
        page_ptr2page_index(ro.allocator_ptr_1g)]
}

/// The two 2M object pages of the container `container_ptr` with read-only data `ro`: the container with its offline
/// request table and its PCID allocator.
pub open spec fn kill_container_retire_heads(container_ptr: RwLockContainerPtr, ro: ContainerRO) -> Seq<PageIndex> {
    seq![page_ptr2page_index(container_ptr), page_ptr2page_index(ro.pcid_allocator)]
}

/// The merged tails of both 2M object pages `heads`.
pub open spec fn kill_container_retire_tails(heads: Seq<PageIndex>) -> Set<PageIndex> { page_2m_tail_indices(heads[0]) + page_2m_tail_indices(heads[1]) }

/// Besides containers, the killer write-holds with the permissions given exactly what retiring the marked container
/// `container_ptr` into the killer's container `owner_ptr` takes: the container's marked cpu set, its offline request
/// cell, scheduler shard, and allocator caches on every cpu, its PCID allocator and allocator pools and quotas, the 4K
/// and 2M pools and quotas of `owner_ptr`'s allocators, and the container's object pages with their tails.
pub open spec fn kill_container_retire_held_locks(
    k: KernelK, lctx: LocalContext, container_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, cpu_set_perm: LockPerm, flag_perms: Map<CpuId, LockPerm>,
    pcid_perm: LockPerm, shard_perms: Map<CpuId, LockPerm>, caches_4k: Map<CpuId, LockPerm>, caches_2m: Map<CpuId, LockPerm>, caches_1g: Map<CpuId, LockPerm>,
    pools_4k: Map<RwLockPageAllocatorPtr, LockPerm>, pools_2m: Map<RwLockPageAllocatorPtr, LockPerm>, pool_1g: LockPerm, quotas_4k: Map<RwLockPageAllocatorPtr, LockPerm>,
    quotas_2m: Map<RwLockPageAllocatorPtr, LockPerm>, quota_1g: LockPerm, page_perms: Map<PageIndex, LockPerm>, tails_container: Map<PageIndex, LockPerm>,
    tails_pcid: Map<PageIndex, LockPerm>,
) -> bool {
    let ro = k.ctn_mp.spec_index(container_ptr).view_rodata().view();
    let owner_ro = k.ctn_mp.spec_index(owner_ptr).view_rodata().view();
    let flags_ptr = cpu_offline_flags_ptr(container_ptr);
    let pages_4k = kill_container_retire_pages_4k(ro);
    let heads = kill_container_retire_heads(container_ptr, ro);
    let (a4, a2, a1, o4, o2) = (ro.allocator_ptr_4k, ro.allocator_ptr_2m, ro.allocator_ptr_1g, owner_ro.allocator_ptr_4k, owner_ro.allocator_ptr_2m);
    &&& k.ctn_mp.dom().contains(container_ptr)
    &&& k.ctn_mp.dom().contains(owner_ptr)
    &&& typed_lock_map_contains_mode(lctx.cpu_set_lock_map(), ro.cpu_set, TypedLockMode::Write)
    &&& cpu_set_perm.state() is WriteLock && cpu_set_perm.thread_id() == lctx.thread_id() && cpu_set_perm.lock_id() == k.cpu_set_mp.spec_index(ro.cpu_set).locking_thread()->Write_lock_id
    &&& forall|x: (RwLockCpuOfflineFlagsPtr, CpuId)| #![trigger lctx.cpu_offline_flag_lock_map().dom().contains(x)]
        lctx.cpu_offline_flag_lock_map().dom().contains(x) ==> x.0 == flags_ptr && index_valid(NUM_CPUS, x.1)
    &&& forall|i: CpuId| #![trigger flag_perms.dom().contains(i)] #![trigger flag_perms[i]] index_valid(NUM_CPUS, i) ==> {
        &&& flag_perms.dom().contains(i)
        &&& flag_perms[i].state() is WriteLock
        &&& flag_perms[i].thread_id() == lctx.thread_id()
        &&& flag_perms[i].lock_id() == k.cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(i).view().locking_thread()->Write_lock_id
        &&& typed_lock_map_contains_mode(lctx.cpu_offline_flag_lock_map(), (flags_ptr, i), TypedLockMode::Write)
    }
    &&& lctx.pcid_allocator_lock_map().dom() == set![ro.pcid_allocator]
    &&& typed_lock_map_contains_mode(lctx.pcid_allocator_lock_map(), ro.pcid_allocator, TypedLockMode::Write)
    &&& pcid_perm.state() is WriteLock && pcid_perm.thread_id() == lctx.thread_id() && pcid_perm.lock_id() == k.pcid_allc_mp.spec_index(ro.pcid_allocator).locking_thread()->Write_lock_id
    &&& forall|x: (RwLockSchedulerPtr, CpuId)| #![trigger lctx.scheduler_lock_map().dom().contains(x)]
        lctx.scheduler_lock_map().dom().contains(x) ==> x.0 == ro.scheduler && index_valid(NUM_CPUS, x.1)
    &&& forall|i: CpuId| #![trigger shard_perms.dom().contains(i)] #![trigger shard_perms[i]] index_valid(NUM_CPUS, i) ==> {
        &&& shard_perms.dom().contains(i)
        &&& shard_perms[i].state() is WriteLock
        &&& shard_perms[i].thread_id() == lctx.thread_id()
        &&& k.sched_mp.spec_index(ro.scheduler).shards.spec_index(i).view().locking_thread() == (RwLockState::Write { thread_id: lctx.thread_id(), lock_id: shard_perms[i].lock_id() })
        &&& typed_lock_map_contains_mode(lctx.scheduler_lock_map(), (ro.scheduler, i), TypedLockMode::Write)
    }
    &&& forall|x: (RwLockPageAllocatorPtr, CpuId)| #![trigger lctx.allocator_cache_4k_lock_map().dom().contains(x)]
        lctx.allocator_cache_4k_lock_map().dom().contains(x) ==> x.0 == a4 && index_valid(NUM_CPUS, x.1)
    &&& forall|i: CpuId| #![trigger caches_4k.dom().contains(i)] #![trigger caches_4k[i]] index_valid(NUM_CPUS, i) ==> {
        &&& caches_4k.dom().contains(i)
        &&& caches_4k[i].state() is WriteLock
        &&& caches_4k[i].thread_id() == lctx.thread_id()
        &&& k.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().locking_thread() == (RwLockState::Write { thread_id: lctx.thread_id(), lock_id: caches_4k[i].lock_id() })
        &&& typed_lock_map_contains_mode(lctx.allocator_cache_4k_lock_map(), (a4, i), TypedLockMode::Write)
    }
    &&& forall|x: (RwLockPageAllocatorPtr, CpuId)| #![trigger lctx.allocator_cache_2m_lock_map().dom().contains(x)]
        lctx.allocator_cache_2m_lock_map().dom().contains(x) ==> x.0 == a2 && index_valid(NUM_CPUS, x.1)
    &&& forall|i: CpuId| #![trigger caches_2m.dom().contains(i)] #![trigger caches_2m[i]] index_valid(NUM_CPUS, i) ==> {
        &&& caches_2m.dom().contains(i)
        &&& caches_2m[i].state() is WriteLock
        &&& caches_2m[i].thread_id() == lctx.thread_id()
        &&& k.allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().locking_thread() == (RwLockState::Write { thread_id: lctx.thread_id(), lock_id: caches_2m[i].lock_id() })
        &&& typed_lock_map_contains_mode(lctx.allocator_cache_2m_lock_map(), (a2, i), TypedLockMode::Write)
    }
    &&& forall|x: (RwLockPageAllocatorPtr, CpuId)| #![trigger lctx.allocator_cache_1g_lock_map().dom().contains(x)]
        lctx.allocator_cache_1g_lock_map().dom().contains(x) ==> x.0 == a1 && index_valid(NUM_CPUS, x.1)
    &&& forall|i: CpuId| #![trigger caches_1g.dom().contains(i)] #![trigger caches_1g[i]] index_valid(NUM_CPUS, i) ==> {
        &&& caches_1g.dom().contains(i)
        &&& caches_1g[i].state() is WriteLock
        &&& caches_1g[i].thread_id() == lctx.thread_id()
        &&& k.allc_1g_mp.spec_index(a1).cpu_caches.spec_index(i).view().locking_thread() == (RwLockState::Write { thread_id: lctx.thread_id(), lock_id: caches_1g[i].lock_id() })
        &&& typed_lock_map_contains_mode(lctx.allocator_cache_1g_lock_map(), (a1, i), TypedLockMode::Write)
    }
    &&& lctx.allocator_global_pool_4k_lock_map().dom() == set![a4, o4]
    &&& pools_4k.dom() == set![a4, o4]
    &&& typed_lock_map_contains_mode(lctx.allocator_global_pool_4k_lock_map(), a4, TypedLockMode::Write)
    &&& pools_4k[a4].state() is WriteLock && pools_4k[a4].thread_id() == lctx.thread_id() && pools_4k[a4].lock_id() == k.allc_4k_mp.spec_index(a4).global_pool.locking_thread()->Write_lock_id
    &&& typed_lock_map_contains_mode(lctx.allocator_global_pool_4k_lock_map(), o4, TypedLockMode::Write)
    &&& pools_4k[o4].state() is WriteLock && pools_4k[o4].thread_id() == lctx.thread_id() && pools_4k[o4].lock_id() == k.allc_4k_mp.spec_index(o4).global_pool.locking_thread()->Write_lock_id
    &&& lctx.allocator_global_pool_2m_lock_map().dom() == set![a2, o2]
    &&& pools_2m.dom() == set![a2, o2]
    &&& typed_lock_map_contains_mode(lctx.allocator_global_pool_2m_lock_map(), a2, TypedLockMode::Write)
    &&& pools_2m[a2].state() is WriteLock && pools_2m[a2].thread_id() == lctx.thread_id() && pools_2m[a2].lock_id() == k.allc_2m_mp.spec_index(a2).global_pool.locking_thread()->Write_lock_id
    &&& typed_lock_map_contains_mode(lctx.allocator_global_pool_2m_lock_map(), o2, TypedLockMode::Write)
    &&& pools_2m[o2].state() is WriteLock && pools_2m[o2].thread_id() == lctx.thread_id() && pools_2m[o2].lock_id() == k.allc_2m_mp.spec_index(o2).global_pool.locking_thread()->Write_lock_id
    &&& lctx.allocator_global_pool_1g_lock_map().dom() == set![a1]
    &&& typed_lock_map_contains_mode(lctx.allocator_global_pool_1g_lock_map(), a1, TypedLockMode::Write)
    &&& pool_1g.state() is WriteLock && pool_1g.thread_id() == lctx.thread_id() && pool_1g.lock_id() == k.allc_1g_mp.spec_index(a1).global_pool.locking_thread()->Write_lock_id
    &&& lctx.allocator_quota_4k_lock_map().dom() == set![a4, o4]
    &&& quotas_4k.dom() == set![a4, o4]
    &&& typed_lock_map_contains_mode(lctx.allocator_quota_4k_lock_map(), a4, TypedLockMode::Write)
    &&& quotas_4k[a4].state() is WriteLock && quotas_4k[a4].thread_id() == lctx.thread_id() && quotas_4k[a4].lock_id() == k.allc_4k_mp.spec_index(a4).quota.locking_thread()->Write_lock_id
    &&& typed_lock_map_contains_mode(lctx.allocator_quota_4k_lock_map(), o4, TypedLockMode::Write)
    &&& quotas_4k[o4].state() is WriteLock && quotas_4k[o4].thread_id() == lctx.thread_id() && quotas_4k[o4].lock_id() == k.allc_4k_mp.spec_index(o4).quota.locking_thread()->Write_lock_id
    &&& lctx.allocator_quota_2m_lock_map().dom() == set![a2, o2]
    &&& quotas_2m.dom() == set![a2, o2]
    &&& typed_lock_map_contains_mode(lctx.allocator_quota_2m_lock_map(), a2, TypedLockMode::Write)
    &&& quotas_2m[a2].state() is WriteLock && quotas_2m[a2].thread_id() == lctx.thread_id() && quotas_2m[a2].lock_id() == k.allc_2m_mp.spec_index(a2).quota.locking_thread()->Write_lock_id
    &&& typed_lock_map_contains_mode(lctx.allocator_quota_2m_lock_map(), o2, TypedLockMode::Write)
    &&& quotas_2m[o2].state() is WriteLock && quotas_2m[o2].thread_id() == lctx.thread_id() && quotas_2m[o2].lock_id() == k.allc_2m_mp.spec_index(o2).quota.locking_thread()->Write_lock_id
    &&& lctx.allocator_quota_1g_lock_map().dom() == set![a1]
    &&& typed_lock_map_contains_mode(lctx.allocator_quota_1g_lock_map(), a1, TypedLockMode::Write)
    &&& quota_1g.state() is WriteLock && quota_1g.thread_id() == lctx.thread_id() && quota_1g.lock_id() == k.allc_1g_mp.spec_index(a1).quota.locking_thread()->Write_lock_id
    &&& page_perms.dom() == pages_4k.to_set().insert(heads[0]).insert(heads[1])
    &&& lctx.page_lock_map().dom() == page_perms.dom() + page_2m_tail_indices(heads[0]) + page_2m_tail_indices(heads[1])
    &&& forall|p: PageIndex| #![trigger page_perms.dom().contains(p)] page_perms.dom().contains(p) ==> {
        &&& typed_lock_map_contains_mode(lctx.page_lock_map(), p, TypedLockMode::Write)
        &&& page_perms[p].state() is WriteLock && page_perms[p].thread_id() == lctx.thread_id() && page_perms[p].lock_id() == k.pg_arr.spec_index(p).view().locking_thread()->Write_lock_id
    }
    &&& owned_2m_tail_lock_perms_wf(tails_container, k.pg_arr, &lctx, heads[0])
    &&& owned_2m_tail_lock_perms_wf(tails_pcid, k.pg_arr, &lctx, heads[1])
}
} // verus!
