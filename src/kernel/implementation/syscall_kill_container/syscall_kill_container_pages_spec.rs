use vstd::prelude::*;
use crate::*;

verus! {
/// The killer on `cpu_id`, which runs `thread_ptr` of `process_ptr` in its container `owner_ptr`, write-holds with the
/// permissions given exactly its cpu, its process, and itself, and also its container and the marked container
/// `container_ptr`, which owns no process, thread, or indirect thread; every other container or cpu set it holds is marked.
/// It holds no page, table, endpoint, scheduler, PCID allocator, dirty-PCID record, or cpu offline flag.
pub open spec fn kill_container_pages_killer_state(
    k: KernelK, lctx: LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    owner_ptr: RwLockContainerPtr, cpu_perm: LockPerm, process_perm: LockPerm, thread_perm: LockPerm, container_perm: LockPerm, owner_perm: LockPerm,
) -> bool {
    let cpu = k.cpu_arr.spec_index(cpu_id).view().view().view();
    let target = k.ctn_mp.spec_index(container_ptr);
    &&& lctx.cpu_id() == cpu_id
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& k.prc_mp.dom().contains(process_ptr)
    &&& k.thr_mp.dom().contains(thread_ptr)
    &&& k.ctn_mp.dom().contains(container_ptr)
    &&& k.ctn_mp.dom().contains(owner_ptr)
    &&& lctx.cpu_lock_map().dom() =~= set![cpu_id]
    &&& typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write)
    &&& cpu.state is Running
    &&& cpu.current_process == Some(process_ptr)
    &&& cpu.current_thread == Some(thread_ptr)
    &&& cpu.owning_container == owner_ptr
    &&& lctx.process_lock_map().dom() =~= set![process_ptr]
    &&& typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write)
    &&& lctx.thread_lock_map().dom() =~= set![thread_ptr]
    &&& typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write)
    &&& !(k.thr_mp.spec_index(thread_ptr).view().state is SCHEDULED)
    &&& typed_lock_map_contains_mode(lctx.container_lock_map(), owner_ptr, TypedLockMode::Write)
    &&& typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write)
    &&& forall|c: RwLockContainerPtr| #![trigger lctx.container_lock_map().dom().contains(c)] lctx.container_lock_map().dom().contains(c)
        ==> k.ctn_mp.dom().contains(c) && (c != owner_ptr ==> k.ctn_mp.spec_index(c).being_killed())
    &&& owner_ptr != container_ptr
    &&& target.being_killed()
    &&& target.view_ghost().uppertree_seq.view().contains(owner_ptr)
    &&& target.view_ghost().owned_processes.view() == Set::<RwLockProcessPtr>::empty()
    &&& target.view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty()
    &&& target.view_ghost().owned_indirect_threads.view() == Set::<RwLockThreadPtr>::empty()
    &&& forall|s: RwLockCpuSetPtr| #![trigger lctx.cpu_set_lock_map().dom().contains(s)] lctx.cpu_set_lock_map().dom().contains(s) ==> k.cpu_set_mp.spec_index(s).being_killed()
    &&& lctx.page_lock_map().dom().is_empty()
    &&& lctx.pagetable_lock_map().dom().is_empty()
    &&& lctx.pagetable_window_lock_map().dom().is_empty()
    &&& lctx.iommu_table_lock_map().dom().is_empty()
    &&& lctx.iommu_root_table_lock_map().dom().is_empty()
    &&& lctx.endpoint_lock_map().dom().is_empty()
    &&& lctx.scheduler_lock_map().dom().is_empty()
    &&& lctx.pcid_allocator_lock_map().dom().is_empty()
    &&& lctx.pcid_needflush_lock_map().dom().is_empty()
    &&& lctx.cpu_offline_flag_lock_map().dom().is_empty()
    &&& cpu_perm.state() is WriteLock && cpu_perm.thread_id() == lctx.thread_id() && cpu_perm.lock_id() == k.cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id
    &&& process_perm.state() is WriteLock && process_perm.thread_id() == lctx.thread_id() && process_perm.lock_id() == k.prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id
    &&& thread_perm.state() is WriteLock && thread_perm.thread_id() == lctx.thread_id() && thread_perm.lock_id() == k.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id
    &&& container_perm.state() is WriteLock && container_perm.thread_id() == lctx.thread_id() && container_perm.lock_id() == target.locking_thread()->Write_lock_id
    &&& owner_perm.state() is WriteLock && owner_perm.thread_id() == lctx.thread_id() && owner_perm.lock_id() == k.ctn_mp.spec_index(owner_ptr).locking_thread()->Write_lock_id
}

/// The killer write-holds, with the permissions given, the 4K and 2M allocator caches on every cpu of the marked
/// container `container_ptr`'s 4K and 2M allocators `a4` and `a2`, and the 4K and 2M global pools and quotas of those
/// allocators and of its own container `owner_ptr`'s allocators `o4` and `o2`; it holds no other allocator lock.
pub open spec fn kill_container_pages_allocator_locks(
    k: KernelK, lctx: LocalContext, container_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, a4: RwLockPageAllocatorPtr, o4: RwLockPageAllocatorPtr,
    a2: RwLockPageAllocatorPtr, o2: RwLockPageAllocatorPtr,
    caches_4k: Map<CpuId, LockPerm>, caches_2m: Map<CpuId, LockPerm>, pools_4k: Map<RwLockPageAllocatorPtr, LockPerm>, pools_2m: Map<RwLockPageAllocatorPtr, LockPerm>,
    quotas_4k: Map<RwLockPageAllocatorPtr, LockPerm>, quotas_2m: Map<RwLockPageAllocatorPtr, LockPerm>,
) -> bool {
    &&& k.ctn_mp.dom().contains(container_ptr)
    &&& k.ctn_mp.dom().contains(owner_ptr)
    &&& k.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == a4
    &&& k.ctn_mp.spec_index(owner_ptr).view_rodata().view().allocator_ptr_4k == o4
    &&& k.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m == a2
    &&& k.ctn_mp.spec_index(owner_ptr).view_rodata().view().allocator_ptr_2m == o2
    &&& k.allc_4k_mp.dom().contains(a4)
    &&& k.allc_4k_mp.dom().contains(o4)
    &&& k.allc_2m_mp.dom().contains(a2)
    &&& k.allc_2m_mp.dom().contains(o2)
    &&& a4 != o4
    &&& a2 != o2
    &&& forall|x: (RwLockPageAllocatorPtr, CpuId)| #![trigger lctx.allocator_cache_4k_lock_map().dom().contains(x)]
        lctx.allocator_cache_4k_lock_map().dom().contains(x) ==> x.0 == a4 && index_valid(NUM_CPUS, x.1)
    &&& forall|c: CpuId| #![trigger caches_4k.dom().contains(c)] #![trigger caches_4k[c]] #![trigger lctx.allocator_cache_4k_lock_map().dom().contains((a4, c))]
        index_valid(NUM_CPUS, c) ==> {
        &&& caches_4k.dom().contains(c)
        &&& typed_lock_map_contains_mode(lctx.allocator_cache_4k_lock_map(), (a4, c), TypedLockMode::Write)
        &&& caches_4k[c].state() is WriteLock
        &&& caches_4k[c].thread_id() == lctx.thread_id()
        &&& caches_4k[c].lock_id() == k.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(c).view().locking_thread()->Write_lock_id
    }
    &&& forall|x: (RwLockPageAllocatorPtr, CpuId)| #![trigger lctx.allocator_cache_2m_lock_map().dom().contains(x)]
        lctx.allocator_cache_2m_lock_map().dom().contains(x) ==> x.0 == a2 && index_valid(NUM_CPUS, x.1)
    &&& forall|c: CpuId| #![trigger caches_2m.dom().contains(c)] #![trigger caches_2m[c]] #![trigger lctx.allocator_cache_2m_lock_map().dom().contains((a2, c))]
        index_valid(NUM_CPUS, c) ==> {
        &&& caches_2m.dom().contains(c)
        &&& typed_lock_map_contains_mode(lctx.allocator_cache_2m_lock_map(), (a2, c), TypedLockMode::Write)
        &&& caches_2m[c].state() is WriteLock
        &&& caches_2m[c].thread_id() == lctx.thread_id()
        &&& caches_2m[c].lock_id() == k.allc_2m_mp.spec_index(a2).cpu_caches.spec_index(c).view().locking_thread()->Write_lock_id
    }
    &&& lctx.allocator_global_pool_4k_lock_map().dom() == set![a4, o4]
    &&& pools_4k.dom() == set![a4, o4]
    &&& typed_lock_map_contains_mode(lctx.allocator_global_pool_4k_lock_map(), a4, TypedLockMode::Write) && typed_lock_map_contains_mode(lctx.allocator_global_pool_4k_lock_map(), o4, TypedLockMode::Write)
    &&& pools_4k[a4].state() is WriteLock && pools_4k[a4].thread_id() == lctx.thread_id() && pools_4k[a4].lock_id() == k.allc_4k_mp.spec_index(a4).global_pool.locking_thread()->Write_lock_id
    &&& pools_4k[o4].state() is WriteLock && pools_4k[o4].thread_id() == lctx.thread_id() && pools_4k[o4].lock_id() == k.allc_4k_mp.spec_index(o4).global_pool.locking_thread()->Write_lock_id
    &&& lctx.allocator_global_pool_2m_lock_map().dom() == set![a2, o2]
    &&& pools_2m.dom() == set![a2, o2]
    &&& typed_lock_map_contains_mode(lctx.allocator_global_pool_2m_lock_map(), a2, TypedLockMode::Write) && typed_lock_map_contains_mode(lctx.allocator_global_pool_2m_lock_map(), o2, TypedLockMode::Write)
    &&& pools_2m[a2].state() is WriteLock && pools_2m[a2].thread_id() == lctx.thread_id() && pools_2m[a2].lock_id() == k.allc_2m_mp.spec_index(a2).global_pool.locking_thread()->Write_lock_id
    &&& pools_2m[o2].state() is WriteLock && pools_2m[o2].thread_id() == lctx.thread_id() && pools_2m[o2].lock_id() == k.allc_2m_mp.spec_index(o2).global_pool.locking_thread()->Write_lock_id
    &&& lctx.allocator_quota_4k_lock_map().dom() == set![a4, o4]
    &&& quotas_4k.dom() == set![a4, o4]
    &&& typed_lock_map_contains_mode(lctx.allocator_quota_4k_lock_map(), a4, TypedLockMode::Write) && typed_lock_map_contains_mode(lctx.allocator_quota_4k_lock_map(), o4, TypedLockMode::Write)
    &&& quotas_4k[a4].state() is WriteLock && quotas_4k[a4].thread_id() == lctx.thread_id() && quotas_4k[a4].lock_id() == k.allc_4k_mp.spec_index(a4).quota.locking_thread()->Write_lock_id
    &&& quotas_4k[o4].state() is WriteLock && quotas_4k[o4].thread_id() == lctx.thread_id() && quotas_4k[o4].lock_id() == k.allc_4k_mp.spec_index(o4).quota.locking_thread()->Write_lock_id
    &&& lctx.allocator_quota_2m_lock_map().dom() == set![a2, o2]
    &&& quotas_2m.dom() == set![a2, o2]
    &&& typed_lock_map_contains_mode(lctx.allocator_quota_2m_lock_map(), a2, TypedLockMode::Write) && typed_lock_map_contains_mode(lctx.allocator_quota_2m_lock_map(), o2, TypedLockMode::Write)
    &&& quotas_2m[a2].state() is WriteLock && quotas_2m[a2].thread_id() == lctx.thread_id() && quotas_2m[a2].lock_id() == k.allc_2m_mp.spec_index(a2).quota.locking_thread()->Write_lock_id
    &&& quotas_2m[o2].state() is WriteLock && quotas_2m[o2].thread_id() == lctx.thread_id() && quotas_2m[o2].lock_id() == k.allc_2m_mp.spec_index(o2).quota.locking_thread()->Write_lock_id
    &&& lctx.holds_no_allocator_locks(PageSize::SZ1g)
}
} // verus!
