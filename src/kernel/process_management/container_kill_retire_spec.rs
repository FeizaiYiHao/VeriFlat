use vstd::prelude::*;
use crate::*;

verus! {
/// A container whose killer set `retire_ready` is marked, owns no process, thread, indirect thread, child, or subtree container,
/// and its 4K, 2M, and 1G allocators hold no quota and no page in any cpu cache.
#[verifier::opaque]
pub open spec fn container_kill_retire_wf(
    container_map: ContainerLockedMap, allocator_4k_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, allocator_2m_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>,
    allocator_1g_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>,
) -> bool {
    forall|c: RwLockContainerPtr| #![trigger container_map.spec_index(c).view_ghost().retire_ready]
        container_map.dom().contains(c) && container_map.spec_index(c).view_ghost().retire_ready ==> {
            let container = container_map.spec_index(c);
            let ro = container.view_rodata().view();
            &&& container.being_killed()
            &&& container.view_ghost().owned_processes.view() == Set::<RwLockProcessPtr>::empty()
            &&& container.view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty()
            &&& container.view_ghost().owned_indirect_threads.view() == Set::<RwLockThreadPtr>::empty()
            &&& container.view().children.view().len() == 0
            &&& container.view_ghost().subtree_set.view() == Set::<RwLockContainerPtr>::empty()
            &&& allocator_4k_map.dom().contains(ro.allocator_ptr_4k) && allocator_4k_map.spec_index(ro.allocator_ptr_4k).quota.view().value == 0
            &&& allocator_2m_map.dom().contains(ro.allocator_ptr_2m) && allocator_2m_map.spec_index(ro.allocator_ptr_2m).quota.view().value == 0
            &&& allocator_1g_map.dom().contains(ro.allocator_ptr_1g) && allocator_1g_map.spec_index(ro.allocator_ptr_1g).quota.view().value == 0
            &&& forall|i: CpuId| #![trigger allocator_4k_map.spec_index(ro.allocator_ptr_4k).cpu_caches.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> allocator_4k_map.spec_index(ro.allocator_ptr_4k).cpu_caches.spec_index(i).view().view().linked_list.view().len() == 0
            &&& forall|i: CpuId| #![trigger allocator_2m_map.spec_index(ro.allocator_ptr_2m).cpu_caches.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> allocator_2m_map.spec_index(ro.allocator_ptr_2m).cpu_caches.spec_index(i).view().view().linked_list.view().len() == 0
            &&& forall|i: CpuId| #![trigger allocator_1g_map.spec_index(ro.allocator_ptr_1g).cpu_caches.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> allocator_1g_map.spec_index(ro.allocator_ptr_1g).cpu_caches.spec_index(i).view().view().linked_list.view().len() == 0
        }
}

/// The retire-ready container `c` is marked, empty, and holds no quota and no cached page.
pub proof fn container_kill_retire_wf_at(
    container_map: ContainerLockedMap, allocator_4k_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, allocator_2m_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>,
    allocator_1g_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, c: RwLockContainerPtr,
)
    requires
        container_kill_retire_wf(container_map, allocator_4k_map, allocator_2m_map, allocator_1g_map),
        container_map.dom().contains(c),
        container_map.spec_index(c).view_ghost().retire_ready,
    ensures
        ({
            let container = container_map.spec_index(c);
            let ro = container.view_rodata().view();
            &&& container.being_killed()
            &&& container.view_ghost().owned_processes.view() == Set::<RwLockProcessPtr>::empty()
            &&& container.view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty()
            &&& container.view_ghost().owned_indirect_threads.view() == Set::<RwLockThreadPtr>::empty()
            &&& container.view().children.view().len() == 0
            &&& container.view_ghost().subtree_set.view() == Set::<RwLockContainerPtr>::empty()
            &&& allocator_4k_map.dom().contains(ro.allocator_ptr_4k) && allocator_4k_map.spec_index(ro.allocator_ptr_4k).quota.view().value == 0
            &&& allocator_2m_map.dom().contains(ro.allocator_ptr_2m) && allocator_2m_map.spec_index(ro.allocator_ptr_2m).quota.view().value == 0
            &&& allocator_1g_map.dom().contains(ro.allocator_ptr_1g) && allocator_1g_map.spec_index(ro.allocator_ptr_1g).quota.view().value == 0
            &&& forall|i: CpuId| #![trigger allocator_4k_map.spec_index(ro.allocator_ptr_4k).cpu_caches.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> allocator_4k_map.spec_index(ro.allocator_ptr_4k).cpu_caches.spec_index(i).view().view().linked_list.view().len() == 0
            &&& forall|i: CpuId| #![trigger allocator_2m_map.spec_index(ro.allocator_ptr_2m).cpu_caches.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> allocator_2m_map.spec_index(ro.allocator_ptr_2m).cpu_caches.spec_index(i).view().view().linked_list.view().len() == 0
            &&& forall|i: CpuId| #![trigger allocator_1g_map.spec_index(ro.allocator_ptr_1g).cpu_caches.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> allocator_1g_map.spec_index(ro.allocator_ptr_1g).cpu_caches.spec_index(i).view().view().linked_list.view().len() == 0
        }),
{ reveal(container_kill_retire_wf); }

/// A container that owns the thread `thread_ptr` directly or indirectly is not retire-ready.
pub proof fn container_with_thread_not_retire_ready_at(
    container_map: ContainerLockedMap, allocator_4k_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, allocator_2m_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>,
    allocator_1g_map: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, c: RwLockContainerPtr, thread_ptr: RwLockThreadPtr,
)
    requires
        container_kill_retire_wf(container_map, allocator_4k_map, allocator_2m_map, allocator_1g_map),
        container_map.dom().contains(c),
        container_map.spec_index(c).view_ghost().owned_threads.view().contains(thread_ptr)
            || container_map.spec_index(c).view_ghost().owned_indirect_threads.view().contains(thread_ptr),
    ensures
        !container_map.spec_index(c).view_ghost().retire_ready,
{ reveal(container_kill_retire_wf); }

/// The container `container_ptr` that owns no thread has no thread queued on shard `cpu_id` of its scheduler.
pub proof fn container_without_threads_shard_empty_at(k: KernelK, container_ptr: RwLockContainerPtr, cpu_id: CpuId)
    requires
        k.inv(),
        k.ctn_mp.dom().contains(container_ptr),
        k.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty(),
        index_valid(NUM_CPUS, cpu_id),
    ensures k.sched_mp.spec_index(k.ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler).shards.spec_index(cpu_id).view().view().queue.view().len() == 0,
{
    let sched = k.ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler;
    container_scheduler_wf_at(k.ctn_mp, k.sched_mp, container_ptr);
    if k.sched_mp.spec_index(sched).shard(cpu_id).queue.view().len() > 0 {
        let t = k.sched_mp.spec_index(sched).shard(cpu_id).queue.view()[0];
        assert(k.sched_mp.spec_index(sched).shard(cpu_id).queue.view().contains(t));
        container_thread_scheduler_wf_at(k.ctn_mp, k.thr_mp, k.sched_mp, sched, cpu_id, t); container_thread_wf_at(k.ctn_mp, k.thr_mp, t);
        assert(k.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().contains(t));
    }
}
} // verus!
