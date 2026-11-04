use vstd::prelude::*;
use crate::*;

verus! {
/// A container with `retire_ready` set is marked and owns no process, thread, indirect thread, child, or subtree container,
/// and its 4K, 2M, and 1G allocators hold no quota and no page in any cpu cache.
#[verifier::opaque]
pub open spec fn container_kill_retire_wf(
    ctn_mp: ContainerLockedMap, allc_4k_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, allc_2m_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>,
    allc_1g_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>,
) -> bool {
    forall|c: RwLockContainerPtr|
        #![trigger ctn_mp.spec_index(c).view_ghost().retire_ready]
        ctn_mp.dom().contains(c) && ctn_mp.spec_index(c).view_ghost().retire_ready ==> {
            let container = ctn_mp.spec_index(c);
            let ro = container.view_rodata().view();
            &&& container.being_killed()
            &&& container.view_ghost().owned_processes.view() == Set::<RwLockProcessPtr>::empty()
            &&& container.view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty()
            &&& container.view_ghost().owned_indirect_threads.view() == Set::<RwLockThreadPtr>::empty()
            &&& container.view().children.view().len() == 0
            &&& container.view_ghost().subtree_set.view() == Set::<RwLockContainerPtr>::empty()
            &&& allc_4k_mp.dom().contains(ro.allocator_ptr_4k)
            &&& allc_4k_mp.spec_index(ro.allocator_ptr_4k).quota.view().value == 0
            &&& allc_2m_mp.dom().contains(ro.allocator_ptr_2m)
            &&& allc_2m_mp.spec_index(ro.allocator_ptr_2m).quota.view().value == 0
            &&& allc_1g_mp.dom().contains(ro.allocator_ptr_1g)
            &&& allc_1g_mp.spec_index(ro.allocator_ptr_1g).quota.view().value == 0
            &&& forall|cpu_id: CpuId|
                #![trigger allc_4k_mp.spec_index(ro.allocator_ptr_4k).cpu_caches.spec_index(cpu_id)]
                index_valid(NUM_CPUS, cpu_id) ==> allc_4k_mp.spec_index(ro.allocator_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().linked_list.view().len() == 0
            &&& forall|cpu_id: CpuId|
                #![trigger allc_2m_mp.spec_index(ro.allocator_ptr_2m).cpu_caches.spec_index(cpu_id)]
                index_valid(NUM_CPUS, cpu_id) ==> allc_2m_mp.spec_index(ro.allocator_ptr_2m).cpu_caches.spec_index(cpu_id).view().view().linked_list.view().len() == 0
            &&& forall|cpu_id: CpuId|
                #![trigger allc_1g_mp.spec_index(ro.allocator_ptr_1g).cpu_caches.spec_index(cpu_id)]
                index_valid(NUM_CPUS, cpu_id) ==> allc_1g_mp.spec_index(ro.allocator_ptr_1g).cpu_caches.spec_index(cpu_id).view().view().linked_list.view().len() == 0
        }
}

/// The retire-ready container `ctn_ptr` is marked, empty, and holds no quota and no cached page.
pub proof fn container_kill_retire_wf_at(
    ctn_mp: ContainerLockedMap, allc_4k_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, allc_2m_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>,
    allc_1g_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, ctn_ptr: RwLockContainerPtr,
)
    requires
        container_kill_retire_wf(ctn_mp, allc_4k_mp, allc_2m_mp, allc_1g_mp),
        ctn_mp.dom().contains(ctn_ptr),
        ctn_mp.spec_index(ctn_ptr).view_ghost().retire_ready,
    ensures
        ({
            let container = ctn_mp.spec_index(ctn_ptr);
            let ro = container.view_rodata().view();
            &&& container.being_killed()
            &&& container.view_ghost().owned_processes.view() == Set::<RwLockProcessPtr>::empty()
            &&& container.view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty()
            &&& container.view_ghost().owned_indirect_threads.view() == Set::<RwLockThreadPtr>::empty()
            &&& container.view().children.view().len() == 0
            &&& container.view_ghost().subtree_set.view() == Set::<RwLockContainerPtr>::empty()
            &&& allc_4k_mp.dom().contains(ro.allocator_ptr_4k)
            &&& allc_4k_mp.spec_index(ro.allocator_ptr_4k).quota.view().value == 0
            &&& allc_2m_mp.dom().contains(ro.allocator_ptr_2m)
            &&& allc_2m_mp.spec_index(ro.allocator_ptr_2m).quota.view().value == 0
            &&& allc_1g_mp.dom().contains(ro.allocator_ptr_1g)
            &&& allc_1g_mp.spec_index(ro.allocator_ptr_1g).quota.view().value == 0
            &&& forall|cpu_id: CpuId|
                #![trigger allc_4k_mp.spec_index(ro.allocator_ptr_4k).cpu_caches.spec_index(cpu_id)]
                index_valid(NUM_CPUS, cpu_id) ==> allc_4k_mp.spec_index(ro.allocator_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().linked_list.view().len() == 0
            &&& forall|cpu_id: CpuId|
                #![trigger allc_2m_mp.spec_index(ro.allocator_ptr_2m).cpu_caches.spec_index(cpu_id)]
                index_valid(NUM_CPUS, cpu_id) ==> allc_2m_mp.spec_index(ro.allocator_ptr_2m).cpu_caches.spec_index(cpu_id).view().view().linked_list.view().len() == 0
            &&& forall|cpu_id: CpuId|
                #![trigger allc_1g_mp.spec_index(ro.allocator_ptr_1g).cpu_caches.spec_index(cpu_id)]
                index_valid(NUM_CPUS, cpu_id) ==> allc_1g_mp.spec_index(ro.allocator_ptr_1g).cpu_caches.spec_index(cpu_id).view().view().linked_list.view().len() == 0
        }),
{ reveal(container_kill_retire_wf); }

/// A container that owns the thread `thrd_ptr` directly or indirectly is not retire-ready.
pub proof fn container_owns_thread_implies_not_retire_ready(
    ctn_mp: ContainerLockedMap, allc_4k_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, allc_2m_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>,
    allc_1g_mp: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, ctn_ptr: RwLockContainerPtr, thrd_ptr: RwLockThreadPtr,
)
    requires
        container_kill_retire_wf(ctn_mp, allc_4k_mp, allc_2m_mp, allc_1g_mp),
        ctn_mp.dom().contains(ctn_ptr),
        ctn_mp.spec_index(ctn_ptr).view_ghost().owned_threads.view().contains(thrd_ptr)
            || ctn_mp.spec_index(ctn_ptr).view_ghost().owned_indirect_threads.view().contains(thrd_ptr),
    ensures
        !ctn_mp.spec_index(ctn_ptr).view_ghost().retire_ready,
{ reveal(container_kill_retire_wf); }

/// The container `ctn_ptr` that owns no thread has no thread queued on shard `cpu_id` of its scheduler.
pub proof fn container_owns_no_thread_implies_shard_empty(k: KernelK, ctn_ptr: RwLockContainerPtr, cpu_id: CpuId)
    requires
        k.inv(),
        k.ctn_mp.dom().contains(ctn_ptr),
        k.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty(),
        index_valid(NUM_CPUS, cpu_id),
    ensures k.sched_mp.spec_index(k.ctn_mp.spec_index(ctn_ptr).view_rodata().view().scheduler).shards.spec_index(cpu_id).view().view().queue.view().len() == 0,
{
    let sched_ptr = k.ctn_mp.spec_index(ctn_ptr).view_rodata().view().scheduler;
    container_scheduler_wf_container_at(k.ctn_mp, k.sched_mp, ctn_ptr);
    if k.sched_mp.spec_index(sched_ptr).shard(cpu_id).queue.view().len() > 0 {
        let thrd_ptr = k.sched_mp.spec_index(sched_ptr).shard(cpu_id).queue.view()[0];
        assert(k.sched_mp.spec_index(sched_ptr).shard(cpu_id).queue.view().contains(thrd_ptr));
        container_thread_scheduler_wf_shard_at(k.ctn_mp, k.thrd_mp, k.sched_mp, sched_ptr, cpu_id, thrd_ptr); container_thread_wf_thread_at(k.ctn_mp, k.thrd_mp, thrd_ptr);
        assert(k.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_threads.view().contains(thrd_ptr));
    }
}
} // verus!
