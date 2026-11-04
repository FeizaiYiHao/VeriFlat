use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn container_scheduler_wf(container_map: ContainerLockedMap, scheduler_map: SchedulerUnLockedMap) -> bool {
        &&& forall|c_ptr:RwLockContainerPtr|
            #![trigger container_map.dom().contains(c_ptr)]
            container_map.dom().contains(c_ptr)
                ==> scheduler_map.dom().contains(container_map.spec_index(c_ptr).view_rodata().view().scheduler) && scheduler_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().scheduler).owning_container == c_ptr
        &&& forall|s_ptr:RwLockSchedulerPtr|
            #![trigger scheduler_map.dom().contains(s_ptr)]
            scheduler_map.dom().contains(s_ptr)
                ==> container_map.dom().contains(scheduler_map.spec_index(s_ptr).owning_container) && container_map.spec_index(scheduler_map.spec_index(s_ptr).owning_container).view_rodata().view().scheduler == s_ptr
    }

    pub proof fn container_scheduler_wf_at(container_map: ContainerLockedMap, scheduler_map: SchedulerUnLockedMap, ctn_ptr: RwLockContainerPtr)
        requires
            container_scheduler_wf(container_map, scheduler_map),
            container_map.dom().contains(ctn_ptr),
        ensures
            scheduler_map.dom().contains(container_map.spec_index(ctn_ptr).view_rodata().view().scheduler),
            scheduler_map.spec_index(container_map.spec_index(ctn_ptr).view_rodata().view().scheduler).owning_container == ctn_ptr,
    { reveal(container_scheduler_wf); }

    /// A thread is `SCHEDULED { cpu_id }` exactly when it is queued on shard `cpu_id` of its
    /// container's scheduler.
    // Proof dependencies (confirmed): container_thread_wf,
    // container_scheduler_wf.
    #[verifier::opaque]
    pub open spec fn container_thread_scheduler_wf(container_map: ContainerLockedMap, thread_map: ThreadLockedMap, scheduler_map: SchedulerUnLockedMap) -> bool {
        &&& forall|t_ptr:RwLockThreadPtr|
            #![trigger thread_map.spec_index(t_ptr).view().state]
            #![trigger thread_map.spec_index(t_ptr).view().owning_container]
            thread_map.dom().contains(t_ptr) && thread_map.spec_index(t_ptr).view().state is SCHEDULED ==> {
                let thread = thread_map.spec_index(t_ptr).view();
                let queue = scheduler_map.spec_index(container_map.spec_index(thread.owning_container).view_rodata().view().scheduler).shard(thread.state->SCHEDULED_cpu_id).queue;
                &&& index_valid(NUM_CPUS, thread.state->SCHEDULED_cpu_id)
                &&& queue.view().contains(t_ptr)
                &&& queue.map().dom().contains(thread.scheduler_linkedlist_node.addr())
                &&& queue.map().spec_index(thread.scheduler_linkedlist_node.addr()) == t_ptr
            }
        &&& forall|s_ptr:RwLockSchedulerPtr, cpu_id: CpuId, t_ptr:RwLockThreadPtr|
            #![trigger scheduler_map.spec_index(s_ptr).shard(cpu_id).queue.view().contains(t_ptr)]
            #![trigger thread_map.spec_index(t_ptr).view().state, scheduler_map.dom().contains(s_ptr), index_valid(NUM_CPUS, cpu_id)]
            #![trigger thread_map.spec_index(t_ptr).view().owning_container, scheduler_map.dom().contains(s_ptr), index_valid(NUM_CPUS, cpu_id)]
            scheduler_map.dom().contains(s_ptr) && index_valid(NUM_CPUS, cpu_id) && scheduler_map.spec_index(s_ptr).shard(cpu_id).queue.view().contains(t_ptr) ==> {
                &&& thread_map.dom().contains(t_ptr)
                &&& thread_map.spec_index(t_ptr).view().state == (ThreadState::SCHEDULED { cpu_id })
                &&& thread_map.spec_index(t_ptr).view().owning_container == scheduler_map.spec_index(s_ptr).owning_container
            }
    }

    pub proof fn container_thread_scheduler_wf_at(container_map: ContainerLockedMap, thread_map: ThreadLockedMap, scheduler_map: SchedulerUnLockedMap, sched_ptr: RwLockSchedulerPtr, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr)
        requires
            container_thread_scheduler_wf(container_map, thread_map, scheduler_map),
            scheduler_map.dom().contains(sched_ptr),
            index_valid(NUM_CPUS, cpu_id),
        ensures
            scheduler_map.spec_index(sched_ptr).shard(cpu_id).queue.view().contains(thrd_ptr) ==> {
                &&& thread_map.dom().contains(thrd_ptr)
                &&& thread_map.spec_index(thrd_ptr).view().state == (ThreadState::SCHEDULED { cpu_id })
                &&& thread_map.spec_index(thrd_ptr).view().owning_container == scheduler_map.spec_index(sched_ptr).owning_container
            },
    { reveal(container_thread_scheduler_wf); }

    pub proof fn container_thread_scheduler_wf_thread_at(container_map: ContainerLockedMap, thread_map: ThreadLockedMap, scheduler_map: SchedulerUnLockedMap, thrd_ptr: RwLockThreadPtr)
        requires
            container_thread_scheduler_wf(container_map, thread_map, scheduler_map),
        ensures
            thread_map.dom().contains(thrd_ptr) && thread_map.spec_index(thrd_ptr).view().state is SCHEDULED ==> {
                let thread = thread_map.spec_index(thrd_ptr).view();
                let queue = scheduler_map.spec_index(container_map.spec_index(thread.owning_container).view_rodata().view().scheduler).shard(thread.state->SCHEDULED_cpu_id).queue;
                &&& index_valid(NUM_CPUS, thread.state->SCHEDULED_cpu_id)
                &&& queue.view().contains(thrd_ptr)
                &&& queue.map().dom().contains(thread.scheduler_linkedlist_node.addr())
                &&& queue.map().spec_index(thread.scheduler_linkedlist_node.addr()) == thrd_ptr
            },
    { reveal(container_thread_scheduler_wf); }
}
