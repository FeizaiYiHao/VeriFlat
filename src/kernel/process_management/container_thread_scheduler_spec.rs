use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn container_scheduler_wf(container_map: ContainerLockedMap, scheduler_map: SchedulerLockedMap) -> bool {
        &&& forall|c_ptr:RwLockContainerPtr|
            #![trigger container_map.dom().contains(c_ptr)]
            container_map.dom().contains(c_ptr) ==>
            scheduler_map.dom().contains(container_map.spec_index(c_ptr).view_rodata().view().scheduler) &&
            scheduler_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().scheduler).view().owning_container == c_ptr
        &&& forall|s_ptr:RwLockSchedulerPtr|
            #![trigger scheduler_map.dom().contains(s_ptr)]
            scheduler_map.dom().contains(s_ptr) ==>
            container_map.dom().contains(scheduler_map.spec_index(s_ptr).view().owning_container) &&
            container_map.spec_index(scheduler_map.spec_index(s_ptr).view().owning_container).view_rodata().view().scheduler == s_ptr
    }

    pub proof fn container_scheduler_wf_at(container_map: ContainerLockedMap, scheduler_map: SchedulerLockedMap, container_ptr: RwLockContainerPtr)
        requires
            container_scheduler_wf(container_map, scheduler_map),
            container_map.dom().contains(container_ptr),
        ensures
            scheduler_map.dom().contains(container_map.spec_index(container_ptr).view_rodata().view().scheduler),
            scheduler_map.spec_index(container_map.spec_index(container_ptr).view_rodata().view().scheduler).view().owning_container == container_ptr,
    {
        reveal(container_scheduler_wf);
    }

    // Proof dependencies (confirmed): container_thread_wf,
    // container_scheduler_wf.
    #[verifier::opaque]
    pub open spec fn container_thread_scheduler_wf(container_map: ContainerLockedMap, thread_map: ThreadLockedMap, scheduler_map: SchedulerLockedMap) -> bool {
        &&& forall|t_ptr:RwLockThreadPtr|
            #![trigger thread_map.spec_index(t_ptr).view().state]
            #![trigger thread_map.spec_index(t_ptr).view().owning_container]
            thread_map.dom().contains(t_ptr) && thread_map.spec_index(t_ptr).view().state is SCHEDULED ==>
            scheduler_map.spec_index(container_map.spec_index(thread_map.spec_index(t_ptr).view().owning_container).view_rodata().view().scheduler).view().queue.view().contains(t_ptr) &&
            scheduler_map.spec_index(container_map.spec_index(thread_map.spec_index(t_ptr).view().owning_container).view_rodata().view().scheduler).view().queue.map().dom().contains(thread_map.spec_index(t_ptr).view().scheduler_linkedlist_node.addr()) &&
            scheduler_map.spec_index(container_map.spec_index(thread_map.spec_index(t_ptr).view().owning_container).view_rodata().view().scheduler).view().queue.map().spec_index(thread_map.spec_index(t_ptr).view().scheduler_linkedlist_node.addr()) == t_ptr
        &&& forall|s_ptr:RwLockSchedulerPtr, t_ptr:RwLockThreadPtr|
            #![trigger scheduler_map.spec_index(s_ptr).view().queue.view().contains(t_ptr)]
            #![trigger thread_map.spec_index(t_ptr).view().state, scheduler_map.spec_index(s_ptr).view().queue]
            #![trigger thread_map.spec_index(t_ptr).view().owning_container, scheduler_map.spec_index(s_ptr).view().queue]
            scheduler_map.dom().contains(s_ptr) && scheduler_map.spec_index(s_ptr).view().queue.view().contains(t_ptr) ==>
            thread_map.dom().contains(t_ptr) && thread_map.spec_index(t_ptr).view().state is SCHEDULED &&
            thread_map.spec_index(t_ptr).view().owning_container == scheduler_map.spec_index(s_ptr).view().owning_container
    }

    pub proof fn container_thread_scheduler_wf_at(
        container_map: ContainerLockedMap, thread_map: ThreadLockedMap, scheduler_map: SchedulerLockedMap, scheduler_ptr: RwLockSchedulerPtr,
        thread_ptr: RwLockThreadPtr,
    )
        requires
            container_thread_scheduler_wf(container_map, thread_map, scheduler_map),
            scheduler_map.dom().contains(scheduler_ptr),
        ensures
            scheduler_map.spec_index(scheduler_ptr).view().queue.view().contains(thread_ptr) ==> {
                &&& thread_map.dom().contains(thread_ptr)
                &&& thread_map.spec_index(thread_ptr).view().state is SCHEDULED
                &&& thread_map.spec_index(thread_ptr).view().owning_container == scheduler_map.spec_index(scheduler_ptr).view().owning_container
            },
    {
        reveal(container_thread_scheduler_wf);
    }
}
