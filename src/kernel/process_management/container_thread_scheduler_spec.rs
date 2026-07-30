use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn container_scheduler_wf(container_map: ContainerLockedMap, 
            scheduler_map: SchedulerLockedMap) -> bool {
        &&&
        forall|c_ptr:RwLockContainerPtr|
            #![trigger container_map.dom().contains(c_ptr)]
            container_map.dom().contains(c_ptr)
            ==>
            scheduler_map.dom().contains(container_map.spec_index(c_ptr).view_rodata().view().scheduler) 
            && 
            scheduler_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().scheduler).view().owning_container == c_ptr
        &&&
        forall|s_ptr:RwLockSchedulerPtr|
            #![trigger scheduler_map.dom().contains(s_ptr)]
            scheduler_map.dom().contains(s_ptr)
            ==>
            container_map.dom().contains(scheduler_map.spec_index(s_ptr).view().owning_container)
            &&
            container_map.spec_index(scheduler_map.spec_index(s_ptr).view().owning_container).view_rodata().view().scheduler == s_ptr
    }

    #[verifier::opaque]
    pub open spec fn container_thread_scheduler_wf(container_map: ContainerLockedMap,
            thread_map: ThreadLockedMap, 
            scheduler_map: SchedulerLockedMap) -> bool {
        &&&
        forall|t_ptr:RwLockThreadPtr|
            #![trigger thread_map.spec_index(t_ptr).view().state]
            #![trigger thread_map.spec_index(t_ptr).view().owning_container]
            thread_map.dom().contains(t_ptr) && thread_map.spec_index(t_ptr).view().state is SCHEDULED
            ==>
            scheduler_map.spec_index(container_map.spec_index(thread_map.spec_index(t_ptr).view().owning_container).view_rodata().view().scheduler).view().queue.view().contains(t_ptr)
            &&
            scheduler_map.spec_index(container_map.spec_index(thread_map.spec_index(t_ptr).view().owning_container).view_rodata().view().scheduler).view().queue.map().dom().contains(thread_map.spec_index(t_ptr).view().scheduler_linkedlist_node.addr())
            &&
            scheduler_map.spec_index(container_map.spec_index(thread_map.spec_index(t_ptr).view().owning_container).view_rodata().view().scheduler).view().queue.map().spec_index(thread_map.spec_index(t_ptr).view().scheduler_linkedlist_node.addr())
                ==
                t_ptr
        &&&
        forall|s_ptr:RwLockSchedulerPtr, t_ptr:RwLockThreadPtr|
            #![trigger scheduler_map.spec_index(s_ptr).view().queue.view().contains(t_ptr)]
            #![trigger thread_map.spec_index(t_ptr).view().state, scheduler_map.spec_index(s_ptr).view().queue]
            #![trigger thread_map.spec_index(t_ptr).view().owning_container, scheduler_map.spec_index(s_ptr).view().queue]
            scheduler_map.dom().contains(s_ptr) && scheduler_map.spec_index(s_ptr).view().queue.view().contains(t_ptr)
            ==>
            thread_map.dom().contains(t_ptr)
            &&
            thread_map.spec_index(t_ptr).view().state is SCHEDULED
            &&
            thread_map.spec_index(t_ptr).view().owning_container ==  scheduler_map.spec_index(s_ptr).view().owning_container
    }
}
