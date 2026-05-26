use vstd::prelude::*;
use crate::*;

verus! {
   pub proof fn container_scheduler_wf_proof()
        ensures
            forall|container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, (), (), CONTAINER_HAS_KILL_STATE>, scheduler_map: LockedMap<RwLockSchedulerPtr, Scheduler, (), (), (), SCHEDULER_HAS_KILL_STATE>|
                container_scheduler_wf(container_map, scheduler_map) <==> container_scheduler_wf_inner(container_map, scheduler_map)
    {}

    pub closed spec fn container_scheduler_wf(container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, (), (), CONTAINER_HAS_KILL_STATE>, scheduler_map: LockedMap<RwLockSchedulerPtr, Scheduler, (), (), (), SCHEDULER_HAS_KILL_STATE>) -> bool {
        container_scheduler_wf_inner(container_map, scheduler_map)
    }
    pub open spec fn container_scheduler_wf_inner(container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, (), (), CONTAINER_HAS_KILL_STATE>, 
            scheduler_map: LockedMap<RwLockSchedulerPtr, Scheduler, (), (), (), SCHEDULER_HAS_KILL_STATE>) -> bool {
        &&&
        forall|c_ptr:RwLockContainerPtr|
            #![trigger container_map.spec_index(c_ptr).view_rodata().view().scheduler]
            container_map.dom().contains(c_ptr)
            ==>
            scheduler_map.dom().contains(container_map.spec_index(c_ptr).view_rodata().view().scheduler) 
            && 
            scheduler_map.spec_index(container_map.spec_index(c_ptr).view_rodata().view().scheduler).view().owning_container == c_ptr
        &&&
        forall|s_ptr:RwLockSchedulerPtr|
            #![trigger container_map.dom().contains(scheduler_map.spec_index(s_ptr).view().owning_container)]
            scheduler_map.dom().contains(s_ptr)
            ==>
            container_map.dom().contains(scheduler_map.spec_index(s_ptr).view().owning_container)
            &&
            container_map.spec_index(scheduler_map.spec_index(s_ptr).view().owning_container).view_rodata().view().scheduler == s_ptr
    }

    pub proof fn container_thread_scheduler_wf_proof()
        ensures
            forall|container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, (), (), CONTAINER_HAS_KILL_STATE>, thread_map: LockedMap<RwLockThreadPtr, Thread, (), (), (), THREAD_HAS_KILL_STATE>, scheduler_map: LockedMap<RwLockSchedulerPtr, Scheduler, (), (), (), SCHEDULER_HAS_KILL_STATE>|
                container_thread_scheduler_wf(container_map, thread_map, scheduler_map) <==> container_thread_scheduler_wf_inner(container_map, thread_map, scheduler_map)
    {}

    pub closed spec fn container_thread_scheduler_wf(container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, (), (), CONTAINER_HAS_KILL_STATE>,
        thread_map: LockedMap<RwLockThreadPtr, Thread, (), (), (), THREAD_HAS_KILL_STATE>, scheduler_map: LockedMap<RwLockSchedulerPtr, Scheduler, (), (), (), SCHEDULER_HAS_KILL_STATE>) -> bool {
        container_thread_scheduler_wf_inner(container_map, thread_map, scheduler_map)
    }
    pub open spec fn container_thread_scheduler_wf_inner(container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, (), (), CONTAINER_HAS_KILL_STATE>,
            thread_map: LockedMap<RwLockThreadPtr, Thread, (), (), (), THREAD_HAS_KILL_STATE>, 
            scheduler_map: LockedMap<RwLockSchedulerPtr, Scheduler, (), (), (), SCHEDULER_HAS_KILL_STATE>) -> bool {
        &&&
        forall|t_ptr:RwLockThreadPtr|
            #![trigger thread_map.spec_index(t_ptr).view().state]
            thread_map.dom().contains(t_ptr) && thread_map.spec_index(t_ptr).view().state is SCHEDULED
            ==>
            scheduler_map.spec_index(container_map.spec_index(thread_map.spec_index(t_ptr).view().owning_container).view_rodata().view().scheduler).view().queue.view().contains(t_ptr)
            &&
            scheduler_map.spec_index(container_map.spec_index(thread_map.spec_index(t_ptr).view().owning_container).view_rodata().view().scheduler).view().queue.map().spec_index(t_ptr)
                ==
                thread_map.spec_index(t_ptr).view().scheduler_linkedlist_node.addr()
        &&&
        forall|s_ptr:RwLockSchedulerPtr, t_ptr:RwLockThreadPtr|
            #![trigger scheduler_map.spec_index(s_ptr).view().queue.view().contains(t_ptr)]
            scheduler_map.dom().contains(s_ptr) && scheduler_map.spec_index(s_ptr).view().queue.view().contains(t_ptr)
            ==>
            thread_map.dom().contains(t_ptr)
            &&
            thread_map.spec_index(t_ptr).view().state is SCHEDULED
            &&
            thread_map.spec_index(t_ptr).view().owning_container ==  scheduler_map.spec_index(s_ptr).view().owning_container
    }
}