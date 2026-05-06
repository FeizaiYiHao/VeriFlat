use std::os::unix::thread;

use vstd::prelude::*;
use crate::*;

verus! {
   pub proof fn container_thread_wf_proof()
        ensures
            forall|container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, CONTAINER_HAS_KILL_STATE>, thread_map: LockedMap<RwLockThreadPtr, Thread, (), THREAD_HAS_KILL_STATE>|
                container_thread_wf(container_map, thread_map) <==> container_thread_wf_inner(container_map, thread_map)
    {}

    pub closed spec fn container_thread_wf(container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, CONTAINER_HAS_KILL_STATE>, thread_map: LockedMap<RwLockThreadPtr, Thread, (), THREAD_HAS_KILL_STATE>) -> bool {
        container_thread_wf_inner(container_map, thread_map)
    }
    pub open spec fn container_thread_wf_inner(container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, CONTAINER_HAS_KILL_STATE>, 
            thread_map: LockedMap<RwLockThreadPtr, Thread, (), THREAD_HAS_KILL_STATE>) -> bool {
        &&&
        forall|c_ptr:RwLockContainerPtr, t_ptr:RwLockThreadPtr|
            #![trigger container_map.spec_index(c_ptr).view(), thread_map.spec_index(t_ptr).view()]
            container_map.dom().contains(c_ptr) && container_map.spec_index(c_ptr).view().owned_threads.view().contains(t_ptr)
            ==>
            thread_map.dom().contains(t_ptr) && thread_map.spec_index(t_ptr).view().owning_container == c_ptr
        &&&
        forall|t_ptr:RwLockThreadPtr|
            #![trigger container_map.dom().contains(thread_map.spec_index(t_ptr).view().owning_container)]
            thread_map.dom().contains(t_ptr)
            ==>
            container_map.dom().contains(thread_map.spec_index(t_ptr).view().owning_container)
            &&
            container_map.spec_index(thread_map.spec_index(t_ptr).view().owning_container).view().owned_threads.view().contains(t_ptr)
    }

}