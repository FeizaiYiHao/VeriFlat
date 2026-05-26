use std::os::unix::thread;

use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn container_thread_wf(container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, (), (), CONTAINER_HAS_KILL_STATE>, 
            thread_map: LockedMap<RwLockThreadPtr, Thread, (), (), (), THREAD_HAS_KILL_STATE>) -> bool {
        &&&
        forall|c_ptr:RwLockContainerPtr, t_ptr:RwLockThreadPtr|
            #![trigger container_map.spec_index(c_ptr).view(), thread_map.spec_index(t_ptr).view()]
            container_map.dom().contains(c_ptr) && container_map.spec_index(c_ptr).view().owned_threads.view().contains(t_ptr)
            ==>
            thread_map.dom().contains(t_ptr) && thread_map.spec_index(t_ptr).view().owning_container == c_ptr
            &&
            thread_map.spec_index(t_ptr).view().container_depth == container_map.spec_index(c_ptr).view_rodata().view().depth
            &&
            thread_map.spec_index(t_ptr).view().upper_container_seq == container_map.spec_index(c_ptr).view().uppertree_seq
        &&&
        forall|t_ptr:RwLockThreadPtr|
            #![trigger container_map.dom().contains(thread_map.spec_index(t_ptr).view().owning_container)]
            thread_map.dom().contains(t_ptr)
            ==>
            container_map.dom().contains(thread_map.spec_index(t_ptr).view().owning_container)
            &&
            container_map.spec_index(thread_map.spec_index(t_ptr).view().owning_container).view().owned_threads.view().contains(t_ptr)
        &&&
        forall|c_ptr:RwLockContainerPtr, t_ptr:RwLockThreadPtr|
            #![trigger container_map.spec_index(c_ptr).view().owned_indirect_threads.view().contains(t_ptr)]
            container_map.dom().contains(c_ptr) && container_map.spec_index(c_ptr).view().owned_indirect_threads.view().contains(t_ptr)
            ==>
            thread_map.dom().contains(t_ptr) && thread_map.spec_index(t_ptr).view().upper_container_seq.view().contains(c_ptr)
        &&&
        forall|t_ptr:RwLockThreadPtr, c_ptr:RwLockContainerPtr,|
            #![trigger thread_map.spec_index(t_ptr).view().upper_container_seq.view().contains(c_ptr)]
            thread_map.dom().contains(t_ptr) && thread_map.spec_index(t_ptr).view().upper_container_seq.view().contains(c_ptr)
            ==>
            container_map.dom().contains(c_ptr)
            &&
            container_map.spec_index(c_ptr).view().owned_indirect_threads.view().contains(t_ptr)
    }

}
