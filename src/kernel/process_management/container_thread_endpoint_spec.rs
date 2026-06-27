use std::os::unix::thread;

use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn thread_endpoint_ref_counter_wf(thread_map: ThreadLockedMap, endpoint_map: LockedMap<RwLockEndpointPtr, Endpoint, (), (), (), ENDPOINT_HAS_KILL_STATE>) -> bool 
    {
        &&&
        forall|t_ptr:RwLockThreadPtr, edp_index:EndpointIdx|
            #![trigger thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int)]
            thread_map.dom().contains(t_ptr) && thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int) is Some
            ==>
            endpoint_map.dom().contains(thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int).unwrap())
            &&
            endpoint_map.spec_index(thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int).unwrap()).view().owning_threads.view().contains((t_ptr, edp_index))
        &&&
        forall|e_ptr: RwLockEndpointPtr, t_ptr:RwLockThreadPtr, edp_index:EndpointIdx|
            #![trigger endpoint_map.spec_index(e_ptr).view().owning_threads.view().contains((t_ptr, edp_index))]
            endpoint_map.dom().contains(e_ptr) && endpoint_map.spec_index(e_ptr).view().owning_threads.view().contains((t_ptr, edp_index))
            ==>
            thread_map.dom().contains(t_ptr) && thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int) == Some(e_ptr)
    }

    #[verifier::opaque]
    pub open spec fn thread_endpoint_queue_wf(thread_map: ThreadLockedMap, endpoint_map: LockedMap<RwLockEndpointPtr, Endpoint, (), (), (), ENDPOINT_HAS_KILL_STATE>) -> bool 
        recommends
        //     threads_inv(thread_map), @Xiangdong TODO
            thread_endpoint_ref_counter_wf(thread_map, endpoint_map)
    {
        &&&
        forall|t_ptr:RwLockThreadPtr|
            #![trigger thread_map.spec_index(t_ptr).view().state]
            thread_map.dom().contains(t_ptr) && thread_map.spec_index(t_ptr).view().state is BLOCKED
            ==>
            endpoint_map.spec_index(thread_map.spec_index(t_ptr).view().blocking_endpoint_ptr.unwrap()).view().queue.view().contains(t_ptr)
            &&
            endpoint_map.spec_index(thread_map.spec_index(t_ptr).view().blocking_endpoint_ptr.unwrap()).view().queue.map().spec_index(t_ptr)
                == 
                thread_map.spec_index(t_ptr).view().endpoint_linkedlist_node.addr()
        &&&
        forall|e_ptr:RwLockEndpointPtr, t_ptr: RwLockThreadPtr,|
            #![trigger endpoint_map.spec_index(e_ptr).view().queue.view().contains(t_ptr)]
            endpoint_map.dom().contains(e_ptr) && endpoint_map.spec_index(e_ptr).view().queue.view().contains(t_ptr)
            ==>
            thread_map.dom().contains(t_ptr)
            &&
            thread_map.spec_index(t_ptr).view().state is BLOCKED
            &&
            thread_map.spec_index(t_ptr).view().blocking_endpoint_ptr.unwrap() == e_ptr

    }

    #[verifier::opaque]
    pub open spec fn container_thread_endpoint_wf(container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, (), (), CONTAINER_HAS_KILL_STATE>, thread_map: ThreadLockedMap, endpoint_map: LockedMap<RwLockEndpointPtr, Endpoint, (), (), (), ENDPOINT_HAS_KILL_STATE>) -> bool 
    {
        &&&
        forall|t_ptr:RwLockThreadPtr, edp_index:EndpointIdx|
            #![trigger thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int)]
            thread_map.dom().contains(t_ptr) && thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int) is Some
            ==>
            {
                |||
                endpoint_map.spec_index(thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int).unwrap()).view().owning_container
                    ==
                    thread_map.spec_index(t_ptr).view().owning_container
                |||
                container_map.spec_index(endpoint_map.spec_index(thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int).unwrap()).view().owning_container)
                    .view().subtree_set.view().contains(thread_map.spec_index(t_ptr).view().owning_container)
            }
            
    }

}
