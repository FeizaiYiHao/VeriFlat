use vstd::prelude::*;
use crate::*;

verus! {
   pub proof fn container_endpoint_wf_proof()
        ensures
            forall|container_map: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>, endpoint_map: LockedMap<RwLockEndpointPtr, Endpoint, (),  ENDPOINT_HAS_KILL_STATE>|
                container_endpoint_wf(container_map, endpoint_map) <==> container_endpoint_wf_inner(container_map, endpoint_map)
    {}

    pub closed spec fn container_endpoint_wf(container_map: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>, endpoint_map: LockedMap<RwLockEndpointPtr, Endpoint, (),  ENDPOINT_HAS_KILL_STATE>) -> bool {
        container_endpoint_wf_inner(container_map, endpoint_map)
    }
    pub open spec fn container_endpoint_wf_inner(container_map: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>, 
            endpoint_map: LockedMap<RwLockEndpointPtr, Endpoint, (),  ENDPOINT_HAS_KILL_STATE>) -> bool {
        &&&
        forall|c_ptr:RwLockContainerPtr, e_ptr:RwLockEndpointPtr|
            #![trigger container_map.spec_index(c_ptr).view().owned_endpoints.view().contains(e_ptr)]
            container_map.dom().contains(c_ptr) && container_map.spec_index(c_ptr).view().owned_endpoints.view().contains(e_ptr)
            ==>
            endpoint_map.dom().contains(e_ptr) && endpoint_map.spec_index(e_ptr).view().owning_container == c_ptr
        &&&
        forall|e_ptr:RwLockEndpointPtr|
            #![trigger container_map.dom().contains(endpoint_map.spec_index(e_ptr).view().owning_container)]
            endpoint_map.dom().contains(e_ptr)
            ==>
            container_map.dom().contains(endpoint_map.spec_index(e_ptr).view().owning_container)
            &&
            container_map.spec_index(endpoint_map.spec_index(e_ptr).view().owning_container).view().owned_endpoints.view().contains(e_ptr)
    }

}