use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn container_endpoint_wf(container_map: ContainerLockedMap, endpoint_map: EndpointLockedMap) -> bool {
        &&& forall|c_ptr:RwLockContainerPtr, e_ptr:RwLockEndpointPtr|
            #![trigger container_map.spec_index(c_ptr).view().owned_endpoints.view().contains(e_ptr)]
            #![trigger endpoint_map.spec_index(e_ptr).view(), container_map.spec_index(c_ptr).view()]
            container_map.dom().contains(c_ptr) && container_map.spec_index(c_ptr).view().owned_endpoints.view().contains(e_ptr) ==>
            endpoint_map.dom().contains(e_ptr) && endpoint_map.spec_index(e_ptr).view().owning_container == c_ptr
        &&& forall|e_ptr:RwLockEndpointPtr|
            #![trigger container_map.dom().contains(endpoint_map.spec_index(e_ptr).view().owning_container)]
            #![trigger endpoint_map.spec_index(e_ptr).view()]
            endpoint_map.dom().contains(e_ptr) ==>
            container_map.dom().contains(endpoint_map.spec_index(e_ptr).view().owning_container) &&
            container_map.spec_index(endpoint_map.spec_index(e_ptr).view().owning_container).view().owned_endpoints.view().contains(e_ptr)
    }

    pub proof fn container_endpoint_wf_at(container_map: ContainerLockedMap, endpoint_map: EndpointLockedMap, endpoint_ptr: RwLockEndpointPtr)
        requires
            container_endpoint_wf(container_map, endpoint_map),
            endpoint_map.dom().contains(endpoint_ptr),
        ensures
            container_map.dom().contains(endpoint_map.spec_index(endpoint_ptr).view().owning_container),
            container_map.spec_index(endpoint_map.spec_index(endpoint_ptr).view().owning_container).view().owned_endpoints.view().contains(endpoint_ptr),
    {
        reveal(container_endpoint_wf);
    }
}
