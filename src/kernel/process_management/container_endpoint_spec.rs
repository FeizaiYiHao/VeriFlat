use vstd::prelude::*;
use crate::*;

verus! {
/// Container owned_endpoints and endpoint owning_container agree.
#[verifier::opaque]
pub open spec fn container_endpoint_wf(ctn_mp: ContainerLockedMap, ep_mp: EndpointLockedMap) -> bool {
    // Container -> owned endpoints.
    &&& forall|c: RwLockContainerPtr, e: RwLockEndpointPtr|
        #![trigger ctn_mp.spec_index(c).view_ghost().owned_endpoints.view().contains(e)]
        ctn_mp.dom().contains(c) && ctn_mp.spec_index(c).view_ghost().owned_endpoints.view().contains(e) ==> {
            &&& ep_mp.dom().contains(e)
            &&& ep_mp.spec_index(e).view().owning_container == c
        }
    // Endpoint -> owning container.
    &&& forall|e: RwLockEndpointPtr|
        #![trigger ctn_mp.dom().contains(ep_mp.spec_index(e).view().owning_container)]
        #![trigger ep_mp.spec_index(e).view()]
        ep_mp.dom().contains(e) ==> {
            let ctn_ptr = ep_mp.spec_index(e).view().owning_container;
            &&& ctn_mp.dom().contains(ctn_ptr)
            &&& ctn_mp.spec_index(ctn_ptr).view_ghost().owned_endpoints.view().contains(e)
        }
}

pub proof fn container_endpoint_wf_endpoint_at(ctn_mp: ContainerLockedMap, ep_mp: EndpointLockedMap, ep_ptr: RwLockEndpointPtr)
    requires
        container_endpoint_wf(ctn_mp, ep_mp),
        ep_mp.dom().contains(ep_ptr),
    ensures
        ctn_mp.dom().contains(ep_mp.spec_index(ep_ptr).view().owning_container),
        ctn_mp.spec_index(ep_mp.spec_index(ep_ptr).view().owning_container).view_ghost().owned_endpoints.view().contains(ep_ptr),
{ reveal(container_endpoint_wf); }
}
