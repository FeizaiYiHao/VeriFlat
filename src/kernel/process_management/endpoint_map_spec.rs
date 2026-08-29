use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn endpoint_perms_wf(endpoint_map: EndpointLockedMap) -> bool {
        &&&
        endpoint_map.perms_wf()
        &&&
        endpoints_inv(endpoint_map)
    }

    pub open spec fn endpoints_inv(endpoint_map: EndpointLockedMap) -> bool {
        &&&
        forall|endpoint_p: RwLockEndpointPtr|
            #![trigger endpoint_map.dom().contains(endpoint_p)]
            endpoint_map.dom().contains(endpoint_p)
            ==>
            endpoint_map.spec_index(endpoint_p).inv()
    }
}
