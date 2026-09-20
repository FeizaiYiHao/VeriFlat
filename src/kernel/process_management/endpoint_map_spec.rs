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

    pub proof fn endpoint_perms_wf_at(
        endpoint_map: EndpointLockedMap,
        endpoint_ptr: RwLockEndpointPtr,
    )
        requires
            endpoint_perms_wf(endpoint_map),
            endpoint_map.dom().contains(endpoint_ptr),
        ensures
            endpoint_map.perms_wf(),
            endpoint_map.view().spec_index(endpoint_ptr).is_init(),
            endpoint_map.view().spec_index(endpoint_ptr).addr()
                == endpoint_ptr,
            endpoint_map.spec_index(endpoint_ptr).inv(),
            endpoint_map.spec_index(endpoint_ptr).is_init(),
            endpoint_map.spec_index(endpoint_ptr).view().inv(),
    {
        reveal(endpoint_perms_wf);
        reveal(endpoints_inv);
    }
}
