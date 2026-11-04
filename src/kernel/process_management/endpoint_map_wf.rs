use vstd::prelude::*;
use crate::*;

verus! {
/// The endpoint map's permissions are well formed and every endpoint satisfies its own invariant.
#[verifier::opaque]
pub open spec fn endpoint_perms_wf(ep_mp: EndpointLockedMap) -> bool {
    &&& ep_mp.perms_wf()
    &&& forall|e: RwLockEndpointPtr|
        #![trigger ep_mp.dom().contains(e)]
        ep_mp.dom().contains(e) ==> ep_mp.spec_index(e).inv()
}

pub proof fn endpoint_perms_wf_at(ep_mp: EndpointLockedMap, ep_ptr: RwLockEndpointPtr)
    requires
        endpoint_perms_wf(ep_mp),
        ep_mp.dom().contains(ep_ptr),
    ensures
        ep_mp.view().spec_index(ep_ptr).is_init(),
        ep_mp.view().spec_index(ep_ptr).addr() == ep_ptr,
        ep_mp.spec_index(ep_ptr).inv(),
        ep_mp.spec_index(ep_ptr).is_init(),
        ep_mp.spec_index(ep_ptr).view().inv(),
{ reveal(endpoint_perms_wf); }

pub proof fn endpoint_perms_wf_map(ep_mp: EndpointLockedMap)
    requires endpoint_perms_wf(ep_mp)
    ensures ep_mp.perms_wf()
{ reveal(endpoint_perms_wf); }
}
