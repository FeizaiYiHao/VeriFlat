use vstd::prelude::*;
use crate::*;

verus! {
/// A thread's endpoint descriptor names an endpoint of the thread's own container or of one of its ancestors.
// Proof dependencies (confirmed): thread_perms_wf, thread_endpoint_ref_counter_wf, container_endpoint_wf.
#[verifier::opaque]
pub open spec fn container_thread_endpoint_wf(ctn_mp: ContainerLockedMap, thrd_mp: ThreadLockedMap, ep_mp: EndpointLockedMap) -> bool {
    &&& forall|t: RwLockThreadPtr, ep_idx: EndpointIdx|
        #![trigger thrd_mp.spec_index(t).view().endpoint_descriptors.view().spec_index(ep_idx as int)]
        #![trigger thrd_mp.dom().contains(t), edp_idx_valid(ep_idx)]
        thrd_mp.dom().contains(t)
            && edp_idx_valid(ep_idx)
            && thrd_mp.spec_index(t).view().endpoint_descriptors.view().spec_index(ep_idx as int) is Some
            ==> {
                let e_owner = ep_mp.spec_index(thrd_mp.spec_index(t).view().endpoint_descriptors.view().spec_index(ep_idx as int).unwrap()).view().owning_container;
                let t_owner = thrd_mp.spec_index(t).view().owning_container;
                ||| e_owner == t_owner
                ||| ctn_mp.spec_index(e_owner).view_ghost().subtree_set.view().contains(t_owner)
            }
}

pub proof fn container_thread_endpoint_wf_at(ctn_mp: ContainerLockedMap, thrd_mp: ThreadLockedMap, ep_mp: EndpointLockedMap, thrd_ptr: RwLockThreadPtr, ep_idx: EndpointIdx)
    requires
        container_thread_endpoint_wf(ctn_mp, thrd_mp, ep_mp),
    ensures
        thrd_mp.dom().contains(thrd_ptr) && edp_idx_valid(ep_idx) && thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view().spec_index(ep_idx as int) is Some ==> ({
            let e_owner = ep_mp.spec_index(thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view().spec_index(ep_idx as int).unwrap()).view().owning_container;
            let t_owner = thrd_mp.spec_index(thrd_ptr).view().owning_container;
            ||| e_owner == t_owner
            ||| ctn_mp.spec_index(e_owner).view_ghost().subtree_set.view().contains(t_owner)
        }),
{ reveal(container_thread_endpoint_wf); }
}
