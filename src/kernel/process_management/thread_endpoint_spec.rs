use vstd::prelude::*;
use crate::*;

verus! {
/// A thread's endpoint descriptor slot and the endpoint's owning_threads name each other.
// Proof dependencies (confirmed for descriptor updates): thread_perms_wf.
#[verifier::opaque]
pub open spec fn thread_endpoint_ref_counter_wf(thrd_mp: ThreadLockedMap, ep_mp: EndpointLockedMap) -> bool {
    // Descriptor slot -> endpoint.
    &&& forall|t: RwLockThreadPtr, ep_idx: EndpointIdx|
        #![trigger thrd_mp.spec_index(t).view().endpoint_descriptors.view().spec_index(ep_idx as int)]
        #![trigger thrd_mp.dom().contains(t), edp_idx_valid(ep_idx)]
        thrd_mp.dom().contains(t)
            && edp_idx_valid(ep_idx)
            && thrd_mp.spec_index(t).view().endpoint_descriptors.view().spec_index(ep_idx as int) is Some
            ==> {
                let ep_ptr = thrd_mp.spec_index(t).view().endpoint_descriptors.view().spec_index(ep_idx as int).unwrap();
                &&& ep_mp.dom().contains(ep_ptr)
                &&& ep_mp.spec_index(ep_ptr).view().owning_threads.view().contains((t, ep_idx))
            }
    // Endpoint -> descriptor slot.
    &&& forall|e: RwLockEndpointPtr, t: RwLockThreadPtr, ep_idx: EndpointIdx|
        #![trigger ep_mp.spec_index(e).view().owning_threads.view().contains((t, ep_idx))]
        ep_mp.dom().contains(e) && ep_mp.spec_index(e).view().owning_threads.view().contains((t, ep_idx)) ==> {
            &&& thrd_mp.dom().contains(t)
            &&& edp_idx_valid(ep_idx)
            &&& thrd_mp.spec_index(t).view().endpoint_descriptors.view().spec_index(ep_idx as int) == Some(e)
        }
}

pub proof fn thread_endpoint_ref_counter_wf_thread_at(thrd_mp: ThreadLockedMap, ep_mp: EndpointLockedMap, thrd_ptr: RwLockThreadPtr, ep_idx: EndpointIdx)
    requires
        thread_endpoint_ref_counter_wf(thrd_mp, ep_mp),
    ensures
        thrd_mp.dom().contains(thrd_ptr) && edp_idx_valid(ep_idx) && thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view().spec_index(ep_idx as int) is Some ==> ({
            let ep_ptr = thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view().spec_index(ep_idx as int).unwrap();
            &&& ep_mp.dom().contains(ep_ptr)
            &&& ep_mp.spec_index(ep_ptr).view().owning_threads.view().contains((thrd_ptr, ep_idx))
        }),
{ reveal(thread_endpoint_ref_counter_wf); }

pub proof fn thread_endpoint_ref_counter_wf_endpoint_at(thrd_mp: ThreadLockedMap, ep_mp: EndpointLockedMap, ep_ptr: RwLockEndpointPtr, thrd_ptr: RwLockThreadPtr, ep_idx: EndpointIdx)
    requires
        thread_endpoint_ref_counter_wf(thrd_mp, ep_mp),
    ensures
        ep_mp.dom().contains(ep_ptr) && ep_mp.spec_index(ep_ptr).view().owning_threads.view().contains((thrd_ptr, ep_idx)) ==> {
            &&& thrd_mp.dom().contains(thrd_ptr)
            &&& edp_idx_valid(ep_idx)
            &&& thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view().spec_index(ep_idx as int) == Some(ep_ptr)
        },
{ reveal(thread_endpoint_ref_counter_wf); }

/// A thread waits on an endpoint iff it is in that endpoint's queue, in the direction of the queue.
// Proof dependencies (confirmed): thread_perms_wf, thread_endpoint_ref_counter_wf.
#[verifier::opaque]
pub open spec fn thread_endpoint_queue_wf(thrd_mp: ThreadLockedMap, ep_mp: EndpointLockedMap) -> bool
    recommends
        thread_perms_wf(thrd_mp),
        thread_endpoint_ref_counter_wf(thrd_mp, ep_mp)
{
    // Waiting thread -> endpoint queue.
    &&& forall|t: RwLockThreadPtr|
        #![trigger thrd_mp.spec_index(t).view().state]
        #![trigger thrd_mp.spec_index(t).view().blocking_endpoint_ptr]
        thrd_mp.dom().contains(t) && thrd_mp.spec_index(t).view().state.is_endpoint_waiting() ==> {
            let ep_ptr = thrd_mp.spec_index(t).view().blocking_endpoint_ptr.unwrap();
            let node = thrd_mp.spec_index(t).view().endpoint_linkedlist_node.addr();
            &&& ep_mp.dom().contains(ep_ptr)
            &&& ep_mp.spec_index(ep_ptr).view().queue.view().contains(t)
            // the thread's queue node maps back to it
            &&& ep_mp.spec_index(ep_ptr).view().queue.map().dom().contains(node)
            &&& ep_mp.spec_index(ep_ptr).view().queue.map().spec_index(node) == t
        }
    // Endpoint queue -> waiting thread.
    &&& forall|e: RwLockEndpointPtr, t: RwLockThreadPtr|
        #![trigger ep_mp.spec_index(e).view().queue.view().contains(t)]
        #![trigger thrd_mp.spec_index(t).view().state, ep_mp.dom().contains(e)]
        #![trigger thrd_mp.spec_index(t).view().blocking_endpoint_ptr, ep_mp.dom().contains(e)]
        ep_mp.dom().contains(e) && ep_mp.spec_index(e).view().queue.view().contains(t) ==> {
            &&& thrd_mp.dom().contains(t)
            &&& thrd_mp.spec_index(t).view().state.is_endpoint_waiting()
            &&& thrd_mp.spec_index(t).view().blocking_endpoint_ptr.unwrap() == e
            &&& match ep_mp.spec_index(e).view().queue_state {
                EndpointState::SEND => thrd_mp.spec_index(t).view().state.is_endpoint_send_waiting(),
                EndpointState::RECEIVE => thrd_mp.spec_index(t).view().state.is_endpoint_receive_waiting(),
            }
        }
}

pub proof fn thread_endpoint_queue_wf_thread_at(thrd_mp: ThreadLockedMap, ep_mp: EndpointLockedMap, thrd_ptr: RwLockThreadPtr)
    requires
        thread_endpoint_queue_wf(thrd_mp, ep_mp),
    ensures
        thrd_mp.dom().contains(thrd_ptr) && thrd_mp.spec_index(thrd_ptr).view().state.is_endpoint_waiting() ==> ({
            let ep_ptr = thrd_mp.spec_index(thrd_ptr).view().blocking_endpoint_ptr.unwrap();
            let node = thrd_mp.spec_index(thrd_ptr).view().endpoint_linkedlist_node.addr();
            &&& ep_mp.dom().contains(ep_ptr)
            &&& ep_mp.spec_index(ep_ptr).view().queue.view().contains(thrd_ptr)
            &&& ep_mp.spec_index(ep_ptr).view().queue.map().dom().contains(node)
            &&& ep_mp.spec_index(ep_ptr).view().queue.map().spec_index(node) == thrd_ptr
        }),
{ reveal(thread_endpoint_queue_wf); }

pub proof fn thread_endpoint_queue_wf_endpoint_at(thrd_mp: ThreadLockedMap, ep_mp: EndpointLockedMap, ep_ptr: RwLockEndpointPtr, thrd_ptr: RwLockThreadPtr)
    requires
        thread_endpoint_queue_wf(thrd_mp, ep_mp),
    ensures
        ep_mp.dom().contains(ep_ptr) && ep_mp.spec_index(ep_ptr).view().queue.view().contains(thrd_ptr) ==> {
            &&& thrd_mp.dom().contains(thrd_ptr)
            &&& thrd_mp.spec_index(thrd_ptr).view().state.is_endpoint_waiting()
            &&& thrd_mp.spec_index(thrd_ptr).view().blocking_endpoint_ptr.unwrap() == ep_ptr
            &&& match ep_mp.spec_index(ep_ptr).view().queue_state {
                EndpointState::SEND => thrd_mp.spec_index(thrd_ptr).view().state.is_endpoint_send_waiting(),
                EndpointState::RECEIVE => thrd_mp.spec_index(thrd_ptr).view().state.is_endpoint_receive_waiting(),
            }
        },
{ reveal(thread_endpoint_queue_wf); }
}
