use vstd::prelude::*;
use crate::*;

verus! {
    // Proof dependencies (confirmed for descriptor updates): thread_perms_wf.
    #[verifier::opaque]
    pub open spec fn thread_endpoint_ref_counter_wf(thread_map: ThreadLockedMap, endpoint_map: EndpointLockedMap) -> bool {
        &&& forall|t_ptr:RwLockThreadPtr, edp_index:EndpointIdx|
            #![trigger thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int)]
            thread_map.dom().contains(t_ptr) && edp_idx_valid(edp_index) && thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int) is Some
                ==> endpoint_map.dom().contains(thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int).unwrap())
                && endpoint_map.spec_index(thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int).unwrap()).view().owning_threads.view().contains((t_ptr, edp_index))
        &&& forall|e_ptr: RwLockEndpointPtr, t_ptr:RwLockThreadPtr, edp_index:EndpointIdx|
            #![trigger endpoint_map.spec_index(e_ptr).view().owning_threads.view().contains((t_ptr, edp_index))]
            endpoint_map.dom().contains(e_ptr) && endpoint_map.spec_index(e_ptr).view().owning_threads.view().contains((t_ptr, edp_index))
                ==> thread_map.dom().contains(t_ptr) && edp_idx_valid(edp_index) && thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int) == Some(e_ptr)
    }

    pub proof fn thread_endpoint_ref_counter_wf_thread_at(thread_map: ThreadLockedMap, endpoint_map: EndpointLockedMap, t_ptr: RwLockThreadPtr, edp_index: EndpointIdx)
        requires
            thread_endpoint_ref_counter_wf(thread_map, endpoint_map),
        ensures
            thread_map.dom().contains(t_ptr) && edp_idx_valid(edp_index) && thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int) is Some ==> ({
                let e_ptr = thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int).unwrap();
                &&& endpoint_map.dom().contains(e_ptr)
                &&& endpoint_map.spec_index(e_ptr).view().owning_threads.view().contains((t_ptr, edp_index))
            }),
    { reveal(thread_endpoint_ref_counter_wf); }

    pub proof fn thread_endpoint_ref_counter_wf_endpoint_at(thread_map: ThreadLockedMap, endpoint_map: EndpointLockedMap, e_ptr: RwLockEndpointPtr, t_ptr: RwLockThreadPtr, edp_index: EndpointIdx)
        requires
            thread_endpoint_ref_counter_wf(thread_map, endpoint_map),
        ensures
            endpoint_map.dom().contains(e_ptr) && endpoint_map.spec_index(e_ptr).view().owning_threads.view().contains((t_ptr, edp_index)) ==> {
                &&& thread_map.dom().contains(t_ptr)
                &&& edp_idx_valid(edp_index)
                &&& thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int) == Some(e_ptr)
            },
    { reveal(thread_endpoint_ref_counter_wf); }

    // Proof dependencies (confirmed): thread_perms_wf,
    // thread_endpoint_ref_counter_wf.
    #[verifier::opaque]
    pub open spec fn thread_endpoint_queue_wf(thread_map: ThreadLockedMap, endpoint_map: EndpointLockedMap) -> bool
        recommends
            thread_perms_wf(thread_map),
            thread_endpoint_ref_counter_wf(thread_map, endpoint_map)
    {
        &&& forall|t_ptr:RwLockThreadPtr|
            #![trigger thread_map.spec_index(t_ptr).view().state]
            #![trigger thread_map.spec_index(t_ptr).view().blocking_endpoint_ptr]
            thread_map.dom().contains(t_ptr) && thread_map.spec_index(t_ptr).view().state.is_endpoint_waiting()
                ==> endpoint_map.dom().contains(thread_map.spec_index(t_ptr).view().blocking_endpoint_ptr.unwrap())
                && endpoint_map.spec_index(thread_map.spec_index(t_ptr).view().blocking_endpoint_ptr.unwrap()).view().queue.view().contains(t_ptr)
                && endpoint_map.spec_index(thread_map.spec_index(t_ptr).view().blocking_endpoint_ptr.unwrap()).view().queue.map().dom().contains(thread_map.spec_index(t_ptr).view().endpoint_linkedlist_node.addr())
                && endpoint_map.spec_index(thread_map.spec_index(t_ptr).view().blocking_endpoint_ptr.unwrap()).view().queue.map().spec_index(thread_map.spec_index(t_ptr).view().endpoint_linkedlist_node.addr()) == t_ptr
        &&& forall|e_ptr:RwLockEndpointPtr, t_ptr: RwLockThreadPtr,|
            #![trigger endpoint_map.spec_index(e_ptr).view().queue.view().contains(t_ptr)]
            #![trigger thread_map.spec_index(t_ptr).view().state, endpoint_map.dom().contains(e_ptr)]
            #![trigger thread_map.spec_index(t_ptr).view().blocking_endpoint_ptr, endpoint_map.dom().contains(e_ptr)]
            endpoint_map.dom().contains(e_ptr) && endpoint_map.spec_index(e_ptr).view().queue.view().contains(t_ptr)
                ==> thread_map.dom().contains(t_ptr) && thread_map.spec_index(t_ptr).view().state.is_endpoint_waiting() && thread_map.spec_index(t_ptr).view().blocking_endpoint_ptr.unwrap() == e_ptr
                && match endpoint_map.spec_index(e_ptr).view().queue_state {
                    EndpointState::SEND => thread_map.spec_index(t_ptr).view().state.is_endpoint_send_waiting(),
                    EndpointState::RECEIVE => thread_map.spec_index(t_ptr).view().state.is_endpoint_receive_waiting(),
                }
    }

    pub proof fn thread_endpoint_queue_wf_thread_at(thread_map: ThreadLockedMap, endpoint_map: EndpointLockedMap, t_ptr: RwLockThreadPtr)
        requires
            thread_endpoint_queue_wf(thread_map, endpoint_map),
        ensures
            thread_map.dom().contains(t_ptr) && thread_map.spec_index(t_ptr).view().state.is_endpoint_waiting() ==> ({
                let e_ptr = thread_map.spec_index(t_ptr).view().blocking_endpoint_ptr.unwrap();
                let node = thread_map.spec_index(t_ptr).view().endpoint_linkedlist_node.addr();
                &&& endpoint_map.dom().contains(e_ptr)
                &&& endpoint_map.spec_index(e_ptr).view().queue.view().contains(t_ptr)
                &&& endpoint_map.spec_index(e_ptr).view().queue.map().dom().contains(node)
                &&& endpoint_map.spec_index(e_ptr).view().queue.map().spec_index(node) == t_ptr
            }),
    { reveal(thread_endpoint_queue_wf); }

    // Proof dependencies (confirmed): thread_perms_wf,
    // thread_endpoint_ref_counter_wf, container_endpoint_wf.
    #[verifier::opaque]
    pub open spec fn container_thread_endpoint_wf(container_map: ContainerLockedMap, thread_map: ThreadLockedMap, endpoint_map: EndpointLockedMap) -> bool {
        &&& forall|t_ptr:RwLockThreadPtr, edp_index:EndpointIdx|
            #![trigger thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int)]
            #![trigger thread_map.dom().contains(t_ptr), edp_idx_valid(edp_index)]
            thread_map.dom().contains(t_ptr) && edp_idx_valid(edp_index) && thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int) is Some ==> {
                ||| endpoint_map.spec_index(thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int).unwrap()).view().owning_container == thread_map.spec_index(t_ptr).view().owning_container
                ||| container_map.spec_index(endpoint_map.spec_index(thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int).unwrap()).view().owning_container)
                    .view_ghost().subtree_set.view().contains(thread_map.spec_index(t_ptr).view().owning_container)
            }
    }

    pub proof fn container_thread_endpoint_wf_at(container_map: ContainerLockedMap, thread_map: ThreadLockedMap, endpoint_map: EndpointLockedMap, t_ptr: RwLockThreadPtr, edp_index: EndpointIdx)
        requires
            container_thread_endpoint_wf(container_map, thread_map, endpoint_map),
        ensures
            thread_map.dom().contains(t_ptr) && edp_idx_valid(edp_index) && thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int) is Some ==> ({
                let e_owner = endpoint_map.spec_index(thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int).unwrap()).view().owning_container;
                let t_owner = thread_map.spec_index(t_ptr).view().owning_container;
                ||| e_owner == t_owner
                ||| container_map.spec_index(e_owner).view_ghost().subtree_set.view().contains(t_owner)
            }),
    { reveal(container_thread_endpoint_wf); }
}
