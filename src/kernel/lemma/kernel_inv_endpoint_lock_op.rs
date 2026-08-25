use vstd::prelude::*;
use crate::*;

verus! {

// TODO(AGENTS): Replace the assert-forall bridges in this module with direct
// endpoint queue/reference operation postconditions or producer triggers. The
// current endpoint framing relation alone does not instantiate these leaves.

#[verifier::opaque]
pub open spec fn endpoint_invariant_fields_unchanged(
    pre: EndpointLockedMap,
    post: EndpointLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|e_ptr: RwLockEndpointPtr|
        #![trigger post.spec_index(e_ptr).view()]
        pre.dom().contains(e_ptr) ==>
            post.spec_index(e_ptr).view()
                == pre.spec_index(e_ptr).view()
}

pub proof fn endpoint_lock_op_preserves_invariant_fields(
    pre: EndpointLockedMap,
    post: EndpointLockedMap,
    changed: RwLockEndpointPtr,
)
    requires
        post.unchanged_except(&pre, changed),
        post.spec_index(changed).view()
            == pre.spec_index(changed).view(),
    ensures
        endpoint_invariant_fields_unchanged(pre, post),
{
    reveal(endpoint_invariant_fields_unchanged);
}

pub proof fn thread_endpoint_queue_wf_preserved_for_endpoint_invariant_fields(
    thread_map: ThreadLockedMap,
    pre: EndpointLockedMap,
    post: EndpointLockedMap,
)
    requires
        thread_perms_wf(thread_map),
        endpoint_perms_wf(pre),
        endpoint_perms_wf(post),
        thread_endpoint_ref_counter_wf(thread_map, pre),
        thread_endpoint_ref_counter_wf(thread_map, post),
        thread_endpoint_queue_wf(thread_map, pre),
        endpoint_invariant_fields_unchanged(pre, post),
    ensures
        thread_endpoint_queue_wf(thread_map, post),
{
    reveal(thread_endpoint_queue_wf);
    reveal(thread_perms_wf);
 
    reveal(endpoint_perms_wf);
    reveal(endpoints_inv);
    reveal(thread_endpoint_ref_counter_wf);
    assert forall|t_ptr: RwLockThreadPtr|
        #![trigger thread_map.spec_index(t_ptr).view().state]
        thread_map.dom().contains(t_ptr)
            && thread_map.spec_index(t_ptr).view().state.is_endpoint_waiting()
        implies
            post.spec_index(
                thread_map.spec_index(t_ptr).view().blocking_endpoint_ptr.unwrap(),
            ).view().queue.view().contains(t_ptr)
            && post.spec_index(
                thread_map.spec_index(t_ptr).view().blocking_endpoint_ptr.unwrap(),
            ).view().queue.map().dom().contains(
                thread_map.spec_index(t_ptr).view().endpoint_linkedlist_node.addr(),
            )
            && post.spec_index(
                thread_map.spec_index(t_ptr).view().blocking_endpoint_ptr.unwrap(),
            ).view().queue.map().spec_index(
                thread_map.spec_index(t_ptr).view().endpoint_linkedlist_node.addr(),
            ) == t_ptr by {
        assert(edp_idx_valid(
            thread_map.spec_index(t_ptr).view().blocking_endpoint_index.unwrap(),
        )) by { reveal(thread_perms_wf); };
        assert(post.dom().contains(
            thread_map.spec_index(t_ptr).view().blocking_endpoint_ptr.unwrap(),
        )) by { reveal(thread_endpoint_ref_counter_wf); reveal(thread_perms_wf); };
        reveal(endpoint_invariant_fields_unchanged);
    };
    assert forall|e_ptr: RwLockEndpointPtr, t_ptr: RwLockThreadPtr|
        #![trigger post.spec_index(e_ptr).view().queue.view().contains(t_ptr)]
        post.dom().contains(e_ptr)
            && post.spec_index(e_ptr).view().queue.view().contains(t_ptr)
        implies
            thread_map.dom().contains(t_ptr)
            && thread_map.spec_index(t_ptr).view().state.is_endpoint_waiting()
            && thread_map.spec_index(t_ptr).view().blocking_endpoint_ptr.unwrap() == e_ptr
            && match post.spec_index(e_ptr).view().queue_state {
                EndpointState::SEND => thread_map.spec_index(t_ptr).view()
                    .state.is_endpoint_send_waiting(),
                EndpointState::RECEIVE => thread_map.spec_index(t_ptr).view()
                    .state.is_endpoint_receive_waiting(),
            } by {
        reveal(endpoint_invariant_fields_unchanged);
    };
}

pub proof fn container_thread_endpoint_wf_preserved_for_endpoint_invariant_fields(
    container_map: ContainerLockedMap,
    thread_map: ThreadLockedMap,
    pre: EndpointLockedMap,
    post: EndpointLockedMap,
)
    requires
        thread_perms_wf(thread_map),
        thread_endpoint_ref_counter_wf(thread_map, pre),
        thread_endpoint_ref_counter_wf(thread_map, post),
        container_endpoint_wf(container_map, pre),
        container_endpoint_wf(container_map, post),
        container_thread_endpoint_wf(container_map, thread_map, pre),
        endpoint_invariant_fields_unchanged(pre, post),
    ensures
        container_thread_endpoint_wf(container_map, thread_map, post),
{
    reveal(container_thread_endpoint_wf);
    reveal(thread_endpoint_ref_counter_wf);
    reveal(container_endpoint_wf);
    assert forall|t_ptr: RwLockThreadPtr, edp_index: EndpointIdx|
        #![trigger thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int)]
        thread_map.dom().contains(t_ptr)
            && edp_idx_valid(edp_index)
            && thread_map.spec_index(t_ptr).view().endpoint_descriptors.view()
                .spec_index(edp_index as int) is Some
        implies {
            let endpoint_ptr = thread_map.spec_index(t_ptr).view()
                .endpoint_descriptors.view().spec_index(edp_index as int).unwrap();
            ||| post.spec_index(endpoint_ptr).view().owning_container
                    == thread_map.spec_index(t_ptr).view().owning_container
            ||| container_map.spec_index(
                    post.spec_index(endpoint_ptr).view().owning_container,
                ).view().subtree_set.view().contains(
                    thread_map.spec_index(t_ptr).view().owning_container,
                )
        } by {
        reveal(endpoint_invariant_fields_unchanged);
    };
}

#[verifier::opaque]
pub open spec fn thread_endpoint_queue_fields_unchanged(
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|t_ptr: RwLockThreadPtr|
        #![trigger post.spec_index(t_ptr)]
        pre.dom().contains(t_ptr) ==>
        {
            &&& post.spec_index(t_ptr).view().state
                == pre.spec_index(t_ptr).view().state
            &&& post.spec_index(t_ptr).view().blocking_endpoint_ptr
                == pre.spec_index(t_ptr).view().blocking_endpoint_ptr
            &&& post.spec_index(t_ptr).view().endpoint_linkedlist_node
                == pre.spec_index(t_ptr).view().endpoint_linkedlist_node
        }
}

#[verifier::opaque]
pub open spec fn endpoint_queue_fields_unchanged(
    pre: EndpointLockedMap,
    post: EndpointLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|endpoint_ptr: RwLockEndpointPtr|
        #![trigger post.spec_index(endpoint_ptr).view().queue]
        pre.dom().contains(endpoint_ptr) ==> {
            &&& post.spec_index(endpoint_ptr).view().queue
                == pre.spec_index(endpoint_ptr).view().queue
            &&& post.spec_index(endpoint_ptr).view().queue_state
                == pre.spec_index(endpoint_ptr).view().queue_state
        }
}

pub proof fn thread_endpoint_queue_wf_preserved_for_queue_fields(
    pre_thread_map: ThreadLockedMap,
    post_thread_map: ThreadLockedMap,
    pre_endpoint_map: EndpointLockedMap,
    post_endpoint_map: EndpointLockedMap,
)
    requires
        thread_perms_wf(pre_thread_map),
        thread_perms_wf(post_thread_map),
        endpoint_perms_wf(pre_endpoint_map),
        endpoint_perms_wf(post_endpoint_map),
        thread_endpoint_ref_counter_wf(pre_thread_map, pre_endpoint_map),
        thread_endpoint_ref_counter_wf(post_thread_map, post_endpoint_map),
        thread_endpoint_queue_wf(pre_thread_map, pre_endpoint_map),
        thread_endpoint_queue_fields_unchanged(pre_thread_map, post_thread_map),
        endpoint_queue_fields_unchanged(pre_endpoint_map, post_endpoint_map),
    ensures
        thread_endpoint_queue_wf(post_thread_map, post_endpoint_map),
{
    reveal(thread_endpoint_queue_wf);
    reveal(thread_perms_wf);
 
    reveal(endpoint_perms_wf);
    reveal(endpoints_inv);
    reveal(thread_endpoint_ref_counter_wf);
    assert forall|t_ptr: RwLockThreadPtr|
        #![trigger post_thread_map.spec_index(t_ptr).view().state]
        post_thread_map.dom().contains(t_ptr)
            && post_thread_map.spec_index(t_ptr).view().state.is_endpoint_waiting()
        implies
            post_endpoint_map.spec_index(
                post_thread_map.spec_index(t_ptr).view()
                    .blocking_endpoint_ptr.unwrap(),
            ).view().queue.view().contains(t_ptr)
            && post_endpoint_map.spec_index(
                post_thread_map.spec_index(t_ptr).view()
                    .blocking_endpoint_ptr.unwrap(),
            ).view().queue.map().dom().contains(
                post_thread_map.spec_index(t_ptr).view()
                    .endpoint_linkedlist_node.addr(),
            )
            && post_endpoint_map.spec_index(
                post_thread_map.spec_index(t_ptr).view()
                    .blocking_endpoint_ptr.unwrap(),
            ).view().queue.map().spec_index(
                post_thread_map.spec_index(t_ptr).view()
                    .endpoint_linkedlist_node.addr(),
            ) == t_ptr by {
        assert(edp_idx_valid(
            post_thread_map.spec_index(t_ptr).view().blocking_endpoint_index.unwrap(),
        )) by { reveal(thread_perms_wf); };
        assert(post_endpoint_map.dom().contains(
            post_thread_map.spec_index(t_ptr).view().blocking_endpoint_ptr.unwrap(),
        )) by { reveal(thread_endpoint_ref_counter_wf); reveal(thread_perms_wf); };
        reveal(thread_endpoint_queue_fields_unchanged);
        reveal(endpoint_queue_fields_unchanged);
    };
    assert forall|endpoint_ptr: RwLockEndpointPtr, t_ptr: RwLockThreadPtr|
        #![trigger post_endpoint_map.spec_index(endpoint_ptr).view().queue.view().contains(t_ptr)]
        post_endpoint_map.dom().contains(endpoint_ptr)
            && post_endpoint_map.spec_index(endpoint_ptr).view()
                .queue.view().contains(t_ptr)
        implies
            post_thread_map.dom().contains(t_ptr)
            && post_thread_map.spec_index(t_ptr).view().state.is_endpoint_waiting()
            && post_thread_map.spec_index(t_ptr).view()
                .blocking_endpoint_ptr.unwrap() == endpoint_ptr
            && match post_endpoint_map.spec_index(endpoint_ptr).view().queue_state {
                EndpointState::SEND => post_thread_map.spec_index(t_ptr).view()
                    .state.is_endpoint_send_waiting(),
                EndpointState::RECEIVE => post_thread_map.spec_index(t_ptr).view()
                    .state.is_endpoint_receive_waiting(),
            } by {
        reveal(thread_endpoint_queue_fields_unchanged);
        reveal(endpoint_queue_fields_unchanged);
    };
}

#[verifier::opaque]
pub open spec fn endpoint_owning_container_fields_unchanged(
    pre: EndpointLockedMap,
    post: EndpointLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|endpoint_ptr: RwLockEndpointPtr|
        #![trigger post.spec_index(endpoint_ptr).view().owning_container]
        pre.dom().contains(endpoint_ptr) ==>
            post.spec_index(endpoint_ptr).view().owning_container
                == pre.spec_index(endpoint_ptr).view().owning_container
}

#[verifier::opaque]
pub open spec fn thread_endpoint_reference_added(
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& pre.dom().contains(thread_ptr)
    &&& edp_idx_valid(endpoint_index)
    &&& pre.spec_index(thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) is None
    &&& post.spec_index(thread_ptr).view().endpoint_descriptors.view()
        =~= pre.spec_index(thread_ptr).view().endpoint_descriptors.view()
            .update(endpoint_index as int, Some(endpoint_ptr))
    &&& forall|t_ptr: RwLockThreadPtr|
        #![trigger post.spec_index(t_ptr).view().owning_container]
        #![trigger post.spec_index(t_ptr)]
        #![trigger post.spec_index(t_ptr).view().state]
        pre.dom().contains(t_ptr) ==>
        {
            &&& pre.spec_index(t_ptr).view().endpoint_descriptors.wf()
            &&& post.spec_index(t_ptr).view().endpoint_descriptors.wf()
            &&& post.spec_index(t_ptr).view().owning_container
                    == pre.spec_index(t_ptr).view().owning_container
            &&& post.spec_index(t_ptr).view().state
                    == pre.spec_index(t_ptr).view().state
            &&& post.spec_index(t_ptr).view().caller
                    == pre.spec_index(t_ptr).view().caller
            &&& post.spec_index(t_ptr).view().callee
                    == pre.spec_index(t_ptr).view().callee
            &&& post.spec_index(t_ptr).view().scheduler_linkedlist_node.addr()
                    == pre.spec_index(t_ptr).view().scheduler_linkedlist_node.addr()
            &&& post.spec_index(t_ptr).view().owning_proc
                    == pre.spec_index(t_ptr).view().owning_proc
            &&& post.spec_index(t_ptr).view().container_depth
                    == pre.spec_index(t_ptr).view().container_depth
            &&& post.spec_index(t_ptr).view().process_depth
                    == pre.spec_index(t_ptr).view().process_depth
            &&& post.spec_index(t_ptr).view().proc_pagetable_ptr
                    == pre.spec_index(t_ptr).view().proc_pagetable_ptr
            &&& post.spec_index(t_ptr).view().proc_linkedlist_node.addr()
                    == pre.spec_index(t_ptr).view().proc_linkedlist_node.addr()
        }
    &&& forall|t_ptr: RwLockThreadPtr|
        #![trigger post.spec_index(t_ptr).view().endpoint_descriptors]
        pre.dom().contains(t_ptr) && t_ptr != thread_ptr
        ==>
            post.spec_index(t_ptr).view().endpoint_descriptors
                == pre.spec_index(t_ptr).view().endpoint_descriptors
}

pub proof fn thread_endpoint_reference_added_from_single_update(
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
    thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx,
)
    requires
        thread_perms_wf(pre),
        thread_perms_wf(post),
        post.unchanged_except(&pre, thread_ptr),
        pre.dom().contains(thread_ptr),
        edp_idx_valid(endpoint_index),
        pre.spec_index(thread_ptr).view().endpoint_descriptors.wf(),
        pre.spec_index(thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) is None,
        post.spec_index(thread_ptr).view().endpoint_descriptors.wf(),
        post.spec_index(thread_ptr).view().endpoint_descriptors.view()
            =~= pre.spec_index(thread_ptr).view().endpoint_descriptors.view()
                .update(endpoint_index as int, Some(endpoint_ptr)),
        post.spec_index(thread_ptr).view().owning_container
            == pre.spec_index(thread_ptr).view().owning_container,
        post.spec_index(thread_ptr).view().state
            == pre.spec_index(thread_ptr).view().state,
        post.spec_index(thread_ptr).view().caller
            == pre.spec_index(thread_ptr).view().caller,
        post.spec_index(thread_ptr).view().callee
            == pre.spec_index(thread_ptr).view().callee,
        post.spec_index(thread_ptr).view().scheduler_linkedlist_node.addr()
            == pre.spec_index(thread_ptr).view().scheduler_linkedlist_node.addr(),
        post.spec_index(thread_ptr).view().owning_proc
            == pre.spec_index(thread_ptr).view().owning_proc,
        post.spec_index(thread_ptr).view().container_depth
            == pre.spec_index(thread_ptr).view().container_depth,
        post.spec_index(thread_ptr).view().process_depth
            == pre.spec_index(thread_ptr).view().process_depth,
        post.spec_index(thread_ptr).view().proc_pagetable_ptr
            == pre.spec_index(thread_ptr).view().proc_pagetable_ptr,
        post.spec_index(thread_ptr).view().proc_linkedlist_node.addr()
            == pre.spec_index(thread_ptr).view().proc_linkedlist_node.addr(),
    ensures
        thread_endpoint_reference_added(
            pre, post, thread_ptr, endpoint_ptr, endpoint_index),
{
    assert(thread_endpoint_reference_added(
        pre, post, thread_ptr, endpoint_ptr, endpoint_index,
    )) by {
        reveal(thread_endpoint_reference_added);
        reveal(thread_perms_wf);
    };
}

#[verifier::opaque]
pub open spec fn endpoint_reference_added(
    pre: EndpointLockedMap,
    post: EndpointLockedMap,
    thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx,
) -> bool {
    &&& post.unchanged_except(&pre, endpoint_ptr)
    &&& pre.dom().contains(endpoint_ptr)
    &&& post.spec_index(endpoint_ptr).view().owning_threads.view()
        =~= pre.spec_index(endpoint_ptr).view().owning_threads.view()
            .insert((thread_ptr, endpoint_index))
    &&& post.spec_index(endpoint_ptr).view().rf_counter
        == pre.spec_index(endpoint_ptr).view().rf_counter + 1
    &&& post.spec_index(endpoint_ptr).view().owning_container
        == pre.spec_index(endpoint_ptr).view().owning_container
}

pub proof fn endpoint_reference_added_from_single_update(
    pre: EndpointLockedMap,
    post: EndpointLockedMap,
    thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx,
)
    requires
        post.unchanged_except(&pre, endpoint_ptr),
        pre.dom().contains(endpoint_ptr),
        post.spec_index(endpoint_ptr).view().owning_threads.view()
            =~= pre.spec_index(endpoint_ptr).view().owning_threads.view()
                .insert((thread_ptr, endpoint_index)),
        post.spec_index(endpoint_ptr).view().rf_counter
            == pre.spec_index(endpoint_ptr).view().rf_counter + 1,
        post.spec_index(endpoint_ptr).view().owning_container
            == pre.spec_index(endpoint_ptr).view().owning_container,
    ensures
        endpoint_reference_added(
            pre, post, thread_ptr, endpoint_ptr, endpoint_index),
{
    assert(endpoint_reference_added(
        pre, post, thread_ptr, endpoint_ptr, endpoint_index,
    )) by {
        reveal(endpoint_reference_added);
    };
}

pub proof fn container_thread_endpoint_wf_preserved_on_reference_add(
    container_map: ContainerLockedMap,
    pre_thread_map: ThreadLockedMap,
    post_thread_map: ThreadLockedMap,
    pre_endpoint_map: EndpointLockedMap,
    post_endpoint_map: EndpointLockedMap,
    thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr,
    added_endpoint_index: EndpointIdx,
)
    requires
        thread_perms_wf(pre_thread_map),
        thread_perms_wf(post_thread_map),
        thread_endpoint_ref_counter_wf(pre_thread_map, pre_endpoint_map),
        thread_endpoint_ref_counter_wf(post_thread_map, post_endpoint_map),
        container_endpoint_wf(container_map, pre_endpoint_map),
        container_endpoint_wf(container_map, post_endpoint_map),
        container_thread_endpoint_wf(
            container_map,
            pre_thread_map,
            pre_endpoint_map,
        ),
        thread_endpoint_reference_added(
            pre_thread_map,
            post_thread_map,
            thread_ptr,
            endpoint_ptr,
            added_endpoint_index,
        ),
        endpoint_owning_container_fields_unchanged(
            pre_endpoint_map,
            post_endpoint_map,
        ),
        post_endpoint_map.dom().contains(endpoint_ptr),
        container_map.dom().contains(
            post_endpoint_map.spec_index(endpoint_ptr).view().owning_container,
        ),
        {
            ||| post_endpoint_map.spec_index(endpoint_ptr).view().owning_container
                == post_thread_map.spec_index(thread_ptr).view().owning_container
            ||| container_map.spec_index(
                    post_endpoint_map.spec_index(endpoint_ptr).view().owning_container,
                ).view().subtree_set.view().contains(
                    post_thread_map.spec_index(thread_ptr).view().owning_container,
                )
        },
    ensures
        container_thread_endpoint_wf(
            container_map,
            post_thread_map,
            post_endpoint_map,
        ),
{
    reveal(container_thread_endpoint_wf);
    broadcast use vstd::seq::group_seq_lemmas;
    assert forall|t_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx|
        #![trigger post_thread_map.spec_index(t_ptr).view().endpoint_descriptors.view().spec_index(endpoint_index as int)]
        post_thread_map.dom().contains(t_ptr)
            && edp_idx_valid(endpoint_index)
            && post_thread_map.spec_index(t_ptr).view().endpoint_descriptors
                .spec_index(endpoint_index) is Some
        implies {
            let referenced_endpoint = post_thread_map.spec_index(t_ptr).view()
                .endpoint_descriptors.spec_index(endpoint_index);
            ||| post_endpoint_map.spec_index(referenced_endpoint.unwrap())
                    .view().owning_container
                == post_thread_map.spec_index(t_ptr).view().owning_container
            ||| container_map.spec_index(
                    post_endpoint_map.spec_index(referenced_endpoint.unwrap())
                        .view().owning_container,
                ).view().subtree_set.view().contains(
                    post_thread_map.spec_index(t_ptr).view().owning_container,
                )
        } by {
        reveal(thread_endpoint_reference_added);
        reveal(endpoint_owning_container_fields_unchanged);
        reveal(thread_endpoint_ref_counter_wf);
        reveal(container_endpoint_wf);
        if t_ptr == thread_ptr && endpoint_index == added_endpoint_index {
            assert(post_thread_map.spec_index(t_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr)) by { reveal(thread_endpoint_reference_added); };
        }
    };
}

}
