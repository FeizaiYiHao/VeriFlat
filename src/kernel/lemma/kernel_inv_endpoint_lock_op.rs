use vstd::prelude::*;
use crate::*;

verus! {

pub open spec fn endpoint_invariant_fields_unchanged(
    pre: EndpointLockedMap,
    post: EndpointLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|e_ptr: RwLockEndpointPtr|
        #![trigger pre.spec_index(e_ptr).view()]
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
}

pub proof fn lemma_no_change_imply_endpoint_perms_wf_forall()
    ensures
        forall|pre: EndpointLockedMap,
            post: EndpointLockedMap,
            changed: RwLockEndpointPtr|
            #![trigger
                endpoint_perms_wf(pre),
                endpoint_perms_wf(post),
                post.spec_index(changed)
            ]
            endpoint_perms_wf(pre)
            && pre.dom().contains(changed)
            && post.perms_wf()
            && post.unchanged_except(&pre, changed)
            && post.spec_index(changed).inv()
            ==> endpoint_perms_wf(post),
{
    reveal(endpoint_perms_wf);
    reveal(endpoints_inv);
}

pub proof fn lemma_no_change_imply_endpoint_pages_wf_forall()
    ensures
        forall|pre: EndpointLockedMap,
            post: EndpointLockedMap,
            page_array: PageLockedArray|
            #![trigger
                endpoint_pages_wf(pre, page_array),
                endpoint_pages_wf(post, page_array)
            ]
            endpoint_pages_wf(pre, page_array)
            && endpoint_invariant_fields_unchanged(pre, post)
            ==> endpoint_pages_wf(post, page_array),
{
    reveal(endpoint_pages_wf);
}

pub proof fn lemma_no_change_imply_container_endpoint_wf_forall()
    ensures
        forall|container_map: ContainerLockedMap,
            pre: EndpointLockedMap,
            post: EndpointLockedMap|
            #![trigger
                container_endpoint_wf(container_map, pre),
                container_endpoint_wf(container_map, post)
            ]
            container_endpoint_wf(container_map, pre)
            && endpoint_invariant_fields_unchanged(pre, post)
            ==> container_endpoint_wf(container_map, post),
{
    reveal(container_endpoint_wf);
}

pub proof fn lemma_no_change_imply_thread_endpoint_ref_counter_wf_forall()
    ensures
        forall|thread_map: ThreadLockedMap,
            pre: EndpointLockedMap,
            post: EndpointLockedMap|
            #![trigger
                thread_endpoint_ref_counter_wf(thread_map, pre),
                thread_endpoint_ref_counter_wf(thread_map, post)
            ]
            thread_endpoint_ref_counter_wf(thread_map, pre)
            && endpoint_invariant_fields_unchanged(pre, post)
            ==> thread_endpoint_ref_counter_wf(thread_map, post),
{
    reveal(thread_endpoint_ref_counter_wf);
}

pub proof fn lemma_no_change_imply_thread_endpoint_queue_wf_forall()
    ensures
        forall|thread_map: ThreadLockedMap,
            pre: EndpointLockedMap,
            post: EndpointLockedMap|
            #![trigger
                thread_endpoint_queue_wf(thread_map, pre),
                thread_endpoint_queue_wf(thread_map, post)
            ]
            thread_perms_wf(thread_map)
            && endpoint_perms_wf(pre)
            && endpoint_perms_wf(post)
            && thread_endpoint_ref_counter_wf(thread_map, pre)
            && thread_endpoint_ref_counter_wf(thread_map, post)
            && thread_endpoint_queue_wf(thread_map, pre)
            && endpoint_invariant_fields_unchanged(pre, post)
            ==> thread_endpoint_queue_wf(thread_map, post),
{
    reveal(thread_endpoint_queue_wf);
}

pub proof fn lemma_no_change_imply_container_thread_endpoint_wf_forall()
    ensures
        forall|container_map: ContainerLockedMap,
            thread_map: ThreadLockedMap,
            pre: EndpointLockedMap,
            post: EndpointLockedMap|
            #![trigger
                container_thread_endpoint_wf(container_map, thread_map, pre),
                container_thread_endpoint_wf(container_map, thread_map, post)
            ]
            thread_perms_wf(thread_map)
            && thread_endpoint_ref_counter_wf(thread_map, pre)
            && thread_endpoint_ref_counter_wf(thread_map, post)
            && container_endpoint_wf(container_map, pre)
            && container_endpoint_wf(container_map, post)
            && container_thread_endpoint_wf(container_map, thread_map, pre)
            && endpoint_invariant_fields_unchanged(pre, post)
            ==> container_thread_endpoint_wf(container_map, thread_map, post),
{
    reveal(container_thread_endpoint_wf);
    reveal(thread_endpoint_ref_counter_wf);
    reveal(container_endpoint_wf);
}

pub open spec fn thread_endpoint_queue_fields_unchanged(
    pre: ThreadLockedMap,
    post: ThreadLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|t_ptr: RwLockThreadPtr|
        #![trigger pre.spec_index(t_ptr)]
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

pub open spec fn endpoint_queue_fields_unchanged(
    pre: EndpointLockedMap,
    post: EndpointLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|endpoint_ptr: RwLockEndpointPtr|
        #![trigger pre.spec_index(endpoint_ptr).view().queue]
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
}

pub open spec fn endpoint_owning_container_fields_unchanged(
    pre: EndpointLockedMap,
    post: EndpointLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|endpoint_ptr: RwLockEndpointPtr|
        #![trigger pre.spec_index(endpoint_ptr).view().owning_container]
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
    &&& post.unchanged_except(&pre, thread_ptr)
    &&& pre.dom().contains(thread_ptr)
    &&& edp_idx_valid(endpoint_index)
    &&& pre.spec_index(thread_ptr).view().endpoint_descriptors.wf()
    &&& post.spec_index(thread_ptr).view().endpoint_descriptors.wf()
    &&& pre.spec_index(thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) is None
    &&& post.spec_index(thread_ptr).view().endpoint_descriptors.view()
        =~= pre.spec_index(thread_ptr).view().endpoint_descriptors.view()
            .update(endpoint_index as int, Some(endpoint_ptr))
    &&& post.spec_index(thread_ptr).view().owning_container
        == pre.spec_index(thread_ptr).view().owning_container
    &&& post.spec_index(thread_ptr).view().state
        == pre.spec_index(thread_ptr).view().state
    &&& post.spec_index(thread_ptr).view().caller
        == pre.spec_index(thread_ptr).view().caller
    &&& post.spec_index(thread_ptr).view().callee
        == pre.spec_index(thread_ptr).view().callee
    &&& post.spec_index(thread_ptr).view().scheduler_linkedlist_node.addr()
        == pre.spec_index(thread_ptr).view().scheduler_linkedlist_node.addr()
    &&& post.spec_index(thread_ptr).view().owning_proc
        == pre.spec_index(thread_ptr).view().owning_proc
    &&& post.spec_index(thread_ptr).view().container_depth
        == pre.spec_index(thread_ptr).view().container_depth
    &&& post.spec_index(thread_ptr).view().process_depth
        == pre.spec_index(thread_ptr).view().process_depth
    &&& post.spec_index(thread_ptr).view().proc_pagetable_ptr
        == pre.spec_index(thread_ptr).view().proc_pagetable_ptr
    &&& post.spec_index(thread_ptr).view().proc_linkedlist_node.addr()
        == pre.spec_index(thread_ptr).view().proc_linkedlist_node.addr()
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
    reveal(thread_endpoint_reference_added);
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

}
