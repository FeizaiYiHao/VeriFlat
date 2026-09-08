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
        pre_thread_map.dom() =~= post_thread_map.dom(),
        forall|t_ptr: RwLockThreadPtr|
            #![trigger pre_thread_map.spec_index(t_ptr)]
            #![trigger post_thread_map.spec_index(t_ptr)]
            pre_thread_map.dom().contains(t_ptr) ==> {
                &&& post_thread_map.spec_index(t_ptr).view().state == pre_thread_map.spec_index(t_ptr).view().state
                &&& post_thread_map.spec_index(t_ptr).view().blocking_endpoint_ptr == pre_thread_map.spec_index(t_ptr).view().blocking_endpoint_ptr
                &&& post_thread_map.spec_index(t_ptr).view().endpoint_linkedlist_node == pre_thread_map.spec_index(t_ptr).view().endpoint_linkedlist_node
            },
        pre_endpoint_map.dom() =~= post_endpoint_map.dom(),
        forall|endpoint_ptr: RwLockEndpointPtr|
            #![trigger pre_endpoint_map.spec_index(endpoint_ptr).view().queue]
            #![trigger post_endpoint_map.spec_index(endpoint_ptr).view().queue]
            pre_endpoint_map.dom().contains(endpoint_ptr) ==> {
                &&& post_endpoint_map.spec_index(endpoint_ptr).view().queue == pre_endpoint_map.spec_index(endpoint_ptr).view().queue
                &&& post_endpoint_map.spec_index(endpoint_ptr).view().queue_state == pre_endpoint_map.spec_index(endpoint_ptr).view().queue_state
            },
    ensures
        thread_endpoint_queue_wf(post_thread_map, post_endpoint_map),
{
    reveal(thread_endpoint_queue_wf);
}

}
