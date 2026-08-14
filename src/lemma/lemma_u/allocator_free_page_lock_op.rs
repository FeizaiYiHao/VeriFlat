use vstd::prelude::*;
use crate::*;
use crate::kernel::*;
verus! {

pub proof fn container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(
    allocator_map: PageAllocatorUnLockedMap,
    pre: PageLockedArray,
    post: PageLockedArray,
    changed: PageIndex,
)
    requires
        page_array_wf(pre),
        page_array_wf(post),
        allocator_free_page_ptrs_wf(allocator_map),
        container_allocator_free_4k_page_wf(allocator_map, pre),
        page_index_wf(changed),
        post.unchanged_except(&pre, changed),
        !(pre.spec_index(changed).view().view().state is Free4k),
        !(post.spec_index(changed).view().view().state is Free4k),
    ensures
        container_allocator_free_4k_page_wf(allocator_map, post),
{
    assert forall|i: PageIndex|
        #![trigger post.spec_index(i).view().view().state]
        page_index_wf(i)
        && ((pre.spec_index(i).view().view().state is Free4k)
            || (post.spec_index(i).view().view().state is Free4k))
        implies post.spec_index(i) === pre.spec_index(i) by {
        if i == changed {
        }
    };
    assert(container_allocator_free_4k_page_wf(allocator_map, post)) by {
        reveal(container_allocator_free_4k_page_wf);
        reveal(container_allocator_global_free_4k_page_wf);
        reveal(container_allocator_cpu_cache_free_4k_page_wf);
        reveal(allocator_free_page_ptrs_wf);
        page_ptr_valid_imply_page_index_valid();
    };
}

pub proof fn container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(
    allocator_map: PageAllocatorUnLockedMap,
    pre: PageLockedArray,
    post: PageLockedArray,
    changed: PageIndex,
)
    requires
        page_array_wf(pre),
        page_array_wf(post),
        allocator_free_page_ptrs_wf(allocator_map),
        container_allocator_free_2m_page_wf(allocator_map, pre),
        page_index_wf(changed),
        post.unchanged_except(&pre, changed),
        !(pre.spec_index(changed).view().view().state is Free2m),
        !(post.spec_index(changed).view().view().state is Free2m),
    ensures
        container_allocator_free_2m_page_wf(allocator_map, post),
{
    assert forall|i: PageIndex|
        #![trigger post.spec_index(i).view().view().state]
        page_index_wf(i)
        && ((pre.spec_index(i).view().view().state is Free2m)
            || (post.spec_index(i).view().view().state is Free2m))
        implies post.spec_index(i) === pre.spec_index(i) by {
        if i == changed {
        }
    };
    assert(container_allocator_free_2m_page_wf(allocator_map, post)) by {
        reveal(container_allocator_free_2m_page_wf);
        reveal(container_allocator_global_free_2m_page_wf);
        reveal(container_allocator_cpu_cache_free_2m_page_wf);
        reveal(allocator_free_page_ptrs_wf);
        page_ptr_valid_imply_page_index_valid();
    };
}

pub proof fn container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(
    allocator_map: PageAllocatorUnLockedMap,
    pre: PageLockedArray,
    post: PageLockedArray,
    changed: PageIndex,
)
    requires
        page_array_wf(pre),
        page_array_wf(post),
        allocator_free_page_ptrs_wf(allocator_map),
        container_allocator_free_1g_page_wf(allocator_map, pre),
        page_index_wf(changed),
        post.unchanged_except(&pre, changed),
        !(pre.spec_index(changed).view().view().state is Free1g),
        !(post.spec_index(changed).view().view().state is Free1g),
    ensures
        container_allocator_free_1g_page_wf(allocator_map, post),
{
    assert forall|i: PageIndex|
        #![trigger post.spec_index(i).view().view().state]
        page_index_wf(i)
        && ((pre.spec_index(i).view().view().state is Free1g)
            || (post.spec_index(i).view().view().state is Free1g))
        implies post.spec_index(i) === pre.spec_index(i) by {
        if i == changed {
        }
    };
    assert(container_allocator_free_1g_page_wf(allocator_map, post)) by {
        reveal(container_allocator_free_1g_page_wf);
        reveal(container_allocator_global_free_1g_page_wf);
        reveal(container_allocator_cpu_cache_free_1g_page_wf);
        reveal(allocator_free_page_ptrs_wf);
        page_ptr_valid_imply_page_index_valid();
    };
}

pub proof fn lemma_container_allocator_free_4k_page_wf_preserved_for_lock_op(
    pre: KernelK,
    post: KernelK,
)
    requires
        container_allocator_free_4k_page_wf(pre.allocator_4k_map, pre.page_array),
        post.page_array == pre.page_array,
        post.allocator_4k_map.dom() == pre.allocator_4k_map.dom(),
        forall|a: RwLockPageAllocatorPtr|
            #![trigger post.allocator_4k_map.spec_index(a).owning_container]
            #![trigger post.allocator_4k_map.spec_index(a).global_pool.view()]
            post.allocator_4k_map.dom().contains(a) ==>
                post.allocator_4k_map.spec_index(a).owning_container == pre.allocator_4k_map.spec_index(a).owning_container
                && post.allocator_4k_map.spec_index(a).global_pool.view() == pre.allocator_4k_map.spec_index(a).global_pool.view(),
        forall|a: RwLockPageAllocatorPtr, i: CpuId|
            #![trigger post.allocator_4k_map.spec_index(a).cpu_caches.spec_index(i).view().view()]
            post.allocator_4k_map.dom().contains(a) && cpu_id_valid(i) ==>
                post.allocator_4k_map.spec_index(a).cpu_caches.spec_index(i).view().view()
                    == pre.allocator_4k_map.spec_index(a).cpu_caches.spec_index(i).view().view(),
    ensures
        container_allocator_free_4k_page_wf(post.allocator_4k_map, post.page_array),
{
    assert(container_allocator_global_free_4k_page_wf(
        post.allocator_4k_map, post.page_array,
    )) by {
        reveal(container_allocator_free_4k_page_wf);
        reveal(container_allocator_global_free_4k_page_wf);
    };
    assert(container_allocator_cpu_cache_free_4k_page_wf(
        post.allocator_4k_map, post.page_array,
    )) by {
        reveal(container_allocator_free_4k_page_wf);
        reveal(container_allocator_cpu_cache_free_4k_page_wf);
    };
    assert(container_allocator_free_4k_page_wf(
        post.allocator_4k_map, post.page_array,
    )) by {
        reveal(container_allocator_free_4k_page_wf);
    };
}

/// Forall-lifted form of the field-framing lemma. The old and new invariant
/// terms jointly bind `pre` and `post`; callers only need to introduce this
/// rule in the scoped assertion that asks for the new invariant.
pub proof fn lemma_no_change_imply_container_allocator_free_4k_page_wf_forall()
    ensures
        forall|pre: KernelK, post: KernelK|
            #![trigger
                container_allocator_free_4k_page_wf(
                    pre.allocator_4k_map,
                    pre.page_array,
                ),
                container_allocator_free_4k_page_wf(
                    post.allocator_4k_map,
                    post.page_array,
                )
            ]
            container_allocator_free_4k_page_wf(
                pre.allocator_4k_map,
                pre.page_array,
            )
            && post.page_array == pre.page_array
            && post.allocator_4k_map.dom() == pre.allocator_4k_map.dom()
            && (forall|a: RwLockPageAllocatorPtr|
                #![trigger post.allocator_4k_map.spec_index(a).owning_container]
                #![trigger post.allocator_4k_map.spec_index(a).global_pool.view()]
                post.allocator_4k_map.dom().contains(a) ==>
                    post.allocator_4k_map.spec_index(a).owning_container
                        == pre.allocator_4k_map.spec_index(a).owning_container
                    && post.allocator_4k_map.spec_index(a).global_pool.view()
                        == pre.allocator_4k_map.spec_index(a).global_pool.view())
            && (forall|a: RwLockPageAllocatorPtr, i: CpuId|
                #![trigger post.allocator_4k_map.spec_index(a)
                    .cpu_caches.spec_index(i).view().view()]
                post.allocator_4k_map.dom().contains(a) && cpu_id_valid(i) ==>
                    post.allocator_4k_map.spec_index(a).cpu_caches
                        .spec_index(i).view().view()
                    == pre.allocator_4k_map.spec_index(a).cpu_caches
                        .spec_index(i).view().view())
            ==>
                container_allocator_free_4k_page_wf(
                    post.allocator_4k_map,
                    post.page_array,
                ),
{
    assert forall|pre: KernelK, post: KernelK|
        #![auto]
        container_allocator_free_4k_page_wf(
            pre.allocator_4k_map,
            pre.page_array,
        )
        && post.page_array == pre.page_array
        && post.allocator_4k_map.dom() == pre.allocator_4k_map.dom()
        && (forall|a: RwLockPageAllocatorPtr| #![auto]
            post.allocator_4k_map.dom().contains(a) ==>
                post.allocator_4k_map.spec_index(a).owning_container
                    == pre.allocator_4k_map.spec_index(a).owning_container
                && post.allocator_4k_map.spec_index(a).global_pool.view()
                    == pre.allocator_4k_map.spec_index(a).global_pool.view())
        && (forall|a: RwLockPageAllocatorPtr, i: CpuId| #![auto]
            post.allocator_4k_map.dom().contains(a) && cpu_id_valid(i) ==>
                post.allocator_4k_map.spec_index(a).cpu_caches
                    .spec_index(i).view().view()
                == pre.allocator_4k_map.spec_index(a).cpu_caches
                    .spec_index(i).view().view())
    implies
        container_allocator_free_4k_page_wf(
            post.allocator_4k_map,
            post.page_array,
        )
    by {
        lemma_container_allocator_free_4k_page_wf_preserved_for_lock_op(
            pre,
            post,
        );
    };
}

}
