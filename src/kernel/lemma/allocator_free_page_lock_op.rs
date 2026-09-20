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
        index_valid(NUM_PAGES, changed),
        post.entries_unchanged_except(&pre, changed),
        !(pre.spec_index(changed).view().view().state is Free4k),
        !(post.spec_index(changed).view().view().state is Free4k),
    ensures
        container_allocator_free_4k_page_wf(allocator_map, post),
{
    reveal(container_allocator_free_4k_page_wf);
    reveal(container_allocator_global_free_4k_page_wf);
    reveal(container_allocator_cpu_cache_free_4k_page_wf);
    reveal(allocator_free_page_ptrs_wf);
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
        index_valid(NUM_PAGES, changed),
        post.entries_unchanged_except(&pre, changed),
        !(pre.spec_index(changed).view().view().state is Free2m),
        !(post.spec_index(changed).view().view().state is Free2m),
    ensures
        container_allocator_free_2m_page_wf(allocator_map, post),
{
    reveal(container_allocator_free_2m_page_wf);
    reveal(container_allocator_global_free_2m_page_wf);
    reveal(container_allocator_cpu_cache_free_2m_page_wf);
    reveal(allocator_free_page_ptrs_wf);
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
        index_valid(NUM_PAGES, changed),
        post.entries_unchanged_except(&pre, changed),
        !(pre.spec_index(changed).view().view().state is Free1g),
        !(post.spec_index(changed).view().view().state is Free1g),
    ensures
        container_allocator_free_1g_page_wf(allocator_map, post),
{
    reveal(container_allocator_free_1g_page_wf);
    reveal(container_allocator_global_free_1g_page_wf);
    reveal(container_allocator_cpu_cache_free_1g_page_wf);
    reveal(allocator_free_page_ptrs_wf);
}

pub proof fn lemma_container_allocator_free_4k_page_wf_preserved_for_lock_op(
    pre: KernelK,
    post: KernelK,
)
    requires
        container_allocator_free_4k_page_wf(pre.allc_4k_mp, pre.pg_arr),
        post.pg_arr == pre.pg_arr,
        post.allc_4k_mp.dom() == pre.allc_4k_mp.dom(),
        forall|a: RwLockPageAllocatorPtr|
            #![trigger post.allc_4k_mp.spec_index(a).owning_container]
            #![trigger post.allc_4k_mp.spec_index(a).global_pool.view()]
            post.allc_4k_mp.dom().contains(a) ==>
                post.allc_4k_mp.spec_index(a).owning_container == pre.allc_4k_mp.spec_index(a).owning_container
                && post.allc_4k_mp.spec_index(a).global_pool.view() == pre.allc_4k_mp.spec_index(a).global_pool.view(),
        forall|a: RwLockPageAllocatorPtr, i: CpuId|
            #![trigger post.allc_4k_mp.spec_index(a).cpu_caches.spec_index(i).view().view()]
            post.allc_4k_mp.dom().contains(a) && index_valid(NUM_CPUS, i) ==>
                post.allc_4k_mp.spec_index(a).cpu_caches.spec_index(i).view().view()
                    == pre.allc_4k_mp.spec_index(a).cpu_caches.spec_index(i).view().view(),
    ensures
        container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr),
{
    reveal(container_allocator_free_4k_page_wf);
    reveal(container_allocator_global_free_4k_page_wf);
    reveal(container_allocator_cpu_cache_free_4k_page_wf);
}

pub proof fn lemma_container_allocator_free_2m_page_wf_preserved_for_lock_op(
    pre: KernelK,
    post: KernelK,
)
    requires
        container_allocator_free_2m_page_wf(pre.allc_2m_mp, pre.pg_arr),
        post.pg_arr == pre.pg_arr,
        post.allc_2m_mp.dom() == pre.allc_2m_mp.dom(),
        forall|a: RwLockPageAllocatorPtr|
            #![trigger post.allc_2m_mp.spec_index(a).owning_container]
            #![trigger post.allc_2m_mp.spec_index(a).global_pool.view()]
            post.allc_2m_mp.dom().contains(a) ==>
                post.allc_2m_mp.spec_index(a).owning_container
                    == pre.allc_2m_mp.spec_index(a).owning_container
                && post.allc_2m_mp.spec_index(a).global_pool.view()
                    == pre.allc_2m_mp.spec_index(a).global_pool.view(),
        forall|a: RwLockPageAllocatorPtr, i: CpuId|
            #![trigger post.allc_2m_mp.spec_index(a)
                .cpu_caches.spec_index(i).view().view()]
            post.allc_2m_mp.dom().contains(a) && index_valid(NUM_CPUS, i) ==>
                post.allc_2m_mp.spec_index(a).cpu_caches
                    .spec_index(i).view().view()
                == pre.allc_2m_mp.spec_index(a).cpu_caches
                    .spec_index(i).view().view(),
    ensures
        container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr),
{
    reveal(container_allocator_free_2m_page_wf);
    reveal(container_allocator_global_free_2m_page_wf);
    reveal(container_allocator_cpu_cache_free_2m_page_wf);
}

}
