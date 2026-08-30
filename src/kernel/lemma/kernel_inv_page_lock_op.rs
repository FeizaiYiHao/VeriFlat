use vstd::prelude::*;
use crate::*;

verus! {

/// Kernel invariants read page payloads, never the current page lock owner.
pub open spec fn page_invariant_fields_unchanged(
    pre: PageLockedArray,
    post: PageLockedArray,
) -> bool {
    forall|page_index: PageIndex|
        #![trigger pre.spec_index(page_index)]
        #![trigger post.spec_index(page_index)]
        index_valid(NUM_PAGES, page_index) ==>
            post.spec_index(page_index).view().view()
                == pre.spec_index(page_index).view().view()
}

pub proof fn page_lock_op_preserves_invariant_fields(
    pre: PageLockedArray,
    post: PageLockedArray,
    changed: PageIndex,
)
    requires
        post.unchanged_except(&pre, changed),
    ensures
        page_invariant_fields_unchanged(pre, post),
{
}

/// All non-page inputs read by `KernelK::memory_management_inv`.
pub open spec fn page_memory_management_context_unchanged(
    pre: KernelK,
    post: KernelK,
) -> bool {
    &&& post.pt_mp == pre.pt_mp
    &&& post.it_mp == pre.it_mp
    &&& post.ctn_mp == pre.ctn_mp
    &&& post.pcid_allc_mp == pre.pcid_allc_mp
    &&& post.prc_mp == pre.prc_mp
    &&& post.thr_mp == pre.thr_mp
    &&& post.ep_mp == pre.ep_mp
    &&& post.allc_4k_mp == pre.allc_4k_mp
    &&& post.allc_2m_mp == pre.allc_2m_mp
    &&& post.allc_1g_mp == pre.allc_1g_mp
}

pub proof fn memory_management_inv_preserved_for_page_invariant_fields(
    pre: KernelK,
    post: KernelK,
)
    requires
        pre.memory_management_inv(),
        pagetable_perms_wf(pre.pt_mp),
        page_invariant_fields_unchanged(pre.pg_arr, post.pg_arr),
        page_memory_management_context_unchanged(pre, post),
    ensures
        post.memory_management_inv(),
{
    assert(allocator_pages_wf(
        post.pg_arr,
        post.allc_4k_mp,
        post.allc_2m_mp,
        post.allc_1g_mp,
    )) by {
        reveal(allocator_4k_pages_wf);
        reveal(allocator_2m_pages_wf);
        reveal(allocator_1g_pages_wf);
    };
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by {
        reveal(container_page_owner_wf);
    };
    assert(hugepage_2m_wf(post.pg_arr)) by {
        reveal(hugepage_2m_wf);
    };
    assert(hugepage_1g_wf(post.pg_arr)) by {
        reveal(hugepage_1g_wf);
    };
    assert(page_pagetable_wf(post.pt_mp, post.pg_arr)) by {
        reveal(pagetable_perms_wf);
        reveal(mapped_4k_page_pagetable_wf);
        reveal(mapped_2m_page_pagetable_wf);
        reveal(mapped_1g_page_pagetable_wf);
    };
    assert(container_process_page_pagetable_wf(
        post.ctn_mp,
        post.prc_mp,
        post.pt_mp,
        post.pg_arr,
    )) by {
        reveal(container_process_page_pagetable_wf);
    };
    assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by {
        reveal(container_pages_wf);
    };
    assert(process_pages_wf(post.pg_arr, post.prc_mp)) by {
        reveal(process_pages_wf);
    };
    assert(pagetable_pages_wf(post.pt_mp, post.pg_arr)) by {
        reveal(pagetable_pages_wf);
    };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by {
        reveal(iommu_table_pages_wf);
    };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by {
        reveal(thread_pages_wf);
    };
    assert(pcid_allocator_pages_wf(
        post.pg_arr,
        post.pcid_allc_mp,
    )) by {
        reveal(pcid_allocator_pages_wf);
    };
    assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by {
        reveal(thread_staged_pages_4k_wf);
    };
    assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by {
        reveal(thread_staged_pages_2m_wf);
    };
    assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by {
        reveal(thread_staged_pages_1g_wf);
    };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by {
        reveal(endpoint_pages_wf);
    };
    assert(container_allocator_free_4k_page_wf(
        post.allc_4k_mp,
        post.pg_arr,
    )) by {
        reveal(allocator_free_page_ptrs_wf);
        reveal(container_allocator_free_4k_page_wf);
        reveal(container_allocator_global_free_4k_page_wf);
        reveal(container_allocator_cpu_cache_free_4k_page_wf);
    };
    assert(container_allocator_free_2m_page_wf(
        post.allc_2m_mp,
        post.pg_arr,
    )) by {
        reveal(allocator_free_page_ptrs_wf);
        reveal(container_allocator_free_2m_page_wf);
        reveal(container_allocator_global_free_2m_page_wf);
        reveal(container_allocator_cpu_cache_free_2m_page_wf);
    };
    assert(container_allocator_free_1g_page_wf(
        post.allc_1g_mp,
        post.pg_arr,
    )) by {
        reveal(allocator_free_page_ptrs_wf);
        reveal(container_allocator_free_1g_page_wf);
        reveal(container_allocator_global_free_1g_page_wf);
        reveal(container_allocator_cpu_cache_free_1g_page_wf);
    };
}

pub proof fn lemma_no_change_imply_memory_management_inv_for_page_fields_forall()
    ensures
        forall|pre: KernelK, post: KernelK|
            #![trigger pre.memory_management_inv(), post.memory_management_inv()]
            pre.memory_management_inv()
            && pagetable_perms_wf(pre.pt_mp)
            && page_invariant_fields_unchanged(pre.pg_arr, post.pg_arr)
            && page_memory_management_context_unchanged(pre, post)
            ==> post.memory_management_inv(),
{
    assert forall|pre: KernelK, post: KernelK| #![auto]
        pre.memory_management_inv()
        && pagetable_perms_wf(pre.pt_mp)
        && page_invariant_fields_unchanged(pre.pg_arr, post.pg_arr)
        && page_memory_management_context_unchanged(pre, post)
    implies post.memory_management_inv() by {
        memory_management_inv_preserved_for_page_invariant_fields(pre, post);
    };
}

pub proof fn lemma_no_change_imply_page_array_wf_forall()
    ensures
        forall|pre: PageLockedArray, post: PageLockedArray, changed: PageIndex|
            #![trigger page_array_wf(pre), page_array_wf(post), post.spec_index(changed)]
            page_array_wf(pre)
            && index_valid(NUM_PAGES, changed)
            && post.inv()
            && post.unchanged_except(&pre, changed)
            && post.spec_index(changed).view().inv()
            ==> page_array_wf(post),
{
    reveal(page_array_wf);
}

}
