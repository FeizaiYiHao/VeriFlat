use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {

/// Page lock/unlock changes only lock state. Every memory-management
/// invariant reads the page payload, so equal payloads and equal companion
/// maps preserve the complete memory-management invariant.
pub proof fn memory_management_inv_preserved_for_page_lock_op(
    pre: KernelK,
    post: KernelK,
)
    requires
        pre.memory_management_inv(),
        pagetable_perms_wf(pre.pagetable_map),
        page_array_wf(post.page_array),
        post.pagetable_map == pre.pagetable_map,
        post.container_map == pre.container_map,
        post.process_map == pre.process_map,
        post.thread_map == pre.thread_map,
        post.endpoint_map == pre.endpoint_map,
        post.allocator_4k_map == pre.allocator_4k_map,
        post.allocator_2m_map == pre.allocator_2m_map,
        post.allocator_1g_map == pre.allocator_1g_map,
        post.page_array.payloads_unchanged(&pre.page_array),
    ensures
        post.memory_management_inv(),
{
    assert(allocator_pages_wf(
        post.page_array,
        post.allocator_4k_map,
        post.allocator_2m_map,
        post.allocator_1g_map,
    )) by {
        reveal(LockedArray::payloads_unchanged);
        reveal(allocator_4k_pages_wf);
        reveal(allocator_2m_pages_wf);
        reveal(allocator_1g_pages_wf);
    };
    assert(container_page_owner_wf(post.container_map, post.page_array)) by {
        reveal(LockedArray::payloads_unchanged);
        reveal(container_page_owner_wf);
    };
    assert(container_process_page_pagetable_wf(
        post.container_map,
        post.process_map,
        post.pagetable_map,
        post.page_array,
    )) by {
        reveal(LockedArray::payloads_unchanged);
        reveal(container_process_page_pagetable_wf);
    };
    assert(container_pages_wf(post.page_array, post.container_map)) by {
        reveal(LockedArray::payloads_unchanged);
        reveal(container_pages_wf);
    };
    assert(process_pages_wf(post.page_array, post.process_map)) by {
        reveal(LockedArray::payloads_unchanged);
        reveal(process_pages_wf);
    };
    assert(hugepage_2m_wf(post.page_array)) by {
        reveal(LockedArray::payloads_unchanged);
        reveal(hugepage_2m_wf);
    };
    assert(hugepage_1g_wf(post.page_array)) by {
        reveal(LockedArray::payloads_unchanged);
        reveal(hugepage_1g_wf);
    };
    assert(page_pagetable_wf(post.pagetable_map, post.page_array)) by {
        page_pagetable_wf_preserved_for_page_payloads_unchanged(
            pre.pagetable_map,
            post.pagetable_map,
            pre.page_array,
            post.page_array,
        );
    };
    assert(pagetable_pages_wf(post.pagetable_map, post.page_array)) by {
        reveal(LockedArray::payloads_unchanged);
        reveal(pagetable_pages_wf);
    };
    assert(thread_pages_wf(post.thread_map, post.page_array)) by {
        reveal(LockedArray::payloads_unchanged);
        reveal(thread_pages_wf);
    };
    assert(process_staged_pages_wf(post.process_map, post.page_array)) by {
        reveal(LockedArray::payloads_unchanged);
        reveal(process_staged_pages_4k_wf);
        reveal(process_staged_pages_2m_wf);
        reveal(process_staged_pages_1g_wf);
    };
    assert(endpoint_pages_wf(post.endpoint_map, post.page_array)) by {
        reveal(LockedArray::payloads_unchanged);
        reveal(endpoint_pages_wf);
    };
    assert(container_allocator_free_4k_page_wf(
        post.container_map,
        post.allocator_4k_map,
        post.page_array,
    )) by {
        page_ptr_lemma1();
        reveal(LockedArray::payloads_unchanged);
        reveal(container_allocator_free_4k_page_wf);
        reveal(allocator_free_page_ptrs_wf);
        reveal(container_allocator_wf);
        reveal(container_page_owner_wf);
    };
    assert(container_allocator_free_2m_page_wf(
        post.container_map,
        post.allocator_2m_map,
        post.page_array,
    )) by {
        page_ptr_lemma1();
        reveal(LockedArray::payloads_unchanged);
        reveal(container_allocator_free_2m_page_wf);
        reveal(allocator_free_page_ptrs_wf);
        reveal(container_allocator_wf);
        reveal(container_page_owner_wf);
    };
    assert(container_allocator_free_1g_page_wf(
        post.container_map,
        post.allocator_1g_map,
        post.page_array,
    )) by {
        page_ptr_lemma1();
        reveal(LockedArray::payloads_unchanged);
        reveal(container_allocator_free_1g_page_wf);
        reveal(allocator_free_page_ptrs_wf);
        reveal(container_allocator_wf);
        reveal(container_page_owner_wf);
    };
}

}
