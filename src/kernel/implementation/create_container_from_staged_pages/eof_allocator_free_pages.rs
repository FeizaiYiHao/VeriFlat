use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub broadcast proof fn publish_staged_container_root_eof_allocator_free_4k_global_ptr_valid(
    pre: KernelK,
    post: KernelK,
    parent_container_ptr: RwLockContainerPtr,
    current_thread_ptr: RwLockThreadPtr,
    container_page: PagePtr,
    pcid_allocator_page: PagePtr,
    allocator_4k_page: PagePtr,
    allocator_2m_page: PagePtr,
    allocator_1g_page: PagePtr,
    scheduler_page: PagePtr,
    cpu_set_page: PagePtr,
    process_page: PagePtr,
    pagetable_page: PagePtr,
    l4_page: PagePtr,
    thread_page: PagePtr,
    funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize,
    process_quota_4k: usize,
    alloc_ptr: RwLockPageAllocatorPtr,
    page_ptr: PagePtr,
)
    requires
        pre.inv(),
        !pre.allc_4k_mp.dom().contains(allocator_4k_page),
        forall|ptr: PagePtr|
            #![trigger funding_pages.to_set().contains(ptr)]
            funding_pages.to_set().contains(ptr) ==> page_ptr_valid(ptr),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        post.allc_4k_mp.dom().contains(alloc_ptr),
        post.allc_4k_mp.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr),
    ensures
        #![trigger
            publish_staged_container_root_kernel_state_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.allc_4k_mp.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)
        ]
        page_ptr_valid(page_ptr),
{
    if alloc_ptr == allocator_4k_page {
        assert(post.allc_4k_mp.spec_index(alloc_ptr).global_pool.view().view() == funding_pages) by { reveal(publish_staged_container_root_kernel_state_framing); };
        funding_pages.to_set_ensures();
        assert(funding_pages.to_set().contains(page_ptr));
    } else {
        assert(pre.allc_4k_mp.dom().contains(alloc_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); broadcast use vstd::set::lemma_set_insert_different; };
        assert(post.allc_4k_mp.spec_index(alloc_ptr) == pre.allc_4k_mp.spec_index(alloc_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); };
        assert(allocator_free_page_ptrs_wf(pre.allc_4k_mp)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); reveal(KernelK::allocator_free_pages_wf); };
        reveal(allocator_free_page_ptrs_wf);
    }
}

#[verifier::spinoff_prover]
pub broadcast proof fn publish_staged_container_root_eof_allocator_free_4k_global_backward(
    pre: KernelK,
    post: KernelK,
    parent_container_ptr: RwLockContainerPtr,
    current_thread_ptr: RwLockThreadPtr,
    container_page: PagePtr,
    pcid_allocator_page: PagePtr,
    allocator_4k_page: PagePtr,
    allocator_2m_page: PagePtr,
    allocator_1g_page: PagePtr,
    scheduler_page: PagePtr,
    cpu_set_page: PagePtr,
    process_page: PagePtr,
    pagetable_page: PagePtr,
    l4_page: PagePtr,
    thread_page: PagePtr,
    funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize,
    process_quota_4k: usize,
    alloc_ptr: RwLockPageAllocatorPtr,
    page_ptr: PagePtr,
)
    requires
        pre.inv(),
        container_allocator_global_free_4k_backward_wf(pre.allc_4k_mp, pre.pg_arr,),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        page_ptr_valid(allocator_4k_page),
        page_ptr_valid(allocator_2m_page),
        page_ptr_valid(allocator_1g_page),
        page_ptr_valid(scheduler_page),
        page_ptr_valid(cpu_set_page),
        page_ptr_valid(process_page),
        page_ptr_valid(pagetable_page),
        page_ptr_valid(l4_page),
        !pre.allc_4k_mp.dom().contains(allocator_4k_page),
        forall|ptr: PagePtr|
            #![trigger funding_pages.to_set().contains(ptr)]
            funding_pages.to_set().contains(ptr) ==> page_ptr_valid(ptr),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        post.allc_4k_mp.dom().contains(alloc_ptr),
        post.allc_4k_mp.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr),
    ensures
        #![trigger
            publish_staged_container_root_kernel_state_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.allc_4k_mp.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)
        ]
        {
            &&& post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == PageState::Free4k {
                    allocator_ptr: Ghost(alloc_ptr),
                    state: FreePageAllocatorState::GlobalList,
                }
            &&& post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == post.allc_4k_mp.spec_index(alloc_ptr).owning_container
        },
{
    publish_staged_container_root_eof_allocator_free_4k_global_ptr_valid(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, alloc_ptr, page_ptr,
    );
    page_ptr_valid_imply_page_index_valid();
    page_ptr_roundtrip();
    if alloc_ptr == allocator_4k_page {
        assert(post.allc_4k_mp.spec_index(alloc_ptr).global_pool.view().view() == funding_pages) by { reveal(publish_staged_container_root_kernel_state_framing); };
        funding_pages.to_set_ensures();
        assert(funding_pages.to_set().contains(page_ptr));
        reveal(publish_staged_container_root_kernel_state_framing);
    } else {
        assert(pre.allc_4k_mp.dom().contains(alloc_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); broadcast use vstd::set::lemma_set_insert_different; };
        assert(post.allc_4k_mp.spec_index(alloc_ptr) == pre.allc_4k_mp.spec_index(alloc_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); };
        assert(pre.allc_4k_mp.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr));
        assert({
            &&& pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == PageState::Free4k {
                    allocator_ptr: Ghost(alloc_ptr),
                    state: FreePageAllocatorState::GlobalList,
                }
            &&& pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == pre.allc_4k_mp.spec_index(alloc_ptr).owning_container
        }) by { reveal(container_allocator_global_free_4k_backward_wf); };
        publish_staged_container_root_eof_unmodified_object_page_state_eq(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k, page_ptr2page_index(page_ptr),
        );
    }
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_allocator_free_pages_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        !pre.allc_4k_mp.dom().contains(allocator_4k_page),
        !pre.allc_2m_mp.dom().contains(allocator_2m_page),
        !pre.allc_1g_mp.dom().contains(allocator_1g_page),
        forall|page_ptr: PagePtr|
            #![trigger funding_pages.to_set().contains(page_ptr)]
            funding_pages.to_set().contains(page_ptr) ==> page_ptr_valid(page_ptr),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        post.allocator_free_pages_wf(),
{
    assert(pre.allocator_free_pages_wf()) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); };
    assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by {
        broadcast use publish_staged_container_root_eof_allocator_free_4k_global_ptr_valid;
        reveal(publish_staged_container_root_kernel_state_framing); reveal(allocator_free_page_ptrs_wf);
    };
    assert(allocator_free_page_ptrs_wf(post.allc_2m_mp)) by { reveal(publish_staged_container_root_kernel_state_framing); reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_free_page_ptrs_wf(post.allc_1g_mp)) by { reveal(publish_staged_container_root_kernel_state_framing); reveal(allocator_free_page_ptrs_wf); };
    reveal(KernelK::allocator_free_pages_wf);
}

}
