use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_thread_staged_pages_1g_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
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
        pre.thr_mp.dom().contains(current_thread_ptr),
        forall|page_ptr: PagePtr|
            #![trigger pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr)]
            #![trigger funding_pages.to_set().contains(page_ptr)]
            #![trigger new_container_bootstrap_4k_pages(
                allocator_4k_page,
                allocator_2m_page,
                allocator_1g_page,
                scheduler_page,
                cpu_set_page,
                process_page,
                pagetable_page,
                l4_page,
            ).contains(page_ptr)]
            pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) <==> new_container_bootstrap_4k_pages(
                    allocator_4k_page,
                    allocator_2m_page,
                    allocator_1g_page,
                    scheduler_page,
                    cpu_set_page,
                    process_page,
                    pagetable_page,
                    l4_page,
                ).contains(page_ptr) || funding_pages.to_set().contains(page_ptr) || page_ptr == thread_page,
        forall|page_ptr: PagePtr|
            #![trigger pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr)]
            pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr) <==> page_ptr == container_page || page_ptr == pcid_allocator_page,
        pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr),
{
    assert(thread_staged_pages_1g_wf(pre.thr_mp, pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); reveal(thread_staged_pages_wf); };
    broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq;
    reveal(publish_staged_container_root_kernel_state_framing);
    reveal(LockedMap::unchanged_except);
    reveal(thread_staged_pages_1g_wf);
}

#[verifier::spinoff_prover]
pub broadcast proof fn publish_staged_container_root_eof_thread_staged_pages_4k_forward(
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
    page_index: PageIndex,
)
    requires
        pre.inv(),
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
        page_ptr_valid(thread_page),
        pre.thr_mp.dom().contains(current_thread_ptr),
        forall|page_ptr: PagePtr|
            #![trigger pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr)]
            #![trigger funding_pages.to_set().contains(page_ptr)]
            #![trigger new_container_bootstrap_4k_pages(
                allocator_4k_page,
                allocator_2m_page,
                allocator_1g_page,
                scheduler_page,
                cpu_set_page,
                process_page,
                pagetable_page,
                l4_page,
            ).contains(page_ptr)]
            pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) <==> new_container_bootstrap_4k_pages(
                    allocator_4k_page,
                    allocator_2m_page,
                    allocator_1g_page,
                    scheduler_page,
                    cpu_set_page,
                    process_page,
                    pagetable_page,
                    l4_page,
                ).contains(page_ptr) || funding_pages.to_set().contains(page_ptr) || page_ptr == thread_page,
        forall|page_ptr: PagePtr|
            #![trigger pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr)]
            pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr) <==> page_ptr == container_page || page_ptr == pcid_allocator_page,
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        index_valid(NUM_PAGES, page_index),
        post.pg_arr.spec_index(page_index).view().view().state is Owned4k,
    ensures
        #![trigger
            publish_staged_container_root_kernel_state_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.pg_arr.spec_index(page_index).view().view().state
        ]
        {
            let thread_ptr =
                post.pg_arr.spec_index(page_index).view().view().state->Owned4k_thread_ptr;
            &&& post.thr_mp.dom().contains(thread_ptr)
            &&& post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_index2page_ptr(page_index))
        },
{
    publish_staged_container_root_eof_unmodified_object_page_state_eq(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, page_index,
    );
    assert(thread_staged_pages_4k_wf(pre.thr_mp, pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); reveal(thread_staged_pages_wf); };
    let page_ptr = page_index2page_ptr(page_index);
    let thread_ptr =
        post.pg_arr.spec_index(page_index).view().view().state->Owned4k_thread_ptr;
    assert(pre.thr_mp.dom().contains(thread_ptr)) by { reveal(thread_staged_pages_4k_wf); };
    assert(pre.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr)) by { reveal(thread_staged_pages_4k_wf); };
    if thread_ptr == current_thread_ptr {
        assert(!funding_pages.to_set().contains(page_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); page_index_roundtrip(); };
        assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(page_ptr)) by {
            reveal(new_container_bootstrap_4k_pages); reveal(publish_staged_container_root_kernel_state_framing); page_index_roundtrip();
            broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
        };
        assert(page_ptr == thread_page);
        assert(post.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); };
    } else {
        assert(post.thr_mp.dom().contains(thread_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); reveal(LockedMap::unchanged_except); };
        assert(post.thr_mp.spec_index(thread_ptr) == pre.thr_mp.spec_index(thread_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); reveal(LockedMap::unchanged_except); };
    }
}

#[verifier::spinoff_prover]
pub broadcast proof fn publish_staged_container_root_eof_thread_staged_pages_4k_backward(
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
    thread_ptr: RwLockThreadPtr,
    page_ptr: PagePtr,
)
    requires
        pre.inv(),
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
        page_ptr_valid(thread_page),
        pre.thr_mp.dom().contains(current_thread_ptr),
        forall|staged_page_ptr: PagePtr|
            #![trigger pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(staged_page_ptr)]
            #![trigger funding_pages.to_set().contains(staged_page_ptr)]
            #![trigger new_container_bootstrap_4k_pages(
                allocator_4k_page,
                allocator_2m_page,
                allocator_1g_page,
                scheduler_page,
                cpu_set_page,
                process_page,
                pagetable_page,
                l4_page,
            ).contains(staged_page_ptr)]
            pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(staged_page_ptr) <==> new_container_bootstrap_4k_pages(
                    allocator_4k_page,
                    allocator_2m_page,
                    allocator_1g_page,
                    scheduler_page,
                    cpu_set_page,
                    process_page,
                    pagetable_page,
                    l4_page,
                ).contains(staged_page_ptr) || funding_pages.to_set().contains(staged_page_ptr) || staged_page_ptr == thread_page,
        forall|staged_page_ptr: PagePtr|
            #![trigger pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(staged_page_ptr)]
            pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(staged_page_ptr) <==> staged_page_ptr == container_page || staged_page_ptr == pcid_allocator_page,
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        post.thr_mp.dom().contains(thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr),
    ensures
        #![trigger
            publish_staged_container_root_kernel_state_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr)
        ]
        page_ptr_valid(page_ptr) && post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr }),
{
    assert(thread_staged_pages_4k_wf(pre.thr_mp, pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); reveal(thread_staged_pages_wf); };
    if thread_ptr == current_thread_ptr {
        assert(page_ptr == thread_page) by { reveal(publish_staged_container_root_kernel_state_framing); };
        assert(pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(thread_page));
        assert(pre.pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })) by { reveal(thread_staged_pages_4k_wf); };
        assert(post.pg_arr.spec_index(page_ptr2page_index(thread_page)) == pre.pg_arr.spec_index(page_ptr2page_index(thread_page))) by { reveal(publish_staged_container_root_kernel_state_framing); };
    } else {
        assert(pre.thr_mp.dom().contains(thread_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); reveal(LockedMap::unchanged_except); };
        assert(pre.thr_mp.spec_index(thread_ptr) == post.thr_mp.spec_index(thread_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); reveal(LockedMap::unchanged_except); };
        assert(pre.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr));
        assert(page_ptr_valid(page_ptr)) by { reveal(thread_staged_pages_4k_wf); };
        assert(pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr })) by { reveal(thread_staged_pages_4k_wf); };
        page_ptr_valid_imply_page_index_valid();
        publish_staged_container_root_eof_unmodified_object_page_state_eq(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k, page_ptr2page_index(page_ptr),
        );
    }
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_thread_staged_pages_4k_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
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
        page_ptr_valid(thread_page),
        pre.thr_mp.dom().contains(current_thread_ptr),
        forall|page_ptr: PagePtr|
            #![trigger pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr)]
            #![trigger funding_pages.to_set().contains(page_ptr)]
            #![trigger new_container_bootstrap_4k_pages(
                allocator_4k_page,
                allocator_2m_page,
                allocator_1g_page,
                scheduler_page,
                cpu_set_page,
                process_page,
                pagetable_page,
                l4_page,
            ).contains(page_ptr)]
            pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) <==> new_container_bootstrap_4k_pages(
                    allocator_4k_page,
                    allocator_2m_page,
                    allocator_1g_page,
                    scheduler_page,
                    cpu_set_page,
                    process_page,
                    pagetable_page,
                    l4_page,
                ).contains(page_ptr) || funding_pages.to_set().contains(page_ptr) || page_ptr == thread_page,
        forall|page_ptr: PagePtr|
            #![trigger pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr)]
            pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr) <==> page_ptr == container_page || page_ptr == pcid_allocator_page,
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr),
{
    broadcast use publish_staged_container_root_eof_thread_staged_pages_4k_forward;
    broadcast use publish_staged_container_root_eof_thread_staged_pages_4k_backward;
    reveal(thread_staged_pages_4k_wf);
}

}
