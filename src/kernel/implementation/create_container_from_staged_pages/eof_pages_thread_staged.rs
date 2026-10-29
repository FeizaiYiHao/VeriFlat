use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
pub(super) broadcast proof fn publish_staged_container_root_eof_thread_staged_pages_4k_forward(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize, process_quota_4k: usize, page_index: PageIndex,
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
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        index_valid(NUM_PAGES, page_index),
        post.pg_arr.spec_index(page_index).view().view().state is Owned4k,
    ensures
        #![trigger
            publish_staged_container_root_eof_transition_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.pg_arr.spec_index(page_index).view().view().state
        ]
        {
            let thread_ptr = post.pg_arr.spec_index(page_index).view().view().state->Owned4k_thread_ptr;
            &&& post.thr_mp.dom().contains(thread_ptr)
            &&& post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_index2page_ptr(page_index))
        },
{
    reveal(publish_staged_container_root_eof_transition_framing); reveal(publish_staged_container_root_eof_preconditions);
    publish_staged_container_root_eof_unmodified_object_page_state_eq(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, page_index,
    );
    let page_ptr = page_index2page_ptr(page_index);
    let thread_ptr = post.pg_arr.spec_index(page_index).view().view().state->Owned4k_thread_ptr;
    assert(pre.thr_mp.dom().contains(thread_ptr)) by { reveal(thread_staged_pages_4k_wf); };
    assert(pre.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr)) by { reveal(thread_staged_pages_4k_wf); };
    if thread_ptr == current_thread_ptr {
        assert(!funding_pages.to_set().contains(page_ptr)) by { page_index_roundtrip(); };
        assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(page_ptr)) by {
            reveal(new_container_bootstrap_4k_pages); page_index_roundtrip();
        };
    } else { }
}

pub(super) broadcast proof fn publish_staged_container_root_eof_thread_staged_pages_4k_backward(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize, process_quota_4k: usize, thread_ptr: RwLockThreadPtr, page_ptr: PagePtr,
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
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        post.thr_mp.dom().contains(thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr),
    ensures
        #![trigger
            publish_staged_container_root_eof_transition_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr)
        ]
        page_ptr_valid(page_ptr) && post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr }),
{
    reveal(publish_staged_container_root_eof_transition_framing); reveal(publish_staged_container_root_eof_preconditions);
    if thread_ptr == current_thread_ptr {
        assert(pre.pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })) by { reveal(thread_staged_pages_4k_wf); };
    } else {
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

pub(super) broadcast proof fn publish_staged_container_root_eof_thread_staged_pages_2m_forward(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize, process_quota_4k: usize, page_index: PageIndex,
)
    requires
        thread_staged_pages_2m_wf(pre.thr_mp, pre.pg_arr),
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        index_valid(NUM_PAGES, page_index),
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
        post.pg_arr.spec_index(page_index).view().view().state is Owned2m,
    ensures
        #![trigger
            publish_staged_container_root_eof_transition_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.pg_arr.spec_index(page_index).view().view().state
        ]
        {
            &&& post.thr_mp.dom().contains(post.pg_arr.spec_index(page_index).view().view().state->Owned2m_thread_ptr)
            &&& post.thr_mp.spec_index(post.pg_arr.spec_index(page_index).view().view().state->Owned2m_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_index2page_ptr(page_index))
        },
{
    hide(Seq::contains); reveal(publish_staged_container_root_eof_transition_framing); reveal(publish_staged_container_root_eof_preconditions);
    page_index_valid_imply_page_ptr_valid(); page_index_roundtrip();
    assert(!new_container_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
    ).contains(page_index2page_ptr(page_index))) by {
        reveal(Seq::contains); reveal(new_container_moved_pages); reveal(new_container_bootstrap_4k_pages);
        page_ptr_2m_valid_imply_page_index_2m_valid(container_page); page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
        broadcast use page_2m_ptr_prefix_member_bounds;
    };
    publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, page_index,
    );
    assert(thread_staged_pages_2m_forward_wf(pre.thr_mp, pre.pg_arr)) by { reveal(thread_staged_pages_2m_wf); };
}

pub(super) broadcast proof fn publish_staged_container_root_eof_thread_staged_pages_2m_backward(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize, process_quota_4k: usize, thread_ptr: RwLockThreadPtr, page_ptr: PagePtr,
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
        post.thr_mp.dom().contains(thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr),
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        #![trigger
            publish_staged_container_root_eof_transition_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr)
        ]
        {
            &&& page_ptr_valid(page_ptr)
            &&& post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned2m { thread_ptr })
        },
{
    reveal(publish_staged_container_root_eof_transition_framing); reveal(publish_staged_container_root_eof_preconditions);
    assert(hugepage_2m_tail_forward_wf(pre.pg_arr)) by { reveal(hugepage_2m_wf); };
    page_ptr_2m_valid_imply_page_index_2m_valid(container_page); page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
    assert(pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned2m { thread_ptr })) by { reveal(thread_staged_pages_2m_wf); };
    assert(page_ptr_valid(page_ptr)) by { reveal(thread_staged_pages_2m_wf); };
    page_ptr_valid_imply_page_index_valid();
    assert(!funding_pages.to_set().contains(page_ptr)) by { reveal(thread_staged_pages_4k_wf); };
    assert(!page_2m_tail_indices(page_ptr2page_index(container_page)).contains(page_ptr2page_index(page_ptr))) by {
        if page_2m_tail_indices(page_ptr2page_index(container_page)).contains(page_ptr2page_index(page_ptr)) { }
    };
    assert(!page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).contains(page_ptr2page_index(page_ptr))) by {
        if page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).contains(page_ptr2page_index(page_ptr)) { }
    };
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).contains(page_ptr)) by { reveal(thread_staged_pages_4k_wf); };
    assert(!page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(page_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(page_ptr) {
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(container_page), 512, page_ptr,);
            assert(page_ptr2page_index(page_ptr) != page_ptr2page_index(container_page)) by { page_ptr2page_index_injective(); };
        }
    };
    assert(!page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(page_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(page_ptr) {
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(pcid_allocator_page), 512, page_ptr,);
            assert(page_ptr2page_index(page_ptr) != page_ptr2page_index(pcid_allocator_page)) by { page_ptr2page_index_injective(); };
        }
    };
    assert(!new_container_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
    ).contains(page_ptr)) by { reveal(new_container_moved_pages); page_ptr2page_index_injective(); };
    page_ptr_roundtrip();
    publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, page_ptr2page_index(page_ptr),
    );
}

pub(super) proof fn publish_staged_container_root_eof_thread_staged_pages_wf(
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
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        thread_staged_pages_wf(post.thr_mp, post.pg_arr),
{
    reveal(publish_staged_container_root_eof_transition_framing);
    assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by { broadcast use publish_staged_container_root_eof_thread_staged_pages_4k_forward; broadcast use publish_staged_container_root_eof_thread_staged_pages_4k_backward; reveal(thread_staged_pages_4k_wf); };
    assert(thread_staged_pages_2m_backward_wf(post.thr_mp, post.pg_arr)) by { broadcast use publish_staged_container_root_eof_thread_staged_pages_2m_backward; };
    assert(thread_staged_pages_2m_forward_wf(post.thr_mp, post.pg_arr)) by { broadcast use publish_staged_container_root_eof_thread_staged_pages_2m_forward; };
    reveal(thread_staged_pages_2m_wf);
    assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by { broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; reveal(thread_staged_pages_1g_wf); };
}
}
