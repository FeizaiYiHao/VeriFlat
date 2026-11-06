use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
pub(super) broadcast proof fn publish_staged_container_root_eof_thread_staged_pages_4k_forward(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize, process_quota_4k: usize, pg_idx: PageIndex,
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
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        index_valid(NUM_PAGES, pg_idx),
        post.pg_arr.spec_index(pg_idx).view().view().state is Owned4k,
    ensures
        #![trigger
            publish_staged_container_root_eof_transition_framing(
                pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.pg_arr.spec_index(pg_idx).view().view().state
        ]
        {
            let thrd_ptr = post.pg_arr.spec_index(pg_idx).view().view().state->Owned4k_thread_ptr;
            &&& post.thrd_mp.dom().contains(thrd_ptr)
            &&& post.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k.view().contains(page_index2page_ptr(pg_idx))
        },
{
    hide(Seq::contains); reveal(publish_staged_container_root_eof_transition_framing); reveal(publish_staged_container_root_eof_preconditions);
    publish_staged_container_root_eof_unmodified_object_page_state_eq(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, pg_idx,
    );
    let pg_ptr = page_index2page_ptr(pg_idx);
    let thrd_ptr = post.pg_arr.spec_index(pg_idx).view().view().state->Owned4k_thread_ptr;
    assert(pre.thrd_mp.dom().contains(thrd_ptr)) by { reveal(thread_staged_4k_pages_wf); };
    assert(pre.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k.view().contains(pg_ptr)) by { reveal(thread_staged_4k_pages_wf); };
    if thrd_ptr == current_thrd_ptr {
        assert(!funding_pages.to_set().contains(pg_ptr)) by { page_index_roundtrip(); };
        assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(pg_ptr)) by {
            reveal(Seq::contains); reveal(new_container_bootstrap_4k_pages); page_index_roundtrip();
        };
    } else { }
}

pub(super) broadcast proof fn publish_staged_container_root_eof_thread_staged_pages_4k_backward(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize, process_quota_4k: usize, thrd_ptr: RwLockThreadPtr, pg_ptr: PagePtr,
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
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        post.thrd_mp.dom().contains(thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k.view().contains(pg_ptr),
    ensures
        #![trigger
            publish_staged_container_root_eof_transition_framing(
                pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k.view().contains(pg_ptr)
        ]
        page_ptr_valid(pg_ptr) && post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: thrd_ptr }),
{
    reveal(publish_staged_container_root_eof_transition_framing); reveal(publish_staged_container_root_eof_preconditions);
    if thrd_ptr == current_thrd_ptr {
        assert(pre.pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr })) by { reveal(thread_staged_4k_pages_wf); };
    } else {
        assert(page_ptr_valid(pg_ptr)) by { reveal(thread_staged_4k_pages_wf); };
        assert(pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: thrd_ptr })) by { reveal(thread_staged_4k_pages_wf); };
        page_ptr_valid_imply_page_index_valid();
        publish_staged_container_root_eof_unmodified_object_page_state_eq(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k, page_ptr2page_index(pg_ptr),
        );
    }
}

pub(super) broadcast proof fn publish_staged_container_root_eof_thread_staged_pages_2m_forward(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize, process_quota_4k: usize, pg_idx: PageIndex,
)
    requires
        pre.memory_management_inv(),
        thread_staged_2m_pages_wf(pre.thrd_mp, pre.pg_arr),
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        index_valid(NUM_PAGES, pg_idx),
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
        post.pg_arr.spec_index(pg_idx).view().view().state is Owned2m,
    ensures
        #![trigger
            publish_staged_container_root_eof_transition_framing(
                pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.pg_arr.spec_index(pg_idx).view().view().state
        ]
        {
            &&& post.thrd_mp.dom().contains(post.pg_arr.spec_index(pg_idx).view().view().state->Owned2m_thread_ptr)
            &&& post.thrd_mp.spec_index(post.pg_arr.spec_index(pg_idx).view().view().state->Owned2m_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_index2page_ptr(pg_idx))
        },
{
    hide(Seq::contains); reveal(publish_staged_container_root_eof_transition_framing); reveal(publish_staged_container_root_eof_preconditions);
    page_index_valid_imply_page_ptr_valid(); page_index_roundtrip();
    assert(!new_container_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
    ).contains(page_index2page_ptr(pg_idx))) by {
        reveal(Seq::contains); reveal(new_container_moved_pages); reveal(new_container_bootstrap_4k_pages);
        page_ptr_2m_valid_imply_page_index_2m_valid(container_page); page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
        if page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(page_index2page_ptr(pg_idx)) {
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(container_page), 512, page_index2page_ptr(pg_idx));
            if pg_idx != page_ptr2page_index(container_page) {
                publish_staged_container_root_eof_page_fields_eq_in_moved_2m_tails(
                    pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
                    allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
                    allocator_quota_4k, process_quota_4k, page_ptr2page_index(container_page), pg_idx,
                );
            }
        }
        if page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(page_index2page_ptr(pg_idx)) {
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(pcid_allocator_page), 512, page_index2page_ptr(pg_idx));
            if pg_idx != page_ptr2page_index(pcid_allocator_page) {
                publish_staged_container_root_eof_page_fields_eq_in_moved_2m_tails(
                    pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
                    allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
                    allocator_quota_4k, process_quota_4k, page_ptr2page_index(pcid_allocator_page), pg_idx,
                );
            }
        }
    };
    publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, pg_idx,
    );
    assert(thread_staged_2m_pages_forward_wf(pre.thrd_mp, pre.pg_arr)) by { reveal(thread_staged_2m_pages_wf); };
}

pub(super) broadcast proof fn publish_staged_container_root_eof_thread_staged_pages_2m_backward(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize, process_quota_4k: usize, thrd_ptr: RwLockThreadPtr, pg_ptr: PagePtr,
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
        post.thrd_mp.dom().contains(thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_2m.view().contains(pg_ptr),
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        #![trigger
            publish_staged_container_root_eof_transition_framing(
                pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_2m.view().contains(pg_ptr)
        ]
        {
            &&& page_ptr_valid(pg_ptr)
            &&& post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned2m { thread_ptr: thrd_ptr })
        },
{
    reveal(publish_staged_container_root_eof_transition_framing); reveal(publish_staged_container_root_eof_preconditions);
    assert(hugepage_2m_tail_forward_wf(pre.pg_arr)) by { reveal(hugepage_2m_wf); };
    page_ptr_2m_valid_imply_page_index_2m_valid(container_page); page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
    assert(pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned2m { thread_ptr: thrd_ptr })) by { reveal(thread_staged_2m_pages_wf); };
    assert(page_ptr_valid(pg_ptr)) by { reveal(thread_staged_2m_pages_wf); };
    page_ptr_valid_imply_page_index_valid();
    assert(!funding_pages.to_set().contains(pg_ptr)) by { reveal(thread_staged_4k_pages_wf); };
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).contains(pg_ptr)) by { reveal(thread_staged_4k_pages_wf); };
    assert(!page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(pg_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(pg_ptr) {
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(container_page), 512, pg_ptr,);
            assert(page_ptr2page_index(pg_ptr) != page_ptr2page_index(container_page)) by { page_ptr2page_index_injective(); };
        }
    };
    assert(!page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(pg_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(pg_ptr) {
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(pcid_allocator_page), 512, pg_ptr,);
            assert(page_ptr2page_index(pg_ptr) != page_ptr2page_index(pcid_allocator_page)) by { page_ptr2page_index_injective(); };
        }
    };
    assert(!new_container_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
    ).contains(pg_ptr)) by { reveal(new_container_moved_pages); page_ptr2page_index_injective(); };
    page_ptr_roundtrip();
    publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, page_ptr2page_index(pg_ptr),
    );
}

pub(super) proof fn publish_staged_container_root_eof_thread_staged_pages_wf(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
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
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        thread_staged_pages_wf(post.thrd_mp, post.pg_arr),
{
    hide(Seq::contains); reveal(publish_staged_container_root_eof_transition_framing);
    assert(thread_staged_4k_pages_wf(post.thrd_mp, post.pg_arr)) by { broadcast use publish_staged_container_root_eof_thread_staged_pages_4k_forward; broadcast use publish_staged_container_root_eof_thread_staged_pages_4k_backward; reveal(thread_staged_4k_pages_wf); };
    assert(thread_staged_2m_pages_backward_wf(post.thrd_mp, post.pg_arr)) by { broadcast use publish_staged_container_root_eof_thread_staged_pages_2m_backward; };
    assert(thread_staged_2m_pages_forward_wf(post.thrd_mp, post.pg_arr)) by { broadcast use publish_staged_container_root_eof_thread_staged_pages_2m_forward; };
    reveal(thread_staged_2m_pages_wf);
    assert(thread_staged_1g_pages_wf(post.thrd_mp, post.pg_arr)) by { broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; reveal(thread_staged_1g_pages_wf); };
}
}
