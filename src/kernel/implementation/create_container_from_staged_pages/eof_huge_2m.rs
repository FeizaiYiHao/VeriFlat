use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub broadcast proof fn publish_staged_container_root_eof_hugepage_2m_head_valid(
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
        hugepage_2m_head_valid_wf(pre.pg_arr),
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
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        index_valid(NUM_PAGES, page_index),
        {
            let state = post.pg_arr.spec_index(page_index).view().view().state;
            ||| state is Free2m
            ||| state is Owned2m
            ||| state is Allocated2m
            ||| state is Mapped2m
        },
    ensures
        #![trigger
            publish_staged_container_root_kernel_state_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.pg_arr.spec_index(page_index).view().view().state
        ]
        page_index_2m_valid(page_index),
{
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
    page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
    page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
    assert(page_index_2m_valid(container_head));
    assert(page_index_2m_valid(pcid_allocator_head));
    if page_index == container_head || page_index == pcid_allocator_head {
        return;
    }

    page_index_valid_imply_page_ptr_valid();
    page_index_roundtrip();
    let page_ptr = page_index2page_ptr(page_index);
    assert(!page_2m_all_ptrs(container_head).contains(page_ptr)) by {
        if page_2m_all_ptrs(container_head).contains(page_ptr) {
            reveal(page_2m_all_ptrs);
            page_2m_ptr_prefix_member_bounds(container_head, 512, page_ptr);
            assert(spec_page_index_merge_2m_valid(container_head, page_index));
            assert(page_2m_tail_indices(container_head).contains(page_index)) by { reveal(page_2m_tail_indices); };
            assert(post.pg_arr.spec_index(page_index).view().view().state is Merged2m) by { reveal(publish_staged_container_root_kernel_state_framing); };
        }
    };
    assert(!page_2m_all_ptrs(pcid_allocator_head).contains(page_ptr)) by {
        if page_2m_all_ptrs(pcid_allocator_head).contains(page_ptr) {
            reveal(page_2m_all_ptrs);
            page_2m_ptr_prefix_member_bounds(pcid_allocator_head, 512, page_ptr);
            assert(spec_page_index_merge_2m_valid(pcid_allocator_head, page_index));
            assert(page_2m_tail_indices(pcid_allocator_head).contains(page_index)) by { reveal(page_2m_tail_indices); };
            assert(post.pg_arr.spec_index(page_index).view().view().state is Merged2m) by { reveal(publish_staged_container_root_kernel_state_framing); };
        }
    };
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(page_ptr)) by {
        reveal(new_container_bootstrap_4k_pages); reveal(publish_staged_container_root_kernel_state_framing);
        broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(!funding_pages.to_set().contains(page_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); };
    assert(!new_container_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page,
    ).contains(page_ptr)) by {
        reveal(new_container_moved_pages); broadcast use vstd::set::lemma_set_union;
    };
    publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, page_index,
    );
    reveal(hugepage_2m_head_valid_wf);
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_hugepage_2m_head_valid_wf(
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
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        hugepage_2m_head_valid_wf(post.pg_arr),
{
    assert(hugepage_2m_wf(pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); };
    assert(hugepage_2m_head_valid_wf(pre.pg_arr)) by { reveal(hugepage_2m_wf); };
    broadcast use publish_staged_container_root_eof_hugepage_2m_head_valid;
    assert(hugepage_2m_head_valid_wf(post.pg_arr)) by { reveal(hugepage_2m_head_valid_wf); };
}

#[verifier::spinoff_prover]
pub broadcast proof fn publish_staged_container_root_eof_hugepage_2m_tail_forward(
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
    head_index: PageIndex,
    tail_index: PageIndex,
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
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        index_valid(NUM_PAGES, head_index),
        index_valid(NUM_PAGES, tail_index),
        page_index_2m_valid(head_index),
        {
            let state = post.pg_arr.spec_index(head_index).view().view().state;
            ||| state is Free2m
            ||| state is Owned2m
            ||| state is Allocated2m
            ||| state is Mapped2m
        },
        spec_page_index_merge_2m_valid(head_index, tail_index),
    ensures
        #![trigger
            publish_staged_container_root_kernel_state_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            spec_page_index_merge_2m_valid(head_index, tail_index)
        ]
        {
            &&& post.pg_arr.spec_index(tail_index).view().view().state is Merged2m
            &&& post.pg_arr.spec_index(tail_index).view().view().owning_container == post.pg_arr.spec_index(head_index).view().view().owning_container
        },
{
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
    assert(hugepage_2m_wf(pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); };
    assert(hugepage_2m_head_valid_wf(pre.pg_arr)) by { reveal(hugepage_2m_wf); };
    assert(hugepage_2m_tail_forward_wf(pre.pg_arr)) by { reveal(hugepage_2m_wf); };
    publish_staged_container_root_eof_hugepage_2m_head_valid(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, head_index,
    );
    page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
    page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
    if head_index == container_head {
        assert(page_2m_tail_indices(container_head).contains(tail_index)) by { reveal(page_2m_tail_indices); };
        reveal(publish_staged_container_root_kernel_state_framing);
        return;
    }
    if head_index == pcid_allocator_head {
        assert(page_2m_tail_indices(pcid_allocator_head).contains(tail_index)) by { reveal(page_2m_tail_indices); };
        reveal(publish_staged_container_root_kernel_state_framing);
        return;
    }

    distinct_2m_heads_have_disjoint_all_ptrs(head_index, container_head);
    distinct_2m_heads_have_disjoint_all_ptrs(head_index, pcid_allocator_head);
    page_2m_all_ptrs_contains_head(head_index);
    assert(head_index <= tail_index < head_index + 512) by { reveal(spec_page_index_merge_2m_valid); };
    page_2m_all_ptrs_contains_index(head_index, tail_index);

    let head_ptr = page_index2page_ptr(head_index);
    let tail_ptr = page_index2page_ptr(tail_index);
    assert(!page_2m_all_ptrs(container_head).contains(head_ptr)) by { reveal(Set::disjoint); };
    assert(!page_2m_all_ptrs(pcid_allocator_head).contains(head_ptr)) by { reveal(Set::disjoint); };
    assert(!page_2m_all_ptrs(container_head).contains(tail_ptr)) by { reveal(Set::disjoint); };
    assert(!page_2m_all_ptrs(pcid_allocator_head).contains(tail_ptr)) by { reveal(Set::disjoint); };

    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(head_ptr)) by {
        reveal(new_container_bootstrap_4k_pages); reveal(publish_staged_container_root_kernel_state_framing);
        broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(!funding_pages.to_set().contains(head_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); };
    assert(!new_container_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page,
    ).contains(head_ptr)) by {
        reveal(new_container_moved_pages); broadcast use vstd::set::lemma_set_union;
    };
    publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, head_index,
    );
    assert({
        &&& pre.pg_arr.spec_index(tail_index).view().view().state is Merged2m
        &&& pre.pg_arr.spec_index(tail_index).view().view().owning_container == pre.pg_arr.spec_index(head_index).view().view().owning_container
    }) by { reveal(hugepage_2m_tail_forward_wf); };

    assert(thread_staged_pages_4k_wf(pre.thr_mp, pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); reveal(thread_staged_pages_wf); };
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(tail_ptr)) by {
        if new_container_bootstrap_4k_pages(
            allocator_4k_page,
            allocator_2m_page,
            allocator_1g_page,
            scheduler_page,
            cpu_set_page,
            process_page,
            pagetable_page,
            l4_page,
        ).contains(tail_ptr) {
            assert(pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(tail_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); };
            reveal(thread_staged_pages_4k_wf);
        }
    };
    assert(!funding_pages.to_set().contains(tail_ptr)) by {
        if funding_pages.to_set().contains(tail_ptr) {
            assert(pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(tail_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); };
            reveal(thread_staged_pages_4k_wf);
        }
    };
    assert(!new_container_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page,
    ).contains(tail_ptr)) by {
        reveal(new_container_moved_pages); broadcast use vstd::set::lemma_set_union;
    };
    publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, tail_index,
    );
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_hugepage_2m_tail_forward_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        hugepage_2m_head_valid_wf(post.pg_arr),
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
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        hugepage_2m_tail_forward_wf(post.pg_arr),
{
    assert(hugepage_2m_wf(pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); };
    broadcast use publish_staged_container_root_eof_hugepage_2m_tail_forward;
    assert(hugepage_2m_tail_forward_wf(post.pg_arr)) by { reveal(hugepage_2m_head_valid_wf); reveal(hugepage_2m_tail_forward_wf); };
}

#[verifier::spinoff_prover]
pub broadcast proof fn publish_staged_container_root_eof_hugepage_2m_tail_backward(
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
    tail_index: PageIndex,
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
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        index_valid(NUM_PAGES, tail_index),
        post.pg_arr.spec_index(tail_index).view().view().state is Merged2m,
    ensures
        #![trigger
            publish_staged_container_root_kernel_state_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.pg_arr.spec_index(tail_index).view().view().state
        ]
        {
            let head_index = spec_page_index_truncate_2m(tail_index);
            let head_state = post.pg_arr.spec_index(head_index).view().view().state;
            ||| head_state is Free2m
            ||| head_state is Owned2m
            ||| head_state is Allocated2m
            ||| head_state is Mapped2m
        },
{
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
    let head_index = spec_page_index_truncate_2m(tail_index);
    page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
    page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
    if page_2m_tail_indices(container_head).contains(tail_index) {
        assert(head_index == container_head) by { reveal(page_2m_tail_indices); reveal(spec_page_index_truncate_2m); };
        reveal(publish_staged_container_root_kernel_state_framing);
        return;
    }
    if page_2m_tail_indices(pcid_allocator_head).contains(tail_index) {
        assert(head_index == pcid_allocator_head) by { reveal(page_2m_tail_indices); reveal(spec_page_index_truncate_2m); };
        reveal(publish_staged_container_root_kernel_state_framing);
        return;
    }

    page_index_valid_imply_page_ptr_valid();
    page_index_roundtrip();
    let tail_ptr = page_index2page_ptr(tail_index);
    assert(!page_2m_all_ptrs(container_head).contains(tail_ptr)) by {
        if page_2m_all_ptrs(container_head).contains(tail_ptr) {
            reveal(page_2m_all_ptrs);
            page_2m_ptr_prefix_member_bounds(container_head, 512, tail_ptr);
            if tail_index == container_head {
                assert(post.pg_arr.spec_index(tail_index).view().view().state is Allocated2m) by { reveal(publish_staged_container_root_kernel_state_framing); };
            } else {
                assert(page_2m_tail_indices(container_head).contains(tail_index)) by { reveal(page_2m_tail_indices); };
            }
        }
    };
    assert(!page_2m_all_ptrs(pcid_allocator_head).contains(tail_ptr)) by {
        if page_2m_all_ptrs(pcid_allocator_head).contains(tail_ptr) {
            reveal(page_2m_all_ptrs);
            page_2m_ptr_prefix_member_bounds(pcid_allocator_head, 512, tail_ptr);
            if tail_index == pcid_allocator_head {
                assert(post.pg_arr.spec_index(tail_index).view().view().state is Allocated2m) by { reveal(publish_staged_container_root_kernel_state_framing); };
            } else {
                assert(page_2m_tail_indices(pcid_allocator_head).contains(tail_index)) by { reveal(page_2m_tail_indices); };
            }
        }
    };
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(tail_ptr)) by {
        reveal(new_container_bootstrap_4k_pages); reveal(publish_staged_container_root_kernel_state_framing);
        broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(!funding_pages.to_set().contains(tail_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); };
    assert(!new_container_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page,
    ).contains(tail_ptr)) by {
        reveal(new_container_moved_pages); broadcast use vstd::set::lemma_set_union;
    };
    publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, tail_index,
    );
    assert(pre.pg_arr.spec_index(tail_index).view().view().state is Merged2m);
    assert(hugepage_2m_wf(pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); };
    assert(hugepage_2m_tail_backward_wf(pre.pg_arr)) by { reveal(hugepage_2m_wf); };
    assert({
        let head_state = pre.pg_arr.spec_index(head_index).view().view().state;
        ||| head_state is Free2m
        ||| head_state is Owned2m
        ||| head_state is Allocated2m
        ||| head_state is Mapped2m
    }) by { reveal(hugepage_2m_tail_backward_wf); };
    if head_index == container_head || head_index == pcid_allocator_head {
        reveal(publish_staged_container_root_kernel_state_framing);
        return;
    }

    assert(page_index_2m_valid(head_index)) by { reveal(page_index_2m_valid); reveal(index_valid); reveal(spec_page_index_truncate_2m); };
    distinct_2m_heads_have_disjoint_all_ptrs(head_index, container_head);
    distinct_2m_heads_have_disjoint_all_ptrs(head_index, pcid_allocator_head);
    page_2m_all_ptrs_contains_head(head_index);
    let head_ptr = page_index2page_ptr(head_index);
    assert(!page_2m_all_ptrs(container_head).contains(head_ptr)) by { reveal(Set::disjoint); };
    assert(!page_2m_all_ptrs(pcid_allocator_head).contains(head_ptr)) by { reveal(Set::disjoint); };
    assert(thread_staged_pages_4k_wf(pre.thr_mp, pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); reveal(thread_staged_pages_wf); };
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(head_ptr)) by {
        if new_container_bootstrap_4k_pages(
            allocator_4k_page,
            allocator_2m_page,
            allocator_1g_page,
            scheduler_page,
            cpu_set_page,
            process_page,
            pagetable_page,
            l4_page,
        ).contains(head_ptr) {
            assert(pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(head_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); };
            reveal(thread_staged_pages_4k_wf);
        }
    };
    assert(!funding_pages.to_set().contains(head_ptr)) by {
        if funding_pages.to_set().contains(head_ptr) {
            assert(pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(head_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); };
            reveal(thread_staged_pages_4k_wf);
        }
    };
    assert(!new_container_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page,
    ).contains(head_ptr)) by {
        reveal(new_container_moved_pages); broadcast use vstd::set::lemma_set_union;
    };
    publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, head_index,
    );
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_hugepage_2m_tail_backward_wf(
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
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        hugepage_2m_tail_backward_wf(post.pg_arr),
{
    assert(hugepage_2m_wf(pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); };
    broadcast use publish_staged_container_root_eof_hugepage_2m_tail_backward;
    assert(hugepage_2m_tail_backward_wf(post.pg_arr)) by { reveal(hugepage_2m_tail_backward_wf); };
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_hugepage_2m_wf(
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
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        hugepage_2m_wf(post.pg_arr),
{
    publish_staged_container_root_eof_hugepage_2m_head_valid_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_hugepage_2m_tail_forward_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_hugepage_2m_tail_backward_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(hugepage_2m_wf(post.pg_arr)) by { reveal(hugepage_2m_wf); };
}


}
