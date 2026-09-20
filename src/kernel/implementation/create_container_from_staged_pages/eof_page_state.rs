use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_existing_post_container_page_state_eq(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize, page_index: PageIndex,
)
    requires
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
        page_index != page_ptr2page_index(container_page),
        post.pg_arr.spec_index(page_index).view().view().state
            matches PageState::Allocated2m {
                state: Allocated2MPageState::AsContainer,
            },
    ensures
        post.pg_arr.spec_index(page_index).view().view().state == pre.pg_arr.spec_index(page_index).view().view().state,
{
    page_index_valid_imply_page_ptr_valid();
    page_index_roundtrip();
    let page_ptr = page_index2page_ptr(page_index);
    assert(!funding_pages.to_set().contains(page_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); };
    assert({
        &&& page_index != page_ptr2page_index(pcid_allocator_page)
        &&& !page_2m_tail_indices(page_ptr2page_index(container_page)).contains(page_index)
        &&& !page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).contains(page_index)
        &&& page_index != page_ptr2page_index(allocator_4k_page)
        &&& page_index != page_ptr2page_index(allocator_2m_page)
        &&& page_index != page_ptr2page_index(allocator_1g_page)
        &&& page_index != page_ptr2page_index(scheduler_page)
        &&& page_index != page_ptr2page_index(cpu_set_page)
        &&& page_index != page_ptr2page_index(process_page)
        &&& page_index != page_ptr2page_index(pagetable_page)
        &&& page_index != page_ptr2page_index(l4_page)
    }) by { reveal(publish_staged_container_root_kernel_state_framing); };
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(page_ptr)) by {
        reveal(new_container_bootstrap_4k_pages); broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(!page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(page_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(page_ptr) {
            reveal(page_2m_all_ptrs);
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(container_page), 512, page_ptr,);
            assert(page_2m_tail_indices(page_ptr2page_index(container_page)).contains(page_index)) by { reveal(page_2m_tail_indices); };
        }
    };
    assert(!page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(page_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(page_ptr) {
            reveal(page_2m_all_ptrs);
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(pcid_allocator_page), 512, page_ptr,);
            if page_index == page_ptr2page_index(pcid_allocator_page) {
                assert(post.pg_arr.spec_index(page_index).view().view().state == (PageState::Allocated2m {
                        state: Allocated2MPageState::AsPcidAllocator,
                    })) by { reveal(publish_staged_container_root_kernel_state_framing); };
            } else {
                assert(page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).contains(page_index)) by { reveal(page_2m_tail_indices); };
            }
        }
    };
    publish_staged_container_root_eof_not_in_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page, page_ptr,
    );
    publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, page_index,
    );
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_pre_container_page_in_map(pre: KernelK, page_index: PageIndex,)
    requires
        pre.inv(),
        index_valid(NUM_PAGES, page_index),
        pre.pg_arr.spec_index(page_index).view().view().state
            matches PageState::Allocated2m {
                state: Allocated2MPageState::AsContainer,
            },
    ensures
        pre.ctn_mp.dom().contains(page_index2page_ptr(page_index)),
{
    assert(container_pages_forward_wf(pre.pg_arr, pre.ctn_mp)) by {
        assert(container_pages_wf(pre.pg_arr, pre.ctn_mp)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); };
        reveal(container_pages_wf);
    };
    reveal(container_pages_forward_wf);
}

#[verifier::spinoff_prover]
pub broadcast proof fn publish_staged_container_root_eof_container_pages_forward_new(
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
        page_ptr_2m_valid(container_page),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        index_valid(NUM_PAGES, page_index),
        page_index == page_ptr2page_index(container_page),
        post.pg_arr.spec_index(page_index).view().view().state
            matches PageState::Allocated2m {
                state: Allocated2MPageState::AsContainer,
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
        post.ctn_mp.dom().contains(page_index2page_ptr(page_index)),
{
    assert(page_index2page_ptr(page_index) == container_page) by { page_ptr_roundtrip(); };
    assert(post.ctn_mp.dom() == pre.ctn_mp.dom().insert(container_page)) by { reveal(publish_staged_container_root_kernel_state_framing); };
    broadcast use vstd::set::lemma_set_insert_same;
}

#[verifier::spinoff_prover]
pub broadcast proof fn publish_staged_container_root_eof_container_pages_forward_existing(
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
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        index_valid(NUM_PAGES, page_index),
        page_index != page_ptr2page_index(container_page),
        post.pg_arr.spec_index(page_index).view().view().state
            matches PageState::Allocated2m {
                state: Allocated2MPageState::AsContainer,
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
        post.ctn_mp.dom().contains(page_index2page_ptr(page_index)),
{
    publish_staged_container_root_eof_existing_post_container_page_state_eq(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, page_index,
    );
    publish_staged_container_root_eof_pre_container_page_in_map(pre, page_index,);
    assert(post.ctn_mp.dom() == pre.ctn_mp.dom().insert(container_page)) by { reveal(publish_staged_container_root_kernel_state_framing); };
    broadcast use vstd::set::lemma_set_insert_same;
    broadcast use vstd::set::lemma_set_insert_different;
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_not_in_moved_pages(
    container_page: PagePtr, pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr,
    allocator_1g_page: PagePtr, scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr,
    l4_page: PagePtr, page_ptr: PagePtr,
)
    requires
        !page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(page_ptr),
        !page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(page_ptr),
        !new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(page_ptr),
    ensures
        !new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(page_ptr),
{
    reveal(new_container_moved_pages);
    broadcast use vstd::set::lemma_set_union;
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize, page_index: PageIndex,
)
    requires
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
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
        !funding_pages.to_set().contains(page_index2page_ptr(page_index)),
        !new_container_moved_pages(
            container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
            process_page, pagetable_page, l4_page,
        ).contains(page_index2page_ptr(page_index)),
    ensures
        post.pg_arr.spec_index(page_index).view().view().state == pre.pg_arr.spec_index(page_index).view().view().state,
        post.pg_arr.spec_index(page_index).view().view().owning_container == pre.pg_arr.spec_index(page_index).view().view().owning_container,
        post.pg_arr.spec_index(page_index).view().view().free_list_node_storage == pre.pg_arr.spec_index(page_index).view().view().free_list_node_storage,
{
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
    let allocator_4k_index = page_ptr2page_index(allocator_4k_page);
    let allocator_2m_index = page_ptr2page_index(allocator_2m_page);
    let allocator_1g_index = page_ptr2page_index(allocator_1g_page);
    let scheduler_index = page_ptr2page_index(scheduler_page);
    let cpu_set_index = page_ptr2page_index(cpu_set_page);
    let process_index = page_ptr2page_index(process_page);
    let pagetable_index = page_ptr2page_index(pagetable_page);
    let l4_index = page_ptr2page_index(l4_page);
    let funding_indices = funding_pages.map_values(
        |page_ptr: PagePtr| page_ptr2page_index(page_ptr),
    ).to_set();
    page_index_valid_imply_page_ptr_valid();
    page_index_roundtrip();
    page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
    page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
    assert(staged_4k_page_chain(post.pg_arr, funding_pages)) by { reveal(publish_staged_container_root_kernel_state_framing); };
    staged_4k_page_chain_page_ptrs_valid(post.pg_arr, funding_pages);
    page_ptr_seq_indices_excludes_page(funding_pages, page_index2page_ptr(page_index),);
    assert(!funding_indices.contains(page_index));
    assert(!page_2m_all_ptrs(container_head).contains(page_index2page_ptr(page_index))) by { reveal(new_container_moved_pages); broadcast use vstd::set::lemma_set_union; };
    assert(!page_2m_all_ptrs(pcid_allocator_head).contains(page_index2page_ptr(page_index))) by { reveal(new_container_moved_pages); broadcast use vstd::set::lemma_set_union; };
    assert(!page_2m_tail_indices(container_head).contains(page_index)) by {
        if page_2m_tail_indices(container_head).contains(page_index) {
            assert(container_head <= page_index < container_head + 512) by { reveal(page_2m_tail_indices); };
            page_2m_all_ptrs_contains_index(container_head, page_index);
        }
    };
    assert(!page_2m_tail_indices(pcid_allocator_head).contains(page_index)) by {
        if page_2m_tail_indices(pcid_allocator_head).contains(page_index) {
            assert(pcid_allocator_head <= page_index < pcid_allocator_head + 512) by { reveal(page_2m_tail_indices); };
            page_2m_all_ptrs_contains_index(pcid_allocator_head, page_index);
        }
    };
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(page_index2page_ptr(page_index))) by {
        reveal(new_container_moved_pages); broadcast use vstd::set::lemma_set_union;
    };
    assert({
        &&& page_index != container_head
        &&& page_index != pcid_allocator_head
        &&& page_index != allocator_4k_index
        &&& page_index != allocator_2m_index
        &&& page_index != allocator_1g_index
        &&& page_index != scheduler_index
        &&& page_index != cpu_set_index
        &&& page_index != process_index
        &&& page_index != pagetable_index
        &&& page_index != l4_index
    }) by { page_ptr_roundtrip(); page_2m_all_ptrs_contains_head(container_head); page_2m_all_ptrs_contains_head(pcid_allocator_head); reveal(new_container_bootstrap_4k_pages); };
    assert(!set![
        container_head, pcid_allocator_head, allocator_4k_index, allocator_2m_index, allocator_1g_index, scheduler_index, cpu_set_index,
        process_index, pagetable_index, l4_index,
    ].contains(page_index)) by { broadcast use vstd::set::lemma_set_insert_different; };
    reveal(publish_staged_container_root_kernel_state_framing);
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_existing_container_page_not_staged_4k(
    pre: KernelK, current_thread_ptr: RwLockThreadPtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, container_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
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
        pre.pg_arr.spec_index(page_ptr2page_index(container_ptr)).view().view().state matches PageState::Allocated2m {
                state: Allocated2MPageState::AsContainer,
            },
    ensures
        !funding_pages.to_set().contains(container_ptr),
        !new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(container_ptr),
{
    assert(thread_staged_pages_4k_wf(pre.thr_mp, pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); reveal(thread_staged_pages_wf); };
    assert(!funding_pages.to_set().contains(container_ptr)) by {
        if funding_pages.to_set().contains(container_ptr) {
            assert(pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(container_ptr));
            assert(pre.pg_arr.spec_index(page_ptr2page_index(container_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })) by { reveal(thread_staged_pages_4k_wf); };
        }
    };
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(container_ptr)) by {
        if new_container_bootstrap_4k_pages(
            allocator_4k_page,
            allocator_2m_page,
            allocator_1g_page,
            scheduler_page,
            cpu_set_page,
            process_page,
            pagetable_page,
            l4_page,
        ).contains(container_ptr) {
            assert(pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(container_ptr));
            assert(pre.pg_arr.spec_index(page_ptr2page_index(container_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })) by { reveal(thread_staged_pages_4k_wf); };
        }
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_existing_container_page_not_staged_2m(
    pre: KernelK, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr, pcid_allocator_page: PagePtr,
    container_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        page_ptr_2m_valid(container_ptr),
        pre.thr_mp.dom().contains(current_thread_ptr),
        forall|page_ptr: PagePtr|
            #![trigger pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr)]
            pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr) <==> page_ptr == container_page || page_ptr == pcid_allocator_page,
        pre.pg_arr.spec_index(page_ptr2page_index(container_ptr)).view().view().state matches PageState::Allocated2m {
                state: Allocated2MPageState::AsContainer,
            },
        container_ptr != container_page,
    ensures
        !page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(container_ptr),
        !page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(container_ptr),
{
    assert(thread_staged_pages_2m_wf(pre.thr_mp, pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); reveal(thread_staged_pages_wf); };
    assert(hugepage_2m_wf(pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); };
    assert(hugepage_2m_tail_forward_wf(pre.pg_arr)) by { reveal(hugepage_2m_wf); };
    page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
    page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
    assert(pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(container_page));
    assert(pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(pcid_allocator_page));
    assert(pre.pg_arr.spec_index(page_ptr2page_index(container_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr })) by { reveal(thread_staged_pages_2m_wf); reveal(thread_staged_pages_2m_backward_wf); };
    assert(pre.pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr })) by { reveal(thread_staged_pages_2m_wf); reveal(thread_staged_pages_2m_backward_wf); };
    page_ptr_2m_valid_imply_page_index_2m_valid(container_ptr);
    page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
    page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
    assert(!page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(container_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(container_ptr) {
            reveal(page_2m_all_ptrs);
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(container_page), 512, container_ptr,);
            if page_ptr2page_index(container_ptr) != page_ptr2page_index(container_page) {
                assert(pre.pg_arr.spec_index(page_ptr2page_index(container_ptr)).view().view().state is Merged2m) by { reveal(hugepage_2m_wf); };
            }
        }
    };
    assert(!page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(container_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(container_ptr) {
            reveal(page_2m_all_ptrs);
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(pcid_allocator_page), 512, container_ptr,);
            if page_ptr2page_index(container_ptr) != page_ptr2page_index(pcid_allocator_page) {
                assert(pre.pg_arr.spec_index(page_ptr2page_index(container_ptr)).view().view().state is Merged2m) by { reveal(hugepage_2m_wf); };
            }
        }
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_existing_container_page_state_eq(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize, container_ptr: RwLockContainerPtr,
)
    requires
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
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
        page_ptr_2m_valid(container_ptr),
        !funding_pages.to_set().contains(container_ptr),
        !new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(container_ptr),
        !page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(container_ptr),
        !page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(container_ptr),
    ensures
        post.pg_arr.spec_index(page_ptr2page_index(container_ptr)).view().view().state == pre.pg_arr.spec_index(page_ptr2page_index(container_ptr)).view().view().state,
{
    publish_staged_container_root_eof_not_in_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page, container_ptr,
    );
    page_ptr_2m_valid_imply_page_index_2m_valid(container_ptr);
    let container_index = page_ptr2page_index(container_ptr);
    assert(index_valid(NUM_PAGES, container_index));
    assert(page_index2page_ptr(container_index) == container_ptr) by { page_ptr_roundtrip(); };
    assert(!funding_pages.to_set().contains(page_index2page_ptr(container_index),));
    assert(!new_container_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page,
    ).contains(page_index2page_ptr(container_index)));
    publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, container_index,
    );
}


}
