use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
pub(super) proof fn publish_staged_container_root_eof_not_in_moved_pages(
    container_page: PagePtr, pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, pg_ptr: PagePtr,
)
    requires
        !page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(pg_ptr),
        !page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(pg_ptr),
        !new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(pg_ptr),
    ensures
        !new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(pg_ptr),
{ reveal(new_container_moved_pages); }

pub(super) proof fn publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize, pg_idx: PageIndex,
)
    requires
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
        !funding_pages.to_set().contains(page_index2page_ptr(pg_idx)),
        !new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).contains(page_index2page_ptr(pg_idx)),
    ensures
        post.pg_arr.spec_index(pg_idx).view().view().state == pre.pg_arr.spec_index(pg_idx).view().view().state,
        post.pg_arr.spec_index(pg_idx).view().view().owning_container == pre.pg_arr.spec_index(pg_idx).view().view().owning_container,
        post.pg_arr.spec_index(pg_idx).view().view().free_list_node_storage == pre.pg_arr.spec_index(pg_idx).view().view().free_list_node_storage,
        post.pg_arr.spec_index(pg_idx).view().view().is_io_page == pre.pg_arr.spec_index(pg_idx).view().view().is_io_page,
{
    hide(Seq::contains); reveal(publish_staged_container_root_eof_transition_framing);
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
    let funding_indices = funding_pages.map_values(|pg_ptr: PagePtr| page_ptr2page_index(pg_ptr)).to_set();
    page_index_valid_imply_page_ptr_valid(); page_index_roundtrip();
    page_ptr_2m_valid_imply_page_index_2m_valid(container_page); page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
    assert(!funding_indices.contains(pg_idx)) by { reveal(publish_staged_container_root_eof_preconditions); page_ptr_seq_indices_excludes_page(funding_pages, page_index2page_ptr(pg_idx)); };
    assert(!page_2m_all_ptrs(container_head).contains(page_index2page_ptr(pg_idx))) by { reveal(new_container_moved_pages); };
    assert(!page_2m_all_ptrs(pcid_allocator_head).contains(page_index2page_ptr(pg_idx))) by { reveal(new_container_moved_pages); };
    assert(!page_2m_tail_indices(container_head).contains(pg_idx)) by {
        if page_2m_tail_indices(container_head).contains(pg_idx) { page_2m_all_ptrs_contains_index(container_head, pg_idx); }
    };
    assert(!page_2m_tail_indices(pcid_allocator_head).contains(pg_idx)) by {
        if page_2m_tail_indices(pcid_allocator_head).contains(pg_idx) { page_2m_all_ptrs_contains_index(pcid_allocator_head, pg_idx); }
    };
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(page_index2page_ptr(pg_idx))) by {
        reveal(new_container_moved_pages);
    };
    assert({
        &&& pg_idx != container_head
        &&& pg_idx != pcid_allocator_head
        &&& pg_idx != allocator_4k_index
        &&& pg_idx != allocator_2m_index
        &&& pg_idx != allocator_1g_index
        &&& pg_idx != scheduler_index
        &&& pg_idx != cpu_set_index
        &&& pg_idx != process_index
        &&& pg_idx != pagetable_index
        &&& pg_idx != l4_index
    }) by { page_ptr_roundtrip(); page_2m_all_ptrs_contains_head(container_head); page_2m_all_ptrs_contains_head(pcid_allocator_head); reveal(new_container_bootstrap_4k_pages); };
}

#[verifier::spinoff_prover]
pub(super) broadcast proof fn publish_staged_container_root_eof_unmodified_object_page_state_eq(
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
        {
            let pre_state = pre.pg_arr.spec_index(pg_idx).view().view().state;
            let post_state = post.pg_arr.spec_index(pg_idx).view().view().state;
            ||| (pre_state matches PageState::Allocated4k { state: Allocated4KPageState::AsThread })
            ||| (post_state matches PageState::Allocated4k { state: Allocated4KPageState::AsThread })
            ||| (pre_state matches PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint })
            ||| (post_state matches PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint })
            ||| (pre_state == PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: IOMMU_TYPE } })
            ||| (post_state == PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: IOMMU_TYPE } })
            ||| (pre_state is Allocated4k && pre_state->Allocated4k_state is PageTable && pre_state->Allocated4k_state->PageTable_table_type == IOMMU_TYPE)
            ||| (post_state is Allocated4k && post_state->Allocated4k_state is PageTable && post_state->Allocated4k_state->PageTable_table_type == IOMMU_TYPE)
            ||| (pre_state is Mapped4k)
            ||| (post_state is Mapped4k)
            ||| (pre_state is Unavailable)
            ||| (post_state is Unavailable)
            ||| (pre_state is Mapped2m)
            ||| (post_state is Mapped2m)
            ||| (pre_state is Free2m)
            ||| (post_state is Free2m)
            ||| (pre_state is Free4k)
            ||| (!funding_pages.to_set().contains(page_index2page_ptr(pg_idx)) && (post_state is Free4k))
            ||| (pre_state is Owned1g)
            ||| (post_state is Owned1g)
            ||| (pre_state is Free1g)
            ||| (post_state is Free1g)
            ||| (pre_state is Mapped1g)
            ||| (post_state is Mapped1g)
            ||| (pre_state is Merged1g)
            ||| (post_state is Merged1g)
            ||| (post_state is Owned4k)
            ||| (pre_state is Owned4k && pre_state->Owned4k_thread_ptr != current_thrd_ptr)
            ||| (pg_idx != page_ptr2page_index(container_page) && ((pre_state matches PageState::Allocated2m { state: Allocated2MPageState::AsContainer })
                || (post_state matches PageState::Allocated2m { state: Allocated2MPageState::AsContainer })))
            ||| (pg_idx != page_ptr2page_index(process_page) && ((pre_state matches PageState::Allocated4k { state: Allocated4KPageState::AsProcess })
                || (post_state matches PageState::Allocated4k { state: Allocated4KPageState::AsProcess })))
            ||| (pg_idx != page_ptr2page_index(pagetable_page) && ((pre_state matches PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { .. } })
                || (post_state matches PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { .. } })))
            ||| (pg_idx != page_ptr2page_index(l4_page) && ((pre_state matches PageState::Allocated4k { state: Allocated4KPageState::PageTable { .. } })
                || (post_state matches PageState::Allocated4k { state: Allocated4KPageState::PageTable { .. } })))
            ||| (pg_idx != page_ptr2page_index(scheduler_page) && ((pre_state matches PageState::Allocated4k { state: Allocated4KPageState::AsScheduler })
                || (post_state matches PageState::Allocated4k { state: Allocated4KPageState::AsScheduler })))
            ||| (pg_idx != page_ptr2page_index(cpu_set_page) && ((pre_state matches PageState::Allocated4k { state: Allocated4KPageState::AsCpuSet })
                || (post_state matches PageState::Allocated4k { state: Allocated4KPageState::AsCpuSet })))
            ||| (pg_idx != page_ptr2page_index(allocator_4k_page) && ((pre_state matches PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator })
                || (post_state matches PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator })))
            ||| (pg_idx != page_ptr2page_index(allocator_2m_page) && ((pre_state matches PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator })
                || (post_state matches PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator })))
            ||| (pg_idx != page_ptr2page_index(allocator_1g_page) && ((pre_state matches PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator })
                || (post_state matches PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator })))
            ||| (pg_idx != page_ptr2page_index(pcid_allocator_page) && ((pre_state matches PageState::Allocated2m { state: Allocated2MPageState::AsPcidAllocator })
                || (post_state matches PageState::Allocated2m { state: Allocated2MPageState::AsPcidAllocator })))
        },
    ensures
        #![trigger
            publish_staged_container_root_eof_transition_framing(
                pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.pg_arr.spec_index(pg_idx).view().view().state
        ]
        #![trigger
            publish_staged_container_root_eof_transition_framing(
                pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            pre.pg_arr.spec_index(pg_idx).view().view().state
        ]
        {
            &&& post.pg_arr.spec_index(pg_idx).view().view().state == pre.pg_arr.spec_index(pg_idx).view().view().state
            &&& post.pg_arr.spec_index(pg_idx).view().view().owning_container == pre.pg_arr.spec_index(pg_idx).view().view().owning_container
            &&& post.pg_arr.spec_index(pg_idx).view().view().free_list_node_storage == pre.pg_arr.spec_index(pg_idx).view().view().free_list_node_storage
            &&& post.pg_arr.spec_index(pg_idx).view().view().is_io_page == pre.pg_arr.spec_index(pg_idx).view().view().is_io_page
        },
{
    hide(Seq::contains); reveal(publish_staged_container_root_eof_transition_framing); reveal(publish_staged_container_root_eof_preconditions);
    let pg_ptr = page_index2page_ptr(pg_idx);
    assert(!funding_pages.to_set().contains(pg_ptr)) by { reveal(thread_staged_4k_pages_wf); };
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(pg_ptr)) by {
        reveal(Seq::contains); reveal(thread_staged_4k_pages_wf); reveal(new_container_bootstrap_4k_pages);
    };
    assert(pg_ptr != container_page) by { if pg_ptr == container_page { } };
    assert(pg_ptr != pcid_allocator_page) by { if pg_ptr == pcid_allocator_page { } };
    assert(!page_2m_tail_indices(page_ptr2page_index(container_page)).contains(pg_idx)) by {
        if page_2m_tail_indices(page_ptr2page_index(container_page)).contains(pg_idx) {
            assert(pre.pg_arr.spec_index(pg_idx).view().view().state is Merged2m) by { reveal(hugepage_2m_wf); };
        }
    };
    assert(!page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).contains(pg_idx)) by {
        if page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).contains(pg_idx) {
            assert(pre.pg_arr.spec_index(pg_idx).view().view().state is Merged2m) by { reveal(hugepage_2m_wf); };
        }
    };
    assert(!page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(pg_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(pg_ptr) {
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(container_page), 512, pg_ptr,);
            assert(pg_idx != page_ptr2page_index(container_page)) by { page_ptr2page_index_injective(); };
        }
    };
    assert(!page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(pg_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(pg_ptr) {
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(pcid_allocator_page), 512, pg_ptr,);
            assert(pg_idx != page_ptr2page_index(pcid_allocator_page)) by { page_ptr2page_index_injective(); };
        }
    };
    assert(!new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).contains(pg_ptr)) by { reveal(new_container_moved_pages); };
    publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, pg_idx,
    );
}

pub(super) proof fn publish_staged_container_root_eof_existing_container_page_not_staged_4k(
    pre: KernelK, current_thrd_ptr: RwLockThreadPtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, ctn_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(current_thrd_ptr),
        forall|pg_ptr: PagePtr|
            #![trigger pre.thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_cache_4k.view().contains(pg_ptr)]
            #![trigger funding_pages.to_set().contains(pg_ptr)]
            #![trigger new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).contains(pg_ptr)]
            pre.thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_cache_4k.view().contains(pg_ptr) <==> new_container_bootstrap_4k_pages(
                allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
            ).contains(pg_ptr) || funding_pages.to_set().contains(pg_ptr) || pg_ptr == thread_page,
        pre.pg_arr.spec_index(page_ptr2page_index(ctn_ptr)).view().view().state matches PageState::Allocated2m { state: Allocated2MPageState::AsContainer },
    ensures
        !funding_pages.to_set().contains(ctn_ptr),
        !new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(ctn_ptr),
{
    assert(!funding_pages.to_set().contains(ctn_ptr)) by {
        if funding_pages.to_set().contains(ctn_ptr) {
            assert(pre.pg_arr.spec_index(page_ptr2page_index(ctn_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr })) by { reveal(thread_staged_4k_pages_wf); };
        }
    };
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(ctn_ptr)) by {
        if new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).contains(ctn_ptr) {
            assert(pre.pg_arr.spec_index(page_ptr2page_index(ctn_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr })) by { reveal(thread_staged_4k_pages_wf); };
        }
    };
}

pub(super) proof fn publish_staged_container_root_eof_existing_container_page_not_staged_2m(pre: KernelK, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr, pcid_allocator_page: PagePtr, ctn_ptr: RwLockContainerPtr)
    requires
        pre.inv(),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        page_ptr_2m_valid(ctn_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(container_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(ctn_ptr)).view().view().state matches PageState::Allocated2m { state: Allocated2MPageState::AsContainer },
        ctn_ptr != container_page,
    ensures
        !page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(ctn_ptr),
        !page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(ctn_ptr),
{
    page_ptr_2m_valid_imply_page_index_2m_valid(ctn_ptr);
    page_ptr_2m_valid_imply_page_index_2m_valid(container_page); page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
    assert(!page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(ctn_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(ctn_ptr) {
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(container_page), 512, ctn_ptr,);
            if page_ptr2page_index(ctn_ptr) != page_ptr2page_index(container_page) {
                assert(pre.pg_arr.spec_index(page_ptr2page_index(ctn_ptr)).view().view().state is Merged2m) by { reveal(hugepage_2m_wf); };
            }
        }
    };
    assert(!page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(ctn_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(ctn_ptr) {
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(pcid_allocator_page), 512, ctn_ptr,);
            if page_ptr2page_index(ctn_ptr) != page_ptr2page_index(pcid_allocator_page) {
                assert(pre.pg_arr.spec_index(page_ptr2page_index(ctn_ptr)).view().view().state is Merged2m) by { reveal(hugepage_2m_wf); };
            }
        }
    };
}

pub(super) proof fn publish_staged_container_root_eof_existing_container_page_state_eq(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize, ctn_ptr: RwLockContainerPtr,
)
    requires
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
        page_ptr_2m_valid(ctn_ptr),
        !funding_pages.to_set().contains(ctn_ptr),
        !new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(ctn_ptr),
        !page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(ctn_ptr),
        !page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(ctn_ptr),
    ensures
        post.pg_arr.spec_index(page_ptr2page_index(ctn_ptr)).view().view().state == pre.pg_arr.spec_index(page_ptr2page_index(ctn_ptr)).view().view().state,
{
    publish_staged_container_root_eof_not_in_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, ctn_ptr);
    let container_index = page_ptr2page_index(ctn_ptr);
    assert(page_index2page_ptr(container_index) == ctn_ptr);
    publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, container_index,
    );
}

pub(super) proof fn publish_staged_container_root_eof_pre_container_page_in_map(pre: KernelK, pg_idx: PageIndex,)
    requires
        pre.inv(),
        index_valid(NUM_PAGES, pg_idx),
        pre.pg_arr.spec_index(pg_idx).view().view().state matches PageState::Allocated2m { state: Allocated2MPageState::AsContainer },
    ensures
        pre.ctn_mp.dom().contains(page_index2page_ptr(pg_idx)),
{ assert(container_pages_forward_wf(pre.ctn_mp, pre.pg_arr)) by { reveal(container_pages_wf); }; }

pub(super) proof fn publish_staged_container_root_eof_existing_post_container_page_state_eq(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize, pg_idx: PageIndex,
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
        pg_idx != page_ptr2page_index(container_page),
        post.pg_arr.spec_index(pg_idx).view().view().state matches PageState::Allocated2m { state: Allocated2MPageState::AsContainer },
    ensures
        post.pg_arr.spec_index(pg_idx).view().view().state == pre.pg_arr.spec_index(pg_idx).view().view().state,
{
    hide(Seq::contains); reveal(publish_staged_container_root_eof_transition_framing); page_index_valid_imply_page_ptr_valid();
    let pg_ptr = page_index2page_ptr(pg_idx);
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(pg_ptr)) by { reveal(Seq::contains); reveal(new_container_bootstrap_4k_pages); };
    assert(!page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(pg_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(pg_ptr) { page_2m_ptr_prefix_member_bounds(page_ptr2page_index(container_page), 512, pg_ptr,); }
    };
    assert(!page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(pg_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(pg_ptr) {
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(pcid_allocator_page), 512, pg_ptr,);
            if pg_idx == page_ptr2page_index(pcid_allocator_page) { } else { }
        }
    };
    publish_staged_container_root_eof_not_in_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, pg_ptr);
    publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, pg_idx,
    );
}

pub(super) broadcast proof fn publish_staged_container_root_eof_container_pages_forward_new(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize, process_quota_4k: usize, pg_idx: PageIndex,
)
    requires
        page_ptr_2m_valid(container_page),
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        index_valid(NUM_PAGES, pg_idx),
        pg_idx == page_ptr2page_index(container_page),
        post.pg_arr.spec_index(pg_idx).view().view().state matches PageState::Allocated2m { state: Allocated2MPageState::AsContainer },
    ensures
        #![trigger
            publish_staged_container_root_eof_transition_framing(
                pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.pg_arr.spec_index(pg_idx).view().view().state
        ]
        post.ctn_mp.dom().contains(page_index2page_ptr(pg_idx)),
{
    assert(page_index2page_ptr(pg_idx) == container_page) by { page_ptr_roundtrip(); };
    assert(post.ctn_mp.dom().contains(container_page)) by { reveal(publish_staged_container_root_eof_transition_framing); };
}

pub(super) broadcast proof fn publish_staged_container_root_eof_container_pages_forward_existing(
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
        pg_idx != page_ptr2page_index(container_page),
        post.pg_arr.spec_index(pg_idx).view().view().state matches PageState::Allocated2m { state: Allocated2MPageState::AsContainer },
    ensures
        #![trigger
            publish_staged_container_root_eof_transition_framing(
                pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.pg_arr.spec_index(pg_idx).view().view().state
        ]
        post.ctn_mp.dom().contains(page_index2page_ptr(pg_idx)),
{
    reveal(publish_staged_container_root_eof_transition_framing);
    publish_staged_container_root_eof_existing_post_container_page_state_eq(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, pg_idx,
    );
    publish_staged_container_root_eof_pre_container_page_in_map(pre, pg_idx,);
}

pub(super) broadcast proof fn publish_staged_container_root_eof_container_pages_backward(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize, process_quota_4k: usize, ctn_ptr: RwLockContainerPtr,
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
        post.ctn_mp.dom().contains(ctn_ptr),
    ensures
        #![trigger
            publish_staged_container_root_eof_transition_framing(
                pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.ctn_mp.dom().contains(ctn_ptr)
        ]
        page_ptr_2m_valid(ctn_ptr) && (post.pg_arr.spec_index(page_ptr2page_index(ctn_ptr)).view().view().state matches PageState::Allocated2m { state: Allocated2MPageState::AsContainer }),
{
    reveal(publish_staged_container_root_eof_transition_framing); reveal(publish_staged_container_root_eof_preconditions);
    if ctn_ptr == container_page { } else {
        assert(container_pages_backward_wf(pre.ctn_mp, pre.pg_arr)) by { reveal(container_pages_wf); };
        publish_staged_container_root_eof_existing_container_page_not_staged_4k(pre, current_thrd_ptr, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages, ctn_ptr);
        publish_staged_container_root_eof_existing_container_page_not_staged_2m(pre, current_thrd_ptr, container_page, pcid_allocator_page, ctn_ptr,);
        publish_staged_container_root_eof_existing_container_page_state_eq(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k, ctn_ptr,
        );
    }
}

pub(super) broadcast proof fn publish_staged_container_root_eof_existing_pagetable_closure_page_backward(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize, process_quota_4k: usize, pt_ptr: RwLockPageTableRoot, pt_pg_ptr: PagePtr,
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
        post.pt_mp.dom().contains(pt_ptr),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pt_ptr).page_closure().contains(pt_pg_ptr),
        pt_ptr != pagetable_page,
    ensures
        #![trigger
            publish_staged_container_root_eof_transition_framing(
                pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            whole_pagetable(post.pt_mp, post.pt_lower.view(), pt_ptr).page_closure().contains(pt_pg_ptr)
        ]
        {
            &&& page_ptr_valid(pt_pg_ptr)
            &&& post.pg_arr.spec_index(page_ptr2page_index(pt_pg_ptr)).view().view().state is Allocated4k
            &&& post.pg_arr.spec_index(page_ptr2page_index(pt_pg_ptr)).view().view().state->Allocated4k_state is PageTable
            &&& post.pg_arr.spec_index(page_ptr2page_index(pt_pg_ptr)).view().view().state->Allocated4k_state->PageTable_pagetable_root == pt_ptr
            &&& post.pg_arr.spec_index(page_ptr2page_index(pt_pg_ptr)).view().view().state->Allocated4k_state->PageTable_table_type == PT_TYPE
        },
{
    hide(Seq::contains); reveal(publish_staged_container_root_eof_transition_framing); reveal(publish_staged_container_root_eof_preconditions);
    assert(pagetable_closure_page_backward_wf(pre.pt_mp, pre.pt_lower.view(), pre.pg_arr)) by { reveal(pagetable_pages_wf); };
    assert(page_ptr2page_index(pt_pg_ptr) != page_ptr2page_index(l4_page)) by {
        if page_ptr2page_index(pt_pg_ptr) == page_ptr2page_index(l4_page) {
            assert(pt_pg_ptr == l4_page) by { page_ptr2page_index_injective(); };
            assert(pre.thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_cache_4k.view().contains(l4_page)) by { reveal(new_container_bootstrap_4k_pages); };
            reveal(thread_staged_4k_pages_wf);
        }
    };
    page_ptr_valid_imply_page_index_valid();
    publish_staged_container_root_eof_unmodified_object_page_state_eq(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, page_ptr2page_index(pt_pg_ptr),
    );
}

pub(super) broadcast proof fn publish_staged_container_root_eof_hugepage_2m_head_valid(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize, process_quota_4k: usize, pg_idx: PageIndex,
)
    requires
        hugepage_2m_head_aligned_wf(pre.pg_arr),
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
        {
            let state = post.pg_arr.spec_index(pg_idx).view().view().state;
            ||| state is Free2m
            ||| state is Owned2m
            ||| state is Allocated2m
            ||| state is Mapped2m
        },
    ensures
        #![trigger
            publish_staged_container_root_eof_transition_framing(
                pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.pg_arr.spec_index(pg_idx).view().view().state
        ]
        page_index_2m_valid(pg_idx),
{
    hide(Seq::contains);
    reveal(publish_staged_container_root_eof_transition_framing);
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
    page_ptr_2m_valid_imply_page_index_2m_valid(container_page); page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
    if pg_idx == container_head || pg_idx == pcid_allocator_head { return; }
    page_index_valid_imply_page_ptr_valid(); page_index_roundtrip();
    let pg_ptr = page_index2page_ptr(pg_idx);
    assert(!page_2m_all_ptrs(container_head).contains(pg_ptr)) by { if page_2m_all_ptrs(container_head).contains(pg_ptr) { page_2m_ptr_prefix_member_bounds(container_head, 512, pg_ptr); } };
    assert(!page_2m_all_ptrs(pcid_allocator_head).contains(pg_ptr)) by {
        if page_2m_all_ptrs(pcid_allocator_head).contains(pg_ptr) { page_2m_ptr_prefix_member_bounds(pcid_allocator_head, 512, pg_ptr); }
    };
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(pg_ptr)) by {
        reveal(Seq::contains); reveal(new_container_bootstrap_4k_pages);
    };
    assert(!new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).contains(pg_ptr)) by { reveal(new_container_moved_pages); };
    publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, pg_idx,
    );
}

#[verifier::spinoff_prover]
pub(super) broadcast proof fn publish_staged_container_root_eof_hugepage_2m_tail_forward(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize, process_quota_4k: usize, head_index: PageIndex, tail_index: PageIndex,
)
    requires
        pre.memory_management_inv(),
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
            publish_staged_container_root_eof_transition_framing(
                pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page,
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
    hide(Seq::contains);
    reveal(publish_staged_container_root_eof_transition_framing); reveal(publish_staged_container_root_eof_preconditions);
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
    assert(hugepage_2m_head_aligned_wf(pre.pg_arr)) by { reveal(hugepage_2m_wf); };
    assert(hugepage_2m_tail_forward_wf(pre.pg_arr)) by { reveal(hugepage_2m_wf); };
    publish_staged_container_root_eof_hugepage_2m_head_valid(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, head_index,
    );
    page_ptr_2m_valid_imply_page_index_2m_valid(container_page); page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
    if head_index == container_head {
        assert(page_2m_tail_indices(container_head).contains(tail_index)) by { vstd::set_lib::range_set_properties((container_head + 1) as usize, (container_head + 512) as usize); };
        return;
    }
    if head_index == pcid_allocator_head {
        assert(page_2m_tail_indices(pcid_allocator_head).contains(tail_index)) by { vstd::set_lib::range_set_properties((pcid_allocator_head + 1) as usize, (pcid_allocator_head + 512) as usize); };
        return;
    }
    distinct_2m_heads_have_disjoint_all_ptrs(head_index, container_head); distinct_2m_heads_have_disjoint_all_ptrs(head_index, pcid_allocator_head);
    page_2m_all_ptrs_contains_head(head_index); page_2m_all_ptrs_contains_index(head_index, tail_index);
    let head_ptr = page_index2page_ptr(head_index);
    let tail_ptr = page_index2page_ptr(tail_index);
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(head_ptr)) by {
        reveal(Seq::contains); reveal(new_container_bootstrap_4k_pages);
    };
    assert(!new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).contains(head_ptr)) by { reveal(new_container_moved_pages); };
    publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, head_index,
    );
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(tail_ptr)) by {
        if new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).contains(tail_ptr) {
            reveal(thread_staged_4k_pages_wf);
        }
    };
    assert(!funding_pages.to_set().contains(tail_ptr)) by { if funding_pages.to_set().contains(tail_ptr) { reveal(thread_staged_4k_pages_wf); } };
    assert(!new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).contains(tail_ptr)) by { reveal(new_container_moved_pages); };
    publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, tail_index,
    );
}

pub(super) broadcast proof fn publish_staged_container_root_eof_hugepage_2m_tail_backward(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize, process_quota_4k: usize, tail_index: PageIndex,
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
        index_valid(NUM_PAGES, tail_index),
        post.pg_arr.spec_index(tail_index).view().view().state is Merged2m,
    ensures
        #![trigger
            publish_staged_container_root_eof_transition_framing(
                pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page,
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
    hide(Seq::contains);
    reveal(publish_staged_container_root_eof_transition_framing);
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
    let head_index = spec_page_index_truncate_2m(tail_index);
    page_ptr_2m_valid_imply_page_index_2m_valid(container_page); page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
    if page_2m_tail_indices(container_head).contains(tail_index) { return; }
    if page_2m_tail_indices(pcid_allocator_head).contains(tail_index) { return; }
    page_index_valid_imply_page_ptr_valid(); page_index_roundtrip();
    let tail_ptr = page_index2page_ptr(tail_index);
    assert(!page_2m_all_ptrs(container_head).contains(tail_ptr)) by {
        if page_2m_all_ptrs(container_head).contains(tail_ptr) {
            page_2m_ptr_prefix_member_bounds(container_head, 512, tail_ptr);
            if tail_index == container_head { } else { }
        }
    };
    assert(!page_2m_all_ptrs(pcid_allocator_head).contains(tail_ptr)) by {
        if page_2m_all_ptrs(pcid_allocator_head).contains(tail_ptr) {
            page_2m_ptr_prefix_member_bounds(pcid_allocator_head, 512, tail_ptr);
            if tail_index == pcid_allocator_head { } else { }
        }
    };
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(tail_ptr)) by { reveal(Seq::contains); reveal(new_container_bootstrap_4k_pages); };
    assert(!new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).contains(tail_ptr)) by { reveal(new_container_moved_pages); };
    publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, tail_index,
    );
    assert(hugepage_2m_tail_backward_wf(pre.pg_arr)) by { reveal(hugepage_2m_wf); };
    if head_index == container_head || head_index == pcid_allocator_head { return; }
    distinct_2m_heads_have_disjoint_all_ptrs(head_index, container_head); distinct_2m_heads_have_disjoint_all_ptrs(head_index, pcid_allocator_head);
    page_2m_all_ptrs_contains_head(head_index);
    let head_ptr = page_index2page_ptr(head_index);
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(head_ptr)) by {
        if new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).contains(head_ptr) {
            reveal(publish_staged_container_root_eof_preconditions); reveal(thread_staged_4k_pages_wf);
        }
    };
    assert(!funding_pages.to_set().contains(head_ptr)) by { if funding_pages.to_set().contains(head_ptr) { reveal(publish_staged_container_root_eof_preconditions); reveal(thread_staged_4k_pages_wf); } };
    assert(!new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).contains(head_ptr)) by { reveal(new_container_moved_pages); };
    publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, head_index,
    );
}

pub(super) proof fn publish_staged_container_root_eof_object_page_pagetable_wf_4k(
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
        mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
{
    reveal(publish_staged_container_root_eof_transition_framing);
    assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; reveal(mapped_4k_page_pagetable_wf); reveal(pagetable_lower_wf);
        page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
    };
}

pub(super) proof fn publish_staged_container_root_eof_object_page_pagetable_wf_2m(
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
        mapped_2m_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
{
    reveal(publish_staged_container_root_eof_transition_framing);
    assert(mapped_2m_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; reveal(mapped_2m_page_pagetable_wf); reveal(pagetable_lower_wf);
        page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
        assert(whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_page).cr3() == l4_page);
    };
}

pub(super) proof fn publish_staged_container_root_eof_object_page_pagetable_wf_1g(
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
        mapped_1g_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
{
    reveal(publish_staged_container_root_eof_transition_framing);
    assert(mapped_1g_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_perms_wf);
        page_ptr_roundtrip();
    };
}

pub(super) proof fn publish_staged_container_root_eof_object_page_pagetable_wf(
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
    ensures page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
{
    publish_staged_container_root_eof_object_page_pagetable_wf_4k(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page,
        scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages, allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_object_page_pagetable_wf_2m(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page,
        scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages, allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_object_page_pagetable_wf_1g(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page,
        scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages, allocator_quota_4k, process_quota_4k,
    );
}

pub(super) proof fn publish_staged_container_root_eof_object_pages_wf(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        container_owned_pages_wf(post.ctn_mp, post.pg_arr),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
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
        allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr),
        pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        process_pages_wf(post.prc_mp, post.pg_arr),
        thread_pages_wf(post.thrd_mp, post.pg_arr),
        iommu_table_pages_wf(post.it_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
{
    publish_staged_container_root_eof_object_pages_allocators_pagetable(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_object_pages_process_thread_iommu_endpoint(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_object_pages_scheduler_cpu_set(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_object_pages_pcid_allocator(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_object_page_pagetable_wf(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_object_pages_container_process_pagetable(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_object_pages_iommu(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
}

pub(super) proof fn publish_staged_container_root_eof_hugepage_wf(
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
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
{
    assert(hugepage_2m_head_aligned_wf(post.pg_arr)) by { assert(hugepage_2m_head_aligned_wf(pre.pg_arr)) by { reveal(hugepage_2m_wf); }; broadcast use publish_staged_container_root_eof_hugepage_2m_head_valid; };
    assert(hugepage_2m_tail_forward_wf(post.pg_arr)) by { broadcast use publish_staged_container_root_eof_hugepage_2m_tail_forward; };
    assert(hugepage_2m_tail_backward_wf(post.pg_arr)) by { broadcast use publish_staged_container_root_eof_hugepage_2m_tail_backward; };
    assert(hugepage_2m_wf(post.pg_arr)) by { reveal(hugepage_2m_wf); };
    assert(hugepage_1g_wf(post.pg_arr)) by { broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; reveal(hugepage_1g_wf); };
}

pub(super) proof fn publish_staged_container_root_eof_container_pages_wf(
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
        container_pages_wf(post.ctn_mp, post.pg_arr),
{
    broadcast use publish_staged_container_root_eof_container_pages_forward_new; broadcast use publish_staged_container_root_eof_container_pages_forward_existing; broadcast use publish_staged_container_root_eof_container_pages_backward; reveal(container_pages_wf);
}
}
