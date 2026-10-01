use vstd::prelude::*;
use crate::*;
use super::*;

verus! {

#[verifier::spinoff_prover]
pub(super) proof fn eof_not_in_moved_pages(
    container_page: PagePtr, pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, page_ptr: PagePtr,
)
    requires
        !page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(page_ptr),
        !page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(page_ptr),
        !new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(page_ptr),
    ensures
        !new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(page_ptr),
{
    reveal(new_container_moved_pages);
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_page_fields_eq_outside_moved_pages(
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
    hide(Seq::contains);
    reveal(publish_staged_container_root_kernel_state_framing);
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
    let funding_indices = funding_pages.map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr)).to_set();
    page_index_valid_imply_page_ptr_valid();
    page_index_roundtrip();
    page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
    page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
    staged_4k_page_chain_page_ptrs_valid(pre.pg_arr, funding_pages);
    page_ptr_seq_indices_excludes_page(funding_pages, page_index2page_ptr(page_index),);
    assert(!page_2m_all_ptrs(container_head).contains(page_index2page_ptr(page_index))) by { reveal(new_container_moved_pages); };
    assert(!page_2m_all_ptrs(pcid_allocator_head).contains(page_index2page_ptr(page_index))) by { reveal(new_container_moved_pages); };
    assert(!page_2m_tail_indices(container_head).contains(page_index)) by {
        if page_2m_tail_indices(container_head).contains(page_index) {
            page_2m_all_ptrs_contains_index(container_head, page_index);
        }
    };
    assert(!page_2m_tail_indices(pcid_allocator_head).contains(page_index)) by {
        if page_2m_tail_indices(pcid_allocator_head).contains(page_index) {
            page_2m_all_ptrs_contains_index(pcid_allocator_head, page_index);
        }
    };
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(page_index2page_ptr(page_index))) by {
        reveal(new_container_moved_pages);
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
}

#[verifier::spinoff_prover]
pub(super) broadcast proof fn eof_unmodified_object_page_state_eq(
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
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        index_valid(NUM_PAGES, page_index),
        {
            let pre_state = pre.pg_arr.spec_index(page_index).view().view().state;
            let post_state = post.pg_arr.spec_index(page_index).view().view().state;
            ||| (pre_state matches PageState::Allocated4k {
                    state: Allocated4KPageState::AsThread,
                })
            ||| (post_state matches PageState::Allocated4k {
                    state: Allocated4KPageState::AsThread,
                })
            ||| (pre_state matches PageState::Allocated4k {
                    state: Allocated4KPageState::AsEndpoint,
                })
            ||| (post_state matches PageState::Allocated4k {
                    state: Allocated4KPageState::AsEndpoint,
                })
            ||| (pre_state matches PageState::Allocated4k {
                    state: Allocated4KPageState::AsIommuTableRoot,
                })
            ||| (post_state matches PageState::Allocated4k {
                    state: Allocated4KPageState::AsIommuTableRoot,
                })
            ||| (pre_state is IOMMUTable)
            ||| (post_state is IOMMUTable)
            ||| (pre_state is Mapped4k)
            ||| (post_state is Mapped4k)
            ||| (pre_state is Mapped2m)
            ||| (post_state is Mapped2m)
            ||| (pre_state is Free2m)
            ||| (post_state is Free2m)
            ||| (pre_state is Free4k)
            ||| (!funding_pages.to_set().contains(page_index2page_ptr(page_index)) && (post_state is Free4k))
            ||| (pre_state is Owned1g)
            ||| (post_state is Owned1g)
            ||| (pre_state is Free1g)
            ||| (post_state is Free1g)
            ||| (pre_state is Mapped1g)
            ||| (post_state is Mapped1g)
            ||| (pre_state is Merged1g)
            ||| (post_state is Merged1g)
            ||| (post_state is Owned4k)
            ||| (pre_state is Owned4k && pre_state->Owned4k_thread_ptr != current_thread_ptr)
            ||| (page_index != page_ptr2page_index(container_page) && ((pre_state matches PageState::Allocated2m {
                        state: Allocated2MPageState::AsContainer,
                    }) || (post_state matches PageState::Allocated2m {
                        state: Allocated2MPageState::AsContainer,
                    })))
            ||| (page_index != page_ptr2page_index(process_page) && ((pre_state matches PageState::Allocated4k {
                        state: Allocated4KPageState::AsProcess,
                    }) || (post_state matches PageState::Allocated4k {
                        state: Allocated4KPageState::AsProcess,
                    })))
            ||| (page_index != page_ptr2page_index(pagetable_page) && ((pre_state matches PageState::Allocated4k {
                        state: Allocated4KPageState::AsPageTableRoot,
                    }) || (post_state matches PageState::Allocated4k {
                        state: Allocated4KPageState::AsPageTableRoot,
                    })))
            ||| (page_index != page_ptr2page_index(l4_page) && ((pre_state matches PageState::Allocated4k {
                        state: Allocated4KPageState::PageTable { pagetable_root },
                    }) || (post_state matches PageState::Allocated4k {
                        state: Allocated4KPageState::PageTable { pagetable_root },
                    })))
            ||| (page_index != page_ptr2page_index(scheduler_page) && ((pre_state matches PageState::Allocated4k {
                        state: Allocated4KPageState::AsScheduler,
                    }) || (post_state matches PageState::Allocated4k {
                        state: Allocated4KPageState::AsScheduler,
                    })))
            ||| (page_index != page_ptr2page_index(cpu_set_page) && ((pre_state matches PageState::Allocated4k {
                        state: Allocated4KPageState::AsCpuSet,
                    }) || (post_state matches PageState::Allocated4k {
                        state: Allocated4KPageState::AsCpuSet,
                    })))
            ||| (page_index != page_ptr2page_index(allocator_4k_page) && ((pre_state matches PageState::Allocated4k {
                        state: Allocated4KPageState::As4KAllocator,
                    }) || (post_state matches PageState::Allocated4k {
                        state: Allocated4KPageState::As4KAllocator,
                    })))
            ||| (page_index != page_ptr2page_index(allocator_2m_page) && ((pre_state matches PageState::Allocated4k {
                        state: Allocated4KPageState::As2MAllocator,
                    }) || (post_state matches PageState::Allocated4k {
                        state: Allocated4KPageState::As2MAllocator,
                    })))
            ||| (page_index != page_ptr2page_index(allocator_1g_page) && ((pre_state matches PageState::Allocated4k {
                        state: Allocated4KPageState::As1GAllocator,
                    }) || (post_state matches PageState::Allocated4k {
                        state: Allocated4KPageState::As1GAllocator,
                    })))
            ||| (page_index != page_ptr2page_index(pcid_allocator_page) && ((pre_state matches PageState::Allocated2m {
                        state: Allocated2MPageState::AsPcidAllocator,
                    }) || (post_state matches PageState::Allocated2m {
                        state: Allocated2MPageState::AsPcidAllocator,
                    })))
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
        #![trigger
            publish_staged_container_root_kernel_state_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            pre.pg_arr.spec_index(page_index).view().view().state
        ]
        {
            &&& post.pg_arr.spec_index(page_index).view().view().state == pre.pg_arr.spec_index(page_index).view().view().state
            &&& post.pg_arr.spec_index(page_index).view().view().owning_container == pre.pg_arr.spec_index(page_index).view().view().owning_container
            &&& post.pg_arr.spec_index(page_index).view().view().free_list_node_storage == pre.pg_arr.spec_index(page_index).view().view().free_list_node_storage
        },
{
    reveal(publish_staged_container_root_kernel_state_framing);
    page_index_valid_imply_page_ptr_valid();
    page_index_roundtrip();
    let page_ptr = page_index2page_ptr(page_index);
    assert(!funding_pages.to_set().contains(page_ptr)) by { reveal(thread_staged_pages_4k_wf); };
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(page_ptr)) by {
        reveal(thread_staged_pages_4k_wf); reveal(new_container_bootstrap_4k_pages);
    };
    assert(page_ptr != container_page) by {
        if page_ptr == container_page {
        }
    };
    assert(page_ptr != pcid_allocator_page) by {
        if page_ptr == pcid_allocator_page {
        }
    };
    assert(!page_2m_tail_indices(page_ptr2page_index(container_page)).contains(page_index)) by {
        if page_2m_tail_indices(page_ptr2page_index(container_page)).contains(page_index) {
            assert(pre.pg_arr.spec_index(page_index).view().view().state is Merged2m) by { reveal(hugepage_2m_wf); };
        }
    };
    assert(!page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).contains(page_index)) by {
        if page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).contains(page_index) {
            assert(pre.pg_arr.spec_index(page_index).view().view().state is Merged2m) by { reveal(hugepage_2m_wf); };
        }
    };
    assert(!page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(page_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(page_ptr) {
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(container_page), 512, page_ptr,);
            assert(page_index != page_ptr2page_index(container_page)) by { page_ptr2page_index_injective(); };
        }
    };
    assert(!page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(page_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(page_ptr) {
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(pcid_allocator_page), 512, page_ptr,);
            assert(page_index != page_ptr2page_index(pcid_allocator_page)) by { page_ptr2page_index_injective(); };
        }
    };
    assert(!new_container_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page,
    ).contains(page_ptr)) by { reveal(new_container_moved_pages); };
    eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, page_index,
    );
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_existing_container_page_not_staged_4k(
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
                allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
            ).contains(page_ptr)]
            pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) <==> new_container_bootstrap_4k_pages(
                allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
            ).contains(page_ptr) || funding_pages.to_set().contains(page_ptr) || page_ptr == thread_page,
        pre.pg_arr.spec_index(page_ptr2page_index(container_ptr)).view().view().state matches PageState::Allocated2m {
                state: Allocated2MPageState::AsContainer,
            },
    ensures
        !funding_pages.to_set().contains(container_ptr),
        !new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(container_ptr),
{
    assert(!funding_pages.to_set().contains(container_ptr)) by {
        if funding_pages.to_set().contains(container_ptr) {
            assert(pre.pg_arr.spec_index(page_ptr2page_index(container_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })) by { reveal(thread_staged_pages_4k_wf); };
        }
    };
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(container_ptr)) by {
        if new_container_bootstrap_4k_pages(
            allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
        ).contains(container_ptr) {
            assert(pre.pg_arr.spec_index(page_ptr2page_index(container_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })) by { reveal(thread_staged_pages_4k_wf); };
        }
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_existing_container_page_not_staged_2m(
    pre: KernelK, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr, pcid_allocator_page: PagePtr, container_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        page_ptr_2m_valid(container_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(container_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(container_ptr)).view().view().state matches PageState::Allocated2m {
                state: Allocated2MPageState::AsContainer,
            },
        container_ptr != container_page,
    ensures
        !page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(container_ptr),
        !page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(container_ptr),
{
    assert(hugepage_2m_tail_forward_wf(pre.pg_arr)) by { reveal(hugepage_2m_wf); };
    page_ptr_2m_valid_imply_page_index_2m_valid(container_ptr);
    page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
    page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
    assert(!page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(container_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(container_ptr) {
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(container_page), 512, container_ptr,);
            if page_ptr2page_index(container_ptr) != page_ptr2page_index(container_page) {
                assert(pre.pg_arr.spec_index(page_ptr2page_index(container_ptr)).view().view().state is Merged2m) by { reveal(hugepage_2m_wf); };
            }
        }
    };
    assert(!page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(container_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(container_ptr) {
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(pcid_allocator_page), 512, container_ptr,);
            if page_ptr2page_index(container_ptr) != page_ptr2page_index(pcid_allocator_page) {
                assert(pre.pg_arr.spec_index(page_ptr2page_index(container_ptr)).view().view().state is Merged2m) by { reveal(hugepage_2m_wf); };
            }
        }
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_existing_container_page_state_eq(
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
    eof_not_in_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page, container_ptr,
    );
    page_ptr_2m_valid_imply_page_index_2m_valid(container_ptr);
    let container_index = page_ptr2page_index(container_ptr);
    assert(page_index2page_ptr(container_index) == container_ptr) by { page_ptr_roundtrip(); };
    eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, container_index,
    );
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_pre_container_page_in_map(pre: KernelK, page_index: PageIndex,)
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
    assert(container_pages_forward_wf(pre.pg_arr, pre.ctn_mp)) by { reveal(container_pages_wf); };
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_existing_post_container_page_state_eq(
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
    hide(Seq::contains);
    reveal(publish_staged_container_root_kernel_state_framing);
    page_index_valid_imply_page_ptr_valid();
    page_index_roundtrip();
    let page_ptr = page_index2page_ptr(page_index);
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(page_ptr)) by { reveal(Seq::contains); reveal(new_container_bootstrap_4k_pages); };
    assert(!page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(page_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(page_ptr) {
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(container_page), 512, page_ptr,);
        }
    };
    assert(!page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(page_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(page_ptr) {
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(pcid_allocator_page), 512, page_ptr,);
            if page_index == page_ptr2page_index(pcid_allocator_page) {
            } else {
            }
        }
    };
    eof_not_in_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page, page_ptr,
    );
    eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, page_index,
    );
}

#[verifier::spinoff_prover]
pub(super) broadcast proof fn eof_container_pages_forward_new(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize, process_quota_4k: usize, page_index: PageIndex,
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
    reveal(publish_staged_container_root_kernel_state_framing);
    assert(page_index2page_ptr(page_index) == container_page) by { page_ptr_roundtrip(); };
}

#[verifier::spinoff_prover]
pub(super) broadcast proof fn eof_container_pages_forward_existing(
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
    reveal(publish_staged_container_root_kernel_state_framing);
    eof_existing_post_container_page_state_eq(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, page_index,
    );
    eof_pre_container_page_in_map(pre, page_index,);
}

#[verifier::spinoff_prover]
pub(super) broadcast proof fn eof_container_pages_backward(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize, process_quota_4k: usize, container_ptr: RwLockContainerPtr,
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
        post.ctn_mp.dom().contains(container_ptr),
    ensures
        #![trigger
            publish_staged_container_root_kernel_state_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.ctn_mp.dom().contains(container_ptr)
        ]
        page_ptr_2m_valid(container_ptr) && (post.pg_arr.spec_index(page_ptr2page_index(container_ptr)).view().view().state matches PageState::Allocated2m {
                    state: Allocated2MPageState::AsContainer,
                }),
{
    reveal(publish_staged_container_root_kernel_state_framing);
    if container_ptr == container_page {
    } else {
        assert(container_pages_backward_wf(pre.pg_arr, pre.ctn_mp)) by { reveal(container_pages_wf); };
        eof_existing_container_page_not_staged_4k(
            pre, current_thread_ptr, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page,
            pagetable_page, l4_page, thread_page, funding_pages, container_ptr,
        );
        eof_existing_container_page_not_staged_2m(pre, current_thread_ptr, container_page, pcid_allocator_page, container_ptr,);
        eof_existing_container_page_state_eq(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k, container_ptr,
        );
    }
}

#[verifier::spinoff_prover]
pub(super) broadcast proof fn eof_existing_pagetable_closure_page_backward(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize, process_quota_4k: usize, pt_ptr: RwLockPageTableRoot, pt_page_ptr: PagePtr,
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
        post.pt_mp.dom().contains(pt_ptr),
        post.pt_mp.spec_index(pt_ptr).view().page_closure().contains(pt_page_ptr),
        pt_ptr != pagetable_page,
    ensures
        #![trigger
            publish_staged_container_root_kernel_state_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.pt_mp.spec_index(pt_ptr).view().page_closure().contains(pt_page_ptr)
        ]
        {
            &&& page_ptr_valid(pt_page_ptr)
            &&& post.pg_arr.spec_index(page_ptr2page_index(pt_page_ptr)).view().view().state is Allocated4k
            &&& post.pg_arr.spec_index(page_ptr2page_index(pt_page_ptr)).view().view().state->Allocated4k_state is PageTable
            &&& post.pg_arr.spec_index(page_ptr2page_index(pt_page_ptr)).view().view().state->Allocated4k_state ->PageTable_pagetable_root == pt_ptr
        },
{
    hide(Seq::contains);
    reveal(publish_staged_container_root_kernel_state_framing);
    assert(pagetable_closure_page_backward_wf(pre.pt_mp, pre.pg_arr)) by { reveal(pagetable_pages_wf); };
    assert(page_ptr2page_index(pt_page_ptr) != page_ptr2page_index(l4_page)) by {
        if page_ptr2page_index(pt_page_ptr) == page_ptr2page_index(l4_page) {
            assert(pt_page_ptr == l4_page) by { page_ptr2page_index_injective(); };
            assert(pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(l4_page)) by { reveal(new_container_bootstrap_4k_pages); };
            reveal(thread_staged_pages_4k_wf);
        }
    };
    page_ptr_valid_imply_page_index_valid();
    eof_unmodified_object_page_state_eq(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, page_ptr2page_index(pt_page_ptr),
    );
}

#[verifier::spinoff_prover]
pub(super) broadcast proof fn eof_thread_staged_pages_4k_forward(
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
            let thread_ptr = post.pg_arr.spec_index(page_index).view().view().state->Owned4k_thread_ptr;
            &&& post.thr_mp.dom().contains(thread_ptr)
            &&& post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_index2page_ptr(page_index))
        },
{
    reveal(publish_staged_container_root_kernel_state_framing);
    eof_unmodified_object_page_state_eq(
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
    } else {
    }
}

#[verifier::spinoff_prover]
pub(super) broadcast proof fn eof_thread_staged_pages_4k_backward(
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
    reveal(publish_staged_container_root_kernel_state_framing);
    if thread_ptr == current_thread_ptr {
        assert(pre.pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })) by { reveal(thread_staged_pages_4k_wf); };
    } else {
        assert(page_ptr_valid(page_ptr)) by { reveal(thread_staged_pages_4k_wf); };
        assert(pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr })) by { reveal(thread_staged_pages_4k_wf); };
        page_ptr_valid_imply_page_index_valid();
        eof_unmodified_object_page_state_eq(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k, page_ptr2page_index(page_ptr),
        );
    }
}

#[verifier::spinoff_prover]
pub(super) broadcast proof fn eof_thread_staged_pages_2m_forward(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize, process_quota_4k: usize, page_index: PageIndex,
)
    requires
        thread_staged_pages_2m_wf(pre.thr_mp, pre.pg_arr),
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
        post.pg_arr.spec_index(page_index).view().view().state is Owned2m,
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
            &&& post.thr_mp.dom().contains(post.pg_arr.spec_index(page_index).view().view().state->Owned2m_thread_ptr)
            &&& post.thr_mp.spec_index(post.pg_arr.spec_index(page_index).view().view().state->Owned2m_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_index2page_ptr(page_index))
        },
{
    hide(Seq::contains);
    reveal(publish_staged_container_root_kernel_state_framing);
    page_index_valid_imply_page_ptr_valid();
    page_index_roundtrip();
    assert(!new_container_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page,
    ).contains(page_index2page_ptr(page_index))) by {
        reveal(Seq::contains); reveal(new_container_moved_pages); reveal(new_container_bootstrap_4k_pages);
        page_ptr_2m_valid_imply_page_index_2m_valid(container_page); page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
        broadcast use page_2m_ptr_prefix_member_bounds;
    };
    eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, page_index,
    );
    assert(thread_staged_pages_2m_forward_wf(pre.thr_mp, pre.pg_arr)) by { reveal(thread_staged_pages_2m_wf); };
    let thread_ptr = post.pg_arr.spec_index(page_index).view().view().state->Owned2m_thread_ptr;
}

#[verifier::spinoff_prover]
pub(super) broadcast proof fn eof_thread_staged_pages_2m_backward(
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
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        #![trigger
            publish_staged_container_root_kernel_state_framing(
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
    reveal(publish_staged_container_root_kernel_state_framing);
    assert(hugepage_2m_tail_forward_wf(pre.pg_arr)) by { reveal(hugepage_2m_wf); };
    page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
    page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
    assert(pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned2m { thread_ptr })) by { reveal(thread_staged_pages_2m_wf); };
    assert(page_ptr_valid(page_ptr)) by { reveal(thread_staged_pages_2m_wf); };
    page_ptr_valid_imply_page_index_valid();
    assert(!funding_pages.to_set().contains(page_ptr)) by { reveal(thread_staged_pages_4k_wf); };
    assert(!page_2m_tail_indices(page_ptr2page_index(container_page)).contains(page_ptr2page_index(page_ptr))) by {
        if page_2m_tail_indices(page_ptr2page_index(container_page)).contains(page_ptr2page_index(page_ptr)) {
        }
    };
    assert(!page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).contains(page_ptr2page_index(page_ptr))) by {
        if page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).contains(page_ptr2page_index(page_ptr)) {
        }
    };
    assert(!new_container_bootstrap_4k_pages(
        allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
    ).contains(page_ptr)) by { reveal(thread_staged_pages_4k_wf); };
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
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page,
    ).contains(page_ptr)) by { reveal(new_container_moved_pages); page_ptr2page_index_injective(); };
    page_ptr_roundtrip();
    eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, page_ptr2page_index(page_ptr),
    );
}

#[verifier::spinoff_prover]
pub(super) broadcast proof fn eof_hugepage_2m_head_valid(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize, process_quota_4k: usize, page_index: PageIndex,
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
    hide(Seq::contains);
    reveal(publish_staged_container_root_kernel_state_framing);
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
    page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
    page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
    if page_index == container_head || page_index == pcid_allocator_head {
        return;
    }

    page_index_valid_imply_page_ptr_valid();
    page_index_roundtrip();
    let page_ptr = page_index2page_ptr(page_index);
    assert(!page_2m_all_ptrs(container_head).contains(page_ptr)) by {
        if page_2m_all_ptrs(container_head).contains(page_ptr) {
            page_2m_ptr_prefix_member_bounds(container_head, 512, page_ptr);
        }
    };
    assert(!page_2m_all_ptrs(pcid_allocator_head).contains(page_ptr)) by {
        if page_2m_all_ptrs(pcid_allocator_head).contains(page_ptr) {
            page_2m_ptr_prefix_member_bounds(pcid_allocator_head, 512, page_ptr);
        }
    };
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(page_ptr)) by {
        reveal(Seq::contains); reveal(new_container_bootstrap_4k_pages);
    };
    assert(!new_container_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page,
    ).contains(page_ptr)) by { reveal(new_container_moved_pages); };
    eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, page_index,
    );
}

#[verifier::spinoff_prover]
pub(super) broadcast proof fn eof_hugepage_2m_tail_forward(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
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
    hide(Seq::contains);
    reveal(publish_staged_container_root_kernel_state_framing);
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
    assert(hugepage_2m_head_valid_wf(pre.pg_arr)) by { reveal(hugepage_2m_wf); };
    assert(hugepage_2m_tail_forward_wf(pre.pg_arr)) by { reveal(hugepage_2m_wf); };
    eof_hugepage_2m_head_valid(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, head_index,
    );
    page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
    page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
    if head_index == container_head {
        assert(page_2m_tail_indices(container_head).contains(tail_index)) by { vstd::set_lib::range_set_properties((container_head + 1) as usize, (container_head + 512) as usize); };
        return;
    }
    if head_index == pcid_allocator_head {
        assert(page_2m_tail_indices(pcid_allocator_head).contains(tail_index)) by { vstd::set_lib::range_set_properties((pcid_allocator_head + 1) as usize, (pcid_allocator_head + 512) as usize); };
        return;
    }

    distinct_2m_heads_have_disjoint_all_ptrs(head_index, container_head);
    distinct_2m_heads_have_disjoint_all_ptrs(head_index, pcid_allocator_head);
    page_2m_all_ptrs_contains_head(head_index);
    page_2m_all_ptrs_contains_index(head_index, tail_index);

    let head_ptr = page_index2page_ptr(head_index);
    let tail_ptr = page_index2page_ptr(tail_index);

    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(head_ptr)) by {
        reveal(Seq::contains); reveal(new_container_bootstrap_4k_pages);
    };
    assert(!new_container_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page,
    ).contains(head_ptr)) by { reveal(new_container_moved_pages); };
    eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, head_index,
    );

    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(tail_ptr)) by {
        if new_container_bootstrap_4k_pages(
            allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
        ).contains(tail_ptr) {
            reveal(thread_staged_pages_4k_wf);
        }
    };
    assert(!funding_pages.to_set().contains(tail_ptr)) by {
        if funding_pages.to_set().contains(tail_ptr) {
            reveal(thread_staged_pages_4k_wf);
        }
    };
    assert(!new_container_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page,
    ).contains(tail_ptr)) by { reveal(new_container_moved_pages); };
    eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, tail_index,
    );
}

#[verifier::spinoff_prover]
pub(super) broadcast proof fn eof_hugepage_2m_tail_backward(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
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
    hide(Seq::contains);
    reveal(publish_staged_container_root_kernel_state_framing);
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
    let head_index = spec_page_index_truncate_2m(tail_index);
    page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
    page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
    if page_2m_tail_indices(container_head).contains(tail_index) {
        return;
    }
    if page_2m_tail_indices(pcid_allocator_head).contains(tail_index) {
        return;
    }

    page_index_valid_imply_page_ptr_valid();
    page_index_roundtrip();
    let tail_ptr = page_index2page_ptr(tail_index);
    assert(!page_2m_all_ptrs(container_head).contains(tail_ptr)) by {
        if page_2m_all_ptrs(container_head).contains(tail_ptr) {
            page_2m_ptr_prefix_member_bounds(container_head, 512, tail_ptr);
            if tail_index == container_head {
            } else {
            }
        }
    };
    assert(!page_2m_all_ptrs(pcid_allocator_head).contains(tail_ptr)) by {
        if page_2m_all_ptrs(pcid_allocator_head).contains(tail_ptr) {
            page_2m_ptr_prefix_member_bounds(pcid_allocator_head, 512, tail_ptr);
            if tail_index == pcid_allocator_head {
            } else {
            }
        }
    };
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(tail_ptr)) by { reveal(Seq::contains); reveal(new_container_bootstrap_4k_pages); };
    assert(!new_container_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page,
    ).contains(tail_ptr)) by { reveal(new_container_moved_pages); };
    eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, tail_index,
    );
    assert(hugepage_2m_tail_backward_wf(pre.pg_arr)) by { reveal(hugepage_2m_wf); };
    if head_index == container_head || head_index == pcid_allocator_head {
        return;
    }

    distinct_2m_heads_have_disjoint_all_ptrs(head_index, container_head);
    distinct_2m_heads_have_disjoint_all_ptrs(head_index, pcid_allocator_head);
    page_2m_all_ptrs_contains_head(head_index);
    let head_ptr = page_index2page_ptr(head_index);
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(head_ptr)) by {
        if new_container_bootstrap_4k_pages(
            allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
        ).contains(head_ptr) {
            reveal(thread_staged_pages_4k_wf);
        }
    };
    assert(!funding_pages.to_set().contains(head_ptr)) by {
        if funding_pages.to_set().contains(head_ptr) {
            reveal(thread_staged_pages_4k_wf);
        }
    };
    assert(!new_container_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page,
    ).contains(head_ptr)) by { reveal(new_container_moved_pages); };
    eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, head_index,
    );
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_object_page_pagetable_wf(
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
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures page_pagetable_wf(post.pt_mp, post.pg_arr),
{
    reveal(publish_staged_container_root_kernel_state_framing);
    assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pg_arr)) by {
        broadcast use eof_unmodified_object_page_state_eq; reveal(mapped_4k_page_pagetable_wf); reveal(pagetable_perms_wf);
        page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
    };
    assert(mapped_2m_page_pagetable_wf(post.pt_mp, post.pg_arr)) by {
        broadcast use eof_unmodified_object_page_state_eq; reveal(mapped_2m_page_pagetable_wf); reveal(pagetable_perms_wf);
        page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
    };
    assert(mapped_1g_page_pagetable_wf(post.pt_mp, post.pg_arr)) by {
        broadcast use eof_unmodified_object_page_state_eq; reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_perms_wf);
        page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_object_pages_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        container_page_owner_wf(post.ctn_mp, post.pg_arr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
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
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        pagetable_pages_wf(post.pt_mp, post.pg_arr),
        page_pagetable_wf(post.pt_mp, post.pg_arr),
        process_pages_wf(post.pg_arr, post.prc_mp),
        thread_pages_wf(post.thr_mp, post.pg_arr),
        iommu_table_pages_wf(post.it_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
{
    hide(Seq::contains);
    reveal(publish_staged_container_root_kernel_state_framing);
    assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        assert(allocator_4k_pages_forward_wf(pre.pg_arr, pre.allc_4k_mp)) by { reveal(allocator_4k_pages_wf); };
        assert(allocator_4k_pages_backward_wf(pre.pg_arr, pre.allc_4k_mp)) by { reveal(allocator_4k_pages_wf); };
        assert(allocator_2m_pages_forward_wf(pre.pg_arr, pre.allc_2m_mp)) by { reveal(allocator_2m_pages_wf); };
        assert(allocator_2m_pages_backward_wf(pre.pg_arr, pre.allc_2m_mp)) by { reveal(allocator_2m_pages_wf); };
        assert(allocator_1g_pages_forward_wf(pre.pg_arr, pre.allc_1g_mp)) by { reveal(allocator_1g_pages_wf); };
        assert(allocator_1g_pages_backward_wf(pre.pg_arr, pre.allc_1g_mp)) by { reveal(allocator_1g_pages_wf); };
        assert(allocator_4k_pages_wf(post.pg_arr, post.allc_4k_mp)) by {
            assert(allocator_4k_pages_forward_wf(post.pg_arr, post.allc_4k_mp)) by {
                page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
                broadcast use eof_unmodified_object_page_state_eq;
            };
            assert(allocator_4k_pages_backward_wf(post.pg_arr, post.allc_4k_mp)) by {
                page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
                broadcast use eof_unmodified_object_page_state_eq;
            };
            reveal(allocator_4k_pages_wf);
        };
        assert(allocator_2m_pages_wf(post.pg_arr, post.allc_2m_mp)) by {
            assert(allocator_2m_pages_forward_wf(post.pg_arr, post.allc_2m_mp)) by {
                page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
                broadcast use eof_unmodified_object_page_state_eq;
            };
            assert(allocator_2m_pages_backward_wf(post.pg_arr, post.allc_2m_mp)) by {
                page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
                broadcast use eof_unmodified_object_page_state_eq;
            };
            reveal(allocator_2m_pages_wf);
        };
        assert(allocator_1g_pages_wf(post.pg_arr, post.allc_1g_mp)) by {
            assert(allocator_1g_pages_forward_wf(post.pg_arr, post.allc_1g_mp)) by {
                page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
                broadcast use eof_unmodified_object_page_state_eq;
            };
            assert(allocator_1g_pages_backward_wf(post.pg_arr, post.allc_1g_mp)) by {
                page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
                broadcast use eof_unmodified_object_page_state_eq;
            };
            reveal(allocator_1g_pages_wf);
        };
    };
    assert(pagetable_pages_wf(post.pt_mp, post.pg_arr)) by {
        assert(pagetable_root_page_forward_wf(pre.pt_mp, pre.pg_arr)) by { reveal(pagetable_pages_wf); };
        assert(pagetable_closure_page_forward_wf(pre.pt_mp, pre.pg_arr)) by { reveal(pagetable_pages_wf); };
        assert(pagetable_root_page_backward_wf(pre.pt_mp, pre.pg_arr)) by { reveal(pagetable_pages_wf); };
        assert(pagetable_closure_page_backward_wf(pre.pt_mp, pre.pg_arr)) by { reveal(pagetable_pages_wf); };
        assert(pagetable_root_page_forward_wf(post.pt_mp, post.pg_arr)) by {
            broadcast use eof_unmodified_object_page_state_eq;
            page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
        };
        assert(pagetable_closure_page_forward_wf(post.pt_mp, post.pg_arr)) by {
            broadcast use eof_unmodified_object_page_state_eq;
            page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
        };
        assert(pagetable_root_page_backward_wf(post.pt_mp, post.pg_arr)) by {
            broadcast use eof_unmodified_object_page_state_eq;
            page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
        };
        assert(pagetable_closure_page_backward_wf(post.pt_mp, post.pg_arr)) by { broadcast use eof_existing_pagetable_closure_page_backward; };
        assert(pagetable_pages_wf(post.pt_mp, post.pg_arr)) by { reveal(pagetable_pages_wf); };
    };
    eof_object_page_pagetable_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(process_pages_wf(post.pg_arr, post.prc_mp)) by {
        broadcast use eof_unmodified_object_page_state_eq;
        page_ptr_valid_imply_page_index_valid();
        page_ptr_roundtrip();
        reveal(process_pages_wf);
    };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by {
        broadcast use eof_unmodified_object_page_state_eq;
        thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr,);
    };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { broadcast use eof_unmodified_object_page_state_eq; reveal(iommu_table_pages_wf); };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by {
        broadcast use eof_unmodified_object_page_state_eq;
        endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr,);
    };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by {
        broadcast use eof_unmodified_object_page_state_eq;
        page_ptr_valid_imply_page_index_valid();
        page_ptr_roundtrip();
        reveal(scheduler_pages_wf);
    };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by {
        broadcast use eof_unmodified_object_page_state_eq;
        page_ptr_valid_imply_page_index_valid();
        page_ptr_roundtrip();
        reveal(cpu_set_pages_wf);
    };
    assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by {
        broadcast use eof_unmodified_object_page_state_eq;
        page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
        page_ptr_valid_imply_page_index_valid();
        page_ptr_roundtrip();
        reveal(pcid_allocator_pages_wf);
    };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by {
        reveal(process_pagetable_match); reveal(container_page_owner_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf);
        reveal(mapped_1g_page_pagetable_wf); reveal(container_process_page_pagetable_wf);
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_hugepage_wf(
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
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
{
    assert(hugepage_2m_head_valid_wf(post.pg_arr)) by {
        assert(hugepage_2m_head_valid_wf(pre.pg_arr)) by { reveal(hugepage_2m_wf); };
        broadcast use eof_hugepage_2m_head_valid;
    };
    assert(hugepage_2m_tail_forward_wf(post.pg_arr)) by { broadcast use eof_hugepage_2m_tail_forward; };
    assert(hugepage_2m_tail_backward_wf(post.pg_arr)) by { broadcast use eof_hugepage_2m_tail_backward; };
    assert(hugepage_2m_wf(post.pg_arr)) by { reveal(hugepage_2m_wf); };
    assert(hugepage_1g_wf(post.pg_arr)) by { broadcast use eof_unmodified_object_page_state_eq; reveal(hugepage_1g_wf); };
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_thread_staged_pages_wf(
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
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        thread_staged_pages_wf(post.thr_mp, post.pg_arr),
{
    reveal(publish_staged_container_root_kernel_state_framing);
    assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by {
        broadcast use eof_thread_staged_pages_4k_forward; broadcast use eof_thread_staged_pages_4k_backward; reveal(thread_staged_pages_4k_wf);
    };
    assert(thread_staged_pages_2m_backward_wf(post.thr_mp, post.pg_arr)) by { broadcast use eof_thread_staged_pages_2m_backward; };
    assert(thread_staged_pages_2m_forward_wf(post.thr_mp, post.pg_arr)) by { broadcast use eof_thread_staged_pages_2m_forward; };
    reveal(thread_staged_pages_2m_wf);
    assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by { broadcast use eof_unmodified_object_page_state_eq; reveal(thread_staged_pages_1g_wf); };
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_container_pages_wf(
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
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_pages_wf(post.pg_arr, post.ctn_mp),
{
    broadcast use eof_container_pages_forward_new; broadcast use eof_container_pages_forward_existing; broadcast use eof_container_pages_backward; reveal(container_pages_wf);
}
}
