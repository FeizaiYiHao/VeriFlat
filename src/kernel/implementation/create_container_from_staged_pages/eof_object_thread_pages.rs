use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub broadcast proof fn publish_staged_container_root_eof_unmodified_object_page_state_eq(
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
    assert(thread_staged_pages_4k_wf(pre.thr_mp, pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); reveal(thread_staged_pages_wf); };
    assert(thread_staged_pages_2m_wf(pre.thr_mp, pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); reveal(thread_staged_pages_wf); };
    assert(hugepage_2m_wf(pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); };
    page_index_valid_imply_page_ptr_valid();
    page_index_roundtrip();
    let page_ptr = page_index2page_ptr(page_index);
    assert(!funding_pages.to_set().contains(page_ptr)) by { reveal(thread_staged_pages_4k_wf); reveal(publish_staged_container_root_kernel_state_framing); };
    assert(!new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(page_ptr)) by {
        reveal(thread_staged_pages_4k_wf); reveal(new_container_bootstrap_4k_pages);
        reveal(publish_staged_container_root_kernel_state_framing); broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(page_ptr != container_page) by {
        if page_ptr == container_page {
            assert(pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(container_page));
            assert(pre.pg_arr.spec_index(page_ptr2page_index(container_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr })) by { reveal(thread_staged_pages_2m_wf); reveal(thread_staged_pages_2m_backward_wf); };
            assert(post.pg_arr.spec_index(page_ptr2page_index(container_page)).view().view().state == (PageState::Allocated2m {
                    state: Allocated2MPageState::AsContainer,
                })) by { reveal(publish_staged_container_root_kernel_state_framing); };
        }
    };
    assert(page_ptr != pcid_allocator_page) by {
        if page_ptr == pcid_allocator_page {
            assert(pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(pcid_allocator_page));
            assert(pre.pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr })) by { reveal(thread_staged_pages_2m_wf); reveal(thread_staged_pages_2m_backward_wf); };
            assert(post.pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Allocated2m {
                    state: Allocated2MPageState::AsPcidAllocator,
                })) by { reveal(publish_staged_container_root_kernel_state_framing); };
        }
    };
    assert(!page_2m_tail_indices(page_ptr2page_index(container_page)).contains(page_index)) by {
        if page_2m_tail_indices(page_ptr2page_index(container_page)).contains(page_index) {
            assert(pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(container_page));
            assert(pre.pg_arr.spec_index(page_ptr2page_index(container_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr })) by { reveal(thread_staged_pages_2m_wf); reveal(thread_staged_pages_2m_backward_wf); };
            assert(spec_page_index_merge_2m_valid(page_ptr2page_index(container_page), page_index,)) by { reveal(page_2m_tail_indices); };
            assert(pre.pg_arr.spec_index(page_index).view().view().state is Merged2m) by { reveal(hugepage_2m_wf); };
            assert(post.pg_arr.spec_index(page_index).view().view().state is Merged2m) by { reveal(publish_staged_container_root_kernel_state_framing); };
        }
    };
    assert(!page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).contains(page_index)) by {
        if page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).contains(page_index) {
            assert(pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(pcid_allocator_page));
            assert(pre.pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr })) by { reveal(thread_staged_pages_2m_wf); reveal(thread_staged_pages_2m_backward_wf); };
            assert(spec_page_index_merge_2m_valid(page_ptr2page_index(pcid_allocator_page), page_index,)) by { reveal(page_2m_tail_indices); };
            assert(pre.pg_arr.spec_index(page_index).view().view().state is Merged2m) by { reveal(hugepage_2m_wf); };
            assert(post.pg_arr.spec_index(page_index).view().view().state is Merged2m) by { reveal(publish_staged_container_root_kernel_state_framing); };
        }
    };
    assert(!page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(page_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(page_ptr) {
            reveal(page_2m_all_ptrs);
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(container_page), 512, page_ptr,);
            assert(page_index != page_ptr2page_index(container_page)) by { page_ptr2page_index_injective(); };
            assert(page_2m_tail_indices(page_ptr2page_index(container_page)).contains(page_index)) by { reveal(page_2m_tail_indices); };
        }
    };
    assert(!page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(page_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(page_ptr) {
            reveal(page_2m_all_ptrs);
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(pcid_allocator_page), 512, page_ptr,);
            assert(page_index != page_ptr2page_index(pcid_allocator_page)) by { page_ptr2page_index_injective(); };
            assert(page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).contains(page_index)) by { reveal(page_2m_tail_indices); };
        }
    };
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
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_thread_pages_wf(
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
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        thread_pages_wf(post.thr_mp, post.pg_arr),
{
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by {
        assert(thread_pages_wf(pre.thr_mp, pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); };
        assert(post.thr_mp.dom() == pre.thr_mp.dom()) by { reveal(publish_staged_container_root_kernel_state_framing); reveal(LockedMap::unchanged_except); };
        broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq;
        thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr,);
    };
}


}
