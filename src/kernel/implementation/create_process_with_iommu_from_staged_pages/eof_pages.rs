use vstd::prelude::*;
use vstd::assert_maps_equal;
use vstd::assert_sets_equal;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub(super) proof fn create_process_with_iommu_from_staged_pages_eof_page_table_relations(
    pre: KernelK,
    post: KernelK,
    process_page_ptr: PagePtr,
    pagetable_page_ptr: PagePtr,
    l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr,
    iommu_l4_page_ptr: PagePtr,
    parent_ptr: RwLockProcessPtr,
    staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr,
    pcid_allocator_ptr: RwLockPcidAllocatorPtr,
    pcid: Pcid,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        page_ptr_valid(iommu_table_page_ptr),
        page_ptr_valid(iommu_l4_page_ptr),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        process_page_ptr != iommu_table_page_ptr,
        process_page_ptr != iommu_l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        pagetable_page_ptr != iommu_table_page_ptr,
        pagetable_page_ptr != iommu_l4_page_ptr,
        l4_page_ptr != iommu_table_page_ptr,
        l4_page_ptr != iommu_l4_page_ptr,
        iommu_table_page_ptr != iommu_l4_page_ptr,
        !pre.prc_mp.dom().contains(process_page_ptr),
        !pre.pt_mp.dom().contains(pagetable_page_ptr),
        !pre.it_mp.dom().contains(iommu_table_page_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr)
            .view().temp_alloc_cache_4k.view()
            =~= set![
                process_page_ptr,
                pagetable_page_ptr,
                l4_page_ptr,
                iommu_table_page_ptr,
                iommu_l4_page_ptr,
            ],
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr))
            .view().view().state
            == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr))
            .view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr))
            .view().view().state
            == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr))
            .view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr))
            .view().view().state
            == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr))
            .view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr))
            .view().view().state
            == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr))
            .view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr))
            .view().view().state
            == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr))
            .view().view().owning_container == container_ptr,
        create_process_with_iommu_from_staged_pages_kernel_state_framing(
            pre,
            post,
            process_page_ptr,
            pagetable_page_ptr,
            l4_page_ptr,
            iommu_table_page_ptr,
            iommu_l4_page_ptr,
            parent_ptr,
            staging_thread_ptr,
            container_ptr,
            pcid_allocator_ptr,
            pcid,
        ),
    ensures
        page_pagetable_wf(post.pt_mp, post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        pagetable_pages_wf(post.pt_mp, post.pg_arr),
        iommu_table_pages_wf(post.it_mp, post.pg_arr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
{
    reveal(create_process_with_iommu_from_staged_pages_kernel_state_framing);
    assert(page_pagetable_wf(pre.pt_mp, pre.pg_arr)) by {
        reveal(KernelK::inv);
        reveal(KernelK::memory_management_inv);
    };
    assert(pagetable_perms_wf(post.pt_mp)) by {
        reveal(KernelK::subsystems_inv);
    };
    assert(page_pagetable_wf(post.pt_mp, post.pg_arr)) by {
        reveal(mapped_4k_page_pagetable_wf);
        reveal(mapped_2m_page_pagetable_wf);
        reveal(mapped_1g_page_pagetable_wf);
        reveal(pagetable_perms_wf);
        reveal(PageTable::is_empty);
        page_ptr_valid_imply_page_index_valid();
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(container_process_page_pagetable_wf(
        post.ctn_mp,
        post.prc_mp,
        post.pt_mp,
        post.pg_arr,
    )) by {
        reveal(container_process_page_pagetable_wf);
    };
    assert(pagetable_pages_wf(post.pt_mp, post.pg_arr)) by {
        reveal(pagetable_pages_wf);
    };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by {
        reveal(iommu_table_pages_wf);
    };
    assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by {
        reveal(process_pagetable_match);
    };
    assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by {
        reveal(process_iommu_table_match);
    };
}

#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub(super) proof fn create_process_with_iommu_from_staged_pages_eof_memory_relations(
    pre: KernelK,
    post: KernelK,
    process_page_ptr: PagePtr,
    pagetable_page_ptr: PagePtr,
    l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr,
    iommu_l4_page_ptr: PagePtr,
    parent_ptr: RwLockProcessPtr,
    staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr,
    pcid_allocator_ptr: RwLockPcidAllocatorPtr,
    pcid: Pcid,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        page_ptr_valid(iommu_table_page_ptr),
        page_ptr_valid(iommu_l4_page_ptr),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        process_page_ptr != iommu_table_page_ptr,
        process_page_ptr != iommu_l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        pagetable_page_ptr != iommu_table_page_ptr,
        pagetable_page_ptr != iommu_l4_page_ptr,
        l4_page_ptr != iommu_table_page_ptr,
        l4_page_ptr != iommu_l4_page_ptr,
        iommu_table_page_ptr != iommu_l4_page_ptr,
        !pre.prc_mp.dom().contains(process_page_ptr),
        !pre.pt_mp.dom().contains(pagetable_page_ptr),
        !pre.it_mp.dom().contains(iommu_table_page_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr)
            .view().temp_alloc_cache_4k.view()
            =~= set![
                process_page_ptr,
                pagetable_page_ptr,
                l4_page_ptr,
                iommu_table_page_ptr,
                iommu_l4_page_ptr,
            ],
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr))
            .view().view().state
            == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr))
            .view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr))
            .view().view().state
            == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr))
            .view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr))
            .view().view().state
            == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr))
            .view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr))
            .view().view().state
            == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr))
            .view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr))
            .view().view().state
            == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr))
            .view().view().owning_container == container_ptr,
        create_process_with_iommu_from_staged_pages_kernel_state_framing(
            pre,
            post,
            process_page_ptr,
            pagetable_page_ptr,
            l4_page_ptr,
            iommu_table_page_ptr,
            iommu_l4_page_ptr,
            parent_ptr,
            staging_thread_ptr,
            container_ptr,
            pcid_allocator_ptr,
            pcid,
        ),
    ensures
        allocator_pages_wf(
            post.pg_arr,
            post.allc_4k_mp,
            post.allc_2m_mp,
            post.allc_1g_mp,
        ),
        container_page_owner_wf(post.ctn_mp, post.pg_arr),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
        container_pages_wf(post.pg_arr, post.ctn_mp),
        process_pages_wf(post.pg_arr, post.prc_mp),
        thread_pages_wf(post.thr_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp),
        thread_staged_pages_wf(post.thr_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
        post.allocator_free_pages_wf(),
        container_allocator_wf(
            post.ctn_mp,
            post.allc_4k_mp,
            post.allc_2m_mp,
            post.allc_1g_mp,
        ),
        container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr),
        container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr),
        container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr),
{
    reveal(create_process_with_iommu_from_staged_pages_kernel_state_framing);
    assert(allocator_pages_wf(
        post.pg_arr,
        post.allc_4k_mp,
        post.allc_2m_mp,
        post.allc_1g_mp,
    )) by {
        reveal(allocator_4k_pages_wf);
        reveal(allocator_2m_pages_wf);
        reveal(allocator_1g_pages_wf);
    };
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by {
        reveal(container_page_owner_wf);
    };
    assert(hugepage_2m_wf(post.pg_arr)) by {
        reveal(hugepage_2m_wf);
    };
    assert(hugepage_1g_wf(post.pg_arr)) by {
        reveal(hugepage_1g_wf);
    };
    assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by {
        reveal(container_pages_wf);
    };
    assert(process_pages_wf(post.pg_arr, post.prc_mp)) by {
        reveal(process_pages_wf);
    };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by {
        reveal(thread_pages_wf);
    };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by {
        reveal(scheduler_pages_wf);
    };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by {
        reveal(cpu_set_pages_wf);
    };
    assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by {
        reveal(pcid_allocator_pages_wf);
    };
    assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by {
        reveal(thread_staged_pages_4k_wf);
    };
    assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by {
        reveal(thread_staged_pages_2m_wf);
    };
    assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by {
        reveal(thread_staged_pages_1g_wf);
    };
    assert(thread_staged_pages_wf(post.thr_mp, post.pg_arr)) by {
        reveal(thread_staged_pages_wf);
    };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by {
        reveal(endpoint_pages_wf);
    };
    assert(post.allocator_free_pages_wf()) by {
        reveal(KernelK::allocator_free_pages_wf);
        reveal(allocator_free_page_ptrs_wf);
    };
    assert(container_allocator_wf(
        post.ctn_mp,
        post.allc_4k_mp,
        post.allc_2m_mp,
        post.allc_1g_mp,
    )) by {
        reveal(container_allocator_wf);
    };
    assert(container_allocator_free_4k_page_wf(
        post.allc_4k_mp,
        post.pg_arr,
    )) by {
        reveal(container_allocator_free_4k_page_wf);
        reveal(container_allocator_global_free_4k_page_wf);
        reveal(container_allocator_cpu_cache_free_4k_page_wf);
        reveal(allocator_free_page_ptrs_wf);
    };
    assert(container_allocator_free_2m_page_wf(
        post.allc_2m_mp,
        post.pg_arr,
    )) by {
        reveal(container_allocator_free_2m_page_wf);
        reveal(container_allocator_global_free_2m_page_wf);
        reveal(container_allocator_cpu_cache_free_2m_page_wf);
        reveal(allocator_free_page_ptrs_wf);
    };
    assert(container_allocator_free_1g_page_wf(
        post.allc_1g_mp,
        post.pg_arr,
    )) by {
        reveal(container_allocator_free_1g_page_wf);
        reveal(container_allocator_global_free_1g_page_wf);
        reveal(container_allocator_cpu_cache_free_1g_page_wf);
        reveal(allocator_free_page_ptrs_wf);
    };
}


}
