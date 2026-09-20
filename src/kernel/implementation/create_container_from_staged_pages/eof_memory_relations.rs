use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_memory_relations(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        container_page != pcid_allocator_page,
        page_ptr_valid(allocator_4k_page),
        page_ptr_valid(allocator_2m_page),
        page_ptr_valid(allocator_1g_page),
        page_ptr_valid(scheduler_page),
        page_ptr_valid(cpu_set_page),
        page_ptr_valid(process_page),
        page_ptr_valid(pagetable_page),
        page_ptr_valid(l4_page),
        page_ptr_valid(thread_page),
        new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).len() == 8,
        !new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(thread_page),
        funding_pages.no_duplicates(),
        !funding_pages.to_set().contains(thread_page),
        funding_pages.to_set().disjoint(new_container_moved_pages(
            container_page,
            pcid_allocator_page,
            allocator_4k_page,
            allocator_2m_page,
            allocator_1g_page,
            scheduler_page,
            cpu_set_page,
            process_page,
            pagetable_page,
            l4_page,
        )),
        !funding_pages.to_set().contains(thread_page),
        new_container_bootstrap_4k_pages(
            allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
        ).disjoint(page_2m_all_ptrs(page_ptr2page_index(container_page))),
        new_container_bootstrap_4k_pages(
            allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
        ).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        page_2m_all_ptrs(page_ptr2page_index(container_page)).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        forall|page_ptr: PagePtr|
            #![trigger funding_pages.to_set().contains(page_ptr)]
            funding_pages.to_set().contains(page_ptr) ==> page_ptr_valid(page_ptr),
        !pre.ctn_mp.dom().contains(container_page),
        !pre.pcid_allc_mp.dom().contains(pcid_allocator_page),
        !pre.allc_4k_mp.dom().contains(allocator_4k_page),
        !pre.allc_2m_mp.dom().contains(allocator_2m_page),
        !pre.allc_1g_mp.dom().contains(allocator_1g_page),
        !pre.sched_mp.dom().contains(scheduler_page),
        !pre.cpu_set_mp.dom().contains(cpu_set_page),
        !pre.prc_mp.dom().contains(process_page),
        !pre.pt_mp.dom().contains(pagetable_page),
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
        allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp,),
        container_page_owner_wf(post.ctn_mp, post.pg_arr),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
        page_pagetable_wf(post.pt_mp, post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr,),
        container_pages_wf(post.pg_arr, post.ctn_mp),
        process_pages_wf(post.pg_arr, post.prc_mp),
        pagetable_pages_wf(post.pt_mp, post.pg_arr),
        iommu_table_pages_wf(post.it_mp, post.pg_arr),
        thread_pages_wf(post.thr_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp),
        thread_staged_pages_wf(post.thr_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        post.allocator_free_pages_wf(),
        container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp,),
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp,),
        container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr),
        container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr),
        container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr),
        post.memory_management_inv(),
{
    publish_staged_container_root_eof_allocator_pages_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_container_page_owner_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_hugepage_2m_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_hugepage_1g_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_page_pagetable_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { reveal(publish_staged_container_root_kernel_state_framing); reveal(process_pagetable_match); };
    publish_staged_container_root_eof_container_process_page_pagetable_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_container_pages_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_process_pages_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_pagetable_pages_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_iommu_table_pages_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_thread_pages_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_scheduler_pages_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_cpu_set_pages_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_pcid_allocator_pages_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_thread_staged_pages_4k_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_thread_staged_pages_2m_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_thread_staged_pages_1g_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(thread_staged_pages_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_wf); };
    publish_staged_container_root_eof_endpoint_pages_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { reveal(publish_staged_container_root_kernel_state_framing); reveal(process_iommu_table_match); };
    publish_staged_container_root_eof_allocator_free_pages_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_allocator_quota_4k_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_allocator_quota_2m_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_allocator_quota_1g_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp,)) by { reveal(container_process_allocator_quota_wf); };
    publish_staged_container_root_eof_container_allocator_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_container_allocator_free_4k_page_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_container_allocator_free_2m_page_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_container_allocator_free_1g_page_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(post.memory_management_inv()) by { reveal(KernelK::memory_management_inv); };
}

}
