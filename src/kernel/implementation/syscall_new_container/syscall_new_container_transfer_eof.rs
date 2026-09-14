use vstd::prelude::*;
use crate::*;
use super::syscall_new_container_transfer_spec::transfer_staged_page_preserved_objects_transition_framing;

verus! {
proof fn transfer_staged_thread_page_eof_process(
    pre: KernelK, post: KernelK, page_ptr: PagePtr,
    staging_thread_ptr: RwLockThreadPtr,
    parent: RwLockContainerPtr, child: RwLockContainerPtr,
)
    requires
        pre.inv(),
        transfer_staged_page_preserved_objects_transition_framing(pre, post, page_ptr, staging_thread_ptr, parent, child),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(transfer_staged_page_preserved_objects_transition_framing);
    assert(post.process_management_inv()) by {
        assert(container_tree_wf(post.rt_ctn, post.ctn_mp)) by { reveal(container_perms_wf); reveal(LinkedList::wf_value_list); reveal(container_tree_wf); reveal(container_root_wf); reveal(container_children_parent_wf); reveal(containers_linkedlist_wf); reveal(container_children_depth_wf); reveal(container_subtree_set_wf); reveal(container_uppertree_seq_wf); reveal(container_subtree_set_exclusive); };
        assert(post.ctn_mp.spec_index(post.rt_ctn).view().root_process_in_processes()) by { reveal(container_root_wf); };
        assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
        assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { reveal(per_container_process_tree_wf); };
        assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { reveal(container_endpoint_wf); };
        assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
        assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); reveal(container_thread_wf); reveal(container_process_wf); reveal(process_thread_wf); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf); };
        assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { reveal(container_scheduler_wf); };
        assert(container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
        assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(container_process_wf); reveal(process_pcid_allocator_wf); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { reveal(container_thread_wf); };
    };
}

#[verifier::rlimit(120)]
pub(super) proof fn transfer_staged_thread_page_eof(
    pre: KernelK, post: KernelK, page_ptr: PagePtr,
    staging_thread_ptr: RwLockThreadPtr,
    parent: RwLockContainerPtr, child: RwLockContainerPtr,
)
    requires
        pre.inv(),
        transfer_staged_page_preserved_objects_transition_framing(pre, post, page_ptr, staging_thread_ptr, parent, child),
        post.pg_arr.inv(),
    ensures post.inv(),
{
    reveal(transfer_staged_page_preserved_objects_transition_framing);
    let page_index = page_ptr2page_index(page_ptr);
    assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(page_array_wf(post.pg_arr)) by { reveal(page_array_wf); };
    assert(post.ctn_mp.perms_wf()) by { reveal(container_perms_wf); };
    assert(container_tree_fields_wf(post.ctn_mp)) by { reveal(container_tree_fields_wf); reveal(container_perms_wf); };
    assert(container_perms_wf(post.ctn_mp)) by { reveal(container_perms_wf); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by {
        assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf); };
        assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { reveal(container_page_owner_wf); };
        assert(hugepage_2m_wf(post.pg_arr)) by { reveal(hugepage_2m_wf); };
        assert(hugepage_1g_wf(post.pg_arr)) by { reveal(hugepage_1g_wf); };
        assert(page_pagetable_wf(post.pt_mp, post.pg_arr)) by {
            assert(post.pg_arr.spec_index(page_index).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr })) by { reveal(transfer_staged_page_preserved_objects_transition_framing); };
            assert(!pre.pg_arr.spec_index(page_index).view().view().is_mapped() && !post.pg_arr.spec_index(page_index).view().view().is_mapped()) by { reveal(Page::is_mapped); };
            reveal(page_pagetable_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_perms_wf);
        };
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(container_page_owner_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(process_pagetable_match); };
        assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { reveal(container_pages_wf); };
        assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { reveal(process_pages_wf); };
        assert(pagetable_pages_wf(post.pt_mp, post.pg_arr)) by { reveal(pagetable_pages_wf); };
        assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { reveal(iommu_table_pages_wf); };
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_pages_wf); };
        assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { reveal(scheduler_pages_wf); };
        assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { reveal(pcid_allocator_pages_wf); };
        assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
        assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by {
            assert(post.pg_arr.spec_index(page_index).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr })) by { reveal(transfer_staged_page_preserved_objects_transition_framing); };
            reveal(thread_staged_pages_4k_wf);
        };
        assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_2m_wf); };
        assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by {
            assert(post.pg_arr.spec_index(page_index).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr })) by { reveal(transfer_staged_page_preserved_objects_transition_framing); };
            reveal(thread_staged_pages_1g_wf);
        };
        assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { reveal(endpoint_pages_wf); };
        assert(container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_process_allocator_quota_4k_wf); reveal(container_process_allocator_quota_2m_wf); reveal(container_process_allocator_quota_1g_wf); };
        assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
        assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); };
        assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_global_free_2m_page_wf); reveal(container_allocator_cpu_cache_free_2m_page_wf); reveal(allocator_free_page_ptrs_wf); };
        assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_global_free_1g_page_wf); reveal(container_allocator_cpu_cache_free_1g_page_wf); reveal(allocator_free_page_ptrs_wf); };
    };
    transfer_staged_thread_page_eof_process(pre, post, page_ptr, staging_thread_ptr, parent, child);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf); };
    assert(iommu_root_table_process_wf(&post.irt, post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(process_pci_function_ownership_wf(&post.irt, post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
}
}
