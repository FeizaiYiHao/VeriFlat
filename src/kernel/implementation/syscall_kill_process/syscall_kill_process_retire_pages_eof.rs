use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_retire_pages_spec::kill_retire_table_page_eof_transition_framing;

verus! {
proof fn kill_retire_table_page_eof_subsystems_inv(
    pre: KernelK, post: KernelK, iommu: bool, table: RwLockPageTableRoot, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        kill_retire_table_page_eof_transition_framing(pre, post, iommu, table, pg_ptr, thrd_ptr, allc_ptr, cpu_id, node_addr),
        page_ptr_valid(pg_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.allc_4k_mp.dom().contains(allc_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().free_list_node_storage.addr() == node_addr,
        !pre.allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_table_stale_cpus_only_when_write_locked(post.pt_mp),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        iommu_table_perms_wf(post.it_mp),
        page_array_wf(post.pg_arr),
        thread_perms_wf(post.thrd_mp),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allc_ptr).wf(),
    ensures post.subsystems_inv(),
{
    reveal(kill_retire_table_page_eof_transition_framing);
    assert(allocator_perms_wf(post.allc_4k_mp)) by { reveal(allocator_perms_wf); };
    reveal(KernelK::default_pagetable_wf);
}

proof fn kill_retire_table_page_eof_table_pages(
    pre: KernelK, post: KernelK, iommu: bool, table: RwLockPageTableRoot, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        kill_retire_table_page_eof_transition_framing(pre, post, iommu, table, pg_ptr, thrd_ptr, allc_ptr, cpu_id, node_addr),
        page_ptr_valid(pg_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: table, table_type: if iommu { IOMMU_TYPE } else { PT_TYPE } } }),
        iommu ==> pre.it_mp.dom().contains(table) && pre.it_mp.spec_index(table).view().page_closure().contains(pg_ptr),
        !iommu ==> pre.pt_mp.dom().contains(table) && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).page_closure().contains(pg_ptr),
        post.subsystems_inv(),
    ensures
        pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        iommu_table_pages_wf(post.it_mp, post.pg_arr),
        process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr),
        page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        process_iommu_table_wf(post.prc_mp, post.it_mp),
        iommu_table_no_huge_leaf_wf(post.it_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
{
    reveal(kill_retire_table_page_eof_transition_framing);
    if iommu {
        assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
        assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { reveal(iommu_table_pages_wf); page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); page_index_roundtrip(); };
    } else {
        assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(pagetable_pages_wf); page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); page_index_roundtrip(); };
        assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
    }
    assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { reveal(process_object_pages_owner_wf); reveal(pagetable_pages_wf); reveal(iommu_table_pages_wf); page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); page_index_roundtrip(); };
    assert(page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr)) by { reveal(page_object_owner_wf); reveal(container_owned_pages_wf); };
    assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_wf); };
    assert(process_iommu_table_wf(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_wf); };
    assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_wf); reveal(process_iommu_table_wf); };
}

proof fn kill_retire_table_page_eof_page_relations(
    pre: KernelK, post: KernelK, iommu: bool, table: RwLockPageTableRoot, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        kill_retire_table_page_eof_transition_framing(pre, post, iommu, table, pg_ptr, thrd_ptr, allc_ptr, cpu_id, node_addr),
        page_ptr_valid(pg_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: table, table_type: if iommu { IOMMU_TYPE } else { PT_TYPE } } }),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == pre.thrd_mp.spec_index(thrd_ptr).view().owning_container,
        pre.thrd_mp.dom().contains(thrd_ptr),
        pre.ctn_mp.dom().contains(pre.thrd_mp.spec_index(thrd_ptr).view().owning_container),
        pre.ctn_mp.spec_index(pre.thrd_mp.spec_index(thrd_ptr).view().owning_container).view_rodata().view().allocator_ptr_4k == allc_ptr,
        pre.allc_4k_mp.dom().contains(allc_ptr),
        iommu ==> pre.it_mp.dom().contains(table) && pre.it_mp.spec_index(table).view().page_closure().contains(pg_ptr),
        !iommu ==> pre.pt_mp.dom().contains(table) && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).page_closure().contains(pg_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().free_list_node_storage.addr() == node_addr,
        !pre.allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr),
        !iommu ==> page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), pre.pg_arr),
        post.subsystems_inv(),
    ensures
        allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr),
        container_owned_pages_wf(post.ctn_mp, post.pg_arr),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
        page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
        container_pages_wf(post.ctn_mp, post.pg_arr),
        process_pages_wf(post.prc_mp, post.pg_arr),
        thread_pages_wf(post.thrd_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr),
        thread_staged_pages_wf(post.thrd_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
        allocator_free_page_ptrs_wf(post.allc_4k_mp),
        allocator_free_page_ptrs_wf(post.allc_2m_mp),
        allocator_free_page_ptrs_wf(post.allc_1g_mp),
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr),
        allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr),
        allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr),
{
    reveal(kill_retire_table_page_eof_transition_framing);
    let pg_idx = page_ptr2page_index(pg_ptr);
    assert(index_valid(NUM_PAGES, pg_idx)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.allc_4k_mp, post.allc_4k_mp, pre.pg_arr, post.pg_arr);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.allc_2m_mp, post.allc_2m_mp, pre.pg_arr, post.pg_arr);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.allc_1g_mp, post.allc_1g_mp, pre.pg_arr, post.pg_arr);
    };
    assert(container_owned_pages_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    if iommu {
        assert(page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { page_pagetable_wf_preserved_for_nonmapped_page_change(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr, pg_idx); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); };
    } else {
        assert(page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { page_pagetable_wf_preserved_for_nonmapped_page_change(post.pt_mp, post.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr, pg_idx); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { page_iommu_table_wf_preserved_for_nonmapped_page_change(pre.ctn_mp, pre.prc_mp, pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr, pg_idx); };
    }
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(container_pages_wf(post.ctn_mp, post.pg_arr)) by { container_pages_wf_preserved_for_page_state_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(process_pages_wf(post.prc_mp, post.pg_arr)) by { process_pages_wf_preserved_for_page_state_eq(pre.prc_mp, post.prc_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
    assert(pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pcid_allc_mp, post.pcid_allc_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_4k_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_staged_4k_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_2m_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_staged_2m_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_1g_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_staged_1g_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
    assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { container_thread_wf_thread_at(pre.ctn_mp, pre.thrd_mp, thrd_ptr); reveal(container_kill_retire_wf); reveal(container_allocator_wf); };
    assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_global_pool_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(allocator_free_4k_pages_wf); reveal(allocator_global_pool_4k_pages_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by {
        reveal(allocator_free_4k_pages_wf); reveal(allocator_cpu_cache_4k_pages_wf); reveal(container_allocator_wf); reveal(allocator_free_page_ptrs_wf); reveal(page_array_wf);
        broadcast use vstd::seq_lib::lemma_seq_concat_contains_all_elements; broadcast use vstd::seq_lib::lemma_seq_contains_after_push;
        pre.allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().insert_ensures(0, pg_ptr);
    };
    assert(allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, pg_idx); };
    assert(allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, pg_idx); };
}

proof fn kill_retire_table_page_eof_allocator_quota_wf(
    pre: KernelK, post: KernelK, iommu: bool, table: RwLockPageTableRoot, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        kill_retire_table_page_eof_transition_framing(pre, post, iommu, table, pg_ptr, thrd_ptr, allc_ptr, cpu_id, node_addr),
        pre.thrd_mp.dom().contains(thrd_ptr),
        pre.ctn_mp.dom().contains(pre.thrd_mp.spec_index(thrd_ptr).view().owning_container),
        pre.ctn_mp.spec_index(pre.thrd_mp.spec_index(thrd_ptr).view().owning_container).view_rodata().view().allocator_ptr_4k == allc_ptr,
        pre.allc_4k_mp.dom().contains(allc_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
        post.subsystems_inv(),
    ensures container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    reveal(kill_retire_table_page_eof_transition_framing);
    let depth = pre.thrd_mp.spec_index(thrd_ptr).view().container_depth;
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp)) by {
        reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); reveal(container_thread_wf);
        lemma_thread_effective_quota_4k_fold_sum_eq_forall();
        lemma_thread_pending_4k_folds_change_by_forall(thrd_ptr, 1int, depth as int, 0int);
    };
    assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_2m_mp)) by { container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_2m_mp); };
    assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_1g_mp)) by { container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_1g_mp); };
}

proof fn kill_retire_table_page_eof_process_management_inv(
    pre: KernelK, post: KernelK, iommu: bool, table: RwLockPageTableRoot, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        kill_retire_table_page_eof_transition_framing(pre, post, iommu, table, pg_ptr, thrd_ptr, allc_ptr, cpu_id, node_addr),
        pre.thrd_mp.dom().contains(thrd_ptr),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(kill_retire_table_page_eof_transition_framing);
    assert(thread_endpoint_ref_counter_wf(post.thrd_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.ep_mp); };
    assert(thread_endpoint_queue_wf(post.thrd_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.ep_mp); };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thrd_mp, post.ep_mp)) by { container_thread_endpoint_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp, post.ep_mp); };
    assert(container_thread_scheduler_wf(post.ctn_mp, post.thrd_mp, post.sched_mp)) by { container_thread_scheduler_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp, post.sched_mp); };
    assert(container_thread_wf(post.ctn_mp, post.thrd_mp)) by { container_thread_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp); };
    assert(process_thread_wf(post.prc_mp, post.thrd_mp)) by { process_thread_wf_preserved_for_thread_process_management_fields(post.prc_mp, pre.thrd_mp, post.thrd_mp); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
    assert(thread_cpu_wf(post.thrd_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.cpu_arr); };
    assert(thread_caller_callee_wf(post.thrd_mp)) by { thread_caller_callee_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp); };
    assert(thread_dangling_chain_end_wf(post.thrd_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thrd_mp, post.thrd_mp); };
}

/// The CPU TLBs and paging-structure caches keep only what the table still holds: a page table, which resolves no user
/// root entry and lists no cpu stale, backs no cached entry.
proof fn kill_retire_table_page_eof_tlb_caches(
    pre: KernelK, post: KernelK, iommu: bool, table: RwLockPageTableRoot, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        kill_retire_table_page_eof_transition_framing(pre, post, iommu, table, pg_ptr, thrd_ptr, allc_ptr, cpu_id, node_addr),
        !iommu ==> pre.pt_mp.dom().contains(table),
        !iommu ==> forall|l4i: L4Index| #![trigger whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).spec_resolve_mapping_l4(l4i)]
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).kernel_l4_end() <= l4i && pei_valid(l4i) ==> whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).spec_resolve_mapping_l4(l4i) is None,
        !iommu ==> pre.pt_mp.spec_index(table).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
    ensures
        cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
        structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    reveal(kill_retire_table_page_eof_transition_framing);
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(cpu_tlb_wf); broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_va_1g_valid_index_roundtrip; };
    assert(structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(structure_cache_wf); };
}

/// The table page leaving its zombie table for the owner's cpu cache, with the killer's pending refund grown by one,
/// keeps the kernel invariant and every non-lock field the projection reads.
pub(crate) proof fn kill_retire_table_page_eof(
    pre: KernelK, post: KernelK, iommu: bool, table: RwLockPageTableRoot, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
)
    requires
        pre.inv(),
        kill_retire_table_page_eof_transition_framing(pre, post, iommu, table, pg_ptr, thrd_ptr, allc_ptr, cpu_id, node_addr),
        page_ptr_valid(pg_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: table, table_type: if iommu { IOMMU_TYPE } else { PT_TYPE } } }),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == pre.thrd_mp.spec_index(thrd_ptr).view().owning_container,
        pre.thrd_mp.dom().contains(thrd_ptr),
        pre.ctn_mp.dom().contains(pre.thrd_mp.spec_index(thrd_ptr).view().owning_container),
        pre.ctn_mp.spec_index(pre.thrd_mp.spec_index(thrd_ptr).view().owning_container).view_rodata().view().allocator_ptr_4k == allc_ptr,
        pre.allc_4k_mp.dom().contains(allc_ptr),
        iommu ==> pre.it_mp.dom().contains(table) && pre.it_mp.spec_index(table).view().page_closure().contains(pg_ptr),
        !iommu ==> pre.pt_mp.dom().contains(table) && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).page_closure().contains(pg_ptr),
        !iommu ==> whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).leaves_present(),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().free_list_node_storage.addr() == node_addr,
        pre.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
        !pre.allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_table_stale_cpus_only_when_write_locked(post.pt_mp),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        iommu_table_perms_wf(post.it_mp),
        page_array_wf(post.pg_arr),
        !iommu ==> page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), pre.pg_arr),
        !iommu ==> pre.pt_mp.spec_index(table).locking_thread() is Write,
        !iommu ==> forall|l4i: L4Index| #![trigger whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).spec_resolve_mapping_l4(l4i)]
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).kernel_l4_end() <= l4i && pei_valid(l4i) ==> whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).spec_resolve_mapping_l4(l4i) is None,
        !iommu ==> pre.pt_mp.spec_index(table).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        thread_perms_wf(post.thrd_mp),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allc_ptr).wf(),
    ensures
        post.inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
        !iommu ==> (whole_pagetable(pre.pt_mp, pre.pt_lower.view(), table).leaves_present() ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), table).leaves_present()),
        iommu ==> (pre.it_mp.spec_index(table).view().leaves_present() ==> post.it_mp.spec_index(table).view().leaves_present()),
{
    kill_retire_table_page_eof_subsystems_inv(pre, post, iommu, table, pg_ptr, thrd_ptr, allc_ptr, cpu_id, node_addr);
    kill_retire_table_page_eof_table_pages(pre, post, iommu, table, pg_ptr, thrd_ptr, allc_ptr, cpu_id, node_addr);
    kill_retire_table_page_eof_page_relations(pre, post, iommu, table, pg_ptr, thrd_ptr, allc_ptr, cpu_id, node_addr);
    kill_retire_table_page_eof_allocator_quota_wf(pre, post, iommu, table, pg_ptr, thrd_ptr, allc_ptr, cpu_id, node_addr);
    kill_retire_table_page_eof_process_management_inv(pre, post, iommu, table, pg_ptr, thrd_ptr, allc_ptr, cpu_id, node_addr);
    kill_retire_table_page_eof_tlb_caches(pre, post, iommu, table, pg_ptr, thrd_ptr, allc_ptr, cpu_id, node_addr);
    reveal(kill_retire_table_page_eof_transition_framing);
    assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(iommu_tlb_wf(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf); reveal(iommu_root_table_process_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_pagetable_pcid_match); };
    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post)) by {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
        kernel_cpu_nonlock_fields_unchanged_for_equal(pre.cpu_arr, post.cpu_arr);
        kernel_process_nonlock_fields_unchanged_for_equal(pre.prc_mp, post.prc_mp);
    };
    kernel_endpoint_nonlock_fields_unchanged_for_equal(pre.ep_mp, post.ep_mp);
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_allocator_wf); };
}
} // verus!
