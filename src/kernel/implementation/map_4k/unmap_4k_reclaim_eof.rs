use vstd::prelude::*;
use crate::*;
use super::unmap_4k_reclaim_spec::reclaim_last_4k_mapping_to_cpu_cache_transition;

verus! {
#[verifier::spinoff_prover]
proof fn reclaim_last_4k_mapping_to_cpu_cache_eof_process_management_inv(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot,
    va: VAddr, page_ptr: PagePtr, thread_ptr: RwLockThreadPtr,
    owner: RwLockContainerPtr, depth: usize,
    allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    old_counter: usize, new_counter: usize, node_addr: usize,
)
    requires
        pre.inv(),
        reclaim_last_4k_mapping_to_cpu_cache_transition(pre, post, pagetable, va, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(reclaim_last_4k_mapping_to_cpu_cache_transition);
    assert(post.process_management_inv()) by {
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by {
            assert(forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)] pre.thr_mp.dom().contains(t)
                ==> post.thr_mp.spec_index(t).view().endpoint_descriptors == pre.thr_mp.spec_index(t).view().endpoint_descriptors);
            reveal(thread_endpoint_ref_counter_wf);
        };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_queue_wf); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(container_thread_endpoint_wf); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { reveal(container_thread_scheduler_wf); };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { reveal(container_thread_wf); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { reveal(process_thread_wf); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { reveal(thread_cpu_wf); };
        assert(thread_caller_callee_wf(post.thr_mp)) by { reveal(thread_caller_callee_wf); };
    };
}

#[verifier::spinoff_prover]
proof fn reclaim_last_4k_mapping_to_cpu_cache_eof_page_relations(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot,
    va: VAddr, page_ptr: PagePtr, thread_ptr: RwLockThreadPtr,
    owner: RwLockContainerPtr, depth: usize,
    allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    old_counter: usize, new_counter: usize, node_addr: usize,
)
    requires
        pre.inv(),
        reclaim_last_4k_mapping_to_cpu_cache_transition(pre, post, pagetable, va, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr),
        post.subsystems_inv(),
    ensures
        allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_page_owner_wf(post.ctn_mp, post.pg_arr),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
        page_pagetable_wf(post.pt_mp, post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
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
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr),
        container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr),
        container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr),
{
    reveal(reclaim_last_4k_mapping_to_cpu_cache_transition);
    let page_index = page_ptr2page_index(page_ptr);
    assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
    assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf); };
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { reveal(container_pages_wf); };
    assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { reveal(process_pages_wf); };
    assert(hugepage_2m_wf(post.pg_arr)) by { reveal(hugepage_2m_wf); };
    assert(hugepage_1g_wf(post.pg_arr)) by { reveal(hugepage_1g_wf); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { reveal(iommu_table_pages_wf); };
    assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { reveal(pcid_allocator_pages_wf); };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_pages_wf); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { reveal(scheduler_pages_wf); };
    assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_4k_wf); };
    assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_2m_wf); };
    assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_1g_wf); };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { reveal(endpoint_pages_wf); };
    assert(pagetable_pages_wf(post.pt_mp, post.pg_arr)) by { reveal(pagetable_pages_wf); };
    assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pg_arr)) by { reveal(mapped_4k_page_pagetable_wf); reveal(page_array_wf); reveal(pagetable_perms_wf); page_ptr_valid_imply_page_index_valid(); };
    assert(page_pagetable_wf(post.pt_mp, post.pg_arr)) by { reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_perms_wf); reveal(page_array_wf); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); };
    assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_match); };
    assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_match); };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
    assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_global_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); reveal(page_array_wf); };
    assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(container_allocator_wf); reveal(allocator_free_page_ptrs_wf); reveal(page_array_wf); broadcast use vstd::seq_lib::lemma_seq_concat_contains_all_elements; broadcast use vstd::seq_lib::lemma_seq_contains_after_push; pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().insert_ensures(0, page_ptr); };
    assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_global_free_2m_page_wf); reveal(container_allocator_cpu_cache_free_2m_page_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_global_free_1g_page_wf); reveal(container_allocator_cpu_cache_free_1g_page_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(post.allocator_free_pages_wf()) by { reveal(allocator_free_page_ptrs_wf); };
}

#[verifier::spinoff_prover]
proof fn reclaim_last_4k_mapping_to_cpu_cache_eof_allocator_quota_wf(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot,
    va: VAddr, page_ptr: PagePtr, thread_ptr: RwLockThreadPtr,
    owner: RwLockContainerPtr, depth: usize,
    allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    old_counter: usize, new_counter: usize, node_addr: usize,
)
    requires
        pre.inv(),
        reclaim_last_4k_mapping_to_cpu_cache_transition(pre, post, pagetable, va, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr),
        post.subsystems_inv(),
    ensures container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    reveal(reclaim_last_4k_mapping_to_cpu_cache_transition);
    assert(container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by {
            reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); reveal(container_thread_wf); reveal(container_uppertree_seq_wf); reveal(thread_perms_wf);
            lemma_thread_effective_quota_4k_fold_sum_eq_forall();
            lemma_thread_pending_4k_folds_change_by_forall(thread_ptr, if depth == pre.thr_mp.spec_index(thread_ptr).view().container_depth { 1int } else { 0int }, depth as int, if depth < pre.thr_mp.spec_index(thread_ptr).view().container_depth { 1int } else { 0int });

        };
        assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp)) by {
            reveal(container_process_allocator_quota_2m_wf); reveal(container_thread_wf);
            lemma_thread_effective_quota_2m_fold_sum_eq_forall();
            lemma_thread_pending_2m_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp);
        };
        assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp)) by {
            reveal(container_process_allocator_quota_1g_wf); reveal(container_thread_wf);
            lemma_thread_effective_quota_1g_fold_sum_eq_forall();
            lemma_thread_pending_1g_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp);
        };
    };
}

proof fn reclaim_last_4k_mapping_to_cpu_cache_eof_memory_management_inv(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot,
    va: VAddr, page_ptr: PagePtr, thread_ptr: RwLockThreadPtr,
    owner: RwLockContainerPtr, depth: usize,
    allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    old_counter: usize, new_counter: usize, node_addr: usize,
)
    requires
        pre.inv(),
        reclaim_last_4k_mapping_to_cpu_cache_transition(pre, post, pagetable, va, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr),
        post.subsystems_inv(),
    ensures post.memory_management_inv(),
{
    reclaim_last_4k_mapping_to_cpu_cache_eof_page_relations(pre, post, pagetable, va, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr);
    reclaim_last_4k_mapping_to_cpu_cache_eof_allocator_quota_wf(pre, post, pagetable, va, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr);
}

pub(super) proof fn reclaim_last_4k_mapping_to_cpu_cache_eof(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot,
    va: VAddr, page_ptr: PagePtr, thread_ptr: RwLockThreadPtr,
    owner: RwLockContainerPtr, depth: usize,
    allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    old_counter: usize, new_counter: usize, node_addr: usize,
)
    requires
        pre.inv(),
        page_ptr_valid(page_ptr),
        reclaim_last_4k_mapping_to_cpu_cache_transition(pre, post, pagetable, va, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr),
        post.pt_mp.perms_wf(),
        post.pt_mp.spec_index(pagetable).inv(),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().inv(),
        post.thr_mp.perms_wf(),
        post.thr_mp.spec_index(thread_ptr).inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_ptr).wf(),
    ensures
        post.inv(),
        post == (KernelK { pt_mp: post.pt_mp, pg_arr: post.pg_arr, thr_mp: post.thr_mp, allc_4k_mp: post.allc_4k_mp, ..pre }),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable),
        post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread(),
        post.pt_mp.spec_index(pagetable).being_killed() == pre.pt_mp.spec_index(pagetable).being_killed(),
        post.pt_mp.spec_index(pagetable).view().mapping_4k() == pre.pt_mp.spec_index(pagetable).view().mapping_4k().remove(va),
        post.pt_mp.spec_index(pagetable).view().mapping_2m() == pre.pt_mp.spec_index(pagetable).view().mapping_2m(),
        post.pt_mp.spec_index(pagetable).view().mapping_1g() == pre.pt_mp.spec_index(pagetable).view().mapping_1g(),
        post.pt_mp.spec_index(pagetable).view().page_closure() == pre.pt_mp.spec_index(pagetable).view().page_closure(),
        post.pt_mp.spec_index(pagetable).view().kernel_entries == pre.pt_mp.spec_index(pagetable).view().kernel_entries,
        post.pt_mp.spec_index(pagetable).view().kernel_l4_end == pre.pt_mp.spec_index(pagetable).view().kernel_l4_end,
        post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_ptr2page_index(page_ptr)),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count == pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count - 1,
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().mappings() == pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().mappings().remove((pagetable, va)),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } }),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread() == pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread(),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed() == pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed(),
        pagetable_tlb_entries_present(post.cpu_tlb, post.cpu_arr, post.pcid_needflush, pagetable, post.pt_mp.spec_index(pagetable).view()),
        new_counter == old_counter + 1,
        post.thr_mp.spec_index(thread_ptr).view().free_quota_pending_4k_at_depth(depth) == new_counter,
        post.thr_mp.spec_index(thread_ptr).locking_thread() == pre.thr_mp.spec_index(thread_ptr).locking_thread(),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: post.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k, indirect_free_quota_pending_4k: post.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..pre.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view() == pre.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view() + if depth == pre.thr_mp.spec_index(thread_ptr).view().container_depth { 1int } else { 0int },
        post.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() == if depth < pre.thr_mp.spec_index(thread_ptr).view().container_depth { pre.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().update(depth as int, new_counter) } else { pre.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() },
        post.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread() == pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread(),
        post.allc_4k_mp.unchanged_except(&pre.allc_4k_mp, allocator_ptr),
        post.allc_4k_mp.spec_index(allocator_ptr).quota == pre.allc_4k_mp.spec_index(allocator_ptr).quota,
        post.allc_4k_mp.spec_index(allocator_ptr).total_free_pages.view() == pre.allc_4k_mp.spec_index(allocator_ptr).total_free_pages.view() + 1,
        post.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view() == pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().insert(0, page_ptr),
        post.allc_4k_mp.spec_index(allocator_ptr).global_pool == pre.allc_4k_mp.spec_index(allocator_ptr).global_pool,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
        kernel_k_to_nonlock_kernel_u(post) == kernel_k_to_nonlock_kernel_u(pre),
{
    reveal(reclaim_last_4k_mapping_to_cpu_cache_transition);
    assert(pagetable_hidden_leaves_only_when_wlocked(post.pt_mp)) by { reveal(pagetable_perms_wf); reveal(pagetable_hidden_leaves_only_when_wlocked); };
    assert(post.subsystems_inv()) by { reveal(pagetable_perms_wf); reveal(page_array_wf); reveal(thread_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(allocator_perms_wf); reveal(KernelK::default_pagetable_wf); };
    reclaim_last_4k_mapping_to_cpu_cache_eof_memory_management_inv(pre, post, pagetable, va, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr);
    reclaim_last_4k_mapping_to_cpu_cache_eof_process_management_inv(pre, post, pagetable, va, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
    assert(post.pt_mp.spec_index(pagetable).view().user_view(LockStateU::Unlocked).mapping_4k =~= pre.pt_mp.spec_index(pagetable).view().user_view(LockStateU::Unlocked).mapping_4k) by { vstd::map::axiom_map_ext_equal(post.pt_mp.spec_index(pagetable).view().user_view(LockStateU::Unlocked).mapping_4k, pre.pt_mp.spec_index(pagetable).view().user_view(LockStateU::Unlocked).mapping_4k); };
    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post)) by {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged);
        reveal(kernel_thread_nonlock_fields_unchanged);
        kernel_iommu_table_nonlock_fields_unchanged_for_equal(pre.it_mp, post.it_mp);
        kernel_cpu_nonlock_fields_unchanged_for_equal(pre.cpu_arr, post.cpu_arr);
        kernel_process_nonlock_fields_unchanged_for_equal(pre.prc_mp, post.prc_mp);
    };
    kernel_endpoint_nonlock_fields_unchanged_for_equal(pre.ep_mp, post.ep_mp);
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_allocator_wf); };
    kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(&pre, &post);
}
}
