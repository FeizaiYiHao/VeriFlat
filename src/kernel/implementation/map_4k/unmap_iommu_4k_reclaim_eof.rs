use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::unmap_iommu_4k_reclaim_spec::reclaim_last_iommu_4k_mapping_to_cpu_cache_eof_transition_framing;

verus! {
proof fn reclaim_last_iommu_4k_mapping_to_cpu_cache_eof_process_management_inv(
    pre: KernelK, post: KernelK, iommu_table: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index), page_ptr: PagePtr, thread_ptr: RwLockThreadPtr, owner: RwLockContainerPtr,
    depth: usize, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, old_counter: usize, new_counter: usize, node_addr: usize,
)
    requires
        pre.inv(),
        reclaim_last_iommu_4k_mapping_to_cpu_cache_eof_transition_framing(pre, post, iommu_table, indices, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(reclaim_last_iommu_4k_mapping_to_cpu_cache_eof_transition_framing);
    assert(post.process_management_inv()) by {
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { container_thread_endpoint_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { container_thread_scheduler_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp); };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { container_thread_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { process_thread_wf_preserved_for_thread_process_management_fields(post.prc_mp, pre.thr_mp, post.thr_mp); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.cpu_arr); };
        assert(thread_caller_callee_wf(post.thr_mp)) by { thread_caller_callee_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp); };
        assert(thread_dangling_chain_end_wf(post.thr_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thr_mp, post.thr_mp); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
    };
}

proof fn reclaim_last_iommu_4k_mapping_to_cpu_cache_eof_page_relations(
    pre: KernelK, post: KernelK, iommu_table: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index), page_ptr: PagePtr, thread_ptr: RwLockThreadPtr, owner: RwLockContainerPtr,
    depth: usize, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, old_counter: usize, new_counter: usize, node_addr: usize,
)
    requires
        pre.inv(),
        reclaim_last_iommu_4k_mapping_to_cpu_cache_eof_transition_framing(pre, post, iommu_table, indices, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr),
        ({
            let iova = spec_index2va(indices);
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view();
            &&& pre.it_mp.dom().contains(iommu_table)
            &&& pei_valid(indices.0)
            &&& pei_valid(indices.1)
            &&& pei_valid(indices.2)
            &&& pei_valid(indices.3)
            &&& pre.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(iova)
            &&& pre.it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(iova).addr == page_ptr
            &&& pre.it_mp.spec_index(iommu_table).locking_thread() is Write
            &&& page_ptr_valid(page_ptr)
            &&& old_page.ref_count == 1
            &&& old_page.state is Mapped4k
            &&& !old_page.is_io_page
            &&& old_page.owning_container == owner
            &&& old_page.free_list_node_storage.addr() == node_addr
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& pre.allc_4k_mp.dom().contains(allocator_ptr)
            &&& !pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr)
            &&& pre.ctn_mp.dom().contains(owner)
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr
        }),
        post.subsystems_inv(),
    ensures
        allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_page_owner_wf(post.ctn_mp, post.pg_arr),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
        page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
        container_pages_wf(post.pg_arr, post.ctn_mp),
        process_pages_wf(post.pg_arr, post.prc_mp),
        process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp),
        page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp),
        pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        iommu_table_pages_wf(post.it_mp, post.pg_arr),
        thread_pages_wf(post.thr_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp),
        thread_staged_pages_wf(post.thr_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp),
        post.allocator_free_pages_wf(),
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr),
        container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr),
        container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr),
{
    reveal(reclaim_last_iommu_4k_mapping_to_cpu_cache_eof_transition_framing);
    let page_index = page_ptr2page_index(page_ptr);
    assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(pre.pg_arr.spec_index(page_index).view().view().iommu_mappings().contains((iommu_table, spec_index2va(indices))) && pre.pg_arr.spec_index(page_index).view().view().mappings().len() == 0) by {
        reveal(page_iommu_table_wf); page_array_wf_at(pre.pg_arr, page_index); page_ptr_roundtrip();
    };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); reveal(page_array_wf); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
    assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_4k_mp, post.allc_4k_mp);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_1g_mp, post.allc_1g_mp);
    };
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.ctn_mp, post.ctn_mp); };
    assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.prc_mp, post.prc_mp); };
    assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp)) by { reveal(page_object_owner_wf); reveal(container_page_owner_wf); };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
    assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.pcid_allc_mp, post.pcid_allc_mp); };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
    assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_4k_page_pagetable_wf); reveal(page_array_wf); reveal(pagetable_lower_wf); };
    assert(page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_lower_wf); reveal(page_array_wf); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by {
        container_process_page_pagetable_wf_preserved_for_page_mapping_fields_eq(post.ctn_mp, post.prc_mp, post.pt_mp, pre.pg_arr, post.pg_arr);
        reveal(mapped_4k_page_pagetable_wf);
        reveal(mapped_2m_page_pagetable_wf);
    };
    assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_match); };
    assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); reveal(process_iommu_table_match); };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { container_allocator_wf_preserved_for_owner_depth_eq(pre.ctn_mp, post.ctn_mp, pre.allc_4k_mp, post.allc_4k_mp, pre.allc_2m_mp, post.allc_2m_mp, pre.allc_1g_mp, post.allc_1g_mp); };
    assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_global_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by {
        reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(container_allocator_wf); reveal(allocator_free_page_ptrs_wf); reveal(page_array_wf);
        broadcast use vstd::seq_lib::lemma_seq_concat_contains_all_elements; broadcast use vstd::seq_lib::lemma_seq_contains_after_push;
        pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().insert_ensures(0, page_ptr);
    };
    assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, page_ptr2page_index(page_ptr)); };
    assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_ptr2page_index(page_ptr)); };
}

proof fn reclaim_last_iommu_4k_mapping_to_cpu_cache_eof_allocator_quota_wf(
    pre: KernelK, post: KernelK, iommu_table: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index), page_ptr: PagePtr, thread_ptr: RwLockThreadPtr, owner: RwLockContainerPtr,
    depth: usize, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, old_counter: usize, new_counter: usize, node_addr: usize,
)
    requires
        pre.inv(),
        reclaim_last_iommu_4k_mapping_to_cpu_cache_eof_transition_framing(pre, post, iommu_table, indices, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr),
        ({
            let old_thread = pre.thr_mp.spec_index(thread_ptr);
            &&& pre.allc_4k_mp.dom().contains(allocator_ptr)
            &&& pre.thr_mp.dom().contains(thread_ptr)
            &&& old_thread.locking_thread() is Write
            &&& pre.ctn_mp.dom().contains(owner)
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().depth == depth
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr
            &&& depth <= old_thread.view().container_depth
            &&& (if depth == old_thread.view().container_depth { owner == old_thread.view().owning_container } else { old_thread.view().upper_container_seq.view().spec_index(depth as int) == owner })
            &&& old_counter == old_thread.view().free_quota_pending_4k_at_depth(depth)
        }),
        post.subsystems_inv(),
    ensures container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    reveal(reclaim_last_iommu_4k_mapping_to_cpu_cache_eof_transition_framing);
    assert(container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by {
            reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); reveal(container_thread_wf); reveal(container_uppertree_seq_wf); reveal(thread_perms_wf);
            lemma_thread_effective_quota_4k_fold_sum_eq_forall();
            lemma_thread_pending_4k_folds_change_by_forall(thread_ptr, if depth == pre.thr_mp.spec_index(thread_ptr).view().container_depth { 1int } else { 0int }, depth as int, if depth < pre.thr_mp.spec_index(thread_ptr).view().container_depth { 1int } else { 0int });
        };
        assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp)) by {
            container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_2m_mp); reveal(container_thread_wf);
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

proof fn reclaim_last_iommu_4k_mapping_to_cpu_cache_eof_memory_management_inv(
    pre: KernelK, post: KernelK, iommu_table: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index), page_ptr: PagePtr, thread_ptr: RwLockThreadPtr, owner: RwLockContainerPtr,
    depth: usize, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, old_counter: usize, new_counter: usize, node_addr: usize,
)
    requires
        pre.inv(),
        reclaim_last_iommu_4k_mapping_to_cpu_cache_eof_transition_framing(pre, post, iommu_table, indices, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr),
        ({
            let iova = spec_index2va(indices);
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view();
            let old_thread = pre.thr_mp.spec_index(thread_ptr);
            &&& pre.it_mp.dom().contains(iommu_table)
            &&& pei_valid(indices.0)
            &&& pei_valid(indices.1)
            &&& pei_valid(indices.2)
            &&& pei_valid(indices.3)
            &&& pre.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(iova)
            &&& pre.it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(iova).addr == page_ptr
            &&& pre.it_mp.spec_index(iommu_table).locking_thread() is Write
            &&& page_ptr_valid(page_ptr)
            &&& old_page.ref_count == 1
            &&& old_page.state is Mapped4k
            &&& !old_page.is_io_page
            &&& old_page.owning_container == owner
            &&& old_page.free_list_node_storage.addr() == node_addr
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& pre.allc_4k_mp.dom().contains(allocator_ptr)
            &&& !pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr)
            &&& pre.thr_mp.dom().contains(thread_ptr)
            &&& old_thread.locking_thread() is Write
            &&& pre.ctn_mp.dom().contains(owner)
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().depth == depth
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr
            &&& depth <= old_thread.view().container_depth
            &&& (if depth == old_thread.view().container_depth { owner == old_thread.view().owning_container } else { old_thread.view().upper_container_seq.view().spec_index(depth as int) == owner })
            &&& old_counter == old_thread.view().free_quota_pending_4k_at_depth(depth)
        }),
        post.subsystems_inv(),
    ensures post.memory_management_inv(),
{
    reclaim_last_iommu_4k_mapping_to_cpu_cache_eof_page_relations(pre, post, iommu_table, indices, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr);
    reclaim_last_iommu_4k_mapping_to_cpu_cache_eof_allocator_quota_wf(pre, post, iommu_table, indices, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr);
    assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        let thread = pre.thr_mp.spec_index(thread_ptr).view();
        reveal(reclaim_last_iommu_4k_mapping_to_cpu_cache_eof_transition_framing);
        container_thread_wf_at(pre.ctn_mp, pre.thr_mp, thread_ptr); container_thread_wf_uppertree_at(pre.ctn_mp, pre.thr_mp, thread_ptr);
        if depth < thread.container_depth {
            container_perms_wf_at(pre.ctn_mp, thread.owning_container); assert(thread.upper_container_seq.view().contains(owner));
            container_uppertree_seq_wf_at(pre.rt_ctn, pre.ctn_mp, thread.owning_container, owner);
        }
        reveal(container_kill_retire_wf); reveal(container_allocator_wf);
    };
}

pub(super) proof fn reclaim_last_iommu_4k_mapping_to_cpu_cache_eof(
    pre: KernelK, post: KernelK, iommu_table: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index), page_ptr: PagePtr, thread_ptr: RwLockThreadPtr, owner: RwLockContainerPtr,
    depth: usize, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, old_counter: usize, new_counter: usize, node_addr: usize, was_present: bool,
)
    requires
        pre.inv(),
        reclaim_last_iommu_4k_mapping_to_cpu_cache_eof_transition_framing(pre, post, iommu_table, indices, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr),
        ({
            let iova = spec_index2va(indices);
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view();
            let old_thread = pre.thr_mp.spec_index(thread_ptr);
            &&& pre.it_mp.dom().contains(iommu_table)
            &&& pei_valid(indices.0)
            &&& pei_valid(indices.1)
            &&& pei_valid(indices.2)
            &&& pei_valid(indices.3)
            &&& pre.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(iova)
            &&& pre.it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(iova).present == was_present
            &&& (was_present ==> pre.it_mp.spec_index(iommu_table).view().did is None)
            &&& pre.it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(iova).addr == page_ptr
            &&& pre.it_mp.spec_index(iommu_table).locking_thread() is Write
            &&& page_ptr_valid(page_ptr)
            &&& old_page.ref_count == 1
            &&& old_page.state is Mapped4k
            &&& !old_page.is_io_page
            &&& old_page.owning_container == owner
            &&& old_page.free_list_node_storage.addr() == node_addr
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& pre.allc_4k_mp.dom().contains(allocator_ptr)
            &&& !pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr)
            &&& pre.thr_mp.dom().contains(thread_ptr)
            &&& old_thread.locking_thread() is Write
            &&& pre.ctn_mp.dom().contains(owner)
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().depth == depth
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr
            &&& depth <= old_thread.view().container_depth
            &&& (if depth == old_thread.view().container_depth { owner == old_thread.view().owning_container } else { old_thread.view().upper_container_seq.view().spec_index(depth as int) == owner })
            &&& old_counter == old_thread.view().free_quota_pending_4k_at_depth(depth)
        }),
        iommu_table_perms_wf(post.it_mp),
        // Produced by `page_array_remove_last_4k_iommu_mapping_to_cache` and `thread_map_add_free_quota_pending_4k`.
        page_array_wf(post.pg_arr),
        thread_perms_wf(post.thr_mp),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().inv(),
        post.thr_mp.perms_wf(),
        post.thr_mp.spec_index(thread_ptr).inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_ptr).wf(),
        !was_present ==> iommu_table_tlb_entries_present(pre.iommu_tlb, pre.irt.view(), pre.it_mp, iommu_table),
    ensures
        post.inv(),
        iommu_table_tlb_entries_present(post.iommu_tlb, post.irt.view(), post.it_mp, iommu_table),
        post == (KernelK { it_mp: post.it_mp, pg_arr: post.pg_arr, thr_mp: post.thr_mp, allc_4k_mp: post.allc_4k_mp, ..pre }),
        post.it_mp.unchanged_except(&pre.it_mp, iommu_table),
        post.it_mp.spec_index(iommu_table).locking_thread() == pre.it_mp.spec_index(iommu_table).locking_thread(),
        post.it_mp.spec_index(iommu_table).being_killed() == pre.it_mp.spec_index(iommu_table).being_killed(),
        post.it_mp.spec_index(iommu_table).view().mapping_4k() == pre.it_mp.spec_index(iommu_table).view().mapping_4k().remove(spec_index2va(indices)),
        post.it_mp.spec_index(iommu_table).view().mapping_2m() == pre.it_mp.spec_index(iommu_table).view().mapping_2m(),
        post.it_mp.spec_index(iommu_table).view().mapping_1g() == pre.it_mp.spec_index(iommu_table).view().mapping_1g(),
        post.it_mp.spec_index(iommu_table).view().page_closure() == pre.it_mp.spec_index(iommu_table).view().page_closure(),
        post.it_mp.spec_index(iommu_table).view().kernel_entries == pre.it_mp.spec_index(iommu_table).view().kernel_entries,
        post.it_mp.spec_index(iommu_table).view().kernel_l4_end == pre.it_mp.spec_index(iommu_table).view().kernel_l4_end,
        post.it_mp.spec_index(iommu_table).view().cr3 == pre.it_mp.spec_index(iommu_table).view().cr3,
        post.it_mp.spec_index(iommu_table).view().proc_ptr == pre.it_mp.spec_index(iommu_table).view().proc_ptr,
        post.it_mp.spec_index(iommu_table).view().did == pre.it_mp.spec_index(iommu_table).view().did,
        was_present ==> post.it_mp.spec_index(iommu_table).view().user_view(LockStateU::Unlocked).mapping_4k
            == pre.it_mp.spec_index(iommu_table).view().user_view(LockStateU::Unlocked).mapping_4k.remove(spec_index2va(indices)),
        post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_ptr2page_index(page_ptr)),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count == pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count - 1,
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().iommu_mappings()
            == pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().iommu_mappings().remove((iommu_table, spec_index2va(indices))),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } }),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread() == pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread(),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed() == pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed(),
        new_counter == old_counter + 1,
        post.thr_mp.spec_index(thread_ptr).view().free_quota_pending_4k_at_depth(depth) == new_counter,
        post.thr_mp.spec_index(thread_ptr).locking_thread() == pre.thr_mp.spec_index(thread_ptr).locking_thread(),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: post.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: post.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..pre.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view() == pre.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view() + if depth == pre.thr_mp.spec_index(thread_ptr).view().container_depth { 1int } else { 0int },
        post.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view()
            == if depth < pre.thr_mp.spec_index(thread_ptr).view().container_depth { pre.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().update(depth as int, new_counter) }
            else { pre.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() },
        post.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread() == pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread(),
        post.allc_4k_mp.unchanged_except(&pre.allc_4k_mp, allocator_ptr),
        post.allc_4k_mp.spec_index(allocator_ptr).quota == pre.allc_4k_mp.spec_index(allocator_ptr).quota,
        post.allc_4k_mp.spec_index(allocator_ptr).total_free_pages.view() == pre.allc_4k_mp.spec_index(allocator_ptr).total_free_pages.view() + 1,
        post.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view() == pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().insert(0, page_ptr),
        post.allc_4k_mp.spec_index(allocator_ptr).global_pool == pre.allc_4k_mp.spec_index(allocator_ptr).global_pool,
        !was_present ==> kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        was_present ==> kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &KernelK { it_mp: pre.it_mp, ..post }),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
{
    reveal(reclaim_last_iommu_4k_mapping_to_cpu_cache_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(pagetable_perms_wf); reveal(allocator_perms_wf); reveal(KernelK::default_pagetable_wf); };
    reclaim_last_iommu_4k_mapping_to_cpu_cache_eof_memory_management_inv(pre, post, iommu_table, indices, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr);
    reclaim_last_iommu_4k_mapping_to_cpu_cache_eof_process_management_inv(pre, post, iommu_table, indices, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr);
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp) && iommu_table_tlb_entries_present(post.iommu_tlb, post.irt.view(), post.it_mp, iommu_table)) by {
        reveal(iommu_tlb_wf_spec); reveal(iommu_root_table_process_wf); reveal(iommu_table_tlb_entries_present);
    };
    if was_present {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &KernelK { it_mp: pre.it_mp, ..post })) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); kernel_pagetable_nonlock_fields_unchanged_for_equal(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view()); reveal(kernel_iommu_table_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
            kernel_cpu_nonlock_fields_unchanged_for_equal(pre.cpu_arr, post.cpu_arr);
            kernel_process_nonlock_fields_unchanged_for_equal(pre.prc_mp, post.prc_mp);
        };
    } else {
        assert(post.it_mp.spec_index(iommu_table).view().user_view(LockStateU::Unlocked).mapping_4k =~= pre.it_mp.spec_index(iommu_table).view().user_view(LockStateU::Unlocked).mapping_4k);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post)) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); kernel_pagetable_nonlock_fields_unchanged_for_equal(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view()); reveal(kernel_iommu_table_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
            kernel_cpu_nonlock_fields_unchanged_for_equal(pre.cpu_arr, post.cpu_arr);
            kernel_process_nonlock_fields_unchanged_for_equal(pre.prc_mp, post.prc_mp);
        };
    }
    kernel_endpoint_nonlock_fields_unchanged_for_equal(pre.ep_mp, post.ep_mp);
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_allocator_wf); };
}
}
