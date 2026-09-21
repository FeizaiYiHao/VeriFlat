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
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); };
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
            reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); reveal(container_thread_wf); reveal(container_uppertree_seq_wf);
            lemma_thread_effective_quota_4k_fold_sum_eq_forall();
            if !(forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k]
                post.ctn_mp.dom().contains(c) ==> (process_effective_quota_4k_fold_sum(post.ctn_mp.spec_index(c).view().owned_processes.view(), post.prc_mp)
                + thread_effective_quota_4k_fold_sum(post.ctn_mp.spec_index(c).view_ghost().owned_threads.view(), post.thr_mp)
                + thread_direct_pending_4k_fold_sum(post.ctn_mp.spec_index(c).view_ghost().owned_threads.view(), post.thr_mp)
                + thread_indirect_pending_4k_fold_sum_at_depth(post.ctn_mp.spec_index(c).view_ghost().owned_indirect_threads.view(), post.thr_mp, post.ctn_mp.spec_index(c).view_rodata().view().depth as int)
                + post.allc_4k_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).quota.view().view()
                == post.allc_4k_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).total_free_pages.view())) {
                let c = choose|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k] post.ctn_mp.dom().contains(c) && !(process_effective_quota_4k_fold_sum(post.ctn_mp.spec_index(c).view().owned_processes.view(), post.prc_mp)
                + thread_effective_quota_4k_fold_sum(post.ctn_mp.spec_index(c).view_ghost().owned_threads.view(), post.thr_mp)
                + thread_direct_pending_4k_fold_sum(post.ctn_mp.spec_index(c).view_ghost().owned_threads.view(), post.thr_mp)
                + thread_indirect_pending_4k_fold_sum_at_depth(post.ctn_mp.spec_index(c).view_ghost().owned_indirect_threads.view(), post.thr_mp, post.ctn_mp.spec_index(c).view_rodata().view().depth as int)
                + post.allc_4k_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).quota.view().view()
                == post.allc_4k_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).total_free_pages.view());
                let direct = post.ctn_mp.spec_index(c).view_ghost().owned_threads.view();
                let indirect = post.ctn_mp.spec_index(c).view_ghost().owned_indirect_threads.view();
                let c_depth = post.ctn_mp.spec_index(c).view_rodata().view().depth as int;
                if c == owner && depth == pre.thr_mp.spec_index(thread_ptr).view().container_depth {
                    let pre_value = |t: RwLockThreadPtr| pre.thr_mp.spec_index(t).view().direct_free_quota_pending_4k.view() as int;
                    let post_value = |t: RwLockThreadPtr| post.thr_mp.spec_index(t).view().direct_free_quota_pending_4k.view() as int;
                    assert({
                        &&& (|sum: int, t: RwLockThreadPtr| sum + pre_value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + pre.thr_mp.spec_index(t).view().direct_free_quota_pending_4k.view())
                        &&& (|sum: int, t: RwLockThreadPtr| sum + post_value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + post.thr_mp.spec_index(t).view().direct_free_quota_pending_4k.view())
                        &&& direct.fold(0int, |sum: int, t: RwLockThreadPtr| sum + post_value(t)) == direct.fold(0int, |sum: int, t: RwLockThreadPtr| sum + pre_value(t)) + 1
                    }) by { lemma_set_fold_int_sum_change_by(direct, pre_value, post_value, thread_ptr, 1int); };
                } else {
                    lemma_thread_direct_pending_4k_fold_eq(direct, pre.thr_mp, post.thr_mp);
                }
                if c == owner && depth < pre.thr_mp.spec_index(thread_ptr).view().container_depth {
                    assert(indirect.contains(thread_ptr)) by { reveal(thread_perms_wf); };
                    let pre_value = |t: RwLockThreadPtr| pre.thr_mp.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(c_depth) as int;
                    let post_value = |t: RwLockThreadPtr| post.thr_mp.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(c_depth) as int;
                    assert({
                        &&& (|sum: int, t: RwLockThreadPtr| sum + pre_value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + pre.thr_mp.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(c_depth))
                        &&& (|sum: int, t: RwLockThreadPtr| sum + post_value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + post.thr_mp.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(c_depth))
                        &&& indirect.fold(0int, |sum: int, t: RwLockThreadPtr| sum + post_value(t)) == indirect.fold(0int, |sum: int, t: RwLockThreadPtr| sum + pre_value(t)) + 1
                    }) by { lemma_set_fold_int_sum_change_by(indirect, pre_value, post_value, thread_ptr, 1int); };
                } else {
                    lemma_thread_indirect_pending_4k_fold_eq_at_depth(indirect, pre.thr_mp, post.thr_mp, c_depth);
                }
            }
        };
        lemma_thread_effective_quota_2m_fold_sum_eq_forall();
        lemma_thread_pending_2m_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp);
        assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp)) by {
            reveal(container_process_allocator_quota_2m_wf);
            reveal(container_thread_wf);
        };
        assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp)) by {
            reveal(container_process_allocator_quota_1g_wf);
            if !(forall|c: RwLockContainerPtr|
                #![trigger post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g]
                post.ctn_mp.dom().contains(c) ==> {
                    let direct = post.ctn_mp.spec_index(c).view_ghost().owned_threads.view();
                    let indirect = post.ctn_mp.spec_index(c).view_ghost().owned_indirect_threads.view();
                    let c_depth = post.ctn_mp.spec_index(c).view_rodata().view().depth as int;
                    process_effective_quota_1g_fold_sum(post.ctn_mp.spec_index(c).view().owned_processes.view(), post.prc_mp)
                        + thread_effective_quota_1g_fold_sum(direct, post.thr_mp)
                        + thread_direct_pending_1g_fold_sum(direct, post.thr_mp)
                        + thread_indirect_pending_1g_fold_sum_at_depth(indirect, post.thr_mp, c_depth)
                        + post.allc_1g_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g).quota.view().view()
                        == post.allc_1g_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g).total_free_pages.view()
                }) {
                let c = choose|c: RwLockContainerPtr|
                    #![trigger post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g]
                    post.ctn_mp.dom().contains(c) && !{
                        let direct = post.ctn_mp.spec_index(c).view_ghost().owned_threads.view();
                        let indirect = post.ctn_mp.spec_index(c).view_ghost().owned_indirect_threads.view();
                        let c_depth = post.ctn_mp.spec_index(c).view_rodata().view().depth as int;
                        process_effective_quota_1g_fold_sum(post.ctn_mp.spec_index(c).view().owned_processes.view(), post.prc_mp)
                            + thread_effective_quota_1g_fold_sum(direct, post.thr_mp)
                            + thread_direct_pending_1g_fold_sum(direct, post.thr_mp)
                            + thread_indirect_pending_1g_fold_sum_at_depth(indirect, post.thr_mp, c_depth)
                            + post.allc_1g_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g).quota.view().view()
                            == post.allc_1g_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g).total_free_pages.view()
                    };
                let direct = post.ctn_mp.spec_index(c).view_ghost().owned_threads.view();
                let indirect = post.ctn_mp.spec_index(c).view_ghost().owned_indirect_threads.view();
                let c_depth = post.ctn_mp.spec_index(c).view_rodata().view().depth as int;
                if !(forall|t: RwLockThreadPtr|
                    #![trigger thread_effective_quota_1g(pre.thr_mp.spec_index(t))]
                    direct.contains(t) ==> thread_effective_quota_1g(post.thr_mp.spec_index(t))
                        == thread_effective_quota_1g(pre.thr_mp.spec_index(t))) {
                    let t = choose|t: RwLockThreadPtr|
                        #![trigger thread_effective_quota_1g(pre.thr_mp.spec_index(t))]
                        direct.contains(t) && thread_effective_quota_1g(post.thr_mp.spec_index(t))
                            != thread_effective_quota_1g(pre.thr_mp.spec_index(t));
                    assert(pre.thr_mp.dom().contains(t)) by { reveal(container_thread_wf); };
                    assert(thread_effective_quota_1g(post.thr_mp.spec_index(t))
                        == thread_effective_quota_1g(pre.thr_mp.spec_index(t)));
                }
                if !(forall|t: RwLockThreadPtr|
                    #![trigger pre.thr_mp.spec_index(t).view().direct_free_quota_pending_1g]
                    direct.contains(t) ==> post.thr_mp.spec_index(t).view().direct_free_quota_pending_1g.view()
                        == pre.thr_mp.spec_index(t).view().direct_free_quota_pending_1g.view()) {
                    let t = choose|t: RwLockThreadPtr|
                        #![trigger pre.thr_mp.spec_index(t).view().direct_free_quota_pending_1g]
                        direct.contains(t) && post.thr_mp.spec_index(t).view().direct_free_quota_pending_1g.view()
                            != pre.thr_mp.spec_index(t).view().direct_free_quota_pending_1g.view();
                    assert(pre.thr_mp.dom().contains(t)) by { reveal(container_thread_wf); };
                }
                if !(forall|t: RwLockThreadPtr|
                    #![trigger pre.thr_mp.spec_index(t).view().indirect_free_quota_pending_1g]
                    indirect.contains(t) ==> post.thr_mp.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(c_depth)
                        == pre.thr_mp.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(c_depth)) {
                    let t = choose|t: RwLockThreadPtr|
                        #![trigger pre.thr_mp.spec_index(t).view().indirect_free_quota_pending_1g]
                        indirect.contains(t) && post.thr_mp.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(c_depth)
                            != pre.thr_mp.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(c_depth);
                    assert(pre.thr_mp.dom().contains(t)) by { reveal(container_thread_wf); };
                }
                lemma_thread_effective_quota_1g_fold_eq(direct, pre.thr_mp, post.thr_mp);
                lemma_thread_direct_pending_1g_fold_eq(direct, pre.thr_mp, post.thr_mp);
                lemma_thread_indirect_pending_1g_fold_eq_at_depth(indirect, pre.thr_mp, post.thr_mp, c_depth);
            }
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
    ensures post.inv(),
{
    reveal(reclaim_last_4k_mapping_to_cpu_cache_transition);
    assert(post.subsystems_inv()) by { reveal(pagetable_perms_wf); reveal(page_array_wf); reveal(thread_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(allocator_perms_wf); reveal(KernelK::default_pagetable_wf); };
    reclaim_last_4k_mapping_to_cpu_cache_eof_memory_management_inv(pre, post, pagetable, va, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr);
    reclaim_last_4k_mapping_to_cpu_cache_eof_process_management_inv(pre, post, pagetable, va, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, old_counter, new_counter, node_addr);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}
}
