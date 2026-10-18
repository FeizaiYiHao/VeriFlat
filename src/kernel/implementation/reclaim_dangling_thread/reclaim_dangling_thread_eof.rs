use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::reclaim_dangling_thread_spec::reclaim_dangling_thread_transition;

verus! {
proof fn reclaim_dangling_thread_eof_subsystems_inv(
    pre: KernelK, post: KernelK, cpu_id: CpuId, dangling_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, cache_node_addr: usize,
)
    requires
        pre.inv(),
        reclaim_dangling_thread_transition(pre, post, cpu_id, dangling_ptr, owner, allocator_ptr, cache_node_addr),
        page_array_wf(post.pg_arr),
        container_perms_wf(post.ctn_mp),
        post.thr_mp.perms_wf(),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_ptr).wf(),
    ensures post.subsystems_inv(),
{
    reveal(reclaim_dangling_thread_transition);
    assert(thread_perms_wf(post.thr_mp)) by {
        reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
    };
    assert(allocator_perms_wf(post.allc_4k_mp)) by { reveal(allocator_perms_wf); };
    reveal(KernelK::default_pagetable_wf);
}

proof fn reclaim_dangling_thread_eof_page_relations(
    pre: KernelK, post: KernelK, cpu_id: CpuId, dangling_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, cache_node_addr: usize,
)
    requires
        pre.inv(),
        reclaim_dangling_thread_transition(pre, post, cpu_id, dangling_ptr, owner, allocator_ptr, cache_node_addr),
        post.subsystems_inv(),
    ensures
        allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_page_owner_wf(post.ctn_mp, post.pg_arr),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
        page_pagetable_wf(post.pt_mp, post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
        container_pages_wf(post.pg_arr, post.ctn_mp),
        process_pages_wf(post.pg_arr, post.prc_mp),
        process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp),
        pagetable_pages_wf(post.pt_mp, post.pg_arr),
        pagetable_pages_wf(post.it_mp, post.pg_arr),
        thread_pages_wf(post.thr_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp),
        thread_staged_pages_wf(post.thr_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
        post.allocator_free_pages_wf(),
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr),
        container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr),
        container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr),
{
    reveal(reclaim_dangling_thread_transition);
    let page_index = page_ptr2page_index(dangling_ptr);
    let dangling = pre.thr_mp.spec_index(dangling_ptr).view();
    page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); page_index_roundtrip();
    assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_4k_mp, post.allc_4k_mp);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_1g_mp, post.allc_1g_mp);
    };
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(page_pagetable_wf(post.pt_mp, post.pg_arr)) by { page_pagetable_wf_preserved_for_nonmapped_page_change(pre.pt_mp, post.pt_mp, pre.pg_arr, post.pg_arr, page_index); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); };
    assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.ctn_mp, post.ctn_mp); };
    assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.prc_mp, post.prc_mp); };
    assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    assert(pagetable_pages_wf(post.pt_mp, post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, post.pt_mp, pre.pg_arr, post.pg_arr); };
    assert(pagetable_pages_wf(post.it_mp, post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_pages_wf); page_ptr2page_index_injective(); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
    assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.pcid_allc_mp, post.pcid_allc_mp); };
    assert(thread_staged_pages_wf(post.thr_mp, post.pg_arr)) by {
        vstd::set_lib::lemma_set_empty_equivalency_len(dangling.temp_alloc_cache_4k.view());
        vstd::set_lib::lemma_set_empty_equivalency_len(dangling.temp_alloc_cache_2m.view());
        vstd::set_lib::lemma_set_empty_equivalency_len(dangling.temp_alloc_cache_1g.view());
        reveal(thread_staged_pages_4k_wf); reveal(thread_staged_pages_2m_wf); reveal(thread_staged_pages_1g_wf);
    };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
    assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        container_allocator_wf_preserved_for_owner_depth_eq(pre.ctn_mp, post.ctn_mp, pre.allc_4k_mp, post.allc_4k_mp, pre.allc_2m_mp, post.allc_2m_mp, pre.allc_1g_mp, post.allc_1g_mp);
    };
    assert(container_allocator_global_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by {
        reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(container_allocator_wf); reveal(allocator_free_page_ptrs_wf); reveal(page_array_wf);
        broadcast use vstd::seq_lib::lemma_seq_concat_contains_all_elements; broadcast use vstd::seq_lib::lemma_seq_contains_after_push;
        pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().insert_ensures(0, dangling_ptr);
    };
    assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, page_index); };
    assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_index); };
}

proof fn reclaim_dangling_thread_eof_allocator_quota_wf(
    pre: KernelK, post: KernelK, cpu_id: CpuId, dangling_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, cache_node_addr: usize,
)
    requires
        pre.inv(),
        reclaim_dangling_thread_transition(pre, post, cpu_id, dangling_ptr, owner, allocator_ptr, cache_node_addr),
    ensures container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    reveal(reclaim_dangling_thread_transition);
    thread_perms_wf_at(pre.thr_mp, dangling_ptr);
    lemma_container_thread_quota_folds_remove_empty_thread_forall(pre.rt_ctn, pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, pre.thr_mp.spec_index(dangling_ptr).view().owning_container, dangling_ptr);
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by { reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); };
    assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp)) by { reveal(container_process_allocator_quota_2m_wf); };
    assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp)) by { reveal(container_process_allocator_quota_1g_wf); };
}

proof fn reclaim_dangling_thread_eof_thread_relations(
    pre: KernelK, post: KernelK, cpu_id: CpuId, dangling_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, cache_node_addr: usize,
)
    requires
        pre.inv(),
        reclaim_dangling_thread_transition(pre, post, cpu_id, dangling_ptr, owner, allocator_ptr, cache_node_addr),
        post.subsystems_inv(),
    ensures
        container_tree_wf(post.rt_ctn, post.ctn_mp),
        post.ctn_mp.spec_index(post.rt_ctn).view_ghost().owned_processes.view().contains(post.ctn_mp.spec_index(post.rt_ctn).view().root_process),
        container_process_wf(post.ctn_mp, post.prc_mp),
        per_container_process_tree_wf(post.ctn_mp, post.prc_mp),
        container_endpoint_wf(post.ctn_mp, post.ep_mp),
        container_scheduler_wf(post.ctn_mp, post.sched_mp),
        container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp),
        container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp),
        container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp),
        process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp),
        thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp),
        thread_endpoint_queue_wf(post.thr_mp, post.ep_mp),
        thread_caller_callee_wf(post.thr_mp),
        container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp),
        container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp),
        container_thread_wf(post.ctn_mp, post.thr_mp),
        process_thread_wf(post.prc_mp, post.thr_mp),
        process_emptied_threads_wf(post.prc_mp, post.thr_mp),
        container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr),
        thread_cpu_wf(post.thr_mp, post.cpu_arr),
{
    reveal(reclaim_dangling_thread_transition);
    let uppers = pre.ctn_mp.spec_index(pre.thr_mp.spec_index(dangling_ptr).view().owning_container).view_ghost().uppertree_seq.view();
    assert(container_tree_wf(post.rt_ctn, post.ctn_mp)) by { container_no_change_to_tree_fields_imply_wf(pre.rt_ctn, pre.ctn_mp, post.ctn_mp); };
    assert(post.ctn_mp.spec_index(post.rt_ctn).view_ghost().owned_processes.view().contains(post.ctn_mp.spec_index(post.rt_ctn).view().root_process)) by { reveal(container_root_wf); };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { reveal(per_container_process_tree_wf); };
    assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { container_endpoint_wf_preserved_for_endpoint_owner_eq(pre.ctn_mp, post.ctn_mp, pre.ep_mp, post.ep_mp); };
    assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { container_scheduler_wf_preserved_for_scheduler_owner_eq(pre.ctn_mp, post.ctn_mp, pre.sched_mp, post.sched_mp); };
    assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
    assert(container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp)) by { container_cpu_offline_flags_wf_preserved_for_flags_owner_eq(pre.ctn_mp, post.ctn_mp, pre.cpu_offline_mp, post.cpu_offline_mp); };
    assert(container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
    assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); };
    assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_perms_wf); reveal(thread_endpoint_ref_counter_wf); };
    assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_queue_wf); };
    assert(thread_caller_callee_wf(post.thr_mp)) by { reveal(thread_caller_callee_wf); };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); reveal(container_endpoint_wf); reveal(container_thread_endpoint_wf); };
    assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); };
    assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { reveal(container_thread_wf); uppers.to_set_ensures(); };
    assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { reveal(process_thread_wf); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); reveal(process_thread_wf); };
    assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr) && thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { reveal(container_cpu_wf); reveal(cpu_array_wf); reveal(thread_cpu_wf); };
}

/// The reclaimed dangling thread and its page returned to the owner's allocator keep the kernel invariant.
pub(super) proof fn reclaim_dangling_thread_eof(
    pre: KernelK, post: KernelK, cpu_id: CpuId, dangling_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, cache_node_addr: usize,
)
    requires
        pre.inv(),
        reclaim_dangling_thread_transition(pre, post, cpu_id, dangling_ptr, owner, allocator_ptr, cache_node_addr),
        page_array_wf(post.pg_arr),
        container_perms_wf(post.ctn_mp),
        post.thr_mp.perms_wf(),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_ptr).wf(),
    ensures post.inv(),
{
    reclaim_dangling_thread_eof_subsystems_inv(pre, post, cpu_id, dangling_ptr, owner, allocator_ptr, cache_node_addr);
    reclaim_dangling_thread_eof_page_relations(pre, post, cpu_id, dangling_ptr, owner, allocator_ptr, cache_node_addr);
    reclaim_dangling_thread_eof_allocator_quota_wf(pre, post, cpu_id, dangling_ptr, owner, allocator_ptr, cache_node_addr);
    reclaim_dangling_thread_eof_thread_relations(pre, post, cpu_id, dangling_ptr, owner, allocator_ptr, cache_node_addr);
    reveal(reclaim_dangling_thread_transition);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match);
        reveal(container_cpu_wf);
    };
}

/// The reclamation, between the lock acquisitions that follow the step's start `start` and the releases that end the
/// step, gives the reclaimed-dangling-thread fields from `start`.
pub(super) proof fn reclaim_dangling_thread_eof_fields(
    start: KernelK, entry: KernelK, mid: KernelK, post: KernelK, cpu_id: CpuId, dangling_ptr: RwLockThreadPtr, owner: RwLockContainerPtr,
    allocator_ptr: RwLockPageAllocatorPtr, cache_node_addr: usize,
)
    requires
        entry.inv(),
        entry == (KernelK { pg_arr: entry.pg_arr, allc_4k_mp: entry.allc_4k_mp, ..start }),
        kernel_container_nonlock_fields_and_quotas_unchanged(&start, &entry),
        reclaim_dangling_thread_transition(entry, mid, cpu_id, dangling_ptr, owner, allocator_ptr, cache_node_addr),
        post == (KernelK { pg_arr: post.pg_arr, allc_4k_mp: post.allc_4k_mp, ..mid }),
        kernel_container_nonlock_fields_and_quotas_unchanged(&mid, &post),
    ensures
        kernel_dangling_thread_reclaimed_fields(&start, &post, dangling_ptr),
        post.cpu_arr == start.cpu_arr,
        post.prc_mp == start.prc_mp,
        post.thr_mp.dom() == start.thr_mp.dom().remove(dangling_ptr),
        forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)] post.thr_mp.dom().contains(t) ==> post.thr_mp.spec_index(t) == start.thr_mp.spec_index(t),
        post.ctn_mp.dom() == start.ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)] post.ctn_mp.dom().contains(c) ==> {
            &&& post.ctn_mp.spec_index(c).view() == start.ctn_mp.spec_index(c).view()
            &&& post.ctn_mp.spec_index(c).view_rodata() == start.ctn_mp.spec_index(c).view_rodata()
            &&& post.ctn_mp.spec_index(c).locking_thread() == start.ctn_mp.spec_index(c).locking_thread()
            &&& post.ctn_mp.spec_index(c).being_killed() == start.ctn_mp.spec_index(c).being_killed()
        },
{
    reveal(reclaim_dangling_thread_transition); reveal(kernel_dangling_thread_reclaimed_fields); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
    page_ptr_roundtrip();
    reveal(container_page_owner_wf); reveal(container_allocator_wf);
}
} // verus!
