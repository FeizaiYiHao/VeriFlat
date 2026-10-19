use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::release_endpoint_spec::release_endpoint_eof_transition_framing;

verus! {
proof fn release_endpoint_eof_subsystems_inv(
    pre: KernelK, post: KernelK, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, index: EndpointIdx, allocator_ptr: RwLockPageAllocatorPtr, node_addr: usize,
)
    requires
        pre.inv(),
        release_endpoint_eof_transition_framing(pre, post, thread_ptr, endpoint_ptr, index, allocator_ptr, node_addr),
        pre.thr_mp.dom().contains(thread_ptr),
        page_array_wf(post.pg_arr),
        container_perms_wf(post.ctn_mp),
        post.thr_mp.perms_wf(),
        post.thr_mp.spec_index(thread_ptr).inv(),
        post.ep_mp.perms_wf(),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_ptr).wf(),
    ensures post.subsystems_inv(),
{
    reveal(release_endpoint_eof_transition_framing);
    assert(thread_perms_wf(post.thr_mp)) by {
        reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked);
    };
    assert(endpoint_perms_wf(post.ep_mp)) by { reveal(endpoint_perms_wf); };
    assert(allocator_perms_wf(post.allc_4k_mp)) by { reveal(allocator_perms_wf); };
    reveal(KernelK::default_pagetable_wf);
}

proof fn release_endpoint_eof_page_relations(
    pre: KernelK, post: KernelK, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, index: EndpointIdx, owner: RwLockContainerPtr,
    allocator_ptr: RwLockPageAllocatorPtr, node_addr: usize,
)
    requires
        pre.inv(),
        release_endpoint_eof_transition_framing(pre, post, thread_ptr, endpoint_ptr, index, allocator_ptr, node_addr),
        page_ptr_valid(endpoint_ptr),
        pre.thr_mp.dom().contains(thread_ptr),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.ctn_mp.dom().contains(owner),
        pre.pg_arr.spec_index(page_ptr2page_index(endpoint_ptr)).view().view().owning_container == owner,
        pre.pg_arr.spec_index(page_ptr2page_index(endpoint_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint }),
        pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        pre.allc_4k_mp.dom().contains(allocator_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(endpoint_ptr)).view().view().free_list_node_storage.addr() == node_addr,
        !pre.allc_4k_mp.spec_index(allocator_ptr).global_pool.view().view().contains(endpoint_ptr),
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
        page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp),
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
    reveal(release_endpoint_eof_transition_framing);
    let page_index = page_ptr2page_index(endpoint_ptr);
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
    assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp)) by { reveal(page_object_owner_wf); reveal(container_page_owner_wf); };
    assert(pagetable_pages_wf(post.pt_mp, post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, post.pt_mp, pre.pg_arr, post.pg_arr); };
    assert(pagetable_pages_wf(post.it_mp, post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { cpu_set_pages_wf_preserved_for_page_state_eq(pre.cpu_set_mp, post.cpu_set_mp, pre.pg_arr, post.pg_arr); };
    assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.pcid_allc_mp, post.pcid_allc_mp); };
    assert(thread_staged_pages_wf(post.thr_mp, post.pg_arr)) by {
        thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
    };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { reveal(endpoint_pages_wf); };
    assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        container_allocator_wf_preserved_for_owner_depth_eq(pre.ctn_mp, post.ctn_mp, pre.allc_4k_mp, post.allc_4k_mp, pre.allc_2m_mp, post.allc_2m_mp, pre.allc_1g_mp, post.allc_1g_mp);
    };
    assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by {
        reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(container_allocator_wf);
        reveal(allocator_free_page_ptrs_wf);
        pre.allc_4k_mp.spec_index(allocator_ptr).global_pool.view().view().insert_ensures(0, endpoint_ptr);
    };
    assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, page_index); };
    assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_index); };
}

proof fn release_endpoint_eof_allocator_quota_wf(
    pre: KernelK, post: KernelK, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, index: EndpointIdx, allocator_ptr: RwLockPageAllocatorPtr, node_addr: usize,
)
    requires
        pre.inv(),
        release_endpoint_eof_transition_framing(pre, post, thread_ptr, endpoint_ptr, index, allocator_ptr, node_addr),
        pre.thr_mp.dom().contains(thread_ptr),
    ensures container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    reveal(release_endpoint_eof_transition_framing);
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by {
        container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(pre.ctn_mp, pre.prc_mp, pre.thr_mp, post.thr_mp, pre.allc_4k_mp);
        reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf);
    };
    assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp)) by {
        container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(pre.ctn_mp, pre.prc_mp, pre.thr_mp, post.thr_mp, pre.allc_2m_mp);
        container_process_allocator_quota_2m_wf_preserved_for_container_allocator_eq(pre.ctn_mp, post.ctn_mp, post.prc_mp, post.thr_mp, pre.allc_2m_mp, post.allc_2m_mp, pre.allc_4k_mp, pre.allc_1g_mp);
    };
    assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp)) by {
        reveal(container_process_allocator_quota_1g_wf); reveal(container_thread_wf);
        lemma_thread_effective_quota_1g_fold_sum_eq_forall();
        lemma_thread_pending_1g_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp);
    };
}

proof fn release_endpoint_eof_process_relations(
    pre: KernelK, post: KernelK, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, index: EndpointIdx, allocator_ptr: RwLockPageAllocatorPtr, node_addr: usize,
)
    requires
        pre.inv(),
        release_endpoint_eof_transition_framing(pre, post, thread_ptr, endpoint_ptr, index, allocator_ptr, node_addr),
        index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).view().state is RUNNING || pre.thr_mp.spec_index(thread_ptr).view().state is KILLED,
        pre.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[index as int] == Some(endpoint_ptr),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view() == set![(thread_ptr, index)],
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view() == Seq::<RwLockThreadPtr>::empty(),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(release_endpoint_eof_transition_framing);
    assert(container_tree_wf(post.rt_ctn, post.ctn_mp)) by { container_no_change_to_tree_fields_imply_wf(pre.rt_ctn, pre.ctn_mp, post.ctn_mp); };
    assert(post.ctn_mp.spec_index(post.rt_ctn).view_ghost().owned_processes.view().contains(post.ctn_mp.spec_index(post.rt_ctn).view().root_process)) by { reveal(container_root_wf); };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { reveal(per_container_process_tree_wf); };
    assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
    assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
    assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
    assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { reveal(container_endpoint_wf); };
    assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { container_cpu_wf_preserved_for_container_cpu_fields_eq(pre.ctn_mp, post.ctn_mp, post.cpu_set_mp, post.cpu_arr); };
    assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { thread_perms_wf_at(pre.thr_mp, thread_ptr); reveal(thread_endpoint_ref_counter_wf); };
    assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_queue_wf); };
    assert(thread_caller_callee_wf(post.thr_mp)) by { thread_caller_callee_wf_preserved_for_call_link_eq(pre.thr_mp, post.thr_mp); };
    assert(thread_dangling_chain_end_wf(post.thr_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thr_mp, post.thr_mp); };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by {
        thread_perms_wf_at(pre.thr_mp, thread_ptr); reveal(container_thread_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(container_endpoint_wf);
    };
    assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { container_scheduler_wf_preserved_for_scheduler_owner_eq(pre.ctn_mp, post.ctn_mp, pre.sched_mp, post.sched_mp); };
    assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
    assert(container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp)) by { container_cpu_offline_flags_wf_preserved_for_flags_owner_eq(pre.ctn_mp, post.ctn_mp, pre.cpu_offline_mp, post.cpu_offline_mp); };
    assert(container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
    assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); };
    assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { container_thread_scheduler_wf_preserved_for_scheduled_thread_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp); };
    assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { container_thread_wf_preserved_for_container_thread_link_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp); };
    assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { process_thread_wf_preserved_for_process_thread_link_eq(pre.prc_mp, post.prc_mp, pre.thr_mp, post.thr_mp); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); reveal(process_thread_wf); };
    assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_running_thread_eq(pre.thr_mp, post.thr_mp, pre.cpu_arr, post.cpu_arr); };
}

/// The cleared last reference, the removed endpoint, and its page returned to the owner's global pool keep the kernel invariant.
pub(super) proof fn release_endpoint_eof(
    pre: KernelK, post: KernelK, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, index: EndpointIdx, owner: RwLockContainerPtr,
    allocator_ptr: RwLockPageAllocatorPtr, node_addr: usize,
)
    requires
        pre.inv(),
        release_endpoint_eof_transition_framing(pre, post, thread_ptr, endpoint_ptr, index, allocator_ptr, node_addr),
        index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        page_ptr_valid(endpoint_ptr),
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).view().state is RUNNING || pre.thr_mp.spec_index(thread_ptr).view().state is KILLED,
        pre.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[index as int] == Some(endpoint_ptr),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view() == set![(thread_ptr, index)],
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view() == Seq::<RwLockThreadPtr>::empty(),
        pre.ctn_mp.dom().contains(owner),
        pre.pg_arr.spec_index(page_ptr2page_index(endpoint_ptr)).view().view().owning_container == owner,
        pre.pg_arr.spec_index(page_ptr2page_index(endpoint_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint }),
        pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        pre.allc_4k_mp.dom().contains(allocator_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(endpoint_ptr)).view().view().free_list_node_storage.addr() == node_addr,
        !pre.allc_4k_mp.spec_index(allocator_ptr).global_pool.view().view().contains(endpoint_ptr),
        page_array_wf(post.pg_arr),
        container_perms_wf(post.ctn_mp),
        post.thr_mp.perms_wf(),
        post.thr_mp.spec_index(thread_ptr).inv(),
        post.ep_mp.perms_wf(),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_ptr).wf(),
    ensures post.inv(),
{
    release_endpoint_eof_subsystems_inv(pre, post, thread_ptr, endpoint_ptr, index, allocator_ptr, node_addr);
    release_endpoint_eof_page_relations(pre, post, thread_ptr, endpoint_ptr, index, owner, allocator_ptr, node_addr);
    release_endpoint_eof_allocator_quota_wf(pre, post, thread_ptr, endpoint_ptr, index, allocator_ptr, node_addr);
    assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        reveal(release_endpoint_eof_transition_framing); page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
        page_object_owner_wf_at(pre.pg_arr, pre.ctn_mp, pre.thr_mp, page_ptr2page_index(endpoint_ptr));
        container_thread_endpoint_wf_at(pre.ctn_mp, pre.thr_mp, pre.ep_mp, thread_ptr, index); container_thread_wf_at(pre.ctn_mp, pre.thr_mp, thread_ptr);
        reveal(container_endpoint_wf); reveal(container_kill_retire_wf); reveal(container_allocator_wf);
    };
    release_endpoint_eof_process_relations(pre, post, thread_ptr, endpoint_ptr, index, allocator_ptr, node_addr);
    reveal(release_endpoint_eof_transition_framing);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match);
        reveal(container_cpu_wf);
    };
}

/// The release, between the lock acquisitions that follow the endpoint lock at `start` and the releases that end it, gives the
/// released-endpoint fields from `start`.
pub(super) proof fn release_endpoint_eof_fields(
    start: KernelK, entry: KernelK, mid: KernelK, post: KernelK, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, index: EndpointIdx,
    owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, node_addr: usize,
)
    requires
        entry.inv(),
        entry == (KernelK { pg_arr: entry.pg_arr, allc_4k_mp: entry.allc_4k_mp, ..start }),
        kernel_container_nonlock_fields_and_quotas_unchanged(&start, &entry),
        release_endpoint_eof_transition_framing(entry, mid, thread_ptr, endpoint_ptr, index, allocator_ptr, node_addr),
        page_ptr_valid(endpoint_ptr),
        entry.ctn_mp.dom().contains(owner),
        entry.pg_arr.spec_index(page_ptr2page_index(endpoint_ptr)).view().view().owning_container == owner,
        entry.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        post == (KernelK { pg_arr: post.pg_arr, allc_4k_mp: post.allc_4k_mp, ..mid }),
        kernel_container_nonlock_fields_and_quotas_unchanged(&mid, &post),
    ensures
        post == (KernelK { ctn_mp: post.ctn_mp, thr_mp: post.thr_mp, ep_mp: post.ep_mp, pg_arr: post.pg_arr, allc_4k_mp: post.allc_4k_mp, ..start }),
        post.thr_mp.unchanged_except(&start.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { endpoint_descriptors: post.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors, ..start.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view() == start.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view().update(index as int, None),
        post.thr_mp.spec_index(thread_ptr).locking_thread() == start.thr_mp.spec_index(thread_ptr).locking_thread(),
        post.thr_mp.spec_index(thread_ptr).being_killed() == start.thr_mp.spec_index(thread_ptr).being_killed(),
        post.ep_mp.dom() == start.ep_mp.dom().remove(endpoint_ptr),
        forall|e: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(e)] post.ep_mp.dom().contains(e) ==> post.ep_mp.spec_index(e) == start.ep_mp.spec_index(e),
        post.ctn_mp.dom() == start.ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)]
            start.ctn_mp.dom().contains(c) ==> {
                let a = start.ctn_mp.spec_index(c);
                let b = post.ctn_mp.spec_index(c);
                &&& b.view() == a.view()
                &&& b.view_rodata() == a.view_rodata()
                &&& b.locking_thread() == a.locking_thread()
                &&& b.being_killed() == a.being_killed()
                &&& b.killer_info() == a.killer_info()
                &&& b.view_ghost() == if c == start.ep_mp.spec_index(endpoint_ptr).view().owning_container {
                        ContainerGhost { owned_endpoints: Ghost(a.view_ghost().owned_endpoints.view().remove(endpoint_ptr)), ..a.view_ghost() }
                    } else { a.view_ghost() }
                &&& post.allc_4k_mp.spec_index(a.view_rodata().view().allocator_ptr_4k).quota.view().view() as int
                    == start.allc_4k_mp.spec_index(a.view_rodata().view().allocator_ptr_4k).quota.view().view() as int + if a.view().owned_pages.view().contains(endpoint_ptr) { 1int } else { 0int }
            },
{
    reveal(release_endpoint_eof_transition_framing); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
    page_ptr_roundtrip();
    reveal(container_page_owner_wf); reveal(container_allocator_wf);
}
} // verus!
