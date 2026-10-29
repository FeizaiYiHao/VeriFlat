use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_thread_exit_destroy_spec::thread_exit_destroy_eof_transition_framing;

verus! {
proof fn thread_exit_destroy_eof_subsystems_inv(
    pre: KernelK, post: KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, proc_node_addr: usize, cache_node_addr: usize,
)
    requires
        pre.inv(),
        pre.cpu_op.view().view()[cpu_id as int] is InStep,
        thread_exit_destroy_eof_transition_framing(pre, post, cpu_id, container_ptr, process_ptr, thread_ptr, owner, allocator_ptr, proc_node_addr, cache_node_addr),
        index_valid(NUM_CPUS, cpu_id),
        progress_peer_of(pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()) is None,
        page_array_wf(post.pg_arr),
        post.cpu_arr.inv(),
        post.cpu_arr.spec_index(cpu_id).view().is_init(),
        post.cpu_arr.spec_index(cpu_id).view().view().wf(),
        pcid_needflush_wf(post.pcid_needflush),
        cpu_hw_cr3_pcid_wf(post.cpu_hw_cr3_pcid, post.cpu_arr, post.pcid_needflush),
        post.cpu_tlb.inv(),
        post.ctn_mp.perms_wf(),
        post.prc_mp.perms_wf(),
        post.prc_mp.spec_index(process_ptr).inv(),
        post.thr_mp.perms_wf(),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_ptr).wf(),
        pcid_allocator_perms_wf(post.pcid_allc_mp),
    ensures post.subsystems_inv(),
{
    reveal(thread_exit_destroy_eof_transition_framing);
    assert(cpu_array_wf(post.cpu_arr, post.dflt_pt.view())) by { reveal(cpu_array_wf); };
    assert(cpu_op_wf(post.cpu_op.view().view(), post.cpu_arr)) by { reveal(cpu_op_wf); };
    assert(cpu_offline_flags_wf(post.cpu_offline_mp, post.cpu_arr)) by { reveal(cpu_offline_flags_wf); };
    assert(container_perms_wf(post.ctn_mp)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    assert(process_perms_wf(post.prc_mp)) by { reveal(process_perms_wf); };
    assert(thread_perms_wf(post.thr_mp)) by {
        reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
        reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
    };
    assert(allocator_perms_wf(post.allc_4k_mp)) by { reveal(allocator_perms_wf); };
    reveal(KernelK::default_pagetable_wf);
}

proof fn thread_exit_destroy_eof_staged_pages(
    pre: KernelK, post: KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, proc_node_addr: usize, cache_node_addr: usize,
)
    requires
        pre.inv(),
        thread_exit_destroy_eof_transition_framing(pre, post, cpu_id, container_ptr, process_ptr, thread_ptr, owner, allocator_ptr, proc_node_addr, cache_node_addr),
        page_ptr_valid(thread_ptr),
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        pre.pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsThread }),
    ensures thread_staged_pages_wf(post.thr_mp, post.pg_arr),
{
    reveal(thread_exit_destroy_eof_transition_framing);
    let thread = pre.thr_mp.spec_index(thread_ptr).view();
    page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); page_index_roundtrip();
    assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by { vstd::set_lib::lemma_set_empty_equivalency_len(thread.temp_alloc_cache_4k.view()); reveal(thread_staged_pages_4k_wf); };
    assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by { vstd::set_lib::lemma_set_empty_equivalency_len(thread.temp_alloc_cache_2m.view()); reveal(thread_staged_pages_2m_wf); };
    assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by { vstd::set_lib::lemma_set_empty_equivalency_len(thread.temp_alloc_cache_1g.view()); reveal(thread_staged_pages_1g_wf); };
}

proof fn thread_exit_destroy_eof_page_relations(
    pre: KernelK, post: KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, proc_node_addr: usize, cache_node_addr: usize,
)
    requires
        pre.inv(),
        thread_exit_destroy_eof_transition_framing(pre, post, cpu_id, container_ptr, process_ptr, thread_ptr, owner, allocator_ptr, proc_node_addr, cache_node_addr),
        index_valid(NUM_CPUS, cpu_id),
        page_ptr_valid(thread_ptr),
        pre.thr_mp.dom().contains(thread_ptr),
        !pre.thr_mp.spec_index(thread_ptr).being_killed(),
        pre.thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().caller is None,
        pre.thr_mp.spec_index(thread_ptr).view().callee is None,
        forall|j: int| #![trigger pre.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view().spec_index(j)] 0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> pre.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view().spec_index(j) is None,
        pre.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        pre.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        pre.thr_mp.spec_index(thread_ptr).view().proc_linkedlist_node.addr() == proc_node_addr,
        pre.prc_mp.dom().contains(process_ptr),
        pre.prc_mp.spec_index(process_ptr).view().quota_4k + pre.thr_mp.spec_index(thread_ptr).view().quota_4k <= usize::MAX,
        pre.prc_mp.spec_index(process_ptr).view().quota_2m + pre.thr_mp.spec_index(thread_ptr).view().quota_2m <= usize::MAX,
        pre.prc_mp.spec_index(process_ptr).view().quota_1g + pre.thr_mp.spec_index(thread_ptr).view().quota_1g <= usize::MAX,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.dom().contains(owner),
        pre.pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().view().owning_container == owner,
        pre.pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsThread }),
        pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        pre.allc_4k_mp.dom().contains(allocator_ptr),
        !pre.cpu_arr.spec_index(cpu_id).view().being_killed(),
        pre.prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(thread_ptr),
        pre.prc_mp.spec_index(process_ptr).view().owned_threads.map().dom().contains(proc_node_addr),
        pre.prc_mp.spec_index(process_ptr).view().owned_threads.map().spec_index(proc_node_addr) == thread_ptr,
        !pre.prc_mp.spec_index(process_ptr).being_killed(),
        pre.pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().view().free_list_node_storage.addr() == cache_node_addr,
        !pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(cache_node_addr),
        pre.pcid_allc_mp.dom().contains(pre.ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator),
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
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp),
        post.allocator_free_pages_wf(),
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr),
        container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr),
        container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr),
{
    reveal(thread_exit_destroy_eof_transition_framing);
    let page_index = page_ptr2page_index(thread_ptr);
    let thread = pre.thr_mp.spec_index(thread_ptr).view();
    page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); page_index_roundtrip();
    assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_4k_mp, post.allc_4k_mp);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_1g_mp, post.allc_1g_mp);
    };
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { page_pagetable_wf_preserved_for_nonmapped_page_change(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr, page_index); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); };
    assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.ctn_mp, post.ctn_mp); };
    assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.prc_mp, post.prc_mp); };
    assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp)) by {
        vstd::set_lib::lemma_set_empty_equivalency_len(thread.temp_alloc_cache_4k.view()); vstd::set_lib::lemma_set_empty_equivalency_len(thread.temp_alloc_cache_2m.view());
        vstd::set_lib::lemma_set_empty_equivalency_len(thread.temp_alloc_cache_1g.view());
        reveal(page_object_owner_wf); reveal(container_page_owner_wf); reveal(thread_staged_pages_4k_wf); reveal(thread_staged_pages_2m_wf); reveal(thread_staged_pages_1g_wf);
    };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_pages_wf); page_ptr2page_index_injective(); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
    assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.pcid_allc_mp, post.pcid_allc_mp); };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
    assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { process_pagetable_match_preserved_for_process_fields_eq(pre.prc_mp, post.prc_mp, post.pt_mp); };
    assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_match); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); };
    assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { container_allocator_wf_preserved_for_owner_depth_eq(pre.ctn_mp, post.ctn_mp, pre.allc_4k_mp, post.allc_4k_mp, pre.allc_2m_mp, post.allc_2m_mp, pre.allc_1g_mp, post.allc_1g_mp); };
    assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        page_object_owner_wf_at(pre.pg_arr, pre.ctn_mp, pre.thr_mp, page_ptr2page_index(thread_ptr));
        container_thread_wf_at(pre.ctn_mp, pre.thr_mp, thread_ptr); pre.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view().to_set_ensures();
        reveal(container_kill_retire_wf); reveal(container_allocator_wf); reveal(container_uppertree_seq_wf);
    };
    assert(container_allocator_global_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by {
        reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(container_allocator_wf); reveal(allocator_free_page_ptrs_wf); reveal(page_array_wf);
        broadcast use vstd::seq_lib::lemma_seq_concat_contains_all_elements; broadcast use vstd::seq_lib::lemma_seq_contains_after_push;
        pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().insert_ensures(0, thread_ptr);
    };
    assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, page_ptr2page_index(thread_ptr)); };
    assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_ptr2page_index(thread_ptr)); };
}

proof fn thread_exit_destroy_eof_allocator_quota_wf(
    pre: KernelK, post: KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, proc_node_addr: usize, cache_node_addr: usize,
)
    requires
        pre.inv(),
        thread_exit_destroy_eof_transition_framing(pre, post, cpu_id, container_ptr, process_ptr, thread_ptr, owner, allocator_ptr, proc_node_addr, cache_node_addr),
        index_valid(NUM_CPUS, cpu_id),
        page_ptr_valid(thread_ptr),
        pre.thr_mp.dom().contains(thread_ptr),
        !pre.thr_mp.spec_index(thread_ptr).being_killed(),
        pre.thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().caller is None,
        pre.thr_mp.spec_index(thread_ptr).view().callee is None,
        forall|j: int| #![trigger pre.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view().spec_index(j)] 0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> pre.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view().spec_index(j) is None,
        pre.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        pre.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        pre.thr_mp.spec_index(thread_ptr).view().proc_linkedlist_node.addr() == proc_node_addr,
        pre.prc_mp.dom().contains(process_ptr),
        pre.prc_mp.spec_index(process_ptr).view().quota_4k + pre.thr_mp.spec_index(thread_ptr).view().quota_4k <= usize::MAX,
        pre.prc_mp.spec_index(process_ptr).view().quota_2m + pre.thr_mp.spec_index(thread_ptr).view().quota_2m <= usize::MAX,
        pre.prc_mp.spec_index(process_ptr).view().quota_1g + pre.thr_mp.spec_index(thread_ptr).view().quota_1g <= usize::MAX,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.dom().contains(owner),
        pre.pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().view().owning_container == owner,
        pre.pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsThread }),
        pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        pre.allc_4k_mp.dom().contains(allocator_ptr),
        !pre.cpu_arr.spec_index(cpu_id).view().being_killed(),
        pre.prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(thread_ptr),
        pre.prc_mp.spec_index(process_ptr).view().owned_threads.map().dom().contains(proc_node_addr),
        pre.prc_mp.spec_index(process_ptr).view().owned_threads.map().spec_index(proc_node_addr) == thread_ptr,
        !pre.prc_mp.spec_index(process_ptr).being_killed(),
        pre.pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().view().free_list_node_storage.addr() == cache_node_addr,
        !pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(cache_node_addr),
        pre.pcid_allc_mp.dom().contains(pre.ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator),
    ensures container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    reveal(thread_exit_destroy_eof_transition_framing);
    thread_perms_wf_at(pre.thr_mp, thread_ptr);
    process_thread_wf_at(pre.prc_mp, pre.thr_mp, thread_ptr);
    lemma_container_process_thread_quota_folds_remove_thread_forall(pre.rt_ctn, pre.ctn_mp, post.ctn_mp, pre.prc_mp, post.prc_mp, pre.thr_mp, post.thr_mp, container_ptr, thread_ptr, process_ptr);
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by { reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); };
    assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp)) by { reveal(container_process_allocator_quota_2m_wf); };
    assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp)) by { reveal(container_process_allocator_quota_1g_wf); };
}

proof fn thread_exit_destroy_eof_thread_relations(
    pre: KernelK, post: KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, proc_node_addr: usize, cache_node_addr: usize,
)
    requires
        pre.inv(),
        thread_exit_destroy_eof_transition_framing(pre, post, cpu_id, container_ptr, process_ptr, thread_ptr, owner, allocator_ptr, proc_node_addr, cache_node_addr),
        index_valid(NUM_CPUS, cpu_id),
        page_ptr_valid(thread_ptr),
        pre.thr_mp.dom().contains(thread_ptr),
        !pre.thr_mp.spec_index(thread_ptr).being_killed(),
        pre.thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().caller is None,
        pre.thr_mp.spec_index(thread_ptr).view().callee is None,
        pre.thr_mp.spec_index(thread_ptr).locking_thread() is Write,
        forall|u: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(u).locking_thread()]
            pre.thr_mp.dom().contains(u) && pre.thr_mp.spec_index(u).wlocked_by_thread(pre.thr_mp.spec_index(thread_ptr).locking_thread()->Write_thread_id) ==> u == thread_ptr,
        forall|j: int| #![trigger pre.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view().spec_index(j)] 0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> pre.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view().spec_index(j) is None,
        pre.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        pre.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        pre.thr_mp.spec_index(thread_ptr).view().proc_linkedlist_node.addr() == proc_node_addr,
        pre.prc_mp.dom().contains(process_ptr),
        pre.prc_mp.spec_index(process_ptr).view().quota_4k + pre.thr_mp.spec_index(thread_ptr).view().quota_4k <= usize::MAX,
        pre.prc_mp.spec_index(process_ptr).view().quota_2m + pre.thr_mp.spec_index(thread_ptr).view().quota_2m <= usize::MAX,
        pre.prc_mp.spec_index(process_ptr).view().quota_1g + pre.thr_mp.spec_index(thread_ptr).view().quota_1g <= usize::MAX,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.dom().contains(owner),
        pre.pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().view().owning_container == owner,
        pre.pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsThread }),
        pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        pre.allc_4k_mp.dom().contains(allocator_ptr),
        !pre.cpu_arr.spec_index(cpu_id).view().being_killed(),
        pre.prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(thread_ptr),
        pre.prc_mp.spec_index(process_ptr).view().owned_threads.map().dom().contains(proc_node_addr),
        pre.prc_mp.spec_index(process_ptr).view().owned_threads.map().spec_index(proc_node_addr) == thread_ptr,
        !pre.prc_mp.spec_index(process_ptr).being_killed(),
        pre.pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().view().free_list_node_storage.addr() == cache_node_addr,
        !pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(cache_node_addr),
        pre.pcid_allc_mp.dom().contains(pre.ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator),
        post.subsystems_inv(),
    ensures
        container_tree_wf(post.rt_ctn, post.ctn_mp),
        post.ctn_mp.spec_index(post.rt_ctn).view_ghost().owned_processes.view().contains(post.ctn_mp.spec_index(post.rt_ctn).view().root_process),
        container_process_wf(post.ctn_mp, post.prc_mp),
        per_container_process_tree_wf(post.ctn_mp, post.prc_mp),
        process_kill_mark_wf(post.ctn_mp, post.prc_mp),
        container_kill_mark_wf(post.ctn_mp, post.prc_mp),
        cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp),
        process_state_lock_wf(post.prc_mp),
        process_emptied_threads_wf(post.prc_mp, post.thr_mp),
        container_endpoint_wf(post.ctn_mp, post.ep_mp),
        thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp),
        thread_endpoint_queue_wf(post.thr_mp, post.ep_mp),
        thread_caller_callee_wf(post.thr_mp),
        thread_dangling_chain_end_wf(post.thr_mp),
        container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp),
        container_scheduler_wf(post.ctn_mp, post.sched_mp),
        container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp),
        container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp),
        container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp),
        process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp),
        container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp),
        container_thread_wf(post.ctn_mp, post.thr_mp),
        process_thread_wf(post.prc_mp, post.thr_mp),
{
    reveal(thread_exit_destroy_eof_transition_framing);
    let uppers = pre.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view();
    process_thread_wf_at(pre.prc_mp, pre.thr_mp, thread_ptr);
    process_perms_wf_at(pre.prc_mp, process_ptr);
    lemma_seq_remove_value_membership::<RwLockThreadPtr>();
    assert(container_tree_wf(post.rt_ctn, post.ctn_mp)) by { container_no_change_to_tree_fields_imply_wf(pre.rt_ctn, pre.ctn_mp, post.ctn_mp); };
    assert(post.ctn_mp.spec_index(post.rt_ctn).view_ghost().owned_processes.view().contains(post.ctn_mp.spec_index(post.rt_ctn).view().root_process)) by { reveal(container_root_wf); };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by {
        per_container_process_tree_wf_preserved_for_tree_fields_eq(pre.ctn_mp, pre.prc_mp, post.prc_mp);
        reveal(per_container_process_tree_wf);
    };
    assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
    assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
    assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
    assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); reveal(process_thread_wf); };
    assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { container_endpoint_wf_preserved_for_endpoint_owner_eq(pre.ctn_mp, post.ctn_mp, pre.ep_mp, post.ep_mp); };
    assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_perms_wf); reveal(thread_endpoint_ref_counter_wf); };
    assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_queue_wf); };
    assert(thread_caller_callee_wf(post.thr_mp)) by { reveal(thread_caller_callee_wf); };
    assert(thread_dangling_chain_end_wf(post.thr_mp)) by {
        thread_dangling_chain_end_on_caller_chain(pre.thr_mp, thread_ptr, Set::<RwLockThreadPtr>::empty(), pre.thr_mp.spec_index(thread_ptr).view().call_depth.view());
        reveal(thread_dangling_chain_end_wf); reveal(thread_caller_callee_wf);
    };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); reveal(container_endpoint_wf); reveal(container_thread_endpoint_wf); };
    assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { container_scheduler_wf_preserved_for_scheduler_owner_eq(pre.ctn_mp, post.ctn_mp, pre.sched_mp, post.sched_mp); };
    assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
    assert(container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp)) by { container_cpu_offline_flags_wf_preserved_for_flags_owner_eq(pre.ctn_mp, post.ctn_mp, pre.cpu_offline_mp, post.cpu_offline_mp); };
    assert(container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
    assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by {
        reveal(process_pcid_allocator_wf);
        let pcid_allocator_ptr = pre.ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator;
        if post.prc_mp.spec_index(process_ptr).view().zombie {
            pcid_allocator_perms_wf_at(pre.pcid_allc_mp, pcid_allocator_ptr);
        }
    };
    assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); };
    assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { reveal(container_thread_wf); uppers.to_set_ensures(); };
    assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { reveal(process_thread_wf); };
}

proof fn thread_exit_destroy_eof_cpu_relations(
    pre: KernelK, post: KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, proc_node_addr: usize, cache_node_addr: usize,
)
    requires
        pre.inv(),
        thread_exit_destroy_eof_transition_framing(pre, post, cpu_id, container_ptr, process_ptr, thread_ptr, owner, allocator_ptr, proc_node_addr, cache_node_addr),
        index_valid(NUM_CPUS, cpu_id),
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        pre.prc_mp.dom().contains(process_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        !pre.cpu_arr.spec_index(cpu_id).view().being_killed(),
        pre.prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(thread_ptr),
        post.subsystems_inv(),
    ensures
        container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr),
        process_cpu_wf(post.prc_mp, post.cpu_arr),
        thread_cpu_wf(post.thr_mp, post.cpu_arr),
{
    reveal(thread_exit_destroy_eof_transition_framing);
    process_perms_wf_at(pre.prc_mp, process_ptr);
    reveal(cpu_array_wf); reveal(thread_cpu_wf);
    assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); };
    assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); reveal(process_thread_wf); };
}

/// The destroyed exiting thread, its idle cpu, its zombie-marked process and container, and its page returned to the
/// owner's allocator keep the kernel invariant.
/// The exiting thread's process keeps its PCI functions and IOMMU tables, so every IOMMU relation survives the destroy step.
proof fn thread_exit_destroy_eof_iommu_relations(
    pre: KernelK, post: KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, proc_node_addr: usize, cache_node_addr: usize,
)
    requires
        pre.inv(),
        thread_exit_destroy_eof_transition_framing(pre, post, cpu_id, container_ptr, process_ptr, thread_ptr, owner, allocator_ptr, proc_node_addr, cache_node_addr),
    ensures
        iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp),
        process_pci_function_ownership_wf(post.irt.view(), post.prc_mp),
        iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp),
{
    reveal(thread_exit_destroy_eof_transition_framing);
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf_spec); reveal(iommu_root_table_process_wf); };
}

pub(super) proof fn thread_exit_destroy_eof(
    pre: KernelK, post: KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, proc_node_addr: usize, cache_node_addr: usize,
)
    requires
        pre.inv(),
        pre.cpu_op.view().view()[cpu_id as int] is InStep,
        thread_exit_destroy_eof_transition_framing(pre, post, cpu_id, container_ptr, process_ptr, thread_ptr, owner, allocator_ptr, proc_node_addr, cache_node_addr),
        index_valid(NUM_CPUS, cpu_id),
        page_ptr_valid(thread_ptr),
        pre.thr_mp.dom().contains(thread_ptr),
        !pre.thr_mp.spec_index(thread_ptr).being_killed(),
        pre.thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().caller is None,
        pre.thr_mp.spec_index(thread_ptr).view().callee is None,
        pre.thr_mp.spec_index(thread_ptr).locking_thread() is Write,
        forall|u: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(u).locking_thread()]
            pre.thr_mp.dom().contains(u) && pre.thr_mp.spec_index(u).wlocked_by_thread(pre.thr_mp.spec_index(thread_ptr).locking_thread()->Write_thread_id) ==> u == thread_ptr,
        forall|j: int| #![trigger pre.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view().spec_index(j)] 0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> pre.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view().spec_index(j) is None,
        pre.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        pre.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        progress_peer_of(pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()) is None,
        pre.thr_mp.spec_index(thread_ptr).view().proc_linkedlist_node.addr() == proc_node_addr,
        pre.prc_mp.dom().contains(process_ptr),
        pre.prc_mp.spec_index(process_ptr).view().quota_4k + pre.thr_mp.spec_index(thread_ptr).view().quota_4k <= usize::MAX,
        pre.prc_mp.spec_index(process_ptr).view().quota_2m + pre.thr_mp.spec_index(thread_ptr).view().quota_2m <= usize::MAX,
        pre.prc_mp.spec_index(process_ptr).view().quota_1g + pre.thr_mp.spec_index(thread_ptr).view().quota_1g <= usize::MAX,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.dom().contains(owner),
        pre.pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().view().owning_container == owner,
        pre.pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsThread }),
        pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        pre.allc_4k_mp.dom().contains(allocator_ptr),
        !pre.cpu_arr.spec_index(cpu_id).view().being_killed(),
        pre.prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(thread_ptr),
        pre.prc_mp.spec_index(process_ptr).view().owned_threads.map().dom().contains(proc_node_addr),
        pre.prc_mp.spec_index(process_ptr).view().owned_threads.map().spec_index(proc_node_addr) == thread_ptr,
        !pre.prc_mp.spec_index(process_ptr).being_killed(),
        pre.pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().view().free_list_node_storage.addr() == cache_node_addr,
        !pre.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(cache_node_addr),
        pre.pcid_allc_mp.dom().contains(pre.ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator),
        page_array_wf(post.pg_arr),
        post.cpu_arr.inv(),
        post.cpu_arr.spec_index(cpu_id).view().is_init(),
        post.cpu_arr.spec_index(cpu_id).view().view().wf(),
        pcid_needflush_wf(post.pcid_needflush),
        cpu_hw_cr3_pcid_wf(post.cpu_hw_cr3_pcid, post.cpu_arr, post.pcid_needflush),
        post.cpu_tlb.inv(),
        post.ctn_mp.perms_wf(),
        post.prc_mp.perms_wf(),
        post.prc_mp.spec_index(process_ptr).inv(),
        post.thr_mp.perms_wf(),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_ptr).wf(),
        pcid_allocator_perms_wf(post.pcid_allc_mp),
    ensures post.inv(),
{
    thread_exit_destroy_eof_subsystems_inv(pre, post, cpu_id, container_ptr, process_ptr, thread_ptr, owner, allocator_ptr, proc_node_addr, cache_node_addr);
    thread_exit_destroy_eof_page_relations(pre, post, cpu_id, container_ptr, process_ptr, thread_ptr, owner, allocator_ptr, proc_node_addr, cache_node_addr);
    thread_exit_destroy_eof_allocator_quota_wf(pre, post, cpu_id, container_ptr, process_ptr, thread_ptr, owner, allocator_ptr, proc_node_addr, cache_node_addr);
    thread_exit_destroy_eof_thread_relations(pre, post, cpu_id, container_ptr, process_ptr, thread_ptr, owner, allocator_ptr, proc_node_addr, cache_node_addr);
    thread_exit_destroy_eof_cpu_relations(pre, post, cpu_id, container_ptr, process_ptr, thread_ptr, owner, allocator_ptr, proc_node_addr, cache_node_addr);
    thread_exit_destroy_eof_iommu_relations(pre, post, cpu_id, container_ptr, process_ptr, thread_ptr, owner, allocator_ptr, proc_node_addr, cache_node_addr);
    reveal(thread_exit_destroy_eof_transition_framing);
    thread_exit_destroy_eof_staged_pages(pre, post, cpu_id, container_ptr, process_ptr, thread_ptr, owner, allocator_ptr, proc_node_addr, cache_node_addr);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match);
        reveal(container_cpu_wf);
    };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}

/// The destroy step, between the lock acquisitions that follow the step's start `start` and the releases that end the
/// step, gives the thread-exit fields from `start`.
pub(super) proof fn thread_exit_destroy_eof_fields(
    start: KernelK, entry: KernelK, mid: KernelK, post: KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, proc_node_addr: usize, cache_node_addr: usize,
)
    requires
        entry.inv(),
        entry == (KernelK { pg_arr: entry.pg_arr, allc_4k_mp: entry.allc_4k_mp, pcid_needflush: entry.pcid_needflush, pcid_allc_mp: entry.pcid_allc_mp, ..start }),
        kernel_container_nonlock_fields_and_quotas_unchanged(&start, &entry),
        thread_exit_destroy_eof_transition_framing(entry, mid, cpu_id, container_ptr, process_ptr, thread_ptr, owner, allocator_ptr, proc_node_addr, cache_node_addr),
        index_valid(NUM_CPUS, cpu_id),
        page_ptr_valid(thread_ptr),
        entry.thr_mp.dom().contains(thread_ptr),
        !entry.thr_mp.spec_index(thread_ptr).being_killed(),
        entry.thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        entry.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        entry.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        entry.thr_mp.spec_index(thread_ptr).view().caller is None,
        entry.thr_mp.spec_index(thread_ptr).view().callee is None,
        forall|j: int| #![trigger entry.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view().spec_index(j)] 0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> entry.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view().spec_index(j) is None,
        entry.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        entry.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        entry.thr_mp.spec_index(thread_ptr).view().proc_linkedlist_node.addr() == proc_node_addr,
        entry.prc_mp.dom().contains(process_ptr),
        entry.prc_mp.spec_index(process_ptr).view().quota_4k + entry.thr_mp.spec_index(thread_ptr).view().quota_4k <= usize::MAX,
        entry.prc_mp.spec_index(process_ptr).view().quota_2m + entry.thr_mp.spec_index(thread_ptr).view().quota_2m <= usize::MAX,
        entry.prc_mp.spec_index(process_ptr).view().quota_1g + entry.thr_mp.spec_index(thread_ptr).view().quota_1g <= usize::MAX,
        entry.ctn_mp.dom().contains(container_ptr),
        entry.ctn_mp.dom().contains(owner),
        entry.pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().view().owning_container == owner,
        entry.pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsThread }),
        entry.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        entry.allc_4k_mp.dom().contains(allocator_ptr),
        !entry.cpu_arr.spec_index(cpu_id).view().being_killed(),
        entry.prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(thread_ptr),
        entry.prc_mp.spec_index(process_ptr).view().owned_threads.map().dom().contains(proc_node_addr),
        entry.prc_mp.spec_index(process_ptr).view().owned_threads.map().spec_index(proc_node_addr) == thread_ptr,
        !entry.prc_mp.spec_index(process_ptr).being_killed(),
        entry.pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().view().free_list_node_storage.addr() == cache_node_addr,
        !entry.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(cache_node_addr),
        entry.pcid_allc_mp.dom().contains(entry.ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator),
        post == (KernelK {
            cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, pcid_needflush: post.pcid_needflush, ctn_mp: post.ctn_mp, prc_mp: post.prc_mp, pg_arr: post.pg_arr,
            allc_4k_mp: post.allc_4k_mp, pcid_allc_mp: post.pcid_allc_mp, ..mid
        }),
        post.cpu_op.view().view() == mid.cpu_op.view().view().update(cpu_id as int, cpu_op_after_step(mid.cpu_arr.spec_index(cpu_id).view().view().view().state)),
        post.cpu_arr.entries_unchanged_except(&mid.cpu_arr, cpu_id),
        post.cpu_arr.spec_index(cpu_id).view().view().view() == mid.cpu_arr.spec_index(cpu_id).view().view().view(),
        post.cpu_arr.spec_index(cpu_id).value.killer_info() == mid.cpu_arr.spec_index(cpu_id).value.killer_info(),
        post.ctn_mp.unchanged_except(&mid.ctn_mp, container_ptr),
        post.ctn_mp.spec_index(container_ptr).view() == mid.ctn_mp.spec_index(container_ptr).view(),
        post.ctn_mp.spec_index(container_ptr).view_rodata() == mid.ctn_mp.spec_index(container_ptr).view_rodata(),
        post.ctn_mp.spec_index(container_ptr).view_ghost() == mid.ctn_mp.spec_index(container_ptr).view_ghost(),
        post.ctn_mp.spec_index(container_ptr).being_killed() == mid.ctn_mp.spec_index(container_ptr).being_killed(),
        post.prc_mp.unchanged_except(&mid.prc_mp, process_ptr),
        post.prc_mp.spec_index(process_ptr).view() == mid.prc_mp.spec_index(process_ptr).view(),
        post.prc_mp.spec_index(process_ptr).view_rodata() == mid.prc_mp.spec_index(process_ptr).view_rodata(),
        post.prc_mp.spec_index(process_ptr).view_ghost() == mid.prc_mp.spec_index(process_ptr).view_ghost(),
        post.prc_mp.spec_index(process_ptr).being_killed() == mid.prc_mp.spec_index(process_ptr).being_killed(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&mid, &post),
    ensures kernel_thread_exit_fields(&start, &post, cpu_id, thread_ptr, entry.pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).view().needflush),
{
    reveal(thread_exit_destroy_eof_transition_framing); reveal(kernel_thread_exit_fields); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
    process_thread_wf_at(entry.prc_mp, entry.thr_mp, thread_ptr);
    page_ptr_roundtrip();
    reveal(container_page_owner_wf); reveal(container_allocator_wf);
    let pcid_allocator_ptr = entry.ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator;
    let zombie = mid.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() == 0;
    let pcid = entry.prc_mp.spec_index(process_ptr).view().pcid;
    assert(entry.prc_mp.spec_index(process_ptr).view_rodata().view().pcid == pcid) by { reveal(process_pagetable_match); };
    assert forall|c: RwLockContainerPtr| #![trigger mid.pcid_allc_mp.spec_index(mid.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator)] entry.ctn_mp.dom().contains(c) implies
        PcidAllocator::free_pcids(mid.pcid_allc_mp.spec_index(mid.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view())
            == if zombie && c == container_ptr {
                PcidAllocator::free_pcids(entry.pcid_allc_mp.spec_index(entry.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view()).insert(pcid)
            } else { PcidAllocator::free_pcids(entry.pcid_allc_mp.spec_index(entry.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view()) } by {
        if c != container_ptr {
            assert(entry.pcid_allc_mp.dom().contains(entry.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator)
                && entry.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator != pcid_allocator_ptr) by { reveal(container_pcid_allocator_wf); };
        } else if zombie {
            pcid_allocator_perms_wf_at(entry.pcid_allc_mp, pcid_allocator_ptr);
        }
    };
}
} // verus!
