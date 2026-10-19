use vstd::prelude::*;
use crate::*;

verus! {
/// The 4K quota commit: the process gains `alloc_amount` 4K quota and the 4K allocator's quota loses it; nothing else changes.
#[verifier::opaque]
pub(super) open spec fn commit_alloc_quota_4k_eof_transition_framing(pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, alloc_ptr_4k: RwLockPageAllocatorPtr, alloc_amount: usize) -> bool {
    let old_process = pre.prc_mp.spec_index(process_ptr);
    let new_process = post.prc_mp.spec_index(process_ptr);
    let old_alloc = pre.allc_4k_mp.spec_index(alloc_ptr_4k);
    let new_alloc = post.allc_4k_mp.spec_index(alloc_ptr_4k);
    &&& *post == (KernelK { prc_mp: post.prc_mp, allc_4k_mp: post.allc_4k_mp, ..*pre })
    &&& post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr)
    &&& new_process.is_init() == old_process.is_init()
    &&& new_process.view_rodata() == old_process.view_rodata()
    &&& new_process.view_ghost() == old_process.view_ghost()
    &&& new_process.locking_thread() == old_process.locking_thread()
    &&& new_process.being_killed() == old_process.being_killed()
    &&& new_process.killer_info() == old_process.killer_info()
    &&& new_process.view() == (Process { quota_4k: new_process.view().quota_4k, ..old_process.view() })
    &&& new_process.view().quota_4k == old_process.view().quota_4k + alloc_amount
    &&& post.allc_4k_mp.unchanged_except(&pre.allc_4k_mp, alloc_ptr_4k)
    &&& new_alloc.quota.is_init() == old_alloc.quota.is_init()
    &&& new_alloc.quota.view_rodata() == old_alloc.quota.view_rodata()
    &&& new_alloc.quota.view_ghost() == old_alloc.quota.view_ghost()
    &&& new_alloc.quota.locking_thread() == old_alloc.quota.locking_thread()
    &&& new_alloc.quota.being_killed() == old_alloc.quota.being_killed()
    &&& new_alloc.cpu_caches == old_alloc.cpu_caches
    &&& new_alloc.global_pool == old_alloc.global_pool
    &&& new_alloc.owning_container == old_alloc.owning_container
    &&& new_alloc.total_free_pages == old_alloc.total_free_pages
    &&& new_alloc.quota.view() == (AllocatorQuota { value: new_alloc.quota.view().value, ..old_alloc.quota.view() })
    &&& new_alloc.quota.view().value + alloc_amount == old_alloc.quota.view().value
}

/// Closes every kernel invariant after the 4K quota commit from the entry invariants, the summary, and the
/// permission maps the two borrows guarantee; also states each container's allocator quota change, which needs allocator-pointer injectivity.
pub(super) proof fn commit_alloc_quota_4k_eof(pre: &KernelK, post: &KernelK, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, alloc_ptr_4k: RwLockPageAllocatorPtr, alloc_amount: usize)
    requires
        pre.inv(),
        commit_alloc_quota_4k_eof_transition_framing(pre, post, process_ptr, alloc_ptr_4k, alloc_amount),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
        pre.prc_mp.spec_index(process_ptr).view().state.view() is Running,
        post.prc_mp.perms_wf(),
        post.allc_4k_mp.perms_wf(),
    ensures
        post.inv(),
        forall|c: RwLockContainerPtr| #![trigger post.allc_4k_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k)]
            pre.ctn_mp.dom().contains(c) ==> post.allc_4k_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).quota.view().view() as int
            == pre.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).quota.view().view() as int - if c == container_ptr { alloc_amount as int } else { 0 },
{
    reveal(commit_alloc_quota_4k_eof_transition_framing);
    assert(allocator_perms_wf(post.allc_4k_mp) && post.allc_4k_mp.spec_index(alloc_ptr_4k).wf()) by { reveal(allocator_perms_wf); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(process_perms_wf); };
    assert(post.memory_management_inv()) by {
        assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { lemma_allocator_pages_wf_preserved_for_allocator_invariant_fields_except_quota_forall(); };
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { lemma_container_process_page_pagetable_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { lemma_page_iommu_table_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
        assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { lemma_process_pages_wf_preserved_for_process_domain_eq_forall(); };
        assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(*pre, *post); };
        assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by {
            reveal(container_process_allocator_quota_4k_wf); reveal(container_process_wf); reveal(container_allocator_wf);
            lemma_process_effective_quota_4k_fold_change_by_forall(process_ptr, alloc_amount as int);
            lemma_process_effective_quota_4k_fold_sum_eq_forall();
        };
        assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp)) by { container_process_allocator_quota_2m_wf_preserved_for_process_2m_fields(post.ctn_mp, post.thr_mp, post.allc_2m_mp, pre.prc_mp, post.prc_mp); };
        assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp)) by { container_process_allocator_quota_1g_wf_preserved_for_process_1g_fields(post.ctn_mp, post.thr_mp, post.allc_1g_mp, pre.prc_mp, post.prc_mp); };
        assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { lemma_container_allocator_wf_preserved_for_allocator_invariant_fields_except_quota_forall(); };
        assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by { lemma_allocator_free_page_ptrs_wf_preserved_for_pool_and_cache_contents_forall(); };
        assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { lemma_process_pagetable_match_preserved_for_process_pagetable_fields_forall(); };
        assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { lemma_process_iommu_table_match_preserved_for_process_iommu_table_fields_forall(); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.it_mp)) by { reveal(process_emptied_tables_wf); };
        assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { lemma_container_allocator_free_4k_page_wf_preserved_for_lock_op(*pre, *post); };
    };
    assert(post.process_management_inv()) by {
        assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
        assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
        assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
        assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { lemma_process_pcid_allocator_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
        assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { lemma_container_process_wf_preserved_for_process_rodata_forall(); };
        assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { lemma_per_container_process_tree_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
        assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { lemma_process_cpu_wf_preserved_for_process_pagetable_fields_forall(); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { lemma_process_thread_wf_preserved_for_process_thread_membership_fields_forall(); };
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { lemma_iommu_root_table_process_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { lemma_process_pci_function_ownership_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { lemma_iommu_tlb_wf_spec_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(iommu_table_lock_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { iommu_table_lock_wf_preserved_for_root_and_process_fields_eq(pre.irt.view(), post.irt.view(), pre.prc_mp, post.prc_mp, post.it_mp); };
    reveal(container_allocator_wf);
}

/// The 2M quota commit: the process gains `alloc_amount` 2M quota and the 2M allocator's quota loses it; nothing else changes.
#[verifier::opaque]
pub(super) open spec fn commit_alloc_quota_2m_eof_transition_framing(pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, alloc_ptr_2m: RwLockPageAllocatorPtr, alloc_amount: usize) -> bool {
    let old_process = pre.prc_mp.spec_index(process_ptr);
    let new_process = post.prc_mp.spec_index(process_ptr);
    let old_alloc = pre.allc_2m_mp.spec_index(alloc_ptr_2m);
    let new_alloc = post.allc_2m_mp.spec_index(alloc_ptr_2m);
    &&& *post == (KernelK { prc_mp: post.prc_mp, allc_2m_mp: post.allc_2m_mp, ..*pre })
    &&& post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr)
    &&& new_process.is_init() == old_process.is_init()
    &&& new_process.view_rodata() == old_process.view_rodata()
    &&& new_process.view_ghost() == old_process.view_ghost()
    &&& new_process.locking_thread() == old_process.locking_thread()
    &&& new_process.being_killed() == old_process.being_killed()
    &&& new_process.killer_info() == old_process.killer_info()
    &&& new_process.view() == (Process { quota_2m: new_process.view().quota_2m, ..old_process.view() })
    &&& new_process.view().quota_2m == old_process.view().quota_2m + alloc_amount
    &&& post.allc_2m_mp.unchanged_except(&pre.allc_2m_mp, alloc_ptr_2m)
    &&& new_alloc.quota.is_init() == old_alloc.quota.is_init()
    &&& new_alloc.quota.view_rodata() == old_alloc.quota.view_rodata()
    &&& new_alloc.quota.view_ghost() == old_alloc.quota.view_ghost()
    &&& new_alloc.quota.locking_thread() == old_alloc.quota.locking_thread()
    &&& new_alloc.quota.being_killed() == old_alloc.quota.being_killed()
    &&& new_alloc.cpu_caches == old_alloc.cpu_caches
    &&& new_alloc.global_pool == old_alloc.global_pool
    &&& new_alloc.owning_container == old_alloc.owning_container
    &&& new_alloc.total_free_pages == old_alloc.total_free_pages
    &&& new_alloc.quota.view() == (AllocatorQuota { value: new_alloc.quota.view().value, ..old_alloc.quota.view() })
    &&& new_alloc.quota.view().value + alloc_amount == old_alloc.quota.view().value
}

/// Closes every kernel invariant after the 2M quota commit from the entry invariants, the summary, and the
/// permission maps the two borrows guarantee; also states each container's allocator quota change, which needs allocator-pointer injectivity.
pub(super) proof fn commit_alloc_quota_2m_eof(pre: &KernelK, post: &KernelK, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, alloc_ptr_2m: RwLockPageAllocatorPtr, alloc_amount: usize)
    requires
        pre.inv(),
        commit_alloc_quota_2m_eof_transition_framing(pre, post, process_ptr, alloc_ptr_2m, alloc_amount),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m == alloc_ptr_2m,
        pre.prc_mp.spec_index(process_ptr).view().state.view() is Running,
        post.prc_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
    ensures
        post.inv(),
        forall|c: RwLockContainerPtr| #![trigger post.allc_2m_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m)]
            pre.ctn_mp.dom().contains(c) ==> post.allc_2m_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m).quota.view().view() as int
            == pre.allc_2m_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m).quota.view().view() as int - if c == container_ptr { alloc_amount as int } else { 0 },
{
    reveal(commit_alloc_quota_2m_eof_transition_framing);
    assert(allocator_perms_wf(post.allc_2m_mp) && post.allc_2m_mp.spec_index(alloc_ptr_2m).wf()) by { reveal(allocator_perms_wf); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(process_perms_wf); };
    assert(post.memory_management_inv()) by {
        assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp); };
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { lemma_container_process_page_pagetable_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { lemma_page_iommu_table_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
        assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { lemma_process_pages_wf_preserved_for_process_domain_eq_forall(); };
        assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(*pre, *post); };
        assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by { container_process_allocator_quota_4k_wf_preserved_for_process_4k_fields(post.ctn_mp, post.thr_mp, post.allc_4k_mp, pre.prc_mp, post.prc_mp); };
        assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp)) by {
            reveal(container_process_allocator_quota_2m_wf); reveal(container_process_wf); reveal(container_allocator_wf);
            lemma_process_effective_quota_2m_fold_change_by_forall(process_ptr, alloc_amount as int);
            lemma_process_effective_quota_2m_fold_sum_eq_forall();
        };
        assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp)) by { container_process_allocator_quota_1g_wf_preserved_for_process_1g_fields(post.ctn_mp, post.thr_mp, post.allc_1g_mp, pre.prc_mp, post.prc_mp); };
        assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { container_allocator_wf_preserved_for_owner_depth_eq(pre.ctn_mp, post.ctn_mp, pre.allc_4k_mp, post.allc_4k_mp, pre.allc_2m_mp, post.allc_2m_mp, pre.allc_1g_mp, post.allc_1g_mp); };
        assert(allocator_free_page_ptrs_wf(post.allc_2m_mp)) by { lemma_allocator_free_page_ptrs_wf_preserved_for_pool_and_cache_contents_forall(); };
        assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { lemma_process_pagetable_match_preserved_for_process_pagetable_fields_forall(); };
        assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { lemma_process_iommu_table_match_preserved_for_process_iommu_table_fields_forall(); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.it_mp)) by { reveal(process_emptied_tables_wf); };
        assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { lemma_container_allocator_free_2m_page_wf_preserved_for_lock_op(*pre, *post); };
    };
    assert(post.process_management_inv()) by {
        assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
        assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
        assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
        assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { lemma_process_pcid_allocator_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
        assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { lemma_container_process_wf_preserved_for_process_rodata_forall(); };
        assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { lemma_per_container_process_tree_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
        assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { lemma_process_cpu_wf_preserved_for_process_pagetable_fields_forall(); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { lemma_process_thread_wf_preserved_for_process_thread_membership_fields_forall(); };
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { lemma_iommu_root_table_process_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { lemma_process_pci_function_ownership_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { lemma_iommu_tlb_wf_spec_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(iommu_table_lock_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { iommu_table_lock_wf_preserved_for_root_and_process_fields_eq(pre.irt.view(), post.irt.view(), pre.prc_mp, post.prc_mp, post.it_mp); };
    reveal(container_allocator_wf);
}

/// The 4K process-to-thread commit: the process loses `alloc_amount` 4K quota and its running thread gains it; nothing else changes.
#[verifier::opaque]
pub(super) open spec fn commit_alloc_thread_quota_4k_eof_transition_framing(pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, alloc_amount: usize) -> bool {
    let old_process = pre.prc_mp.spec_index(process_ptr);
    let new_process = post.prc_mp.spec_index(process_ptr);
    let old_thread = pre.thr_mp.spec_index(thread_ptr);
    let new_thread = post.thr_mp.spec_index(thread_ptr);
    &&& *post == (KernelK { prc_mp: post.prc_mp, thr_mp: post.thr_mp, ..*pre })
    &&& post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr)
    &&& new_process.is_init() == old_process.is_init()
    &&& new_process.view_rodata() == old_process.view_rodata()
    &&& new_process.view_ghost() == old_process.view_ghost()
    &&& new_process.locking_thread() == old_process.locking_thread()
    &&& new_process.being_killed() == old_process.being_killed()
    &&& new_process.killer_info() == old_process.killer_info()
    &&& new_process.view() == (Process { quota_4k: new_process.view().quota_4k, ..old_process.view() })
    &&& new_process.view().quota_4k + alloc_amount == old_process.view().quota_4k
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr)
    &&& new_thread.is_init() == old_thread.is_init()
    &&& new_thread.view_rodata() == old_thread.view_rodata()
    &&& new_thread.view_ghost() == old_thread.view_ghost()
    &&& new_thread.locking_thread() == old_thread.locking_thread()
    &&& new_thread.being_killed() == old_thread.being_killed()
    &&& new_thread.killer_info() == old_thread.killer_info()
    &&& new_thread.view() == (Thread { quota_4k: new_thread.view().quota_4k, ..old_thread.view() })
    &&& new_thread.view().quota_4k == old_thread.view().quota_4k + alloc_amount
}

/// Closes every kernel invariant after the 4K process-to-thread commit from the entry invariants, the summary,
/// and the permission maps the two borrows guarantee.
pub(super) proof fn commit_alloc_thread_quota_4k_eof(pre: &KernelK, post: &KernelK, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, alloc_amount: usize)
    requires
        pre.inv(),
        commit_alloc_thread_quota_4k_eof_transition_framing(pre, post, process_ptr, thread_ptr, alloc_amount),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().contains(thread_ptr),
        pre.prc_mp.spec_index(process_ptr).view().state.view() is Running,
        pre.thr_mp.spec_index(thread_ptr).view().state is RUNNING,
        post.prc_mp.perms_wf(),
        post.thr_mp.perms_wf(),
    ensures post.inv(),
{
    reveal(commit_alloc_thread_quota_4k_eof_transition_framing);
    assert(post.subsystems_inv()) by {
        reveal(KernelK::default_pagetable_wf); reveal(process_perms_wf);
        reveal(thread_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_free_quota_pending_empty_unless_wlocked);
    };
    assert(post.memory_management_inv()) by {
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { lemma_container_process_page_pagetable_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { lemma_page_iommu_table_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
        assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { lemma_process_pages_wf_preserved_for_process_domain_eq_forall(); };
        assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(*pre, *post); };
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_staged_pages_wf(post.thr_mp, post.pg_arr)) by {
            thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
            thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
            thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        };
        assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { lemma_process_pagetable_match_preserved_for_process_pagetable_fields_forall(); };
        assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { lemma_process_iommu_table_match_preserved_for_process_iommu_table_fields_forall(); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.it_mp)) by { reveal(process_emptied_tables_wf); };
        assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by {
            reveal(container_process_allocator_quota_4k_wf); reveal(container_process_wf); reveal(container_thread_wf);
            lemma_process_effective_quota_4k_fold_change_by_forall(process_ptr, -(alloc_amount as int));
            lemma_process_effective_quota_4k_fold_sum_eq_forall();
            lemma_thread_effective_quota_4k_fold_change_by_forall(thread_ptr, alloc_amount as int);
            lemma_thread_effective_quota_4k_fold_sum_eq_forall();
            lemma_thread_pending_4k_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp);
        };
        assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp)) by {
            container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, pre.prc_mp, pre.thr_mp, post.thr_mp, post.allc_2m_mp);
            container_process_allocator_quota_2m_wf_preserved_for_process_2m_fields(post.ctn_mp, post.thr_mp, post.allc_2m_mp, pre.prc_mp, post.prc_mp);
        };
        assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp)) by {
            container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(post.ctn_mp, pre.prc_mp, pre.thr_mp, post.thr_mp, post.allc_1g_mp);
            container_process_allocator_quota_1g_wf_preserved_for_process_1g_fields(post.ctn_mp, post.thr_mp, post.allc_1g_mp, pre.prc_mp, post.prc_mp);
        };
    };
    assert(post.process_management_inv()) by {
        assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
        assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
        assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
        assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { lemma_process_pcid_allocator_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
        assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { lemma_container_process_wf_preserved_for_process_rodata_forall(); };
        assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { lemma_per_container_process_tree_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
        assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { lemma_process_cpu_wf_preserved_for_process_pagetable_fields_forall(); };
        assert(thread_caller_callee_wf(post.thr_mp)) by { thread_caller_callee_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { container_thread_endpoint_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { container_thread_scheduler_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp); };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { container_thread_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { process_thread_wf_preserved_for_process_thread_link_eq(pre.prc_mp, post.prc_mp, pre.thr_mp, post.thr_mp); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.cpu_arr); };
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { lemma_iommu_root_table_process_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { lemma_process_pci_function_ownership_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { lemma_iommu_tlb_wf_spec_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(iommu_table_lock_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { iommu_table_lock_wf_preserved_for_root_and_process_fields_eq(pre.irt.view(), post.irt.view(), pre.prc_mp, post.prc_mp, post.it_mp); };
}

/// The 2M process-to-thread commit: the process loses `alloc_amount` 2M quota and its running thread gains it; nothing else changes.
#[verifier::opaque]
pub(super) open spec fn commit_alloc_thread_quota_2m_eof_transition_framing(pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, alloc_amount: usize) -> bool {
    let old_process = pre.prc_mp.spec_index(process_ptr);
    let new_process = post.prc_mp.spec_index(process_ptr);
    let old_thread = pre.thr_mp.spec_index(thread_ptr);
    let new_thread = post.thr_mp.spec_index(thread_ptr);
    &&& *post == (KernelK { prc_mp: post.prc_mp, thr_mp: post.thr_mp, ..*pre })
    &&& post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr)
    &&& new_process.is_init() == old_process.is_init()
    &&& new_process.view_rodata() == old_process.view_rodata()
    &&& new_process.view_ghost() == old_process.view_ghost()
    &&& new_process.locking_thread() == old_process.locking_thread()
    &&& new_process.being_killed() == old_process.being_killed()
    &&& new_process.killer_info() == old_process.killer_info()
    &&& new_process.view() == (Process { quota_2m: new_process.view().quota_2m, ..old_process.view() })
    &&& new_process.view().quota_2m + alloc_amount == old_process.view().quota_2m
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr)
    &&& new_thread.is_init() == old_thread.is_init()
    &&& new_thread.view_rodata() == old_thread.view_rodata()
    &&& new_thread.view_ghost() == old_thread.view_ghost()
    &&& new_thread.locking_thread() == old_thread.locking_thread()
    &&& new_thread.being_killed() == old_thread.being_killed()
    &&& new_thread.killer_info() == old_thread.killer_info()
    &&& new_thread.view() == (Thread { quota_2m: new_thread.view().quota_2m, ..old_thread.view() })
    &&& new_thread.view().quota_2m == old_thread.view().quota_2m + alloc_amount
}

/// Closes every kernel invariant after the 2M process-to-thread commit from the entry invariants, the summary,
/// and the permission maps the two borrows guarantee.
pub(super) proof fn commit_alloc_thread_quota_2m_eof(pre: &KernelK, post: &KernelK, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, alloc_amount: usize)
    requires
        pre.inv(),
        commit_alloc_thread_quota_2m_eof_transition_framing(pre, post, process_ptr, thread_ptr, alloc_amount),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().contains(thread_ptr),
        pre.prc_mp.spec_index(process_ptr).view().state.view() is Running,
        pre.thr_mp.spec_index(thread_ptr).view().state is RUNNING,
        post.prc_mp.perms_wf(),
        post.thr_mp.perms_wf(),
    ensures post.inv(),
{
    reveal(commit_alloc_thread_quota_2m_eof_transition_framing);
    assert(post.subsystems_inv()) by {
        reveal(KernelK::default_pagetable_wf); reveal(process_perms_wf);
        reveal(thread_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_free_quota_pending_empty_unless_wlocked);
    };
    assert(post.memory_management_inv()) by {
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { lemma_container_process_page_pagetable_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { lemma_page_iommu_table_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
        assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { lemma_process_pages_wf_preserved_for_process_domain_eq_forall(); };
        assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(*pre, *post); };
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_staged_pages_wf(post.thr_mp, post.pg_arr)) by {
            thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
            thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
            thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        };
        assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { lemma_process_pagetable_match_preserved_for_process_pagetable_fields_forall(); };
        assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { lemma_process_iommu_table_match_preserved_for_process_iommu_table_fields_forall(); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.it_mp)) by { reveal(process_emptied_tables_wf); };
        assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by {
            container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(post.ctn_mp, pre.prc_mp, pre.thr_mp, post.thr_mp, post.allc_4k_mp);
            container_process_allocator_quota_4k_wf_preserved_for_process_4k_fields(post.ctn_mp, post.thr_mp, post.allc_4k_mp, pre.prc_mp, post.prc_mp);
        };
        assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp)) by {
            reveal(container_process_allocator_quota_2m_wf); reveal(container_process_wf); reveal(container_thread_wf);
            lemma_process_effective_quota_2m_fold_change_by_forall(process_ptr, -(alloc_amount as int));
            lemma_process_effective_quota_2m_fold_sum_eq_forall();
            lemma_thread_effective_quota_2m_fold_change_by_forall(thread_ptr, alloc_amount as int);
            lemma_thread_effective_quota_2m_fold_sum_eq_forall();
            lemma_thread_pending_2m_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp);
        };
        assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp)) by {
            container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(post.ctn_mp, pre.prc_mp, pre.thr_mp, post.thr_mp, post.allc_1g_mp);
            container_process_allocator_quota_1g_wf_preserved_for_process_1g_fields(post.ctn_mp, post.thr_mp, post.allc_1g_mp, pre.prc_mp, post.prc_mp);
        };
    };
    assert(post.process_management_inv()) by {
        assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
        assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
        assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
        assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { lemma_process_pcid_allocator_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
        assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { lemma_container_process_wf_preserved_for_process_rodata_forall(); };
        assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { lemma_per_container_process_tree_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
        assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { lemma_process_cpu_wf_preserved_for_process_pagetable_fields_forall(); };
        assert(thread_caller_callee_wf(post.thr_mp)) by { thread_caller_callee_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { container_thread_endpoint_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { container_thread_scheduler_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp); };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { container_thread_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { process_thread_wf_preserved_for_process_thread_link_eq(pre.prc_mp, post.prc_mp, pre.thr_mp, post.thr_mp); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.cpu_arr); };
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { lemma_iommu_root_table_process_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { lemma_process_pci_function_ownership_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { lemma_iommu_tlb_wf_spec_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(iommu_table_lock_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { iommu_table_lock_wf_preserved_for_root_and_process_fields_eq(pre.irt.view(), post.irt.view(), pre.prc_mp, post.prc_mp, post.it_mp); };
}
}
