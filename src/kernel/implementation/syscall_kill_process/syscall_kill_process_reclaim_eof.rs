use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_reclaim_spec::*;

verus! {
proof fn kill_reassign_eof_memory(pre: KernelK, post: KernelK, target: RwLockProcessPtr, owner: RwLockProcessPtr, iommu_table: Option<RwLockPageTableRoot>)
    requires
        pre.inv(),
        kill_reassign_eof_transition_framing(pre, post, target, owner, iommu_table),
        post.subsystems_inv(),
        iommu_table_perms_wf(post.it_mp),
    ensures post.memory_management_inv(),
{
    reveal(kill_reassign_eof_transition_framing);
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { reveal(iommu_table_pages_wf); };
    assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
    assert(process_pages_wf(post.prc_mp, post.pg_arr)) by { lemma_process_pages_wf_preserved_for_process_domain_eq_forall(); };
    assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { lemma_process_pagetable_match_preserved_for_process_pagetable_fields_forall(); };
    assert(process_iommu_table_wf(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_iommu_table_wf); };
    assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); reveal(process_pagetable_wf); };
    container_process_allocator_quota_4k_wf_preserved_for_process_4k_fields(post.ctn_mp, post.thrd_mp, post.allc_4k_mp, pre.prc_mp, post.prc_mp);
    container_process_allocator_quota_2m_wf_preserved_for_process_2m_fields(post.ctn_mp, post.thrd_mp, post.allc_2m_mp, pre.prc_mp, post.prc_mp);
    container_process_allocator_quota_1g_wf_preserved_for_process_1g_fields(post.ctn_mp, post.thrd_mp, post.allc_1g_mp, pre.prc_mp, post.prc_mp);
}

proof fn kill_reassign_eof_process(pre: KernelK, post: KernelK, target: RwLockProcessPtr, owner: RwLockProcessPtr, iommu_table: Option<RwLockPageTableRoot>)
    requires
        pre.inv(),
        kill_reassign_eof_transition_framing(pre, post, target, owner, iommu_table),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(kill_reassign_eof_transition_framing);
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { lemma_container_process_wf_preserved_for_process_rodata_forall(); };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { per_container_process_tree_wf_preserved_for_tree_fields_eq(post.ctn_mp, pre.prc_mp, post.prc_mp); };
    assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); };
    assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { lemma_process_cpu_wf_preserved_for_process_pagetable_fields_forall(); };
    assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
    assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
    assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
    assert(process_thread_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_thread_wf); };
    assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
}

/// The IOTLB stays well formed: the only emptied domain is the dropped DID of the target's table, whose anchor the target
/// owned, so no cached context keeps it, and the candidate domain of every other function the target owned carried no
/// present entry, so it was inactive and already empty.
proof fn kill_reassign_eof_iotlb(pre: KernelK, post: KernelK, target: RwLockProcessPtr, owner: RwLockProcessPtr, iommu_table: Option<RwLockPageTableRoot>)
    requires
        pre.inv(),
        kill_reassign_eof_transition_framing(pre, post, target, owner, iommu_table),
        pre.prc_mp.dom().contains(target),
        target != owner,
        post.iommu_tlb.inv(),
        forall|b: usize, d: usize, f: usize| #![trigger pre.irt.view().spec_index_iommu_did(b, d, f)]
            pci_bdf_valid(b, d, f) ==> (pre.irt.view().spec_index_iommu_did(b, d, f) is Some) == (pre.irt.view().spec_index_iommu_root(b, d, f) is Some),
    ensures iommu_tlb_wf(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp),
{
    reveal(kill_reassign_eof_transition_framing);
    reveal(iommu_tlb_wf); reveal(iommu_root_table_process_wf); reveal(process_iommu_table_wf); reveal(IommuTLB::inv);
    if let Some(t) = iommu_table {
        if let Some(did) = pre.it_mp.spec_index(t).view().did {
            assert(post.iommu_tlb.context_cache() =~= Map::new(post.iommu_tlb.context_cache().dom().filter(|bdf: PciBdf| post.iommu_tlb.context_cache()[bdf].1 != did), |bdf: PciBdf| post.iommu_tlb.context_cache()[bdf]));
        }
    }
}

/// Reassigning the PCI functions of the empty target `target` to the killer's process `owner` keeps the kernel invariant:
/// the only emptied domain is the dropped DID of the target's table, and the candidate domain of every other function the
/// target owned carried no present entry, so it was inactive and already empty.
pub(crate) proof fn kill_reassign_eof(pre: KernelK, post: KernelK, target: RwLockProcessPtr, owner: RwLockProcessPtr, iommu_table: Option<RwLockPageTableRoot>)
    requires
        pre.inv(),
        kill_reassign_eof_transition_framing(pre, post, target, owner, iommu_table),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.dom().contains(owner),
        target != owner,
        post.irt.inv(),
        post.iommu_tlb.inv(),
        post.prc_mp.perms_wf(),
        iommu_table_perms_wf(post.it_mp),
        forall|b: usize, d: usize, f: usize| #![trigger pre.irt.view().spec_index_iommu_did(b, d, f)]
            pci_bdf_valid(b, d, f) ==> (pre.irt.view().spec_index_iommu_did(b, d, f) is Some) == (pre.irt.view().spec_index_iommu_root(b, d, f) is Some),
    ensures post.inv(),
{
    reveal(kill_reassign_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(process_perms_wf); };
    kill_reassign_eof_memory(pre, post, target, owner, iommu_table);
    kill_reassign_eof_process(pre, post, target, owner, iommu_table);
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); reveal(process_iommu_table_wf); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
    kill_reassign_eof_iotlb(pre, post, target, owner, iommu_table);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_proc_pcid_match); };
}

proof fn kill_quota_eof_allocator_quota(pre: KernelK, post: KernelK, prc_ptr: RwLockProcessPtr, allc_ptr: RwLockPageAllocatorPtr, size: PageSize)
    requires
        pre.inv(),
        kill_quota_eof_transition_framing(pre, post, prc_ptr, allc_ptr, size),
        pre.prc_mp.dom().contains(prc_ptr),
        size is SZ4k ==> allc_ptr == pre.ctn_mp.spec_index(pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container).view_rodata().view().allocator_ptr_4k,
        size is SZ2m ==> allc_ptr == pre.ctn_mp.spec_index(pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container).view_rodata().view().allocator_ptr_2m,
        size is SZ1g ==> allc_ptr == pre.ctn_mp.spec_index(pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container).view_rodata().view().allocator_ptr_1g,
        size is SZ4k ==> pre.allc_4k_mp.spec_index(allc_ptr).quota.view().value + pre.prc_mp.spec_index(prc_ptr).view().quota_4k <= usize::MAX,
        size is SZ2m ==> pre.allc_2m_mp.spec_index(allc_ptr).quota.view().value + pre.prc_mp.spec_index(prc_ptr).view().quota_2m <= usize::MAX,
        size is SZ1g ==> pre.allc_1g_mp.spec_index(allc_ptr).quota.view().value + pre.prc_mp.spec_index(prc_ptr).view().quota_1g <= usize::MAX,
    ensures
        container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp),
        container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_2m_mp),
        container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_1g_mp),
{
    reveal(kill_quota_eof_transition_framing);
    let process = pre.prc_mp.spec_index(prc_ptr).view();
    let dp4k = if size is SZ4k { -(process.quota_4k as int) } else { 0int };
    let dp2m = if size is SZ2m { -(process.quota_2m as int) } else { 0int };
    let dp1g = if size is SZ1g { -(process.quota_1g as int) } else { 0int };
    process_perms_wf_at(pre.prc_mp, prc_ptr);
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp)) by {
        reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); reveal(container_process_wf);
        lemma_process_effective_quota_4k_fold_change_by_forall(prc_ptr, dp4k); lemma_process_effective_quota_4k_fold_sum_eq_forall();
    };
    assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_2m_mp)) by {
        reveal(container_process_allocator_quota_2m_wf); reveal(container_allocator_wf); reveal(container_process_wf);
        lemma_process_effective_quota_2m_fold_change_by_forall(prc_ptr, dp2m); lemma_process_effective_quota_2m_fold_sum_eq_forall();
    };
    assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_1g_mp)) by {
        reveal(container_process_allocator_quota_1g_wf); reveal(container_allocator_wf); reveal(container_process_wf);
        lemma_process_effective_quota_1g_fold_change_by_forall(prc_ptr, dp1g); lemma_process_effective_quota_1g_fold_sum_eq_forall();
    };
}

proof fn kill_quota_eof_memory(pre: KernelK, post: KernelK, prc_ptr: RwLockProcessPtr, allc_ptr: RwLockPageAllocatorPtr, size: PageSize)
    requires
        pre.inv(),
        kill_quota_eof_transition_framing(pre, post, prc_ptr, allc_ptr, size),
        pre.prc_mp.dom().contains(prc_ptr),
        size is SZ4k ==> allc_ptr == pre.ctn_mp.spec_index(pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container).view_rodata().view().allocator_ptr_4k,
        size is SZ2m ==> allc_ptr == pre.ctn_mp.spec_index(pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container).view_rodata().view().allocator_ptr_2m,
        size is SZ1g ==> allc_ptr == pre.ctn_mp.spec_index(pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container).view_rodata().view().allocator_ptr_1g,
        size is SZ4k ==> pre.allc_4k_mp.spec_index(allc_ptr).quota.view().value + pre.prc_mp.spec_index(prc_ptr).view().quota_4k <= usize::MAX,
        size is SZ2m ==> pre.allc_2m_mp.spec_index(allc_ptr).quota.view().value + pre.prc_mp.spec_index(prc_ptr).view().quota_2m <= usize::MAX,
        size is SZ1g ==> pre.allc_1g_mp.spec_index(allc_ptr).quota.view().value + pre.prc_mp.spec_index(prc_ptr).view().quota_1g <= usize::MAX,
        post.subsystems_inv(),
    ensures post.memory_management_inv(),
{
    reveal(kill_quota_eof_transition_framing);
    container_process_wf_process_at(pre.ctn_mp, pre.prc_mp, prc_ptr);
    assert(allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr)) by { allocator_pages_wf_preserved_for_allocator_fields_except_quota(); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { container_process_page_pagetable_wf_preserved_for_process_fields_except_quota(); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { page_iommu_table_wf_preserved_for_process_fields_except_quota(); };
    assert(process_pages_wf(post.prc_mp, post.pg_arr)) by { lemma_process_pages_wf_preserved_for_process_domain_eq_forall(); };
    assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { lemma_process_pagetable_match_preserved_for_process_pagetable_fields_forall(); };
    assert(process_iommu_table_wf(post.prc_mp, post.it_mp)) by { lemma_process_iommu_table_match_preserved_for_process_iommu_table_fields_forall(); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); };
    assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); reveal(process_pagetable_wf); };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { container_allocator_wf_preserved_for_owner_depth_eq(pre.ctn_mp, post.ctn_mp, pre.allc_4k_mp, post.allc_4k_mp, pre.allc_2m_mp, post.allc_2m_mp, pre.allc_1g_mp, post.allc_1g_mp); };
    assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_kill_retire_wf); reveal(container_allocator_wf); };
    assert(allocator_free_page_ptrs_wf(post.allc_4k_mp) && allocator_free_page_ptrs_wf(post.allc_2m_mp) && allocator_free_page_ptrs_wf(post.allc_1g_mp)) by {
        lemma_allocator_free_page_ptrs_wf_preserved_for_pool_and_cache_contents_forall::<ALLOCATOR_SIZE_4K>(); lemma_allocator_free_page_ptrs_wf_preserved_for_pool_and_cache_contents_forall::<ALLOCATOR_SIZE_2M>();
        lemma_allocator_free_page_ptrs_wf_preserved_for_pool_and_cache_contents_forall::<ALLOCATOR_SIZE_1G>();
    };
    assert(allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { lemma_container_allocator_free_4k_page_wf_preserved_for_lock_op(pre, post); };
    assert(allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { lemma_container_allocator_free_2m_page_wf_preserved_for_lock_op(pre, post); };
    assert(allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by { lemma_container_allocator_free_1g_page_wf_preserved_for_lock_op(pre, post); };
    assert(allocator_1g_cpu_caches_empty_wf(post.allc_1g_mp)) by { reveal(allocator_1g_cpu_caches_empty_wf); };
    kill_quota_eof_allocator_quota(pre, post, prc_ptr, allc_ptr, size);
}

proof fn kill_quota_eof_process(pre: KernelK, post: KernelK, prc_ptr: RwLockProcessPtr, allc_ptr: RwLockPageAllocatorPtr, size: PageSize)
    requires
        pre.inv(),
        kill_quota_eof_transition_framing(pre, post, prc_ptr, allc_ptr, size),
        pre.prc_mp.dom().contains(prc_ptr),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(kill_quota_eof_transition_framing);
    process_perms_wf_at(pre.prc_mp, prc_ptr);
    assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { process_pcid_allocator_wf_preserved_for_process_fields_except_quota(); };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { lemma_container_process_wf_preserved_for_process_rodata_forall(); };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { per_container_process_tree_wf_preserved_for_process_fields_except_quota(); };
    assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
    assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
    assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
    assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { lemma_process_cpu_wf_preserved_for_process_pagetable_fields_forall(); };
    assert(process_thread_wf(post.prc_mp, post.thrd_mp)) by {
        process_thread_wf_preserved_for_process_thread_link_eq(pre.prc_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp);
        lemma_process_thread_wf_preserved_for_process_thread_membership_fields_forall();
    };
    assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
}

/// Returning the target's whole `size` quota to its container's `size` allocator keeps the kernel invariant.
pub(crate) proof fn kill_quota_eof(pre: KernelK, post: KernelK, prc_ptr: RwLockProcessPtr, allc_ptr: RwLockPageAllocatorPtr, size: PageSize)
    requires
        pre.inv(),
        kill_quota_eof_transition_framing(pre, post, prc_ptr, allc_ptr, size),
        pre.prc_mp.dom().contains(prc_ptr),
        size is SZ4k ==> allc_ptr == pre.ctn_mp.spec_index(pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container).view_rodata().view().allocator_ptr_4k,
        size is SZ2m ==> allc_ptr == pre.ctn_mp.spec_index(pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container).view_rodata().view().allocator_ptr_2m,
        size is SZ1g ==> allc_ptr == pre.ctn_mp.spec_index(pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container).view_rodata().view().allocator_ptr_1g,
        size is SZ4k ==> pre.allc_4k_mp.spec_index(allc_ptr).quota.view().value + pre.prc_mp.spec_index(prc_ptr).view().quota_4k <= usize::MAX,
        size is SZ2m ==> pre.allc_2m_mp.spec_index(allc_ptr).quota.view().value + pre.prc_mp.spec_index(prc_ptr).view().quota_2m <= usize::MAX,
        size is SZ1g ==> pre.allc_1g_mp.spec_index(allc_ptr).quota.view().value + pre.prc_mp.spec_index(prc_ptr).view().quota_1g <= usize::MAX,
    ensures post.inv(),
{
    reveal(kill_quota_eof_transition_framing);
    process_perms_wf_at(pre.prc_mp, prc_ptr);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(process_perms_wf); reveal(allocator_perms_wf); };
    kill_quota_eof_memory(pre, post, prc_ptr, allc_ptr, size);
    kill_quota_eof_process(pre, post, prc_ptr, allc_ptr, size);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { cpu_dirty_map_wf_preserved_for_process_fields_except_quota(); };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { iommu_root_table_process_wf_preserved_for_process_fields_except_quota(); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { process_pci_function_ownership_wf_preserved_for_process_fields_except_quota(); };
    assert(iommu_tlb_wf(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { iommu_tlb_wf_spec_preserved_for_process_fields_except_quota(); };
}

proof fn kill_tables_emptied_eof_process(pre: KernelK, post: KernelK, prc_ptr: RwLockProcessPtr)
    requires
        pre.inv(),
        kill_tables_emptied_eof_transition_framing(pre, post, prc_ptr),
        pre.prc_mp.dom().contains(prc_ptr),
        !pre.prc_mp.spec_index(prc_ptr).view().zombie,
        pre.prc_mp.spec_index(prc_ptr).view().owned_threads.view().len() == 0,
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(kill_tables_emptied_eof_transition_framing);
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { per_container_process_tree_wf_preserved_for_tree_fields_eq(pre.ctn_mp, pre.prc_mp, post.prc_mp); reveal(per_container_process_tree_wf); };
    assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
    assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
    assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
    assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); };
    assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); };
    assert(process_thread_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_thread_wf); };
    assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); process_perms_wf_at(pre.prc_mp, prc_ptr); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
}

/// Marking the write-held reclaimed target `prc_ptr`, whose tables map nothing and which owns no thread, as having
/// emptied its tables keeps the kernel invariant.
pub(crate) proof fn kill_tables_emptied_eof(pre: KernelK, post: KernelK, prc_ptr: RwLockProcessPtr, pagetable: RwLockPageTableRoot)
    requires
        pre.inv(),
        kill_tables_emptied_eof_transition_framing(pre, post, prc_ptr),
        pre.prc_mp.dom().contains(prc_ptr),
        !pre.prc_mp.spec_index(prc_ptr).view().zombie,
        pre.prc_mp.spec_index(prc_ptr).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g().dom() =~= Set::<VAddr>::empty(),
        forall|l4i: L4Index| #![trigger whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) ==> whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, l1i) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i) is None,
        forall|l4i: L4Index, l3i: L3Index| #![trigger whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_1g_l3(l4i, l3i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_1g_l3(l4i, l3i) is None,
        pre.prc_mp.spec_index(prc_ptr).view().iommu_table is Some ==> pre.it_mp.spec_index(pre.prc_mp.spec_index(prc_ptr).view().iommu_table->Some_0).view().mapping_4k().dom() =~= Set::<VAddr>::empty(),
    ensures post.inv(),
{
    reveal(kill_tables_emptied_eof_transition_framing);
    process_perms_wf_at(pre.prc_mp, prc_ptr); process_pagetable_wf_process_at(pre.prc_mp, pre.pt_mp, prc_ptr); pre.default_pagetable_wf_at(pagetable);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(process_perms_wf); };
    assert(post.memory_management_inv()) by {
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); };
        assert(process_pages_wf(post.prc_mp, post.pg_arr)) by { lemma_process_pages_wf_preserved_for_process_domain_eq_forall(); };
        assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
        assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { process_pagetable_match_preserved_for_process_fields_eq(pre.prc_mp, post.prc_mp, post.pt_mp); };
        assert(process_iommu_table_wf(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_wf); };
        // A page record names a held leaf of its table (4K, 2M) or a 1G mapping; none is left in the user range.
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by {
            reveal(process_emptied_tables_wf); reveal(process_pagetable_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
            broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_va_1g_valid_index_roundtrip;
        };
        assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); reveal(process_pagetable_wf); };
        container_process_allocator_quota_4k_wf_preserved_for_process_4k_fields(post.ctn_mp, post.thrd_mp, post.allc_4k_mp, pre.prc_mp, post.prc_mp);
        container_process_allocator_quota_2m_wf_preserved_for_process_2m_fields(post.ctn_mp, post.thrd_mp, post.allc_2m_mp, pre.prc_mp, post.prc_mp);
        container_process_allocator_quota_1g_wf_preserved_for_process_1g_fields(post.ctn_mp, post.thrd_mp, post.allc_1g_mp, pre.prc_mp, post.prc_mp);
    };
    kill_tables_emptied_eof_process(pre, post, prc_ptr);
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
    assert(iommu_tlb_wf(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf); reveal(iommu_root_table_process_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_proc_pcid_match); };
}

proof fn kill_zombify_eof_process(pre: KernelK, post: KernelK, prc_ptr: RwLockProcessPtr, pcid_allc_ptr: RwLockPcidAllocatorPtr)
    requires
        pre.inv(),
        kill_zombify_eof_transition_framing(pre, post, prc_ptr, pcid_allc_ptr),
        pre.prc_mp.dom().contains(prc_ptr),
        pre.prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied,
        pre.prc_mp.spec_index(prc_ptr).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(prc_ptr).view().quota_4k == 0,
        pre.prc_mp.spec_index(prc_ptr).view().quota_2m == 0,
        pre.prc_mp.spec_index(prc_ptr).view().quota_1g == 0,
        pcid_allc_ptr == pre.ctn_mp.spec_index(pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container).view_rodata().view().pcid_allocator,
        pre.pcid_allc_mp.dom().contains(pcid_allc_ptr),
        pcid_valid(pre.prc_mp.spec_index(prc_ptr).view().pcid),
        pre.prc_mp.spec_index(prc_ptr).view().pcid != KERNEL_DEFAULT_PCID,
        pre.pcid_allc_mp.spec_index(pcid_allc_ptr).view().id_to_proc.view().spec_index(pre.prc_mp.spec_index(prc_ptr).view().pcid as int).contains(prc_ptr),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(kill_zombify_eof_transition_framing);
    process_perms_wf_at(pre.prc_mp, prc_ptr);
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { per_container_process_tree_wf_preserved_for_tree_fields_eq(pre.ctn_mp, pre.prc_mp, post.prc_mp); reveal(per_container_process_tree_wf); };
    assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
    assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
    assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
    assert(container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
    assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); pcid_allocator_perms_wf_at(pre.pcid_allc_mp, pcid_allc_ptr); };
    assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); reveal(process_thread_wf); reveal(cpu_array_wf); reveal(thread_cpu_wf); };
    assert(process_thread_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_thread_wf); };
    assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
}

/// Making the reclaimed target `prc_ptr` a zombie while its container's PCID allocator releases its PCID keeps the
/// kernel invariant.
pub(crate) proof fn kill_zombify_eof(pre: KernelK, post: KernelK, prc_ptr: RwLockProcessPtr, pcid_allc_ptr: RwLockPcidAllocatorPtr)
    requires
        pre.inv(),
        kill_zombify_eof_transition_framing(pre, post, prc_ptr, pcid_allc_ptr),
        pre.prc_mp.dom().contains(prc_ptr),
        pre.prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied,
        pre.prc_mp.spec_index(prc_ptr).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(prc_ptr).view().quota_4k == 0,
        pre.prc_mp.spec_index(prc_ptr).view().quota_2m == 0,
        pre.prc_mp.spec_index(prc_ptr).view().quota_1g == 0,
        pcid_allc_ptr == pre.ctn_mp.spec_index(pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container).view_rodata().view().pcid_allocator,
        pre.pcid_allc_mp.dom().contains(pcid_allc_ptr),
        pcid_valid(pre.prc_mp.spec_index(prc_ptr).view().pcid),
        pre.prc_mp.spec_index(prc_ptr).view().pcid != KERNEL_DEFAULT_PCID,
        pre.pcid_allc_mp.spec_index(pcid_allc_ptr).view().id_to_proc.view().spec_index(pre.prc_mp.spec_index(prc_ptr).view().pcid as int).contains(prc_ptr),
        pcid_allocator_perms_wf(post.pcid_allc_mp),
    ensures post.inv(),
{
    reveal(kill_zombify_eof_transition_framing);
    process_perms_wf_at(pre.prc_mp, prc_ptr);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(process_perms_wf); };
    assert(post.memory_management_inv()) by {
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); };
        assert(process_pages_wf(post.prc_mp, post.pg_arr)) by { lemma_process_pages_wf_preserved_for_process_domain_eq_forall(); };
        assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
        assert(pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pcid_allc_mp, post.pcid_allc_mp, pre.pg_arr, post.pg_arr); };
        assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { process_pagetable_match_preserved_for_process_fields_eq(pre.prc_mp, post.prc_mp, post.pt_mp); };
        assert(process_iommu_table_wf(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_wf); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); };
        assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); reveal(process_pagetable_wf); };
        container_process_allocator_quota_4k_wf_preserved_for_process_4k_fields(post.ctn_mp, post.thrd_mp, post.allc_4k_mp, pre.prc_mp, post.prc_mp);
        container_process_allocator_quota_2m_wf_preserved_for_process_2m_fields(post.ctn_mp, post.thrd_mp, post.allc_2m_mp, pre.prc_mp, post.prc_mp);
        container_process_allocator_quota_1g_wf_preserved_for_process_1g_fields(post.ctn_mp, post.thrd_mp, post.allc_1g_mp, pre.prc_mp, post.prc_mp);
    };
    kill_zombify_eof_process(pre, post, prc_ptr, pcid_allc_ptr);
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
    assert(iommu_tlb_wf(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf); reveal(iommu_root_table_process_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_proc_pcid_match); };
}

/// EOF closure of `kill_reassign_functions` when the scan finds no function `target` owns: its reverse set is empty.
pub(crate) proof fn kill_reassign_none_eof(root_table: IommuRootTable, process_map: ProcessLockedMap, target: RwLockProcessPtr)
    requires
        process_pci_function_ownership_wf(root_table, process_map),
        process_map.dom().contains(target),
        forall|b: usize, d: usize, f: usize| #![trigger root_table.spec_index_owner(b, d, f)] pci_bdf_valid(b, d, f) ==> root_table.spec_index_owner(b, d, f) != target,
    ensures process_map.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
{
    assert(process_map.spec_index(target).view_ghost().owned_pci_functions.view() =~= Set::<PciBdf>::empty()) by { reveal(process_pci_function_ownership_wf); };
}
} // verus!
