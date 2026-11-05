use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_thread_exit_reclaim_spec::{thread_exit_tables_emptied_eof_transition_framing, thread_exit_detach_process_functions_eof_transition_framing};

verus! {
proof fn thread_exit_tables_emptied_eof_process(pre: KernelK, post: KernelK, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr)
    requires
        pre.inv(),
        thread_exit_tables_emptied_eof_transition_framing(pre, post, prc_ptr),
        pre.prc_mp.dom().contains(prc_ptr),
        !pre.prc_mp.spec_index(prc_ptr).view().zombie,
        pre.prc_mp.spec_index(prc_ptr).view().owned_threads.view().len() == 1,
        pre.prc_mp.spec_index(prc_ptr).view().owned_threads.view().contains(thrd_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(thread_exit_tables_emptied_eof_transition_framing);
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { per_container_process_tree_wf_preserved_for_tree_fields_eq(pre.ctn_mp, pre.prc_mp, post.prc_mp); reveal(per_container_process_tree_wf); };
    assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
    assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
    assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
    assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); };
    assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); };
    assert(process_thread_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_thread_wf); };
    assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); reveal(process_thread_wf); };
}

/// Marking the write-held, live exiting thread `thrd_ptr` as exited changes only its ghost state and keeps the kernel invariant.
pub(super) proof fn thread_exit_mark_exited_eof(pre: KernelK, post: KernelK, thrd_ptr: RwLockThreadPtr)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thrd_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
        !thread_is_dangling(pre.thrd_mp.spec_index(thrd_ptr)),
        post == (KernelK { thrd_mp: post.thrd_mp, ..pre }),
        post.thrd_mp.perms_wf(),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        update_ghost_ensures(pre.thrd_mp.spec_index(thrd_ptr), post.thrd_mp.spec_index(thrd_ptr), ThreadGhost { exited: true, ..pre.thrd_mp.spec_index(thrd_ptr).view_ghost() }),
    ensures post.inv(),
{
    assert(thread_perms_wf(post.thrd_mp)) by {
        reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
        reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
    };
    assert(thread_invariant_fields_unchanged(pre.thrd_mp, post.thrd_mp)) by { thread_lock_op_preserves_invariant_fields(pre.thrd_mp, post.thrd_mp, thrd_ptr); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_invariant_fields(pre, post); };
    assert(process_thread_wf(post.prc_mp, post.thrd_mp)) by {
        thread_invariant_fields_unchanged_implies_process_management_fields(pre.thrd_mp, post.thrd_mp);
        process_thread_wf_preserved_for_thread_process_management_fields(post.prc_mp, pre.thrd_mp, post.thrd_mp);
    };
    assert(thread_dangling_chain_end_wf(post.thrd_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thrd_mp, post.thrd_mp); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
    assert(post.process_management_inv()) by { process_management_inv_preserved_for_thread_invariant_fields(pre, post); };
}

/// Marking the write-held exiting process `prc_ptr`, whose tables map nothing and whose only thread `thrd_ptr`
/// is parked as an exited zombie, as having emptied its tables keeps the kernel invariant.
pub(super) proof fn thread_exit_tables_emptied_eof(
    pre: KernelK, post: KernelK, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot,
)
    requires
        pre.inv(),
        thread_exit_tables_emptied_eof_transition_framing(pre, post, prc_ptr),
        pre.prc_mp.dom().contains(prc_ptr),
        !pre.prc_mp.spec_index(prc_ptr).view().zombie,
        pre.prc_mp.spec_index(prc_ptr).view().owned_threads.view().len() == 1,
        pre.prc_mp.spec_index(prc_ptr).view().owned_threads.view().contains(thrd_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g().dom() =~= Set::<VAddr>::empty(),
        forall|l4i: L4Index| #![trigger whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).kernel_l4_end() <= l4i && pei_valid(l4i) ==> whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, l1i) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i) is None,
        pre.prc_mp.spec_index(prc_ptr).view().iommu_table is Some ==> pre.it_mp.spec_index(pre.prc_mp.spec_index(prc_ptr).view().iommu_table->Some_0).view().mapping_4k().dom() =~= Set::<VAddr>::empty(),
    ensures post.inv(),
{
    reveal(thread_exit_tables_emptied_eof_transition_framing);
    process_perms_wf_at(pre.prc_mp, prc_ptr);
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
            reveal(process_emptied_tables_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
            broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip;
        };
        assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); reveal(process_pagetable_wf); };
        container_process_allocator_quota_4k_wf_preserved_for_process_4k_fields(post.ctn_mp, post.thrd_mp, post.allc_4k_mp, pre.prc_mp, post.prc_mp);
        container_process_allocator_quota_2m_wf_preserved_for_process_2m_fields(post.ctn_mp, post.thrd_mp, post.allc_2m_mp, pre.prc_mp, post.prc_mp);
        container_process_allocator_quota_1g_wf_preserved_for_process_1g_fields(post.ctn_mp, post.thrd_mp, post.allc_1g_mp, pre.prc_mp, post.prc_mp);
    };
    thread_exit_tables_emptied_eof_process(pre, post, prc_ptr, thrd_ptr);
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { process_pci_function_ownership_wf_preserved_for_process_fields_except_quota(); };
    assert(iommu_tlb_wf(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf); reveal(iommu_root_table_process_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_proc_pcid_match); };
}

/// Detaching the IOMMU table `iommu_table` keeps the memory invariants: the table keeps its mappings, pages, and owner.
proof fn thread_exit_detach_process_functions_eof_memory(pre: KernelK, post: KernelK, iommu_table: RwLockPageTableRoot)
    requires
        pre.inv(),
        thread_exit_detach_process_functions_eof_transition_framing(pre, post, iommu_table),
        pre.it_mp.dom().contains(iommu_table),
    ensures post.memory_management_inv(),
{
    assert({
        &&& post == (KernelK { irt: post.irt, iommu_tlb: post.iommu_tlb, it_mp: post.it_mp, ..pre })
        &&& post.it_mp.unchanged_except(&pre.it_mp, iommu_table)
        &&& post.it_mp.lock_id_by_key(iommu_table) == pre.it_mp.lock_id_by_key(iommu_table)
        &&& post.it_mp.spec_index(iommu_table).locking_thread() == pre.it_mp.spec_index(iommu_table).locking_thread()
        &&& post.it_mp.spec_index(iommu_table).being_killed() == pre.it_mp.spec_index(iommu_table).being_killed()
        &&& post.it_mp.spec_index(iommu_table).view() == (PageTable { did: None, ..pre.it_mp.spec_index(iommu_table).view() })
        &&& post.it_mp.spec_index(iommu_table).view().mapping_4k() == pre.it_mp.spec_index(iommu_table).view().mapping_4k()
        &&& post.it_mp.spec_index(iommu_table).view().mapping_2m() == pre.it_mp.spec_index(iommu_table).view().mapping_2m()
        &&& post.it_mp.spec_index(iommu_table).view().mapping_1g() == pre.it_mp.spec_index(iommu_table).view().mapping_1g()
        &&& post.it_mp.spec_index(iommu_table).view().page_closure() == pre.it_mp.spec_index(iommu_table).view().page_closure()
        &&& post.it_mp.spec_index(iommu_table).view().proc_ptr == pre.it_mp.spec_index(iommu_table).view().proc_ptr
    }) by { reveal(thread_exit_detach_process_functions_eof_transition_framing); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { reveal(iommu_table_pages_wf); };
    assert(process_iommu_table_wf(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_wf); };
    assert(pagetable_no_1g_leaf_wf(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_no_1g_leaf_wf); };
    assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_iommu_table_wf); };
    assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { reveal(process_object_pages_owner_wf); reveal(iommu_table_pages_wf); };
}

/// Detaching the IOMMU table `iommu_table` of the exiting process keeps every invariant: only slots of its owner lose their
/// root and DID, the table drops its DID, and that DID loses its anchor together with its IOTLB domain and cached contexts.
pub(super) proof fn thread_exit_detach_process_functions_eof(pre: KernelK, post: KernelK, iommu_table: RwLockPageTableRoot)
    requires
        pre.inv(),
        thread_exit_detach_process_functions_eof_transition_framing(pre, post, iommu_table),
        pre.it_mp.dom().contains(iommu_table),
        post.irt.inv(),
        post.iommu_tlb.inv(),
        iommu_table_perms_wf(post.it_mp),
        forall|b: usize, d: usize, f: usize| #![trigger pre.irt.view().spec_index_iommu_did(b, d, f)]
            pci_bdf_valid(b, d, f) ==> (pre.irt.view().spec_index_iommu_did(b, d, f) is Some) == (pre.irt.view().spec_index_iommu_root(b, d, f) is Some),
    ensures
        post.inv(),
        pre.it_mp.spec_index(iommu_table).view().leaves_present() ==> post.it_mp.spec_index(iommu_table).view().leaves_present(),
{
    thread_exit_detach_process_functions_eof_memory(pre, post, iommu_table);
    reveal(thread_exit_detach_process_functions_eof_transition_framing);
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); reveal(process_iommu_table_wf); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
    // The DID's anchor belonged to the detached owner, so no cached context entry keeps it.
    if let Some(did) = pre.it_mp.spec_index(iommu_table).view().did {
        assert(post.iommu_tlb.context_cache() =~= Map::new(post.iommu_tlb.context_cache().dom().filter(|bdf: PciBdf| post.iommu_tlb.context_cache()[bdf].1 != did), |bdf: PciBdf| post.iommu_tlb.context_cache()[bdf]))
            by { reveal(iommu_root_table_process_wf); };
    }
    assert(iommu_tlb_wf(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf); reveal(iommu_root_table_process_wf); reveal(process_iommu_table_wf); reveal(IommuTLB::inv); };
    assert(post.inv()) by { reveal(KernelK::default_pagetable_wf); };
}
} // verus!
