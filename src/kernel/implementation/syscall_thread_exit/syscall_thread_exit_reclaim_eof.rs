use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_thread_exit_reclaim_spec::{thread_exit_tables_emptied_eof_transition_framing, thread_exit_detach_process_functions_eof_transition_framing};

verus! {
proof fn thread_exit_tables_emptied_eof_process(pre: KernelK, post: KernelK, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr)
    requires
        pre.inv(),
        thread_exit_tables_emptied_eof_transition_framing(pre, post, process_ptr, thread_ptr),
        pre.prc_mp.dom().contains(process_ptr),
        !pre.prc_mp.spec_index(process_ptr).view().zombie,
        pre.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() == 1,
        pre.prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).view_ghost().exited,
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
    assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { reveal(process_thread_wf); };
    assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); reveal(process_thread_wf); };
}

/// Marking the write-held, live exiting thread `thread_ptr` as exited changes only its ghost state and keeps the kernel invariant.
pub(super) proof fn thread_exit_mark_exited_eof(pre: KernelK, post: KernelK, thread_ptr: RwLockThreadPtr)
    requires
        pre.inv(),
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).locking_thread() is Write,
        !thread_is_dangling(pre.thr_mp.spec_index(thread_ptr)),
        post == (KernelK { thr_mp: post.thr_mp, ..pre }),
        post.thr_mp.perms_wf(),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        update_ghost_ensures(pre.thr_mp.spec_index(thread_ptr), post.thr_mp.spec_index(thread_ptr), ThreadGhost { exited: true, ..pre.thr_mp.spec_index(thread_ptr).view_ghost() }),
    ensures post.inv(),
{
    assert(thread_perms_wf(post.thr_mp)) by {
        reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
        reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_partner_only_when_wlocked); reveal(thread_peer_implies_ipc_partner);
    };
    assert(thread_invariant_fields_unchanged(pre.thr_mp, post.thr_mp)) by { thread_lock_op_preserves_invariant_fields(pre.thr_mp, post.thr_mp, thread_ptr); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_invariant_fields(pre, post); };
    assert(process_thread_wf(post.prc_mp, post.thr_mp)) by {
        thread_invariant_fields_unchanged_implies_process_management_fields(pre.thr_mp, post.thr_mp);
        process_thread_wf_preserved_for_thread_process_management_fields(post.prc_mp, pre.thr_mp, post.thr_mp);
    };
    assert(thread_dangling_chain_end_wf(post.thr_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thr_mp, post.thr_mp); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
    assert(post.process_management_inv()) by { process_management_inv_preserved_for_thread_invariant_fields(pre, post); };
}

/// Marking the write-held exiting process `process_ptr`, whose tables map nothing and whose only thread `thread_ptr`
/// is parked as an exited zombie, as having emptied its tables keeps the kernel invariant.
pub(super) proof fn thread_exit_tables_emptied_eof(pre: KernelK, post: KernelK, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr)
    requires
        pre.inv(),
        thread_exit_tables_emptied_eof_transition_framing(pre, post, process_ptr, thread_ptr),
        pre.prc_mp.dom().contains(process_ptr),
        !pre.prc_mp.spec_index(process_ptr).view().zombie,
        pre.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() == 1,
        pre.prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).view_ghost().exited,
        pagetable_c(pre.pt_mp, pre.pt_lower.view(), pre.prc_mp.spec_index(process_ptr).view().pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty(),
        pre.prc_mp.spec_index(process_ptr).view().iommu_table is Some ==> pre.it_mp.spec_index(pre.prc_mp.spec_index(process_ptr).view().iommu_table->Some_0).view().mapping_4k().dom() =~= Set::<VAddr>::empty(),
    ensures post.inv(),
{
    reveal(thread_exit_tables_emptied_eof_transition_framing);
    process_perms_wf_at(pre.prc_mp, process_ptr);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(process_perms_wf); };
    assert(post.memory_management_inv()) by {
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); };
        assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { lemma_process_pages_wf_preserved_for_process_domain_eq_forall(); };
        assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
        assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { process_pagetable_match_preserved_for_process_fields_eq(pre.prc_mp, post.prc_mp, post.pt_mp); };
        assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_match); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); };
        container_process_allocator_quota_4k_wf_preserved_for_process_4k_fields(post.ctn_mp, post.thr_mp, post.allc_4k_mp, pre.prc_mp, post.prc_mp);
        container_process_allocator_quota_2m_wf_preserved_for_process_2m_fields(post.ctn_mp, post.thr_mp, post.allc_2m_mp, pre.prc_mp, post.prc_mp);
        container_process_allocator_quota_1g_wf_preserved_for_process_1g_fields(post.ctn_mp, post.thr_mp, post.allc_1g_mp, pre.prc_mp, post.prc_mp);
    };
    thread_exit_tables_emptied_eof_process(pre, post, process_ptr, thread_ptr);
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf_spec); reveal(iommu_root_table_process_wf); };
    assert(iommu_table_lock_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_table_lock_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_proc_pcid_match); };
}

/// Detaching one function of the exiting process keeps every invariant; the slot's IOTLB domain was already present.
pub(super) proof fn thread_exit_detach_process_functions_eof(pre: KernelK, post: KernelK, bus: usize, device: usize, function: usize)
    requires
        pre.inv(),
        thread_exit_detach_process_functions_eof_transition_framing(pre, post, bus, device, function),
        pci_bdf_valid(bus, device, function),
        post.irt.inv(),
        post.iommu_tlb.inv(),
    ensures
        post.inv(),
        pre.iommu_tlb.view().dom().contains(pci_bdf_did(bus, device, function)),
{
    reveal(thread_exit_detach_process_functions_eof_transition_framing);
    assert(pre.iommu_tlb.view().dom().contains(pci_bdf_did(bus, device, function))) by { reveal(IommuTLB::inv); };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf_spec); };
    assert(iommu_table_lock_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { iommu_table_lock_wf_preserved_for_root_and_process_fields_eq(pre.irt.view(), post.irt.view(), pre.prc_mp, post.prc_mp, post.it_mp); };
    assert(post.inv()) by { reveal(KernelK::default_pagetable_wf); };
}
} // verus!
