use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_thread_exit_reclaim_spec::thread_exit_tables_emptied_transition;

verus! {
proof fn thread_exit_tables_emptied_eof_process(pre: KernelK, post: KernelK, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr)
    requires
        pre.inv(),
        thread_exit_tables_emptied_transition(pre, post, process_ptr, thread_ptr),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(thread_exit_tables_emptied_transition);
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { per_container_process_tree_wf_preserved_for_tree_fields_eq(pre.ctn_mp, pre.prc_mp, post.prc_mp); reveal(per_container_process_tree_wf); };
    assert(process_kill_mark_wf(post.prc_mp)) by { reveal(process_kill_mark_wf); };
    assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); };
    assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); };
    assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { reveal(process_thread_wf); };
    assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); reveal(process_thread_wf); };
}

/// Marking the write-held exiting process `process_ptr`, whose tables map nothing and whose only thread `thread_ptr`
/// is parked as an exited zombie, as having emptied its tables keeps the kernel invariant.
pub(super) proof fn thread_exit_tables_emptied_eof(pre: KernelK, post: KernelK, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr)
    requires
        pre.inv(),
        thread_exit_tables_emptied_transition(pre, post, process_ptr, thread_ptr),
    ensures post.inv(),
{
    reveal(thread_exit_tables_emptied_transition);
    process_perms_wf_at(pre.prc_mp, process_ptr);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(process_perms_wf); };
    assert(post.memory_management_inv()) by {
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); };
        assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { lemma_process_pages_wf_preserved_for_process_domain_eq_forall(); };
        assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
        assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { process_pagetable_match_preserved_for_process_fields_eq(pre.prc_mp, post.prc_mp, post.pt_mp); };
        assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_match); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.it_mp)) by { reveal(process_emptied_tables_wf); };
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
} // verus!
