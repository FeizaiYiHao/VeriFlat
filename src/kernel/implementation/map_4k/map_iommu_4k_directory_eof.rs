use vstd::prelude::*;
use crate::*;
use super::mmap_4k_build_structure_spec::*;
use super::map_iommu_4k_spec::*;

verus! {
/// Retypes the staged page `page_ptr` into a table page of the IOMMU table `iommu_table_ptr`, adds it to the table's page
/// closure, and charges it to `quota_thread_ptr`; every other kernel field is unchanged.
#[verifier::opaque]
pub(super) open spec fn install_staged_4k_iommu_table_page_eof_transition_framing(
    pre: KernelK, post: KernelK, level: MissingPageTableLevel, page_ptr: PagePtr, quota_thread_ptr: RwLockThreadPtr, iommu_table_ptr: RwLockPageTableRoot,
) -> bool {
    let page_index = page_ptr2page_index(page_ptr);
    let old_it = pre.it_mp.spec_index(iommu_table_ptr);
    let new_it = post.it_mp.spec_index(iommu_table_ptr);
    let old_page = pre.pg_arr.spec_index(page_index).view();
    let new_page = post.pg_arr.spec_index(page_index).view();
    let old_thread = pre.thr_mp.spec_index(quota_thread_ptr);
    let new_thread = post.thr_mp.spec_index(quota_thread_ptr);
    &&& post == (KernelK { it_mp: post.it_mp, pg_arr: post.pg_arr, thr_mp: post.thr_mp, ..pre })
    &&& post.it_mp.unchanged_except(&pre.it_mp, iommu_table_ptr)
    &&& new_it.locking_thread() == old_it.locking_thread()
    &&& new_it.being_killed() == old_it.being_killed()
    &&& new_it.view().page_closure() == old_it.view().page_closure().insert(page_ptr)
    &&& new_it.view().mapping_4k() == old_it.view().mapping_4k()
    &&& new_it.view().mapping_2m() == old_it.view().mapping_2m()
    &&& new_it.view().mapping_1g() == old_it.view().mapping_1g()
    &&& new_it.view().kernel_entries == old_it.view().kernel_entries
    &&& new_it.view().kernel_l4_end == old_it.view().kernel_l4_end
    &&& new_it.view().pcid == old_it.view().pcid
    &&& new_it.view().cr3 == old_it.view().cr3
    &&& new_it.view().proc_ptr == old_it.view().proc_ptr
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_index)
    &&& new_page.is_init()
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& new_page.view_rodata() == old_page.view_rodata()
    &&& new_page.view_ghost() == old_page.view_ghost()
    &&& new_page.view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: iommu_table_ptr, table_type: IOMMU_TYPE } })
    &&& new_page.view().perm_4k.view() is None
    &&& new_page.view().addr == old_page.view().addr
    &&& new_page.view().is_io_page == old_page.view().is_io_page
    &&& new_page.view().ref_count == old_page.view().ref_count
    &&& new_page.view().owning_container == old_page.view().owning_container
    &&& new_page.view().mappings.view() == old_page.view().mappings.view()
    &&& new_page.view().iommu_mappings.view() == old_page.view().iommu_mappings.view()
    &&& new_page.view().free_list_node_storage == old_page.view().free_list_node_storage
    &&& new_page.view().free_list == old_page.view().free_list
    &&& new_page.view().perm_2m.view() == old_page.view().perm_2m.view()
    &&& new_page.view().perm_1g.view() == old_page.view().perm_1g.view()
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, quota_thread_ptr)
    &&& new_thread.is_init()
    &&& new_thread.locking_thread() == old_thread.locking_thread()
    &&& new_thread.being_killed() == old_thread.being_killed()
    &&& new_thread.killer_info() == old_thread.killer_info()
    &&& new_thread.view_rodata() == old_thread.view_rodata()
    &&& new_thread.view_ghost() == old_thread.view_ghost()
    &&& new_thread.view() == (Thread {
        quota_4k: new_thread.view().quota_4k, temp_alloc_cache_4k: new_thread.view().temp_alloc_cache_4k, syscall_progress: new_thread.view().syscall_progress, ..old_thread.view()
    })
    &&& new_thread.view().temp_alloc_cache_4k.view() == old_thread.view().temp_alloc_cache_4k.view().remove(page_ptr)
    &&& new_thread.view().quota_4k == old_thread.view().quota_4k - 1
    &&& new_thread.view().syscall_progress.view() == iommu_map_4k_progress_after_directory(old_thread.view().syscall_progress.view(), level)
}

pub(super) proof fn install_staged_4k_iommu_table_page_eof(
    pre: KernelK, post: KernelK, level: MissingPageTableLevel, page_ptr: PagePtr, quota_thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr,
    iommu_table_ptr: RwLockPageTableRoot,
)
    requires
        pre.inv(),
        install_staged_4k_iommu_table_page_eof_transition_framing(pre, post, level, page_ptr, quota_thread_ptr, iommu_table_ptr),
        page_ptr_valid(page_ptr),
        pre.thr_mp.dom().contains(quota_thread_ptr),
        pre.prc_mp.dom().contains(process_ptr),
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        pre.prc_mp.spec_index(process_ptr).view().iommu_table == Some(iommu_table_ptr),
        pre.it_mp.dom().contains(iommu_table_ptr),
        !pre.it_mp.spec_index(iommu_table_ptr).view().page_closure().contains(page_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: quota_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == container_ptr,
        pre.thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr),
        pre.thr_mp.spec_index(quota_thread_ptr).view().quota_4k >= 1,
        iommu_table_perms_wf(post.it_mp),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread() is Write,
        post.thr_mp.perms_wf(),
        post.thr_mp.spec_index(quota_thread_ptr).locking_thread() is Write,
    ensures post.inv(),
{
    reveal(install_staged_4k_iommu_table_page_eof_transition_framing);
    let page_index = page_ptr2page_index(page_ptr);
    assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(post.subsystems_inv()) by {
        assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
        assert(page_array_wf(post.pg_arr)) by { reveal(page_array_wf); reveal(Page::mappings_va_valid); };
        assert(thread_perms_wf(post.thr_mp)) by {
            reveal(thread_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked);
            reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_ipc_transit_wf);
        };
    };
    assert(post.memory_management_inv()) by {
        assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { cpu_set_pages_wf_preserved_for_page_state_eq(pre.cpu_set_mp, post.cpu_set_mp, pre.pg_arr, post.pg_arr); };
        assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
            allocator_4k_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_4k_mp, post.allc_4k_mp);
            allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp);
            allocator_1g_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_1g_mp, post.allc_1g_mp);
        };
        assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
        assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
        assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
        assert(page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
            page_pagetable_wf_preserved_for_nonmapped_page_change(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr, page_index);
        };
        assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_match); };
        assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); reveal(process_iommu_table_match); };
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); };
        assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.ctn_mp, post.ctn_mp); };
        assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.prc_mp, post.prc_mp); };
        assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by {
            reveal(process_kernel_pages_owner_wf); reveal(process_iommu_table_match); reveal(iommu_table_pages_wf);
        };
        assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp)) by { reveal(page_object_owner_wf); reveal(container_page_owner_wf); };
        assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
            pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr);
        };
        assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { reveal(iommu_table_pages_wf); page_ptr_roundtrip(); };
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
        assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
        assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.pcid_allc_mp, post.pcid_allc_mp); };
        assert(thread_staged_pages_wf(post.thr_mp, post.pg_arr)) by {
            assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_4k_wf); };
            assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
            assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
        };
        assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
        assert(container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
            container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_4k_mp);
            container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_2m_mp);
            container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_1g_mp);
        };
        assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(post.allc_4k_mp, pre.pg_arr, post.pg_arr, page_index); };
        assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, page_index); };
        assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_index); };
    };
    assert(post.process_management_inv()) by {
        assert(thread_caller_callee_wf(post.thr_mp)) by { thread_caller_callee_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp); };
        assert(thread_dangling_chain_end_wf(post.thr_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thr_mp, post.thr_mp); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { container_thread_endpoint_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { container_thread_scheduler_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp); };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { container_thread_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thr_mp, post.thr_mp); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { process_thread_wf_preserved_for_thread_process_management_fields(post.prc_mp, pre.thr_mp, post.thr_mp); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp, post.cpu_arr); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
    };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf_spec); reveal(iommu_root_table_process_wf); };
}
}
