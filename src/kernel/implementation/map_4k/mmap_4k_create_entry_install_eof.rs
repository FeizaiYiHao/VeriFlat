use vstd::prelude::*;
use crate::*;
use super::mmap_4k_build_structure_spec::*;

verus! {
/// Retypes the staged page `page_ptr` into a page-table page of `pagetable_ptr`, adds it to the table's page closure,
/// and charges it to `quota_thread_ptr`; every other kernel field is unchanged.
#[verifier::opaque]
pub(super) open spec fn install_staged_4k_page_table_page_eof_transition_framing(
    pre: KernelK, post: KernelK, level: MissingPageTableLevel, page_ptr: PagePtr, quota_thread_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot,
) -> bool {
    let page_index = page_ptr2page_index(page_ptr);
    let old_pt = pre.pt_mp.spec_index(pagetable_ptr);
    let new_pt = post.pt_mp.spec_index(pagetable_ptr);
    let old_c = pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr);
    let new_c = pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr);
    let old_page = pre.pg_arr.spec_index(page_index).view();
    let new_page = post.pg_arr.spec_index(page_index).view();
    let old_thread = pre.thr_mp.spec_index(quota_thread_ptr);
    let new_thread = post.thr_mp.spec_index(quota_thread_ptr);
    &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, pg_arr: post.pg_arr, thr_mp: post.thr_mp, ..pre })
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr)
    &&& post.pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, post.pt_lower.view().spec_index(pagetable_ptr))
    &&& forall|other_pagetable: RwLockPageTableRoot|
        #![trigger pagetable_c(post.pt_mp, post.pt_lower.view(), other_pagetable)]
        pre.pt_mp.dom().contains(other_pagetable) && other_pagetable != pagetable_ptr ==> pagetable_c(post.pt_mp, post.pt_lower.view(), other_pagetable) == pagetable_c(pre.pt_mp, pre.pt_lower.view(), other_pagetable)
    &&& new_pt.locking_thread() == old_pt.locking_thread()
    &&& new_pt.being_killed() == old_pt.being_killed()
    &&& old_pt.locking_thread() is Write ==> new_pt.view_ghost() == post.pt_lower.view().spec_index(pagetable_ptr)
    &&& !(old_pt.locking_thread() is Write) ==> new_pt.view_ghost() == old_pt.view_ghost()
    &&& new_c.page_closure() == old_c.page_closure().insert(page_ptr)
    &&& new_c.mapping_4k() == old_c.mapping_4k()
    &&& new_c.mapping_2m() == old_c.mapping_2m()
    &&& new_c.mapping_1g() == old_c.mapping_1g()
    &&& new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.spec_resolve_mapping_l3(l4i, l3i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && old_c.window_exists(l4i, l3i) ==> new_c.spec_resolve_mapping_l3(l4i, l3i) == old_c.spec_resolve_mapping_l3(l4i, l3i)
    &&& new_pt.view().kernel_entries == old_pt.view().kernel_entries
    &&& new_pt.view().kernel_l4_end == old_pt.view().kernel_l4_end
    &&& new_pt.view().pcid == old_pt.view().pcid
    &&& new_pt.view().cr3 == old_pt.view().cr3
    &&& new_pt.view().proc_ptr == old_pt.view().proc_ptr
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_index)
    &&& new_page.is_init()
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& new_page.view_rodata() == old_page.view_rodata()
    &&& new_page.view_ghost() == old_page.view_ghost()
    &&& new_page.view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: pagetable_ptr, table_type: PT_TYPE } })
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
    &&& new_thread.view().syscall_progress.view() == mmap_4k_progress_after_directory(old_thread.view().syscall_progress.view(), level)
}

pub(super) proof fn install_staged_4k_page_table_page_eof(
    pre: KernelK, post: KernelK, level: MissingPageTableLevel, page_ptr: PagePtr, quota_thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr,
    pagetable_ptr: RwLockPageTableRoot,
)
    requires
        pre.inv(),
        install_staged_4k_page_table_page_eof_transition_framing(pre, post, level, page_ptr, quota_thread_ptr, pagetable_ptr),
        page_ptr_valid(page_ptr),
        pre.thr_mp.dom().contains(quota_thread_ptr),
        pre.prc_mp.dom().contains(process_ptr),
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        pre.pt_mp.dom().contains(pagetable_ptr),
        !pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).page_closure().contains(page_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: quota_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == container_ptr,
        pre.thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr),
        pre.thr_mp.spec_index(quota_thread_ptr).view().quota_4k >= 1,
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        post.pt_mp.spec_index(pagetable_ptr).locking_thread() is Write || post.pt_mp.spec_index(pagetable_ptr).locking_thread() is Read,
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread() is Write,
        post.thr_mp.perms_wf(),
        post.thr_mp.spec_index(quota_thread_ptr).locking_thread() is Write,
    ensures post.inv(),
{
    reveal(install_staged_4k_page_table_page_eof_transition_framing);
    let page_index = page_ptr2page_index(page_ptr);
    assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(post.subsystems_inv()) by {
        assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
        assert(page_array_wf(post.pg_arr)) by { reveal(page_array_wf); reveal(Page::mappings_va_valid); };
        assert(thread_perms_wf(post.thr_mp)) by {
            reveal(thread_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked);
            reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_ipc_partner_only_when_wlocked); reveal(thread_peer_implies_ipc_partner);
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
        assert(page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(pagetable_lower_wf); reveal(pagetable_perms_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); };
        assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { process_pagetable_match_preserved_for_pagetable_fields_eq(post.prc_mp, pre.pt_mp, post.pt_mp); };
        assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_match); };
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { page_iommu_table_wf_preserved_for_nonmapped_page_change(post.ctn_mp, post.prc_mp, pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr, page_index); };
        assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.ctn_mp, post.ctn_mp); };
        assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.prc_mp, post.prc_mp); };
        assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { reveal(process_kernel_pages_owner_wf); reveal(process_pagetable_match); reveal(pagetable_pages_wf); };
        assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp)) by { reveal(page_object_owner_wf); reveal(container_page_owner_wf); };
        assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(pagetable_pages_wf); };
        assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
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
        assert(thread_caller_callee_wf(post.thr_mp)) by {
            assert(thread_process_management_fields_unchanged(pre.thr_mp, post.thr_mp));
            thread_caller_callee_wf_preserved_for_thread_process_management_fields(pre.thr_mp, post.thr_mp);
        };
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
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr); pre.default_pagetable_wf_at(pagetable_ptr);
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip;
        reveal(PageTableC::wf_mapping_4k); reveal(PageTableC::wf_mapping_2m); reveal(tlb_wf_spec);
    };
}
}
