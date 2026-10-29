use vstd::prelude::*;
use crate::*;

verus! {
/// Removes the 4K leaf `iova`, hidden or (in a table without a domain id) present, from IOMMU table `iommu_table` and its
/// reverse entry from a page that keeps other references or is an I/O page; every other kernel field is unchanged.
#[verifier::opaque]
pub(super) open spec fn remove_iommu_4k_mapping_without_free_eof_transition_framing(pre: KernelK, post: KernelK, iommu_table: RwLockPageTableRoot, iova: VAddr, page_ptr: PagePtr) -> bool {
    let page_index = page_ptr2page_index(page_ptr);
    let old_it = pre.it_mp.spec_index(iommu_table);
    let new_it = post.it_mp.spec_index(iommu_table);
    let old_page = pre.pg_arr.spec_index(page_index).view();
    let new_page = post.pg_arr.spec_index(page_index).view();
    &&& post == (KernelK { it_mp: post.it_mp, pg_arr: post.pg_arr, ..pre })
    &&& post.it_mp.unchanged_except(&pre.it_mp, iommu_table)
    &&& new_it.locking_thread() == old_it.locking_thread()
    &&& new_it.being_killed() == old_it.being_killed()
    &&& new_it.view().mapping_4k() == old_it.view().mapping_4k().remove(iova)
    &&& new_it.view().mapping_2m() == old_it.view().mapping_2m()
    &&& new_it.view().mapping_1g() == old_it.view().mapping_1g()
    &&& new_it.view().page_closure() == old_it.view().page_closure()
    &&& new_it.view().kernel_entries == old_it.view().kernel_entries
    &&& new_it.view().kernel_l4_end == old_it.view().kernel_l4_end
    &&& new_it.view().cr3 == old_it.view().cr3
    &&& new_it.view().pcid == old_it.view().pcid
    &&& new_it.view().did == old_it.view().did
    &&& new_it.view().proc_ptr == old_it.view().proc_ptr
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_index)
    &&& new_page.is_init()
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& new_page.view_rodata() == old_page.view_rodata()
    &&& new_page.view_ghost() == old_page.view_ghost()
    &&& new_page.view().iommu_mappings() == old_page.view().iommu_mappings().remove((iommu_table, iova))
    &&& new_page.view().mappings() == old_page.view().mappings()
    &&& new_page.view().owning_container == old_page.view().owning_container
    &&& new_page.view().ref_count == old_page.view().ref_count - 1
    &&& new_page.view().state == if old_page.view().ref_count > 1 { PageState::Mapped4k } else { PageState::Unavailable }
    &&& old_page.view().ref_count > 1 ==> new_page.view() == (Page { iommu_mappings: new_page.view().iommu_mappings, ref_count: new_page.view().ref_count, ..old_page.view() })
    &&& old_page.view().ref_count == 1 ==> new_page.view() == (Page { state: PageState::Unavailable, iommu_mappings: new_page.view().iommu_mappings, ref_count: 0, perm_4k: new_page.view().perm_4k, ..old_page.view() })
        && new_page.view().perm_4k.view() is None
}

pub(super) proof fn remove_iommu_4k_mapping_without_free_eof(pre: KernelK, post: KernelK, iommu_table: RwLockPageTableRoot, iova: VAddr, page_ptr: PagePtr, was_present: bool)
    requires
        pre.inv(),
        remove_iommu_4k_mapping_without_free_eof_transition_framing(pre, post, iommu_table, iova, page_ptr),
        pre.it_mp.dom().contains(iommu_table),
        pre.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(iova),
        pre.it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(iova).present == was_present,
        was_present ==> pre.it_mp.spec_index(iommu_table).view().did is None,
        pre.it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(iova).addr == page_ptr,
        pre.it_mp.spec_index(iommu_table).locking_thread() is Write,
        page_ptr_valid(page_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count > 1 || pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().is_io_page,
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state is Mapped4k,
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().iommu_mappings().contains((iommu_table, iova)),
        post.it_mp.perms_wf(),
        post.it_mp.spec_index(iommu_table).inv(),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().inv(),
        iommu_table_perms_wf(post.it_mp),
        page_array_wf(post.pg_arr),
        !was_present ==> iommu_table_tlb_entries_present(pre.iommu_tlb, pre.irt.view(), pre.it_mp, iommu_table),
    ensures
        post.inv(),
        iommu_table_tlb_entries_present(post.iommu_tlb, post.irt.view(), post.it_mp, iommu_table),
        !was_present ==> kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        was_present ==> kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &KernelK { it_mp: pre.it_mp, ..post }),
        was_present ==> post.it_mp.spec_index(iommu_table).view().user_view(LockStateU::Unlocked).mapping_4k == pre.it_mp.spec_index(iommu_table).view().user_view(LockStateU::Unlocked).mapping_4k.remove(iova),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
{
    reveal(remove_iommu_4k_mapping_without_free_eof_transition_framing);
    let page_index = page_ptr2page_index(page_ptr);
    assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by {
        assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
        assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
            allocator_4k_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_4k_mp, post.allc_4k_mp);
            allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp);
            allocator_1g_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_1g_mp, post.allc_1g_mp);
        };
        assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
        assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.ctn_mp, post.ctn_mp); };
        assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.prc_mp, post.prc_mp); };
        assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
        assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp)) by { reveal(page_object_owner_wf); };
        assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
        assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
        assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
        assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
        assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.pcid_allc_mp, post.pcid_allc_mp); };
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
        assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { reveal(scheduler_pages_wf); };
        assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_staged_pages_wf(post.thr_mp, post.pg_arr)) by {
            thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
            thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        };
        assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
        assert(page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_lower_wf); };
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); };
        assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_match); };
        assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); reveal(process_iommu_table_match); };
        assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(post.allc_4k_mp, pre.pg_arr, post.pg_arr, page_index); };
        assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, page_index); };
        assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_index); };
    };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp) && iommu_table_tlb_entries_present(post.iommu_tlb, post.irt.view(), post.it_mp, iommu_table)) by {
        reveal(iommu_tlb_wf_spec); reveal(iommu_root_table_process_wf); reveal(iommu_table_tlb_entries_present);
    };
    if was_present {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &KernelK { it_mp: pre.it_mp, ..post })) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); kernel_pagetable_nonlock_fields_unchanged_for_equal(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view());
            reveal(kernel_iommu_table_nonlock_fields_unchanged); kernel_cpu_nonlock_fields_unchanged_for_equal(pre.cpu_arr, post.cpu_arr); kernel_process_nonlock_fields_unchanged_for_equal(pre.prc_mp, post.prc_mp);
            reveal(kernel_thread_nonlock_fields_unchanged);
        };
    } else {
        assert(post.it_mp.spec_index(iommu_table).view().user_view(LockStateU::Unlocked).mapping_4k =~= pre.it_mp.spec_index(iommu_table).view().user_view(LockStateU::Unlocked).mapping_4k);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post)) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); kernel_pagetable_nonlock_fields_unchanged_for_equal(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view());
            reveal(kernel_iommu_table_nonlock_fields_unchanged); kernel_cpu_nonlock_fields_unchanged_for_equal(pre.cpu_arr, post.cpu_arr); kernel_process_nonlock_fields_unchanged_for_equal(pre.prc_mp, post.prc_mp);
            reveal(kernel_thread_nonlock_fields_unchanged);
        };
    }
    kernel_endpoint_nonlock_fields_unchanged_for_equal(pre.ep_mp, post.ep_mp);
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
}
}
