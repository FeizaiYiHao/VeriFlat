use vstd::prelude::*;
use crate::*;

verus! {
/// Removes the non-present 4K leaf `va` from `pagetable` and its mapping record from a page that keeps other references
/// or is an I/O page; every other kernel field is unchanged.
#[verifier::opaque]
pub(super) open spec fn remove_4k_mapping_without_free_eof_transition_framing(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr) -> bool {
    let page_index = page_ptr2page_index(page_ptr);
    let old_pt = pre.pt_mp.spec_index(pagetable);
    let new_pt = post.pt_mp.spec_index(pagetable);
    let old_c = pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable);
    let old_page = pre.pg_arr.spec_index(page_index).view();
    let new_page = post.pg_arr.spec_index(page_index).view();
    &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, pg_arr: post.pg_arr, ..pre })
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable)
    &&& post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable))
    &&& forall|p: RwLockPageTableRoot| #![trigger pagetable_c(post.pt_mp, post.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != pagetable ==> pagetable_c(post.pt_mp, post.pt_lower.view(), p) == pagetable_c(pre.pt_mp, pre.pt_lower.view(), p)
    &&& new_pt.locking_thread() == old_pt.locking_thread()
    &&& new_pt.being_killed() == old_pt.being_killed()
    &&& new_pt.view() == old_pt.view()
    &&& new_c.mapping_4k() == old_c.mapping_4k().remove(va)
    &&& new_c.mapping_2m() == old_c.mapping_2m()
    &&& new_c.mapping_1g() == old_c.mapping_1g()
    &&& new_c.page_closure() == old_c.page_closure()
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_index)
    &&& new_page.is_init()
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& new_page.view_rodata() == old_page.view_rodata()
    &&& new_page.view_ghost() == old_page.view_ghost()
    &&& new_page.view().mappings() == old_page.view().mappings().remove((pagetable, va))
    &&& new_page.view().iommu_mappings() == old_page.view().iommu_mappings()
    &&& new_page.view().ref_count == old_page.view().ref_count - 1
    &&& new_page.view().state == if old_page.view().ref_count > 1 { PageState::Mapped4k } else { PageState::Unavailable }
    &&& old_page.view().ref_count > 1 ==> new_page.view() == (Page { mappings: new_page.view().mappings, ref_count: new_page.view().ref_count, ..old_page.view() })
    &&& old_page.view().ref_count == 1 ==> new_page.view() == (Page { state: PageState::Unavailable, mappings: new_page.view().mappings, ref_count: 0, perm_4k: new_page.view().perm_4k, ..old_page.view() })
        && new_page.view().perm_4k.view() is None
}

pub(super) proof fn remove_4k_mapping_without_free_eof(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr)
    requires
        pre.inv(),
        remove_4k_mapping_without_free_eof_transition_framing(pre, post, pagetable, va, page_ptr),
        pre.pt_mp.dom().contains(pagetable),
        pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        !pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().spec_index(va).present,
        pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().spec_index(va).addr == page_ptr,
        page_ptr_valid(page_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count > 1 || pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().is_io_page,
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state is Mapped4k,
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().mappings().contains((pagetable, va)),
        pagetable_tlb_entries_present(pre.cpu_tlb, pre.cpu_arr, pre.pcid_needflush, pagetable, pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable)),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_wlocked(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().inv(),
    ensures post.inv(),
{
    reveal(remove_4k_mapping_without_free_eof_transition_framing);
    let page_index = page_ptr2page_index(page_ptr);
    assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(post.subsystems_inv()) by { reveal(page_array_wf); reveal(KernelK::default_pagetable_wf); };
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
        assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
            pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr);
        };
        assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_4k_page_pagetable_wf); reveal(pagetable_lower_wf); };
        assert(page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_lower_wf); };
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); reveal(mapped_4k_page_pagetable_wf); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by {
            assert(pre.pg_arr.spec_index(page_index).view().view().ref_count == 1 ==> pre.pg_arr.spec_index(page_index).view().view().iommu_mappings().len() == 0);
            reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf);
        };
        assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_match); };
        assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_match); };
        assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(post.allc_4k_mp, pre.pg_arr, post.pg_arr, page_index); };
        assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, page_index); };
        assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_index); };
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}
}
