use vstd::prelude::*;
use crate::*;
use super::mmap_4k_build_structure_spec::*;

verus! {
/// Retypes the staged page `pg_ptr` into a page-table page of `pagetable_ptr`, adds it to the table's page closure,
/// and charges it to `quota_thrd_ptr`; every entry the table held stays, the stale records stay, and every other kernel
/// field is unchanged.
#[verifier::opaque]
pub(super) open spec fn install_staged_4k_page_table_page_eof_transition_framing(
    pre: KernelK, post: KernelK, level: MissingPageTableLevel, pg_ptr: PagePtr, quota_thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot,
) -> bool {
    let pg_idx = page_ptr2page_index(pg_ptr);
    let old_pt = pre.pt_mp.spec_index(pagetable_ptr);
    let new_pt = post.pt_mp.spec_index(pagetable_ptr);
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr);
    let old_page = pre.pg_arr.spec_index(pg_idx).view();
    let new_page = post.pg_arr.spec_index(pg_idx).view();
    let old_thread = pre.thrd_mp.spec_index(quota_thrd_ptr);
    let new_thread = post.thrd_mp.spec_index(quota_thrd_ptr);
    &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, pg_arr: post.pg_arr, thrd_mp: post.thrd_mp, ..pre })
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr)
    &&& post.pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, post.pt_lower.view().spec_index(pagetable_ptr))
    &&& forall|other_pagetable: RwLockPageTableRoot|
        #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), other_pagetable)]
        pre.pt_mp.dom().contains(other_pagetable) && other_pagetable != pagetable_ptr ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), other_pagetable) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), other_pagetable)
    &&& new_pt.locking_thread() == old_pt.locking_thread()
    &&& new_pt.being_killed() == old_pt.being_killed()
    &&& old_pt.locking_thread() is Write ==> new_pt.view_ghost() == post.pt_lower.view().spec_index(pagetable_ptr)
    &&& !(old_pt.locking_thread() is Write) ==> new_pt.view_ghost() == old_pt.view_ghost()
    &&& !(old_pt.locking_thread() is Write) ==> new_pt.view() == old_pt.view()
    &&& new_c.page_closure() == old_c.page_closure().insert(pg_ptr)
    &&& new_c.mapping_4k() == old_c.mapping_4k()
    &&& new_c.mapping_2m() == old_c.mapping_2m()
    &&& new_c.mapping_1g() == old_c.mapping_1g()
    &&& new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
    &&& new_c.higher.table_stale_cpus == old_c.higher.table_stale_cpus
    &&& forall|l4i: L4Index| #![trigger new_c.spec_held_l4(l4i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && old_c.spec_held_l4(l4i) is Some ==> new_c.spec_held_l4(l4i) == old_c.spec_held_l4(l4i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.spec_held_l3(l4i, l3i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && old_c.spec_held_l3(l4i, l3i) is Some ==> new_c.spec_held_l3(l4i, l3i) == old_c.spec_held_l3(l4i, l3i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && old_c.spec_held_l2(l4i, l3i, l2i) is Some
            ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.spec_resolve_mapping_l3(l4i, l3i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && old_c.window_exists(l4i, l3i) ==> new_c.spec_resolve_mapping_l3(l4i, l3i) == old_c.spec_resolve_mapping_l3(l4i, l3i)
    &&& new_pt.view().kernel_entries == old_pt.view().kernel_entries
    &&& new_pt.view().kernel_l4_end == old_pt.view().kernel_l4_end
    &&& new_pt.view().pcid == old_pt.view().pcid
    &&& new_pt.view().cr3 == old_pt.view().cr3
    &&& new_pt.view().proc_ptr == old_pt.view().proc_ptr
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, pg_idx)
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
    &&& post.thrd_mp.unchanged_except(&pre.thrd_mp, quota_thrd_ptr)
    &&& new_thread.is_init()
    &&& new_thread.locking_thread() == old_thread.locking_thread()
    &&& new_thread.being_killed() == old_thread.being_killed()
    &&& new_thread.killer_info() == old_thread.killer_info()
    &&& new_thread.view_rodata() == old_thread.view_rodata()
    &&& new_thread.view_ghost() == old_thread.view_ghost()
    &&& new_thread.view() == (Thread {
        quota_4k: new_thread.view().quota_4k, temp_alloc_cache_4k: new_thread.view().temp_alloc_cache_4k, syscall_progress: new_thread.view().syscall_progress, ..old_thread.view()
    })
    &&& new_thread.view().temp_alloc_cache_4k.view() == old_thread.view().temp_alloc_cache_4k.view().remove(pg_ptr)
    &&& new_thread.view().quota_4k == old_thread.view().quota_4k - 1
    &&& new_thread.view().syscall_progress.view() == mmap_4k_progress_after_directory(old_thread.view().syscall_progress.view(), level)
}

proof fn install_staged_4k_page_table_page_eof_subsystems_inv(
    pre: KernelK, post: KernelK, level: MissingPageTableLevel, pg_ptr: PagePtr, quota_thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr,
    pagetable_ptr: RwLockPageTableRoot,
)
    requires
        pre.inv(),
        install_staged_4k_page_table_page_eof_transition_framing(pre, post, level, pg_ptr, quota_thrd_ptr, pagetable_ptr),
        page_ptr_valid(pg_ptr),
        pre.thrd_mp.dom().contains(quota_thrd_ptr),
        pre.pt_mp.dom().contains(pagetable_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: quota_thrd_ptr }),
        pre.thrd_mp.spec_index(quota_thrd_ptr).view().temp_alloc_cache_4k.view().contains(pg_ptr),
        pre.thrd_mp.spec_index(quota_thrd_ptr).view().quota_4k >= 1,
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() is Write,
        post.thrd_mp.perms_wf(),
        post.thrd_mp.spec_index(quota_thrd_ptr).locking_thread() is Write,
    ensures post.subsystems_inv(),
{
    reveal(install_staged_4k_page_table_page_eof_transition_framing);
    assert(index_valid(NUM_PAGES, page_ptr2page_index(pg_ptr))) by { page_ptr_valid_imply_page_index_valid(); };
    assert(pagetable_table_stale_cpus_only_when_write_locked(post.pt_mp)) by { reveal(pagetable_table_stale_cpus_only_when_write_locked); };
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
    assert(page_array_wf(post.pg_arr)) by { reveal(page_array_wf); reveal(Page::mappings_va_valid); };
    assert(thread_perms_wf(post.thrd_mp)) by {
        reveal(thread_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked);
        reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_ipc_transit_wf);
    };
}

proof fn install_staged_4k_page_table_page_eof_pagetable_pages(
    pre: KernelK, post: KernelK, level: MissingPageTableLevel, pg_ptr: PagePtr, quota_thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr,
    pagetable_ptr: RwLockPageTableRoot,
)
    requires
        pre.inv(),
        install_staged_4k_page_table_page_eof_transition_framing(pre, post, level, pg_ptr, quota_thrd_ptr, pagetable_ptr),
        page_ptr_valid(pg_ptr),
        pre.thrd_mp.dom().contains(quota_thrd_ptr),
        pre.prc_mp.dom().contains(prc_ptr),
        pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == ctn_ptr,
        pre.prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
        !(pre.prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied) && !(pre.prc_mp.spec_index(prc_ptr).view().state.view() is Zombie),
        pre.pt_mp.dom().contains(pagetable_ptr),
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).page_closure().contains(pg_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: quota_thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == ctn_ptr,
        post.subsystems_inv(),
        post.pt_mp.spec_index(pagetable_ptr).locking_thread() is Write || post.pt_mp.spec_index(pagetable_ptr).locking_thread() is Read,
    ensures
        page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view()),
        iommu_table_no_huge_leaf_wf(post.it_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr),
        pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
{
    reveal(install_staged_4k_page_table_page_eof_transition_framing);
    assert(index_valid(NUM_PAGES, page_ptr2page_index(pg_ptr))) by { page_ptr_valid_imply_page_index_valid(); };
    assert(page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        pre.default_pagetable_wf_at(pagetable_ptr); broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip;
        reveal(pagetable_lower_wf); reveal(pagetable_perms_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
    };
    assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { process_pagetable_match_preserved_for_pagetable_fields_eq(post.prc_mp, pre.pt_mp, post.pt_mp); };
    assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_no_huge_leaf_wf); };
    assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by {
        assert(post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().mappings() == pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().mappings());
        reveal(process_emptied_tables_wf); reveal(process_pagetable_wf);
    };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { reveal(process_object_pages_owner_wf); reveal(process_pagetable_wf); reveal(pagetable_pages_wf); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(pagetable_pages_wf); };
}

proof fn install_staged_4k_page_table_page_eof_memory_management_inv(
    pre: KernelK, post: KernelK, level: MissingPageTableLevel, pg_ptr: PagePtr, quota_thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr,
    pagetable_ptr: RwLockPageTableRoot,
)
    requires
        pre.inv(),
        install_staged_4k_page_table_page_eof_transition_framing(pre, post, level, pg_ptr, quota_thrd_ptr, pagetable_ptr),
        page_ptr_valid(pg_ptr),
        pre.thrd_mp.dom().contains(quota_thrd_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: quota_thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.thrd_mp.spec_index(quota_thrd_ptr).view().temp_alloc_cache_4k.view().contains(pg_ptr),
        pre.thrd_mp.spec_index(quota_thrd_ptr).view().quota_4k >= 1,
        post.subsystems_inv(),
        page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view()),
        iommu_table_no_huge_leaf_wf(post.it_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr),
        pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
    ensures post.memory_management_inv(),
{
    reveal(install_staged_4k_page_table_page_eof_transition_framing);
    let pg_idx = page_ptr2page_index(pg_ptr);
    assert(index_valid(NUM_PAGES, pg_idx)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { cpu_set_pages_wf_preserved_for_page_state_eq(pre.cpu_set_mp, post.cpu_set_mp, pre.pg_arr, post.pg_arr); };
    assert(allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.allc_4k_mp, post.allc_4k_mp, pre.pg_arr, post.pg_arr);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.allc_2m_mp, post.allc_2m_mp, pre.pg_arr, post.pg_arr);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.allc_1g_mp, post.allc_1g_mp, pre.pg_arr, post.pg_arr);
    };
    assert(container_owned_pages_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { page_iommu_table_wf_preserved_for_nonmapped_page_change(post.ctn_mp, post.prc_mp, pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr, pg_idx); };
    assert(container_pages_wf(post.ctn_mp, post.pg_arr)) by { container_pages_wf_preserved_for_page_state_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(process_pages_wf(post.prc_mp, post.pg_arr)) by { process_pages_wf_preserved_for_page_state_eq(pre.prc_mp, post.prc_mp, pre.pg_arr, post.pg_arr); };
    assert(page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr)) by { reveal(page_object_owner_wf); reveal(container_owned_pages_wf); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pcid_allc_mp, post.pcid_allc_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_pages_wf(post.thrd_mp, post.pg_arr)) by {
        assert(thread_staged_4k_pages_wf(post.thrd_mp, post.pg_arr)) by { reveal(thread_staged_4k_pages_wf); };
        assert(thread_staged_2m_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_staged_2m_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_staged_1g_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_staged_1g_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
    };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
    assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); };
    assert(container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_4k_mp);
        container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_2m_mp);
        container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_1g_mp);
    };
    assert(allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(post.allc_4k_mp, pre.pg_arr, post.pg_arr, pg_idx); };
    assert(allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, pg_idx); };
    assert(allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, pg_idx); };
}

proof fn install_staged_4k_page_table_page_eof_process_management_inv(
    pre: KernelK, post: KernelK, level: MissingPageTableLevel, pg_ptr: PagePtr, quota_thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot,
)
    requires
        pre.inv(),
        install_staged_4k_page_table_page_eof_transition_framing(pre, post, level, pg_ptr, quota_thrd_ptr, pagetable_ptr),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(install_staged_4k_page_table_page_eof_transition_framing);
    assert(thread_caller_callee_wf(post.thrd_mp)) by {
        assert(thread_process_management_fields_unchanged(pre.thrd_mp, post.thrd_mp));
        thread_caller_callee_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp);
    };
    assert(thread_dangling_chain_end_wf(post.thrd_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thrd_mp, post.thrd_mp); };
    assert(thread_endpoint_ref_counter_wf(post.thrd_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.ep_mp); };
    assert(thread_endpoint_queue_wf(post.thrd_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.ep_mp); };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thrd_mp, post.ep_mp)) by { container_thread_endpoint_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp, post.ep_mp); };
    assert(container_thread_scheduler_wf(post.ctn_mp, post.thrd_mp, post.sched_mp)) by { container_thread_scheduler_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp, post.sched_mp); };
    assert(container_thread_wf(post.ctn_mp, post.thrd_mp)) by { container_thread_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp); };
    assert(process_thread_wf(post.prc_mp, post.thrd_mp)) by { process_thread_wf_preserved_for_thread_process_management_fields(post.prc_mp, pre.thrd_mp, post.thrd_mp); };
    assert(thread_cpu_wf(post.thrd_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.cpu_arr); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
}

/// Point form of the structure-cache closure at one `(cpu_id, pcid)`: an entry the cache keeps was held by the table before,
/// so the table still holds it, and it resolves afterwards exactly when it resolved before.
broadcast proof fn install_staged_4k_page_table_page_eof_structure_cache_at(
    pre: KernelK, post: KernelK, level: MissingPageTableLevel, pg_ptr: PagePtr, quota_thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid,
)
    requires
        pre.inv(),
        install_staged_4k_page_table_page_eof_transition_framing(pre, post, level, pg_ptr, quota_thrd_ptr, pagetable_ptr),
        pre.pt_mp.dom().contains(pagetable_ptr),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
    ensures
        #![trigger post.cpu_tlb.structure_cache((cpu_id, pcid)), install_staged_4k_page_table_page_eof_transition_framing(pre, post, level, pg_ptr, quota_thrd_ptr, pagetable_ptr)]
        index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID && !post.cpu_tlb.structure_cache((cpu_id, pcid)).is_empty()
        && (!post.pcid_needflush.spec_index(cpu_id, pcid).view().needflush || post.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid) ==> {
            let dirty_entry = post.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
            let table = whole_pagetable(post.pt_mp, post.pt_lower.view(), dirty_entry.unwrap().pagetable_ptr);
            &&& dirty_entry is Some
            &&& post.pt_mp.dom().contains(dirty_entry.unwrap().pagetable_ptr)
            &&& single_structure_cache_subset_of_whole_pagetable(post.cpu_tlb.structure_cache((cpu_id, pcid)), table)
            &&& single_structure_cache_present_or_stale(post.cpu_tlb.structure_cache((cpu_id, pcid)), table, cpu_id)
        },
{
    reveal(install_staged_4k_page_table_page_eof_transition_framing);
    structure_cache_wf_at(pre.cpu_tlb, pre.pt_mp, pre.pt_lower.view(), pre.cpu_arr, pre.pcid_needflush, cpu_id, pcid);
    if post.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr == pagetable_ptr {
        pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr); pagetable_lower_wf_at(post.pt_mp, post.pt_lower.view(), pagetable_ptr);
        broadcast use PageTableHigher::spec_resolve_mapping_l4_some_implies_spec_held_l4_eq, PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq,
            WholePageTable::spec_resolve_mapping_l2_some_implies_spec_held_l2_eq;
    }
}

pub(super) proof fn install_staged_4k_page_table_page_eof(
    pre: KernelK, post: KernelK, level: MissingPageTableLevel, pg_ptr: PagePtr, quota_thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr,
    pagetable_ptr: RwLockPageTableRoot,
)
    requires
        pre.inv(),
        install_staged_4k_page_table_page_eof_transition_framing(pre, post, level, pg_ptr, quota_thrd_ptr, pagetable_ptr),
        page_ptr_valid(pg_ptr),
        pre.thrd_mp.dom().contains(quota_thrd_ptr),
        pre.prc_mp.dom().contains(prc_ptr),
        pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == ctn_ptr,
        pre.prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
        !(pre.prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied) && !(pre.prc_mp.spec_index(prc_ptr).view().state.view() is Zombie),
        pre.pt_mp.dom().contains(pagetable_ptr),
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).page_closure().contains(pg_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: quota_thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.thrd_mp.spec_index(quota_thrd_ptr).view().temp_alloc_cache_4k.view().contains(pg_ptr),
        pre.thrd_mp.spec_index(quota_thrd_ptr).view().quota_4k >= 1,
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        post.pt_mp.spec_index(pagetable_ptr).locking_thread() is Write || post.pt_mp.spec_index(pagetable_ptr).locking_thread() is Read,
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() is Write,
        post.thrd_mp.perms_wf(),
        post.thrd_mp.spec_index(quota_thrd_ptr).locking_thread() is Write,
    ensures post.inv(),
{
    install_staged_4k_page_table_page_eof_subsystems_inv(pre, post, level, pg_ptr, quota_thrd_ptr, prc_ptr, ctn_ptr, pagetable_ptr);
    install_staged_4k_page_table_page_eof_pagetable_pages(pre, post, level, pg_ptr, quota_thrd_ptr, prc_ptr, ctn_ptr, pagetable_ptr);
    install_staged_4k_page_table_page_eof_memory_management_inv(pre, post, level, pg_ptr, quota_thrd_ptr, prc_ptr, ctn_ptr, pagetable_ptr);
    install_staged_4k_page_table_page_eof_process_management_inv(pre, post, level, pg_ptr, quota_thrd_ptr, pagetable_ptr);
    reveal(install_staged_4k_page_table_page_eof_transition_framing);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_pagetable_pcid_match); };
    pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr); pagetable_lower_wf_at(post.pt_mp, post.pt_lower.view(), pagetable_ptr);
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        pre.default_pagetable_wf_at(pagetable_ptr);
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, PageTableHigher::spec_resolve_mapping_l4_some_implies_spec_held_l4_eq,
            PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq, WholePageTable::spec_resolve_mapping_l2_some_implies_spec_held_l2_eq,
            WholePageTable::spec_resolve_mapping_4k_l1_some_implies_spec_held_4k_l1_eq, WholePageTable::spec_resolve_mapping_2m_l2_some_implies_spec_held_2m_l2_eq;
        reveal(WholePageTable::wf_mapping_4k); reveal(WholePageTable::wf_mapping_2m); reveal(cpu_tlb_wf);
    };
    assert(structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(structure_cache_wf); broadcast use install_staged_4k_page_table_page_eof_structure_cache_at; };
}

/// An L3 install at `indices` keeps every held L3 entry of a user root resolvable: a held entry other than the new one names an
/// L2 page that the table held before, under the same path, so it resolved before and still does.
pub(super) proof fn install_staged_4k_page_table_page_eof_held_l3_resolves(pre: KernelK, post: KernelK, pagetable_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index), pg_ptr: PagePtr)
    requires
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).wf(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).wf(),
        post.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end == pre.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end,
        pre.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= indices.0 && pei_valid(indices.0) && pei_valid(indices.1),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == pg_ptr,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.l2_perms.dom() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.l2_perms.dom().insert(pg_ptr),
        forall|l4i: L4Index, l3i: L3Index| #![trigger whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_held_l3(l4i, l3i)]
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_held_l3(l4i, l3i) is Some
                ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).spec_held_l3(l4i, l3i) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_held_l3(l4i, l3i),
        forall|l4i: L4Index, l3i: L3Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i)]
            pre.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && !(l4i == indices.0 && l3i == indices.1)
                ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i),
    ensures
        (forall|l4i: L4Index, l3i: L3Index| #![trigger pre.pt_mp.spec_index(pagetable_ptr).view().spec_held_l3(l4i, l3i)]
            pre.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pre.pt_mp.spec_index(pagetable_ptr).view().spec_held_l3(l4i, l3i) is Some
                ==> pre.pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(l4i, l3i) is Some)
            ==> forall|l4i: L4Index, l3i: L3Index| #![trigger post.pt_mp.spec_index(pagetable_ptr).view().spec_held_l3(l4i, l3i)]
                post.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && post.pt_mp.spec_index(pagetable_ptr).view().spec_held_l3(l4i, l3i) is Some
                    ==> post.pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(l4i, l3i) is Some,
{
    broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at, PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq;
    reveal(PageTableHigher::wf_l4); reveal(WholePageTable::l3_links_l2_wf); reveal(WholePageTable::tables_reachable_wf);
}
}
