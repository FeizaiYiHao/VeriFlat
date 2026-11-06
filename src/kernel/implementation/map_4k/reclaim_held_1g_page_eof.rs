use vstd::prelude::*;
use crate::*;

verus! {
/// Clears the record `(pagetable, va)` of a held 1G leaf from the page `pg_ptr`, which keeps other references, and clears that leaf; every other held entry of the table and every other kernel field is unchanged.
#[verifier::opaque]
pub(super) open spec fn remove_held_1g_mapping_without_free_eof_transition_framing(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr) -> bool {
    let pg_idx = page_ptr2page_index(pg_ptr);
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    let old_page = pre.pg_arr.spec_index(pg_idx).view();
    let new_page = post.pg_arr.spec_index(pg_idx).view();
    &&& post == (KernelK { pt_mp: post.pt_mp, pg_arr: post.pg_arr, ..pre })
    &&& post.pt_lower == pre.pt_lower
    &&& post.pt_mp.dom() == pre.pt_mp.dom()
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable)
    &&& forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != pagetable ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p)
    &&& post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread()
    &&& post.pt_mp.spec_index(pagetable).being_killed() == pre.pt_mp.spec_index(pagetable).being_killed()
    &&& post.pt_mp.spec_index(pagetable).view_ghost() == pre.pt_mp.spec_index(pagetable).view_ghost()
    &&& new_c.lower == old_c.lower
    &&& new_c.higher == (PageTableHigher { l3_tables: new_c.higher.l3_tables, mapping_1g: new_c.higher.mapping_1g, ..old_c.higher })
    &&& new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_2m() == old_c.mapping_2m() && new_c.mapping_1g() == old_c.mapping_1g().remove(va)
    &&& new_c.page_closure() == old_c.page_closure()
    &&& forall|l4i: L4Index| #![trigger new_c.spec_resolve_mapping_l4(l4i)] old_c.kernel_l4_end() <= l4i && pei_valid(l4i) ==> new_c.spec_resolve_mapping_l4(l4i) == old_c.spec_resolve_mapping_l4(l4i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.spec_resolve_mapping_l3(l4i, l3i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> new_c.spec_resolve_mapping_l3(l4i, l3i) == old_c.spec_resolve_mapping_l3(l4i, l3i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.spec_resolve_mapping_1g_l3(l4i, l3i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (spec_v2l4index(va), spec_v2l3index(va)) ==> new_c.spec_resolve_mapping_1g_l3(l4i, l3i) == old_c.spec_resolve_mapping_1g_l3(l4i, l3i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_resolve_mapping_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_resolve_mapping_l2(l4i, l3i, l2i) == old_c.spec_resolve_mapping_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == old_c.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_c.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)
    &&& forall|l4i: L4Index| #![trigger new_c.spec_held_l4(l4i)] old_c.kernel_l4_end() <= l4i && pei_valid(l4i) ==> new_c.spec_held_l4(l4i) == old_c.spec_held_l4(l4i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.spec_held_l3(l4i, l3i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> new_c.spec_held_l3(l4i, l3i) == old_c.spec_held_l3(l4i, l3i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.spec_held_1g_l3(l4i, l3i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (spec_v2l4index(va), spec_v2l3index(va)) ==> new_c.spec_held_1g_l3(l4i, l3i) == old_c.spec_held_1g_l3(l4i, l3i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& new_c.spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is None
    &&& new_c.spec_resolve_mapping_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is None
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, pg_idx)
    &&& new_page.is_init()
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& new_page.view_rodata() == old_page.view_rodata()
    &&& new_page.view_ghost() == old_page.view_ghost()
    &&& new_page.view().mappings() == old_page.view().mappings().remove((pagetable, va))
    &&& new_page.view().iommu_mappings() == old_page.view().iommu_mappings()
    &&& new_page.view().state == old_page.view().state
    &&& new_page.view().ref_count == old_page.view().ref_count - 1
    &&& new_page.view() == (Page { mappings: new_page.view().mappings, ref_count: new_page.view().ref_count, ..old_page.view() })
}

/// The page-table relations close after dropping the held 1G leaf `va` and its mapping record on `pg_ptr`.
proof fn remove_held_1g_mapping_without_free_eof_page_tables(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr)
    requires
        pre.inv(),
        remove_held_1g_mapping_without_free_eof_transition_framing(pre, post, pagetable, va, pg_ptr),
        pre.pt_mp.dom().contains(pagetable),
        va_1g_valid(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr == pg_ptr,
        page_ptr_valid(pg_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().ref_count > 1,
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Mapped1g,
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().mappings().contains((pagetable, va)),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().inv(),
        post.subsystems_inv(),
    ensures
        page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        iommu_table_no_huge_leaf_wf(post.it_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
{
    reveal(remove_held_1g_mapping_without_free_eof_transition_framing);
    let pg_idx = page_ptr2page_index(pg_ptr);
    assert(index_valid(NUM_PAGES, pg_idx)) by { page_ptr_valid_imply_page_index_valid(); };
    page_array_wf_at(pre.pg_arr, pg_idx);
    pre.default_pagetable_wf_at(pagetable);
    assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use spec_va_4k_valid_index_roundtrip; reveal(mapped_4k_page_pagetable_wf); reveal(page_array_wf); reveal(pagetable_lower_wf);
    };
    assert(mapped_2m_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use spec_va_2m_valid_index_roundtrip; reveal(mapped_2m_page_pagetable_wf); reveal(page_array_wf); reveal(pagetable_lower_wf);
    };
    assert(mapped_1g_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use spec_va_1g_valid_index_roundtrip, spec_index2va_2m_valid; reveal(mapped_1g_page_pagetable_wf); reveal(page_array_wf); reveal(pagetable_lower_wf);
    };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); reveal(page_array_wf); };
    assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_wf); };
    assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_wf); };
}

/// The memory-management invariant closes after dropping the held 1G leaf `va` and its mapping record on `pg_ptr`.
proof fn remove_held_1g_mapping_without_free_eof_memory_management_inv(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr)
    requires
        pre.inv(),
        remove_held_1g_mapping_without_free_eof_transition_framing(pre, post, pagetable, va, pg_ptr),
        page_ptr_valid(pg_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Mapped1g,
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().inv(),
        post.subsystems_inv(),
        page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        iommu_table_no_huge_leaf_wf(post.it_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
    ensures post.memory_management_inv(),
{
    reveal(remove_held_1g_mapping_without_free_eof_transition_framing);
    let pg_idx = page_ptr2page_index(pg_ptr);
    assert(index_valid(NUM_PAGES, pg_idx)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
    assert(allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.allc_4k_mp, post.allc_4k_mp, pre.pg_arr, post.pg_arr);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.allc_2m_mp, post.allc_2m_mp, pre.pg_arr, post.pg_arr);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.allc_1g_mp, post.allc_1g_mp, pre.pg_arr, post.pg_arr);
    };
    assert(container_owned_pages_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(container_pages_wf(post.ctn_mp, post.pg_arr)) by { container_pages_wf_preserved_for_page_state_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(process_pages_wf(post.prc_mp, post.pg_arr)) by { process_pages_wf_preserved_for_page_state_eq(pre.prc_mp, post.prc_mp, pre.pg_arr, post.pg_arr); };
    assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); };
    assert(page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr)) by { reveal(page_object_owner_wf); };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
    assert(pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pcid_allc_mp, post.pcid_allc_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { reveal(scheduler_pages_wf); };
    assert(thread_staged_pages_wf(post.thrd_mp, post.pg_arr)) by {
        thread_staged_4k_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
        thread_staged_2m_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
        thread_staged_1g_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
    };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
    assert(allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(post.allc_4k_mp, pre.pg_arr, post.pg_arr, pg_idx); };
    assert(allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, pg_idx); };
    assert(allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, pg_idx); };
}

/// `remove_held_1g_mapping_without_free` EOF: the CPU TLB and paging-structure caches stay consistent after the held 1G leaf `va` of `pagetable` is cleared: it does not resolve and the table lists no CPU stale, so no TLB entry or cached directory entry names it.
proof fn remove_held_1g_mapping_without_free_eof_cpu_caches(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr)
    requires
        pre.inv(),
        remove_held_1g_mapping_without_free_eof_transition_framing(pre, post, pagetable, va, pg_ptr),
        pre.pt_mp.dom().contains(pagetable),
        va_1g_valid(va),
        pre.pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l4(spec_v2l4index(va)) is None
            || !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va))->0.perm.present,
        pre.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
    ensures
        cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
        structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    reveal(remove_held_1g_mapping_without_free_eof_transition_framing);
    pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable); pagetable_lower_wf_at(post.pt_mp, post.pt_lower.view(), pagetable);
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        reveal(cpu_tlb_wf); reveal(WholePageTable::wf_mapping_4k); reveal(WholePageTable::wf_mapping_2m); reveal(PageTableHigher::wf_mapping_1g);
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_va_1g_valid_index_roundtrip;
    };
    assert(structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(structure_cache_wf); };
}

/// EOF closure of `remove_held_1g_mapping_without_free`: the held 1G leaf `va` and its record leave together, and no CPU caches the leaf because it does not resolve while the table lists no CPU stale.
pub(super) proof fn remove_held_1g_mapping_without_free_eof(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr)
    requires
        pre.inv(),
        remove_held_1g_mapping_without_free_eof_transition_framing(pre, post, pagetable, va, pg_ptr),
        pre.pt_mp.dom().contains(pagetable),
        va_1g_valid(va),
        pre.pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l4(spec_v2l4index(va)) is None
            || !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va))->0.perm.present,
        pre.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr == pg_ptr,
        page_ptr_valid(pg_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().ref_count > 1,
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Mapped1g,
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().mappings().contains((pagetable, va)),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().inv(),
    ensures
        post.inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
{
    reveal(remove_held_1g_mapping_without_free_eof_transition_framing);
    assert(index_valid(NUM_PAGES, page_ptr2page_index(pg_ptr))) by { page_ptr_valid_imply_page_index_valid(); };
    assert(post.subsystems_inv()) by { reveal(page_array_wf); reveal(KernelK::default_pagetable_wf); reveal(pagetable_table_stale_cpus_only_when_write_locked); };
    remove_held_1g_mapping_without_free_eof_page_tables(pre, post, pagetable, va, pg_ptr);
    remove_held_1g_mapping_without_free_eof_memory_management_inv(pre, post, pagetable, va, pg_ptr);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_pagetable_pcid_match); };
    remove_held_1g_mapping_without_free_eof_cpu_caches(pre, post, pagetable, va, pg_ptr);
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    assert(new_c.user_view(LockStateU::Unlocked).mapping_1g =~= old_c.user_view(LockStateU::Unlocked).mapping_1g) by {
        broadcast use spec_va_1g_valid_index_roundtrip; pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable); old_c.higher.wf_mapping_1g_at(spec_v2l4index(va), spec_v2l3index(va));
    };
    broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, group_kernel_endpoint_nonlock_fields_unchanged_transitive;
    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged); };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
}
}
