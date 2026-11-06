use vstd::prelude::*;
use crate::*;

verus! {
/// Removes the non-present 2M leaf `va` of `pagetable`, held under its window through the read-held table, and its record
/// from the page `pg_ptr`, which keeps other references; only the leaf's L2 entry in the L2 page `l2_ptr` changes, and every
/// other kernel field is unchanged.
#[verifier::opaque]
pub(super) open spec fn remove_2m_mapping_without_free_in_window_eof_transition_framing(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, l2_ptr: PageMapPtr)
    -> bool {
    let pg_idx = page_ptr2page_index(pg_ptr);
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    let old_page = pre.pg_arr.spec_index(pg_idx).view();
    let new_page = post.pg_arr.spec_index(pg_idx).view();
    &&& post == (KernelK { pt_lower: post.pt_lower, pg_arr: post.pg_arr, ..pre })
    &&& post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable))
    &&& forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != pagetable ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p)
    &&& new_c.mapping_2m() == old_c.mapping_2m().remove(va)
    &&& new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_1g() == old_c.mapping_1g() && new_c.page_closure() == old_c.page_closure()
    &&& new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks && new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_entry(p, i)] (p, i) != (l2_ptr, spec_v2l2index(va)) ==> new_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i)
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_owner(p, i)] new_c.lower.l2_owner(p, i) == old_c.lower.l2_owner(p, i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))
            ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
    &&& new_c.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is None
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

/// The page-table relations close after the non-present 2M leaf `va` and its record on `pg_ptr` leave together.
proof fn remove_2m_mapping_without_free_in_window_eof_page_tables(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, l2_ptr: PageMapPtr)
    requires
        pre.inv(),
        remove_2m_mapping_without_free_in_window_eof_transition_framing(pre, post, pagetable, va, pg_ptr, l2_ptr),
        pre.pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().dom().contains(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().spec_index(va).addr == pg_ptr,
        page_ptr_valid(pg_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().ref_count > 1,
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Mapped2m,
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
    reveal(remove_2m_mapping_without_free_in_window_eof_transition_framing);
    let pg_idx = page_ptr2page_index(pg_ptr);
    assert(index_valid(NUM_PAGES, pg_idx)) by { page_ptr_valid_imply_page_index_valid(); };
    page_array_wf_at(pre.pg_arr, pg_idx);
    pre.default_pagetable_wf_at(pagetable);
    assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_4k_index_roundtrip_at; reveal(mapped_4k_page_pagetable_wf); reveal(pagetable_lower_wf);
    };
    assert(mapped_2m_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid; reveal(mapped_2m_page_pagetable_wf); reveal(pagetable_lower_wf);
    };
    assert(mapped_1g_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_lower_wf); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); reveal(page_array_wf); };
    assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_wf); };
    assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_wf); };
}

/// The memory-management invariant closes after the non-present 2M leaf `va` and its record on `pg_ptr` leave together.
proof fn remove_2m_mapping_without_free_in_window_eof_memory_management_inv(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, l2_ptr: PageMapPtr)
    requires
        pre.inv(),
        remove_2m_mapping_without_free_in_window_eof_transition_framing(pre, post, pagetable, va, pg_ptr, l2_ptr),
        page_ptr_valid(pg_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Mapped2m,
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
    reveal(remove_2m_mapping_without_free_in_window_eof_transition_framing);
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

/// The CPU TLB and paging-structure caches stay consistent after the non-present 2M leaf `va` of `pagetable` leaves the L2
/// page `l2_ptr`: no CPU is listed stale for its window, so no TLB entry names it.
proof fn reclaim_unmapped_2m_page_in_window_eof_cpu_caches(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        pre.pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_v2l4index(va),
        ({
            let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
            let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
            &&& old_c.mapping_2m().dom().contains(va)
            &&& !old_c.mapping_2m().spec_index(va).present
            &&& old_c.spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some
            &&& old_c.spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr == l2_ptr
            &&& !old_c.lower.window_stale_cpus.dom().contains((l2_ptr, spec_v2l2index(va)))
            &&& post.pt_mp == pre.pt_mp
            &&& post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable))
            &&& new_c.mapping_2m() == old_c.mapping_2m().remove(va)
            &&& new_c.mapping_4k() == old_c.mapping_4k()
            &&& new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_entry(p, i)] (p, i) != (l2_ptr, spec_v2l2index(va)) ==> new_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))
                    ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
        }),
        post.cpu_tlb == pre.cpu_tlb,
        post.cpu_arr == pre.cpu_arr,
        post.pcid_needflush == pre.pcid_needflush,
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
    ensures
        cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
        structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    broadcast use spec_va_2m_valid_index_roundtrip;
    pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable); pagetable_lower_wf_at(post.pt_mp, post.pt_lower.view(), pagetable);
    old_c.wf_mapping_2m_at(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        reveal(cpu_tlb_wf); reveal(WholePageTable::wf_mapping_4k); reveal(WholePageTable::wf_mapping_2m); broadcast use spec_va_4k_valid_index_roundtrip;
    };
    assert(structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(structure_cache_wf); };
}

/// EOF closure of `remove_2m_mapping_without_free_in_window`: the non-present leaf `va` and its record leave together, the
/// leaf was never user-visible, and no CPU caches it because its window lists no CPU stale.
pub(super) proof fn remove_2m_mapping_without_free_in_window_eof(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, l2_ptr: PageMapPtr)
    requires
        pre.inv(),
        remove_2m_mapping_without_free_in_window_eof_transition_framing(pre, post, pagetable, va, pg_ptr, l2_ptr),
        pre.pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        pre.pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().dom().contains(va),
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().spec_index(va).present,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().spec_index(va).addr == pg_ptr,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr == l2_ptr,
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains((l2_ptr, spec_v2l2index(va))),
        page_ptr_valid(pg_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().ref_count > 1,
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Mapped2m,
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
    reveal(remove_2m_mapping_without_free_in_window_eof_transition_framing);
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    assert(index_valid(NUM_PAGES, page_ptr2page_index(pg_ptr))) by { page_ptr_valid_imply_page_index_valid(); };
    assert(post.subsystems_inv()) by { reveal(page_array_wf); reveal(KernelK::default_pagetable_wf); reveal(pagetable_table_stale_cpus_only_when_write_locked); };
    remove_2m_mapping_without_free_in_window_eof_page_tables(pre, post, pagetable, va, pg_ptr, l2_ptr);
    remove_2m_mapping_without_free_in_window_eof_memory_management_inv(pre, post, pagetable, va, pg_ptr, l2_ptr);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_pagetable_pcid_match); };
    reclaim_unmapped_2m_page_in_window_eof_cpu_caches(pre, post, pagetable, va, l2_ptr);
    assert(new_c.user_view(LockStateU::Unlocked).mapping_2m =~= old_c.user_view(LockStateU::Unlocked).mapping_2m);
    broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, group_kernel_endpoint_nonlock_fields_unchanged_transitive;
    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged); };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
}

/// Removes the non-present 2M leaf `va` of `pagetable`, held under its window through the read-held table, and its record
/// from the page `pg_ptr`, whose last mapping it was; returns the page through its free-list node at `node_addr` to shard
/// `cpu_id` of the owner's 2M allocator `allc_ptr` and credits the thread's pending free 2M quota at `depth`. Only the leaf's
/// L2 entry in the L2 page `l2_ptr` changes in the table.
#[verifier::opaque]
pub(super) open spec fn remove_last_2m_mapping_to_allocator_in_window_eof_transition_framing(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, l2_ptr: PageMapPtr, thrd_ptr: RwLockThreadPtr, depth: usize, allc_ptr: RwLockPageAllocatorPtr,
    cpu_id: CpuId, old_counter: usize, new_counter: usize, node_addr: usize,
) -> bool {
    let pg_idx = page_ptr2page_index(pg_ptr);
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    let old_page = pre.pg_arr.spec_index(pg_idx).view();
    let new_page = post.pg_arr.spec_index(pg_idx).view();
    let old_thread = pre.thrd_mp.spec_index(thrd_ptr);
    let new_thread = post.thrd_mp.spec_index(thrd_ptr);
    let old_allocator = pre.allc_2m_mp.spec_index(allc_ptr);
    let new_allocator = post.allc_2m_mp.spec_index(allc_ptr);
    &&& post == (KernelK { pt_lower: post.pt_lower, pg_arr: post.pg_arr, thrd_mp: post.thrd_mp, allc_2m_mp: post.allc_2m_mp, ..pre })
    &&& post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable))
    &&& forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != pagetable ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p)
    &&& new_c.mapping_2m() == old_c.mapping_2m().remove(va)
    &&& new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_1g() == old_c.mapping_1g() && new_c.page_closure() == old_c.page_closure()
    &&& new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks && new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_entry(p, i)] (p, i) != (l2_ptr, spec_v2l2index(va)) ==> new_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i)
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_owner(p, i)] new_c.lower.l2_owner(p, i) == old_c.lower.l2_owner(p, i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))
            ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
    &&& new_c.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is None
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, pg_idx)
    &&& forall|i: PageIndex|
        #![trigger pre.pg_arr.spec_index(i).view().view().state]
        #![trigger post.pg_arr.spec_index(i).view().view().state]
        index_valid(NUM_PAGES, i) ==> {
            &&& post.pg_arr.spec_index(i).view().view().state == if i == pg_idx {
                PageState::Free2m { allocator_ptr: Ghost(allc_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } }
            } else {
                pre.pg_arr.spec_index(i).view().view().state
            }
            &&& post.pg_arr.spec_index(i).view().view().owning_container == pre.pg_arr.spec_index(i).view().view().owning_container
            &&& (i != pg_idx ==> post.pg_arr.spec_index(i).view().view().mappings() == pre.pg_arr.spec_index(i).view().view().mappings())
        }
    &&& new_page.is_init() == old_page.is_init()
    &&& new_page.view_rodata() == old_page.view_rodata()
    &&& new_page.view_ghost() == old_page.view_ghost()
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& new_page.view().free_list_node_storage.addr() == node_addr
    &&& new_page.view() == (Page {
        state: PageState::Free2m { allocator_ptr: Ghost(allc_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } },
        mappings: Ghost(old_page.view().mappings().remove((pagetable, va))), ref_count: 0, free_list_node_storage: new_page.view().free_list_node_storage, ..old_page.view()
    })
    &&& post.thrd_mp.dom() == pre.thrd_mp.dom()
    &&& post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr)
    &&& forall|t: RwLockThreadPtr|
        #![trigger pre.thrd_mp.spec_index(t).view().temp_alloc_cache_4k]
        #![trigger post.thrd_mp.spec_index(t).view().temp_alloc_cache_4k]
        #![trigger post.thrd_mp.spec_index(t).view().temp_alloc_cache_2m]
        #![trigger post.thrd_mp.spec_index(t).view().temp_alloc_cache_1g]
        pre.thrd_mp.dom().contains(t) ==> {
            &&& post.thrd_mp.spec_index(t).view().temp_alloc_cache_4k == pre.thrd_mp.spec_index(t).view().temp_alloc_cache_4k
            &&& post.thrd_mp.spec_index(t).view().temp_alloc_cache_2m == pre.thrd_mp.spec_index(t).view().temp_alloc_cache_2m
            &&& post.thrd_mp.spec_index(t).view().temp_alloc_cache_1g == pre.thrd_mp.spec_index(t).view().temp_alloc_cache_1g
        }
    &&& new_thread.is_init() == old_thread.is_init()
    &&& new_thread.view_rodata() == old_thread.view_rodata()
    &&& new_thread.view_ghost() == old_thread.view_ghost()
    &&& new_thread.locking_thread() == old_thread.locking_thread()
    &&& new_thread.being_killed() == old_thread.being_killed()
    &&& new_thread.killer_info() == old_thread.killer_info()
    &&& new_thread.view() == (Thread { direct_free_quota_pending_2m: new_thread.view().direct_free_quota_pending_2m, indirect_free_quota_pending_2m: new_thread.view().indirect_free_quota_pending_2m, ..old_thread.view() })
    &&& new_counter == old_counter + 1
    &&& new_thread.view().free_quota_pending_2m_at_depth(depth) == new_counter
    &&& new_thread.view().direct_free_quota_pending_2m.view() == old_thread.view().direct_free_quota_pending_2m.view() + if depth == old_thread.view().container_depth { 1int } else { 0int }
    &&& new_thread.view().indirect_free_quota_pending_2m.view() == if depth < old_thread.view().container_depth { old_thread.view().indirect_free_quota_pending_2m.view().update(depth as int, new_counter) } else { old_thread.view().indirect_free_quota_pending_2m.view() }
    &&& forall|t: RwLockThreadPtr|
        #![trigger pre.thrd_mp.spec_index(t).view().direct_free_quota_pending_4k]
        #![trigger post.thrd_mp.spec_index(t).view().direct_free_quota_pending_4k]
        #![trigger thread_effective_quota_1g(pre.thrd_mp.spec_index(t))]
        #![trigger pre.thrd_mp.spec_index(t).view().direct_free_quota_pending_1g]
        #![trigger pre.thrd_mp.spec_index(t).view().indirect_free_quota_pending_1g]
        pre.thrd_mp.dom().contains(t) ==> {
            &&& post.thrd_mp.spec_index(t).view().quota_4k == pre.thrd_mp.spec_index(t).view().quota_4k
            &&& post.thrd_mp.spec_index(t).view().quota_1g == pre.thrd_mp.spec_index(t).view().quota_1g
            &&& post.thrd_mp.spec_index(t).view().direct_free_quota_pending_4k == pre.thrd_mp.spec_index(t).view().direct_free_quota_pending_4k
            &&& post.thrd_mp.spec_index(t).view().direct_free_quota_pending_1g == pre.thrd_mp.spec_index(t).view().direct_free_quota_pending_1g
            &&& post.thrd_mp.spec_index(t).view().indirect_free_quota_pending_4k == pre.thrd_mp.spec_index(t).view().indirect_free_quota_pending_4k
            &&& post.thrd_mp.spec_index(t).view().indirect_free_quota_pending_1g == pre.thrd_mp.spec_index(t).view().indirect_free_quota_pending_1g
        }
    &&& post.allc_2m_mp.dom() == pre.allc_2m_mp.dom()
    &&& post.allc_2m_mp.unchanged_except(&pre.allc_2m_mp, allc_ptr)
    &&& new_allocator.quota == old_allocator.quota
    &&& new_allocator.total_free_pages.view() == old_allocator.total_free_pages.view() + 1
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().view().view() == old_allocator.cpu_caches.spec_index(cpu_id).view().view().view().insert(0, pg_ptr)
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().view().map() == old_allocator.cpu_caches.spec_index(cpu_id).view().view().map().insert(node_addr, pg_ptr)
    &&& new_allocator.cpu_caches.entries_unchanged_except(&old_allocator.cpu_caches, cpu_id)
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().locking_thread() == old_allocator.cpu_caches.spec_index(cpu_id).view().locking_thread()
    &&& new_allocator.global_pool == old_allocator.global_pool
    &&& new_allocator.owning_container == old_allocator.owning_container
}

/// The process-management invariant closes after the thread is credited one pending free 2M quota at `depth`.
proof fn remove_last_2m_mapping_to_allocator_in_window_eof_process_management_inv(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, l2_ptr: PageMapPtr, thrd_ptr: RwLockThreadPtr, depth: usize, allc_ptr: RwLockPageAllocatorPtr,
    cpu_id: CpuId, old_counter: usize, new_counter: usize, node_addr: usize,
)
    requires
        pre.inv(),
        remove_last_2m_mapping_to_allocator_in_window_eof_transition_framing(pre, post, pagetable, va, pg_ptr, l2_ptr, thrd_ptr, depth, allc_ptr, cpu_id, old_counter, new_counter, node_addr),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(remove_last_2m_mapping_to_allocator_in_window_eof_transition_framing);
    assert(thread_endpoint_ref_counter_wf(post.thrd_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.ep_mp); };
    assert(thread_endpoint_queue_wf(post.thrd_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.ep_mp); };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thrd_mp, post.ep_mp)) by { container_thread_endpoint_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp, post.ep_mp); };
    assert(container_thread_scheduler_wf(post.ctn_mp, post.thrd_mp, post.sched_mp)) by { container_thread_scheduler_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp, post.sched_mp); };
    assert(container_thread_wf(post.ctn_mp, post.thrd_mp)) by { container_thread_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp); };
    assert(process_thread_wf(post.prc_mp, post.thrd_mp)) by { process_thread_wf_preserved_for_thread_process_management_fields(post.prc_mp, pre.thrd_mp, post.thrd_mp); };
    assert(thread_cpu_wf(post.thrd_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.cpu_arr); };
    assert(thread_caller_callee_wf(post.thrd_mp)) by { thread_caller_callee_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp); };
    assert(thread_dangling_chain_end_wf(post.thrd_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thrd_mp, post.thrd_mp); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
}

/// The page-table relations close after the last mapping of `pg_ptr`, the non-present 2M leaf `va`, leaves with its record.
proof fn remove_last_2m_mapping_to_allocator_in_window_eof_page_relations(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, l2_ptr: PageMapPtr, thrd_ptr: RwLockThreadPtr, depth: usize, allc_ptr: RwLockPageAllocatorPtr,
    cpu_id: CpuId, old_counter: usize, new_counter: usize, node_addr: usize,
)
    requires
        pre.inv(),
        remove_last_2m_mapping_to_allocator_in_window_eof_transition_framing(pre, post, pagetable, va, pg_ptr, l2_ptr, thrd_ptr, depth, allc_ptr, cpu_id, old_counter, new_counter, node_addr),
        ({
            let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view();
            &&& pre.pt_mp.dom().contains(pagetable)
            &&& va_2m_valid(va)
            &&& old_c.mapping_2m().dom().contains(va)
            &&& old_c.mapping_2m().spec_index(va).addr == pg_ptr
            &&& page_ptr_valid(pg_ptr)
            &&& old_page.ref_count == 1
            &&& old_page.state is Mapped2m
            &&& old_page.mappings().contains((pagetable, va))
        }),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        post.subsystems_inv(),
    ensures
        page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        iommu_table_no_huge_leaf_wf(post.it_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
{
    reveal(remove_last_2m_mapping_to_allocator_in_window_eof_transition_framing);
    let pg_idx = page_ptr2page_index(pg_ptr);
    assert(index_valid(NUM_PAGES, pg_idx)) by { page_ptr_valid_imply_page_index_valid(); };
    page_array_wf_at(pre.pg_arr, pg_idx);
    pre.default_pagetable_wf_at(pagetable);
    assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_4k_index_roundtrip_at; reveal(mapped_4k_page_pagetable_wf); reveal(page_array_wf); reveal(pagetable_lower_wf);
    };
    assert(mapped_2m_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid; reveal(mapped_2m_page_pagetable_wf); reveal(pagetable_lower_wf); reveal(page_array_wf);
    };
    assert(mapped_1g_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_lower_wf); reveal(page_array_wf); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); reveal(page_array_wf); };
    assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_wf); };
    assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_wf); };
}

/// The 2M allocator relations close after `pg_ptr` enters shard `cpu_id` of the owner allocator's CPU cache.
proof fn remove_last_2m_mapping_to_allocator_in_window_eof_free_2m_pages(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, l2_ptr: PageMapPtr, thrd_ptr: RwLockThreadPtr, depth: usize, allc_ptr: RwLockPageAllocatorPtr,
    cpu_id: CpuId, old_counter: usize, new_counter: usize, node_addr: usize, owner: RwLockContainerPtr,
)
    requires
        pre.inv(),
        remove_last_2m_mapping_to_allocator_in_window_eof_transition_framing(pre, post, pagetable, va, pg_ptr, l2_ptr, thrd_ptr, depth, allc_ptr, cpu_id, old_counter, new_counter, node_addr),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view();
            &&& page_ptr_valid(pg_ptr)
            &&& old_page.state is Mapped2m
            &&& old_page.owning_container == owner
            &&& old_page.free_list_node_storage.addr() == node_addr
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& pre.allc_2m_mp.dom().contains(allc_ptr)
            &&& !pre.allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr)
            &&& pre.ctn_mp.dom().contains(owner)
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_2m == allc_ptr
        }),
        post.subsystems_inv(),
    ensures
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        allocator_free_page_ptrs_wf(post.allc_2m_mp),
        allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr),
{
    reveal(remove_last_2m_mapping_to_allocator_in_window_eof_transition_framing);
    let pg_idx = page_ptr2page_index(pg_ptr);
    assert(index_valid(NUM_PAGES, pg_idx)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
    assert(allocator_free_page_ptrs_wf(post.allc_2m_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_global_pool_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { reveal(allocator_free_2m_pages_wf); reveal(allocator_global_pool_2m_pages_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_cpu_cache_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by {
        reveal(allocator_free_2m_pages_wf); reveal(allocator_cpu_cache_2m_pages_wf); reveal(container_allocator_wf); reveal(allocator_free_page_ptrs_wf); reveal(page_array_wf);
        seq_insert_head_implies_contains::<PagePtr>(); page_ptr_roundtrip(); page_index_roundtrip();
    };
    reveal(allocator_free_2m_pages_wf);
}

/// The page ownership relations close after the 2M head `pg_ptr` turns from a mapped page into a free page of the owner
/// allocator; its tails stay merged into it.
proof fn remove_last_2m_mapping_to_allocator_in_window_eof_page_owners(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, l2_ptr: PageMapPtr, thrd_ptr: RwLockThreadPtr, depth: usize, allc_ptr: RwLockPageAllocatorPtr,
    cpu_id: CpuId, old_counter: usize, new_counter: usize, node_addr: usize,
)
    requires
        pre.inv(),
        remove_last_2m_mapping_to_allocator_in_window_eof_transition_framing(pre, post, pagetable, va, pg_ptr, l2_ptr, thrd_ptr, depth, allc_ptr, cpu_id, old_counter, new_counter, node_addr),
        page_ptr_valid(pg_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Mapped2m,
        post.subsystems_inv(),
    ensures
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
        allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr),
        container_owned_pages_wf(post.ctn_mp, post.pg_arr),
        container_pages_wf(post.ctn_mp, post.pg_arr),
        process_pages_wf(post.prc_mp, post.pg_arr),
        process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr),
        page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
        iommu_table_pages_wf(post.it_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr),
        thread_pages_wf(post.thrd_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        thread_staged_pages_wf(post.thrd_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
        pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr),
        allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr),
{
    reveal(remove_last_2m_mapping_to_allocator_in_window_eof_transition_framing);
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
    assert(page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr)) by { reveal(page_object_owner_wf); reveal(container_owned_pages_wf); };
    assert(hugepage_2m_wf(post.pg_arr)) by { reveal(hugepage_2m_wf); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
    assert(pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pcid_allc_mp, post.pcid_allc_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_pages_wf(post.thrd_mp, post.pg_arr)) by {
        thread_staged_4k_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
        thread_staged_2m_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
        thread_staged_1g_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
    };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
    assert(allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(post.allc_4k_mp, pre.pg_arr, post.pg_arr, pg_idx); };
    assert(allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, pg_idx); };
}

/// The allocator quota and kill-retire relations close after the freed page's quota unit moves to the thread's pending free 2M
/// counter at the owner's `depth`.
proof fn remove_last_2m_mapping_to_allocator_in_window_eof_allocator_quota_wf(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, l2_ptr: PageMapPtr, thrd_ptr: RwLockThreadPtr, depth: usize, allc_ptr: RwLockPageAllocatorPtr,
    cpu_id: CpuId, old_counter: usize, new_counter: usize, node_addr: usize, owner: RwLockContainerPtr,
)
    requires
        pre.inv(),
        remove_last_2m_mapping_to_allocator_in_window_eof_transition_framing(pre, post, pagetable, va, pg_ptr, l2_ptr, thrd_ptr, depth, allc_ptr, cpu_id, old_counter, new_counter, node_addr),
        ({
            let old_thread = pre.thrd_mp.spec_index(thrd_ptr);
            &&& pre.allc_2m_mp.dom().contains(allc_ptr)
            &&& pre.thrd_mp.dom().contains(thrd_ptr)
            &&& old_thread.locking_thread() is Write
            &&& pre.ctn_mp.dom().contains(owner)
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().depth == depth
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_2m == allc_ptr
            &&& depth <= old_thread.view().container_depth
            &&& (if depth == old_thread.view().container_depth { owner == old_thread.view().owning_container } else { old_thread.view().upper_container_seq.view().spec_index(depth as int) == owner })
            &&& old_counter == old_thread.view().free_quota_pending_2m_at_depth(depth)
        }),
        post.subsystems_inv(),
    ensures
        container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    reveal(remove_last_2m_mapping_to_allocator_in_window_eof_transition_framing);
    assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_2m_mp)) by {
        reveal(container_process_allocator_quota_2m_wf); reveal(container_allocator_wf); reveal(container_thread_wf); reveal(container_uppertree_seq_wf); reveal(thread_perms_wf);
        lemma_thread_effective_quota_2m_fold_sum_eq_forall();
        thread_pending_2m_change_at_one_thread_implies_folds_change_by(thrd_ptr, if depth == pre.thrd_mp.spec_index(thrd_ptr).view().container_depth { 1int } else { 0int }, depth as int,
            if depth < pre.thrd_mp.spec_index(thrd_ptr).view().container_depth { 1int } else { 0int });
    };
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp)) by {
        container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_4k_mp);
    };
    assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_1g_mp)) by {
        container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_1g_mp);
    };
    assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        let thread = pre.thrd_mp.spec_index(thrd_ptr).view();
        container_thread_wf_thread_at(pre.ctn_mp, pre.thrd_mp, thrd_ptr); container_thread_wf_uppertree_at(pre.ctn_mp, pre.thrd_mp, thrd_ptr);
        if depth < thread.container_depth {
            container_perms_wf_at(pre.ctn_mp, thread.owning_container); assert(thread.upper_container_seq.view().contains(owner));
            container_uppertree_seq_wf_at(pre.rt_ctn, pre.ctn_mp, thread.owning_container, owner);
        }
        reveal(container_kill_retire_wf); reveal(container_allocator_wf);
    };
}

/// EOF closure of `remove_last_2m_mapping_to_allocator_in_window`: the non-present leaf `va` and its record leave together, so
/// the freed page carries no other record, no CPU caches it because its window lists no CPU stale, and the page's quota unit
/// moves to the thread's pending 2M counter at the owner's depth.
pub(super) proof fn remove_last_2m_mapping_to_allocator_in_window_eof(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, l2_ptr: PageMapPtr, thrd_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, depth: usize,
    allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, old_counter: usize, new_counter: usize, node_addr: usize,
)
    requires
        pre.inv(),
        remove_last_2m_mapping_to_allocator_in_window_eof_transition_framing(pre, post, pagetable, va, pg_ptr, l2_ptr, thrd_ptr, depth, allc_ptr, cpu_id, old_counter, new_counter, node_addr),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view();
            let old_thread = pre.thrd_mp.spec_index(thrd_ptr);
            let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
            &&& pre.pt_mp.dom().contains(pagetable)
            &&& va_2m_valid(va)
            &&& pre.pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_v2l4index(va)
            &&& old_c.mapping_2m().dom().contains(va)
            &&& !old_c.mapping_2m().spec_index(va).present
            &&& old_c.mapping_2m().spec_index(va).addr == pg_ptr
            &&& old_c.spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some
            &&& old_c.spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr == l2_ptr
            &&& !old_c.lower.window_stale_cpus.dom().contains((l2_ptr, spec_v2l2index(va)))
            &&& page_ptr_valid(pg_ptr)
            &&& old_page.ref_count == 1
            &&& old_page.state is Mapped2m
            &&& old_page.mappings().contains((pagetable, va))
            &&& old_page.owning_container == owner
            &&& old_page.free_list_node_storage.addr() == node_addr
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& pre.allc_2m_mp.dom().contains(allc_ptr)
            &&& !pre.allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr)
            &&& pre.thrd_mp.dom().contains(thrd_ptr)
            &&& old_thread.locking_thread() is Write
            &&& pre.ctn_mp.dom().contains(owner)
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().depth == depth
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_2m == allc_ptr
            &&& depth <= old_thread.view().container_depth
            &&& (if depth == old_thread.view().container_depth { owner == old_thread.view().owning_container } else { old_thread.view().upper_container_seq.view().spec_index(depth as int) == owner })
            &&& old_counter == old_thread.view().free_quota_pending_2m_at_depth(depth)
        }),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().inv(),
        post.thrd_mp.perms_wf(),
        post.thrd_mp.spec_index(thrd_ptr).inv(),
        post.allc_2m_mp.perms_wf(),
        post.allc_2m_mp.spec_index(allc_ptr).wf(),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
    ensures
        post.inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
{
    reveal(remove_last_2m_mapping_to_allocator_in_window_eof_transition_framing);
    assert(post.subsystems_inv()) by {
        reveal(page_array_wf); reveal(thread_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked);
        reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(allocator_perms_wf); reveal(thread_ipc_transit_wf); reveal(KernelK::default_pagetable_wf);
        reveal(pagetable_table_stale_cpus_only_when_write_locked);
    };
    remove_last_2m_mapping_to_allocator_in_window_eof_page_relations(pre, post, pagetable, va, pg_ptr, l2_ptr, thrd_ptr, depth, allc_ptr, cpu_id, old_counter, new_counter, node_addr);
    remove_last_2m_mapping_to_allocator_in_window_eof_free_2m_pages(pre, post, pagetable, va, pg_ptr, l2_ptr, thrd_ptr, depth, allc_ptr, cpu_id, old_counter, new_counter, node_addr, owner);
    remove_last_2m_mapping_to_allocator_in_window_eof_page_owners(pre, post, pagetable, va, pg_ptr, l2_ptr, thrd_ptr, depth, allc_ptr, cpu_id, old_counter, new_counter, node_addr);
    remove_last_2m_mapping_to_allocator_in_window_eof_allocator_quota_wf(pre, post, pagetable, va, pg_ptr, l2_ptr, thrd_ptr, depth, allc_ptr, cpu_id, old_counter, new_counter, node_addr, owner);
    assert(post.memory_management_inv()) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); };
    remove_last_2m_mapping_to_allocator_in_window_eof_process_management_inv(pre, post, pagetable, va, pg_ptr, l2_ptr, thrd_ptr, depth, allc_ptr, cpu_id, old_counter, new_counter, node_addr);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_pagetable_pcid_match); };
    reclaim_unmapped_2m_page_in_window_eof_cpu_caches(pre, post, pagetable, va, l2_ptr);
    assert(whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).user_view(LockStateU::Unlocked).mapping_2m
        =~= whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).user_view(LockStateU::Unlocked).mapping_2m);
    broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive;
    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post)) by {
        broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
    };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_allocator_wf); };
}
}
