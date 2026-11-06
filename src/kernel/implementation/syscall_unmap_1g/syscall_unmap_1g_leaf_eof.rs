use vstd::prelude::*;
use crate::*;

verus! {
/// Hiding the present 1G leaf `va` of the write-held `pagetable` changes only that table's record: the leaf keeps its frame and access bits with the present bit clear, every other resolved or held entry and every other field of the record stay, and the lower half and every other table are
/// unchanged.
#[verifier::opaque]
pub(super) open spec fn unmap_1g_hide_leaf_eof_transition_framing(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr) -> bool {
    let old_h = pre.pt_mp.spec_index(pagetable).view();
    let new_h = post.pt_mp.spec_index(pagetable).view();
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    let target = (spec_v2l4index(va), spec_v2l3index(va));
    let hidden = PageEntry { perm: PageEntryPerm { present: false, ..old_c.spec_resolve_mapping_1g_l3(target.0, target.1)->0.perm }, ..old_c.spec_resolve_mapping_1g_l3(target.0, target.1)->0 };
    &&& post == (KernelK { pt_mp: post.pt_mp, ..pre })
    &&& pre.pt_mp.dom().contains(pagetable)
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable)
    &&& forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != pagetable ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p)
    &&& post.pt_mp.lock_id_by_key(pagetable) == pre.pt_mp.lock_id_by_key(pagetable)
    &&& post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread()
    &&& post.pt_mp.spec_index(pagetable).being_killed() == pre.pt_mp.spec_index(pagetable).being_killed()
    &&& post.pt_mp.spec_index(pagetable).view_ghost() == pre.pt_mp.spec_index(pagetable).view_ghost()
    &&& new_h.table_stale_cpus == old_h.table_stale_cpus && new_h.kernel_l4_end == old_h.kernel_l4_end && new_h.kernel_entries == old_h.kernel_entries
    &&& new_h.cr3 == old_h.cr3 && new_h.pcid == old_h.pcid && new_h.did == old_h.did && new_h.proc_ptr == old_h.proc_ptr
    &&& new_h.l4_table == old_h.l4_table && new_h.l3_rev_map == old_h.l3_rev_map && new_h.l2_rev_map == old_h.l2_rev_map
    &&& new_c.page_closure() == old_c.page_closure()
    &&& new_c.mapping_1g() == old_c.mapping_1g().insert(va, MapEntry { present: false, ..old_c.mapping_1g().spec_index(va) })
    &&& forall|i4: L4Index| #![trigger new_c.spec_resolve_mapping_l4(i4)] old_c.kernel_l4_end() <= i4 && pei_valid(i4) ==> new_c.spec_resolve_mapping_l4(i4) == old_c.spec_resolve_mapping_l4(i4)
    &&& forall|i4: L4Index, i3: L3Index| #![trigger new_c.spec_resolve_mapping_l3(i4, i3)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) ==> new_c.spec_resolve_mapping_l3(i4, i3) == old_c.spec_resolve_mapping_l3(i4, i3)
    &&& forall|i4: L4Index, i3: L3Index| #![trigger new_c.spec_resolve_mapping_1g_l3(i4, i3)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && (i4, i3) != target ==> new_c.spec_resolve_mapping_1g_l3(i4, i3) == old_c.spec_resolve_mapping_1g_l3(i4, i3)
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger new_c.spec_resolve_mapping_l2(i4, i3, i2)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) ==> new_c.spec_resolve_mapping_l2(i4, i3, i2) == old_c.spec_resolve_mapping_l2(i4, i3, i2)
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger new_c.spec_resolve_mapping_2m_l2(i4, i3, i2)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) ==> new_c.spec_resolve_mapping_2m_l2(i4, i3, i2) == old_c.spec_resolve_mapping_2m_l2(i4, i3, i2)
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger new_c.spec_resolve_mapping_4k_l1(i4, i3, i2, i1)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1) ==> new_c.spec_resolve_mapping_4k_l1(i4, i3, i2, i1) == old_c.spec_resolve_mapping_4k_l1(i4, i3, i2, i1)
    &&& forall|i4: L4Index| #![trigger new_c.spec_held_l4(i4)] old_c.kernel_l4_end() <= i4 && pei_valid(i4) ==> new_c.spec_held_l4(i4) == old_c.spec_held_l4(i4)
    &&& forall|i4: L4Index, i3: L3Index| #![trigger new_c.spec_held_l3(i4, i3)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) ==> new_c.spec_held_l3(i4, i3) == old_c.spec_held_l3(i4, i3)
    &&& forall|i4: L4Index, i3: L3Index| #![trigger new_c.spec_held_1g_l3(i4, i3)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && (i4, i3) != target ==> new_c.spec_held_1g_l3(i4, i3) == old_c.spec_held_1g_l3(i4, i3)
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger new_c.spec_held_l2(i4, i3, i2)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) ==> new_c.spec_held_l2(i4, i3, i2) == old_c.spec_held_l2(i4, i3, i2)
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger new_c.spec_held_2m_l2(i4, i3, i2)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) ==> new_c.spec_held_2m_l2(i4, i3, i2) == old_c.spec_held_2m_l2(i4, i3, i2)
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger new_c.spec_held_4k_l1(i4, i3, i2, i1)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1) ==> new_c.spec_held_4k_l1(i4, i3, i2, i1) == old_c.spec_held_4k_l1(i4, i3, i2, i1)
    &&& old_c.spec_resolve_mapping_1g_l3(target.0, target.1) is Some
    &&& new_c.spec_resolve_mapping_1g_l3(target.0, target.1) == Some(hidden)
    &&& new_c.spec_held_1g_l3(target.0, target.1) == Some(hidden)
}

/// The invariant survives hiding the present 1G leaf `va` of the write-held `pagetable` while every CPU is listed stale for the whole table: a translation cached for `va` is covered by the table record, every page record still names a held leaf with its frame, and every other entry
/// resolves as before.
pub(super) proof fn unmap_1g_hide_leaf_eof(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        unmap_1g_hide_leaf_eof_transition_framing(pre, post, pagetable, va),
        va_1g_valid(va),
        pre.pt_mp.dom().contains(pagetable),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g().dom().contains(va),
        pre.pt_mp.spec_index(pagetable).locking_thread() is Write,
        pre.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::range(0usize, NUM_CPUS),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_table_stale_cpus_only_when_write_locked(post.pt_mp),
    ensures post.inv(),
{
    reveal(unmap_1g_hide_leaf_eof_transition_framing);
    pre.default_pagetable_wf_at(pagetable);
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    assert(new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_2m() == old_c.mapping_2m() && old_c.kernel_l4_end() == KERNEL_MEM_END_L4INDEX);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by {
        assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
        assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
            broadcast use spec_va_4k_valid_index_roundtrip, spec_va_4k_index_roundtrip_at; reveal(mapped_4k_page_pagetable_wf); reveal(pagetable_lower_wf);
        };
        assert(mapped_2m_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { broadcast use spec_va_2m_valid_index_roundtrip; reveal(mapped_2m_page_pagetable_wf); };
        assert(mapped_1g_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
            broadcast use spec_va_1g_valid_index_roundtrip;
            reveal(mapped_1g_page_pagetable_wf);
            pre.pt_mp.spec_index(pagetable).view().spec_held_l4_resolves_implies_spec_held_1g_l3_eq_resolve(spec_v2l4index(va), spec_v2l3index(va));
            assert(new_c.mapping_1g().spec_index(va).addr == old_c.mapping_1g().spec_index(va).addr);
        };
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
        assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_wf); };
        assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_wf); };
        assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); };
        assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_pagetable_pcid_match); };
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_va_1g_valid_index_roundtrip; reveal(cpu_tlb_wf);
    };
    assert(structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(structure_cache_wf); };
}
} // verus!
