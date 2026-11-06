use vstd::prelude::*;
use crate::*;

verus! {
/// Hiding the resolving L3 entry `(l4i, l3i)` of the write-held `pagetable` changes only that table: the entry becomes a placeholder that keeps its L2 address, every window under it leaves the table, and its mappings, its held chain below the entry, its stale-CPU records, its table pages
/// and every other field of its record stay.
#[verifier::opaque]
pub(super) open spec fn mmap_1g_hide_l3_entry_eof_transition_framing(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index) -> bool {
    let old_h = pre.pt_mp.spec_index(pagetable).view();
    let new_h = post.pt_mp.spec_index(pagetable).view();
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..pre })
    &&& pre.pt_mp.dom().contains(pagetable)
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable)
    &&& post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable))
    &&& forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != pagetable ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p)
    &&& post.pt_mp.lock_id_by_key(pagetable) == pre.pt_mp.lock_id_by_key(pagetable)
    &&& post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread()
    &&& post.pt_mp.spec_index(pagetable).being_killed() == pre.pt_mp.spec_index(pagetable).being_killed()
    &&& old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i)
    &&& old_c.spec_resolve_mapping_l3(l4i, l3i) is Some
    &&& new_h.table_stale_cpus == old_h.table_stale_cpus && new_h.kernel_l4_end == old_h.kernel_l4_end && new_h.kernel_entries == old_h.kernel_entries
    &&& new_h.cr3 == old_h.cr3 && new_h.pcid == old_h.pcid && new_h.did == old_h.did && new_h.proc_ptr == old_h.proc_ptr
    &&& new_h.l3_rev_map == old_h.l3_rev_map && new_h.l2_rev_map == old_h.l2_rev_map
    &&& new_c.lower.l2_perms == old_c.lower.l2_perms && new_c.lower.l1_rev_map == old_c.lower.l1_rev_map && new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
    &&& new_c.page_closure() == old_c.page_closure()
    &&& new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_2m() == old_c.mapping_2m() && new_c.mapping_1g() == old_c.mapping_1g()
    &&& new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks.remove_keys(old_c.lower.pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == l4i && spec_v2l3index(w.va) == l3i))
    &&& old_c.lower.hidden_l1_tables_in_locked_windows() ==> new_c.lower.hidden_l1_tables_in_locked_windows()
    &&& forall|i4: L4Index| #![trigger new_c.spec_resolve_mapping_l4(i4)] old_c.kernel_l4_end() <= i4 && pei_valid(i4) ==> new_c.spec_resolve_mapping_l4(i4) == old_c.spec_resolve_mapping_l4(i4)
    &&& forall|i4: L4Index| #![trigger new_c.spec_held_l4(i4)] old_c.kernel_l4_end() <= i4 && pei_valid(i4) ==> new_c.spec_held_l4(i4) == old_c.spec_held_l4(i4)
    &&& forall|i4: L4Index, i3: L3Index| #![trigger new_c.spec_resolve_mapping_l3(i4, i3)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && (i4, i3) != (l4i, l3i) ==> new_c.spec_resolve_mapping_l3(i4, i3) == old_c.spec_resolve_mapping_l3(i4, i3)
    &&& new_c.spec_resolve_mapping_l3(l4i, l3i) is None
    &&& forall|i4: L4Index, i3: L3Index| #![trigger new_c.spec_held_l3(i4, i3)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && (i4, i3) != (l4i, l3i) ==> new_c.spec_held_l3(i4, i3) == old_c.spec_held_l3(i4, i3)
    &&& new_c.spec_held_l3(l4i, l3i) == Some(PageEntry { addr: old_c.spec_resolve_mapping_l3(l4i, l3i)->0.addr,
            perm: PageEntryPerm { present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: true } })
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger new_c.spec_resolve_mapping_l2(i4, i3, i2)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && (i4, i3) != (l4i, l3i) ==> new_c.spec_resolve_mapping_l2(i4, i3, i2) == old_c.spec_resolve_mapping_l2(i4, i3, i2)
    &&& forall|i2: L2Index| #![trigger new_c.spec_resolve_mapping_l2(l4i, l3i, i2)] pei_valid(i2) ==> new_c.spec_resolve_mapping_l2(l4i, l3i, i2) is None
    &&& forall|i4: L4Index, i3: L3Index| #![trigger new_c.spec_resolve_mapping_1g_l3(i4, i3)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) ==> new_c.spec_resolve_mapping_1g_l3(i4, i3) == old_c.spec_resolve_mapping_1g_l3(i4, i3)
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger new_c.spec_resolve_mapping_2m_l2(i4, i3, i2)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) ==> new_c.spec_resolve_mapping_2m_l2(i4, i3, i2) == old_c.spec_resolve_mapping_2m_l2(i4, i3, i2)
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger new_c.spec_resolve_mapping_4k_l1(i4, i3, i2, i1)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1) ==> new_c.spec_resolve_mapping_4k_l1(i4, i3, i2, i1) == old_c.spec_resolve_mapping_4k_l1(i4, i3, i2, i1)
    &&& forall|i4: L4Index, i3: L3Index| #![trigger new_c.spec_held_1g_l3(i4, i3)] old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) ==> new_c.spec_held_1g_l3(i4, i3) == old_c.spec_held_1g_l3(i4, i3)
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger new_c.spec_held_l2(i4, i3, i2)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) ==> new_c.spec_held_l2(i4, i3, i2) == old_c.spec_held_l2(i4, i3, i2)
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger new_c.spec_held_2m_l2(i4, i3, i2)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) ==> new_c.spec_held_2m_l2(i4, i3, i2) == old_c.spec_held_2m_l2(i4, i3, i2)
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger new_c.spec_held_4k_l1(i4, i3, i2, i1)]
        old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1) ==> new_c.spec_held_4k_l1(i4, i3, i2, i1) == old_c.spec_held_4k_l1(i4, i3, i2, i1)
}

/// The invariant survives hiding the resolving L3 entry `(l4i, l3i)` of the write-held `pagetable` while every CPU is listed stale for the whole table: a directory entry cached under the entry is covered by the table record, no mapping changes, and every other entry resolves as before.
pub(super) proof fn mmap_1g_hide_l3_entry_eof(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index)
    requires
        pre.inv(),
        mmap_1g_hide_l3_entry_eof_transition_framing(pre, post, pagetable, l4i, l3i),
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
    reveal(mmap_1g_hide_l3_entry_eof_transition_framing);
    pre.default_pagetable_wf_at(pagetable);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by {
        assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
        assert(page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
            broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_va_1g_valid_index_roundtrip;
            reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
        };
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
        assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_wf); };
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
