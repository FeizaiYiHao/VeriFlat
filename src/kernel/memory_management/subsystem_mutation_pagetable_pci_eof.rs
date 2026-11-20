use vstd::prelude::*;
use crate::*;

verus! {
/// S of `pagetable_map_update_pci_mapping`: of the write-held table `pagetable_ptr` only the PCI function array of the big-lock
/// payload changed, and it stays well formed; the lock state, kill mark, ghost slot, window halves, and every other table stay.
#[verifier::opaque]
pub(super) open spec fn pagetable_map_update_pci_mapping_eof_transition_framing(pre_pt: PageTableLockedMap, post_pt: PageTableLockedMap, pt_lower: PageTableLowerMap,
    pagetable_ptr: RwLockPageTableRoot) -> bool
{
    let before = pre_pt.spec_index(pagetable_ptr);
    let after = post_pt.spec_index(pagetable_ptr);
    &&& post_pt.perms_wf()
    &&& post_pt.unchanged_except(&pre_pt, pagetable_ptr)
    &&& after.is_init()
    &&& after.locking_thread() == before.locking_thread()
    &&& after.being_killed() == before.being_killed()
    &&& after.view_rodata() == before.view_rodata()
    &&& post_pt.lock_id_by_key(pagetable_ptr) == pre_pt.lock_id_by_key(pagetable_ptr)
    &&& after.view().lower_backup == before.view().lower_backup
    &&& after.view().higher == (PageTableHigher { pci: after.view().higher.pci, ..before.view().higher })
    &&& after.view().higher.pci.wf()
    &&& forall|r: RwLockPageTableRoot| #![trigger whole_pagetable(post_pt, pt_lower, r)]
        pre_pt.dom().contains(r) && r != pagetable_ptr ==> whole_pagetable(post_pt, pt_lower, r) == whole_pagetable(pre_pt, pt_lower, r)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
        #![trigger whole_pagetable(post_pt, pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        #![trigger whole_pagetable(pre_pt, pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        whole_pagetable(post_pt, pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == whole_pagetable(pre_pt, pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)
}

/// EOF closure of `pagetable_map_update_pci_mapping` for the big-lock payload: only the PCI function array changed, and it stays well
/// formed.
proof fn pagetable_map_update_pci_mapping_eof_higher_inv(pre: PageTableHigher<PT_TYPE>, post: PageTableHigher<PT_TYPE>)
    requires
        pre.inv(),
        post == (PageTableHigher { pci: post.pci, ..pre }),
        post.pci.wf(),
    ensures
        post.inv(),
{
    pagetable_map_update_pci_mapping_eof_entries(pre, post);
    pagetable_map_update_pci_mapping_eof_wf_l4(pre, post);
    assert(post.wf_l3()) by { reveal(PageTableHigher::wf_l3); };
    assert(post.disjoint_l4()) by { reveal(PageTableHigher::disjoint_l4); };
    assert(post.disjoint_l3()) by { reveal(PageTableHigher::disjoint_l3); };
    assert(post.wf_mapping_1g()) by { reveal(PageTableHigher::wf_mapping_1g); };
    assert(post.user_only()) by { reveal(PageTableHigher::user_only); };
    assert(post.rwx_upper_level_entries()) by { reveal(PageTableHigher::rwx_upper_level_entries); };
    assert(post.table_pages_wf()) by { reveal(PageTableHigher::table_pages_wf); };
    assert(post.tables_reachable_wf()) by { reveal(PageTableHigher::tables_reachable_wf); };
    assert(post.kernel_entries_wf()) by { reveal(PageTableHigher::kernel_entries_wf); };
}

/// EOF closure of `pagetable_map_update_pci_mapping` for `wf_l4`: the root entries read as before.
proof fn pagetable_map_update_pci_mapping_eof_wf_l4(pre: PageTableHigher<PT_TYPE>, post: PageTableHigher<PT_TYPE>)
    requires
        pre.inv(),
        post == (PageTableHigher { pci: post.pci, ..pre }),
    ensures
        post.wf_l4(),
{
    pagetable_map_update_pci_mapping_eof_entries(pre, post);
    reveal(PageTableHigher::wf_l4);
}

/// EOF closure of `pagetable_map_update_pci_mapping` for the root entries and the root and 1G walks, which do not read the PCI
/// function array: each reads as before.
proof fn pagetable_map_update_pci_mapping_eof_entries(pre: PageTableHigher<PT_TYPE>, post: PageTableHigher<PT_TYPE>)
    requires
        post == (PageTableHigher { pci: post.pci, ..pre }),
    ensures
        forall|i: L4Index| #![trigger post.l4_entry(i)] post.l4_entry(i) == pre.l4_entry(i),
        forall|l4i: L4Index| #![trigger post.spec_held_l4(l4i)] post.spec_held_l4(l4i) == pre.spec_held_l4(l4i),
        forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_resolve_mapping_1g_l3(l4i, l3i)]
            post.spec_resolve_mapping_1g_l3(l4i, l3i) == pre.spec_resolve_mapping_1g_l3(l4i, l3i),
{}

/// EOF closure of `pagetable_map_update_pci_mapping` for the table itself: no table invariant other than the payload's reads the PCI
/// function array.
proof fn pagetable_map_update_pci_mapping_eof_table_wf(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>)
    requires
        pre.wf(),
        post.higher == (PageTableHigher { pci: post.higher.pci, ..pre.higher }),
        post.higher.pci.wf(),
        post.lower == pre.lower,
    ensures
        post.higher.inv(),
        post.wf(),
{
    pagetable_map_update_pci_mapping_eof_higher_inv(pre.higher, post.higher);
    assert(post.tables_reachable_wf()) by { reveal(WholePageTable::tables_reachable_wf); };
    assert(post.l3_links_l2_wf()) by { reveal(WholePageTable::l3_links_l2_wf); };
    assert(post.wf_l2()) by { reveal(WholePageTable::wf_l2); };
    assert(post.wf_l1()) by { reveal(WholePageTable::wf_l1); };
    assert(post.disjoint_l2()) by { reveal(WholePageTable::disjoint_l2); };
    pagetable_map_update_pci_mapping_eof_wf_mapping_4k(pre, post);
    pagetable_map_update_pci_mapping_eof_resolve_2m(pre, post);
    assert(post.wf_mapping_2m()) by { reveal(WholePageTable::wf_mapping_2m); };
    assert(post.user_only()) by { reveal(WholePageTable::user_only); };
    assert(post.rwx_upper_level_entries()) by { reveal(WholePageTable::rwx_upper_level_entries); };
    assert(post.table_pages_wf()) by { reveal(WholePageTable::table_pages_wf); };
    assert(post.wf_window_locks()) by { reveal(WholePageTable::wf_window_locks); };
}

/// EOF closure of `pagetable_map_update_pci_mapping` for `wf_mapping_4k`: the leaves and mappings are unchanged.
proof fn pagetable_map_update_pci_mapping_eof_wf_mapping_4k(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>)
    requires
        pre.wf(),
        post.higher == (PageTableHigher { pci: post.higher.pci, ..pre.higher }),
        post.higher.pci.wf(),
        post.lower == pre.lower,
    ensures post.wf_mapping_4k(),
{
    pagetable_map_update_pci_mapping_eof_resolve_4k(pre, post);
    reveal(WholePageTable::wf_mapping_4k);
}

/// EOF closure of `pagetable_map_update_pci_mapping` for the 4K walks, which do not read the PCI function array: each resolves as
/// before.
proof fn pagetable_map_update_pci_mapping_eof_resolve_4k(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>)
    requires
        post.higher == (PageTableHigher { pci: post.higher.pci, ..pre.higher }),
        post.lower == pre.lower,
    ensures
        post.kernel_l4_end() == pre.kernel_l4_end(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
            post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i),
{}

/// EOF closure of `pagetable_map_update_pci_mapping` for the 2M walks, which do not read the PCI function array: each resolves as
/// before.
proof fn pagetable_map_update_pci_mapping_eof_resolve_2m(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>)
    requires
        post.higher == (PageTableHigher { pci: post.higher.pci, ..pre.higher }),
        post.lower == pre.lower,
    ensures
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)]
            post.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == pre.spec_resolve_mapping_2m_l2(l4i, l3i, l2i),
{}

/// EOF closure of `pagetable_map_update_pci_mapping`: the big-lock and window-half invariants hold after the PCI function array of
/// the write-held table changed.
pub(super) proof fn pagetable_map_update_pci_mapping_eof(
    pre_pt: PageTableLockedMap, post_pt: PageTableLockedMap, pt_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot,
    window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>, pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        pagetable_perms_wf(pre_pt),
        pre_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(pre_pt, pt_lower),
        pagetable_window_holders_hold_pagetable(pre_pt, pt_lower),
        pagetable_hidden_leaves_only_when_locked(pre_pt, pt_lower),
        pagetable_hidden_l1_only_when_locked(pre_pt, pt_lower),
        pagetable_window_stale_cpus_only_when_locked(pre_pt, pt_lower),
        pagetable_window_typed_lock_map_aligned(pre_pt, pt_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(pre_pt, pt_lower),
        pre_pt.dom().contains(pagetable_ptr),
        pre_pt.spec_index(pagetable_ptr).locking_thread() is Write,
        pagetable_map_update_pci_mapping_eof_transition_framing(pre_pt, post_pt, pt_lower, pagetable_ptr),
    ensures
        pagetable_perms_wf(post_pt),
        post_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(post_pt, pt_lower),
        pagetable_window_holders_hold_pagetable(post_pt, pt_lower),
        pagetable_hidden_leaves_only_when_locked(post_pt, pt_lower),
        pagetable_hidden_l1_only_when_locked(post_pt, pt_lower),
        pagetable_window_stale_cpus_only_when_locked(post_pt, pt_lower),
        pagetable_window_typed_lock_map_aligned(post_pt, pt_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(post_pt, pt_lower),
{
    reveal(pagetable_map_update_pci_mapping_eof_transition_framing);
    pagetable_perms_wf_at(pre_pt, pagetable_ptr);
    pagetable_lower_wf_at(pre_pt, pt_lower, pagetable_ptr);
    pagetable_map_update_pci_mapping_eof_table_wf(whole_pagetable(pre_pt, pt_lower, pagetable_ptr), whole_pagetable(post_pt, pt_lower, pagetable_ptr));
    assert(pagetable_perms_wf(post_pt)) by { lock_op_implies_pagetable_perms_wf_preserved_forall(); };
    assert(post_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id)) by {
        reveal(LockedMap::typed_lock_map_aligned);
        assert(post_pt.spec_index(pagetable_ptr).wlocked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).wlocked_by_thread(thread_id));
    };
    assert(pagetable_lower_wf(post_pt, pt_lower)) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(post_pt, pt_lower)) by { reveal(pagetable_window_holders_hold_pagetable); };
    assert(pagetable_hidden_leaves_only_when_locked(post_pt, pt_lower)) by { reveal(pagetable_hidden_leaves_only_when_locked); };
    assert(pagetable_hidden_l1_only_when_locked(post_pt, pt_lower)) by { reveal(pagetable_hidden_l1_only_when_locked); };
    assert(pagetable_window_stale_cpus_only_when_locked(post_pt, pt_lower)) by { reveal(pagetable_window_stale_cpus_only_when_locked); };
    assert(pagetable_window_typed_lock_map_aligned(post_pt, pt_lower, window_lock_map, pagetable_lock_map, thread_id)) by { reveal(pagetable_window_typed_lock_map_aligned); };
}
}
