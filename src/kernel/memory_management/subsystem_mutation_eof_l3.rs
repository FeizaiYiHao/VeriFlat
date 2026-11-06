use vstd::prelude::*;
use crate::*;

verus! {
/// S of `pagetable_map_unlink_hidden_l3_l1_page`: under the big write lock only the window half of `pagetable_ptr` changes, by taking one L1 page that holds no 4K leaf out of an
/// unresolvable path; the lock's ghost slot is reset to the new window half, and every mapping, window lock of a valid user index, and held leaf stays.
#[verifier::opaque]
pub(super) open spec fn pagetable_map_unlink_hidden_l3_l1_page_eof_transition_framing(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot,
) -> bool {
    &&& post_pt.perms_wf()
    &&& post_pt.unchanged_except(&pre_pt, pagetable_ptr)
    &&& post_pt.spec_index(pagetable_ptr).is_init()
    &&& post_pt.spec_index(pagetable_ptr).locking_thread() == pre_pt.spec_index(pagetable_ptr).locking_thread()
    &&& post_pt.spec_index(pagetable_ptr).being_killed() == pre_pt.spec_index(pagetable_ptr).being_killed()
    &&& post_pt.spec_index(pagetable_ptr).view_rodata() == pre_pt.spec_index(pagetable_ptr).view_rodata()
    &&& post_pt.spec_index(pagetable_ptr).view() == pre_pt.spec_index(pagetable_ptr).view()
    &&& post_pt.lock_id_by_key(pagetable_ptr) == pre_pt.lock_id_by_key(pagetable_ptr)
    &&& post_pt.spec_index(pagetable_ptr).view_ghost() == post_lower.spec_index(pagetable_ptr)
    &&& post_lower == pre_lower.insert(pagetable_ptr, post_lower.spec_index(pagetable_ptr))
    &&& post_lower.dom() =~= pre_lower.dom()
    &&& forall|r: RwLockPageTableRoot| #![trigger whole_pagetable(post_pt, post_lower, r)] pre_pt.dom().contains(r) && r != pagetable_ptr ==> whole_pagetable(post_pt, post_lower, r) == whole_pagetable(pre_pt, pre_lower, r)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
        #![trigger whole_pagetable(post_pt, post_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        #![trigger whole_pagetable(pre_pt, pre_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        whole_pagetable(post_pt, post_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == whole_pagetable(pre_pt, pre_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)
    &&& whole_pagetable(post_pt, post_lower, pagetable_ptr).mapping_4k() == whole_pagetable(pre_pt, pre_lower, pagetable_ptr).mapping_4k()
    &&& whole_pagetable(post_pt, post_lower, pagetable_ptr).mapping_2m() == whole_pagetable(pre_pt, pre_lower, pagetable_ptr).mapping_2m()
    &&& whole_pagetable(post_pt, post_lower, pagetable_ptr).mapping_1g() == whole_pagetable(pre_pt, pre_lower, pagetable_ptr).mapping_1g()
    &&& whole_pagetable(post_pt, post_lower, pagetable_ptr).wf()
    &&& whole_pagetable(post_pt, post_lower, pagetable_ptr).kernel_l4_end() == whole_pagetable(pre_pt, pre_lower, pagetable_ptr).kernel_l4_end()
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
        #![trigger whole_pagetable(post_pt, post_lower, pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        #![trigger whole_pagetable(pre_pt, pre_lower, pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        whole_pagetable(pre_pt, pre_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
            ==> whole_pagetable(post_pt, post_lower, pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) == whole_pagetable(pre_pt, pre_lower, pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
        #![trigger whole_pagetable(post_pt, post_lower, pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i)]
        #![trigger whole_pagetable(pre_pt, pre_lower, pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i)]
        whole_pagetable(pre_pt, pre_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
            ==> whole_pagetable(post_pt, post_lower, pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i) == whole_pagetable(pre_pt, pre_lower, pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i)
}

/// EOF closure of `pagetable_map_unlink_hidden_l3_l1_page`: the big-lock and window-half invariants after one L1 page that holds no 4K leaf leaves an unresolvable path; every held leaf stays, so the page records keep following the held chains.
pub(super) proof fn pagetable_map_unlink_hidden_l3_l1_page_eof(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot,
    page_array: PageLockedArray, window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>, pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>,
    thread_id: LockThreadId,
)
    requires
        pagetable_perms_wf(pre_pt),
        pre_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(pre_pt, pre_lower),
        pagetable_window_holders_hold_pagetable(pre_pt, pre_lower),
        pagetable_hidden_leaves_only_when_locked(pre_pt, pre_lower),
        pagetable_hidden_l1_only_when_locked(pre_pt, pre_lower),
        pagetable_window_stale_cpus_only_when_locked(pre_pt, pre_lower),
        pagetable_window_typed_lock_map_aligned(pre_pt, pre_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(pre_pt, pre_lower),
        pagetable_table_stale_cpus_only_when_write_locked(pre_pt),
        pre_pt.dom().contains(pagetable_ptr),
        pre_pt.spec_index(pagetable_ptr).locking_thread() is Write,
        whole_pagetable(pre_pt, pre_lower, pagetable_ptr).kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        page_mappings_pagetable_wf(pre_pt, pre_lower, page_array),
        pagetable_map_unlink_hidden_l3_l1_page_eof_transition_framing(pre_pt, pre_lower, post_pt, post_lower, pagetable_ptr),
    ensures
        pagetable_perms_wf(post_pt),
        post_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(post_pt, post_lower),
        pagetable_window_holders_hold_pagetable(post_pt, post_lower),
        pagetable_hidden_leaves_only_when_locked(post_pt, post_lower),
        pagetable_hidden_l1_only_when_locked(post_pt, post_lower),
        pagetable_window_stale_cpus_only_when_locked(post_pt, post_lower),
        pagetable_window_typed_lock_map_aligned(post_pt, post_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(post_pt, post_lower),
        pagetable_table_stale_cpus_only_when_write_locked(post_pt),
        page_mappings_pagetable_wf(post_pt, post_lower, page_array),
{
    reveal(pagetable_map_unlink_hidden_l3_l1_page_eof_transition_framing);
    assert(page_mappings_pagetable_wf(post_pt, post_lower, page_array)) by {
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_va_1g_valid_index_roundtrip;
        reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
    };
    assert(pagetable_table_stale_cpus_only_when_write_locked(post_pt)) by { reveal(pagetable_table_stale_cpus_only_when_write_locked); };
    assert(pagetable_perms_wf(post_pt)) by { reveal(pagetable_perms_wf); };
    assert(post_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id)) by {
        reveal(LockedMap::typed_lock_map_aligned);
        assert(post_pt.spec_index(pagetable_ptr).locked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).locked_by_thread(thread_id));
        assert(post_pt.spec_index(pagetable_ptr).rlocked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).rlocked_by_thread(thread_id));
        assert(post_pt.spec_index(pagetable_ptr).wlocked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).wlocked_by_thread(thread_id));
    };
    assert(pagetable_lower_wf(post_pt, post_lower)) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(post_pt, post_lower)) by { reveal(pagetable_window_holders_hold_pagetable); };
    assert(pagetable_hidden_leaves_only_when_locked(post_pt, post_lower)) by { reveal(pagetable_hidden_leaves_only_when_locked); };
    assert(pagetable_hidden_l1_only_when_locked(post_pt, post_lower)) by { reveal(pagetable_hidden_l1_only_when_locked); };
    assert(pagetable_window_stale_cpus_only_when_locked(post_pt, post_lower)) by { reveal(pagetable_window_stale_cpus_only_when_locked); };
    assert(pagetable_window_typed_lock_map_aligned(post_pt, post_lower, window_lock_map, pagetable_lock_map, thread_id)) by {
        reveal(pagetable_window_typed_lock_map_aligned);
        broadcast use spec_va_2m_valid_index_roundtrip;
    };
}

/// S of `pagetable_map_remove_l3_entry`: under the big write lock only the entry and window half of `pagetable_ptr` change, by unlinking the L2 page of the unresolvable L3 entry `(l4i, l3i)`; the lock's ghost
/// slot is reset to the new window half, every mapping and every window lock of a valid user index stay, the windows of `(l4i, l3i)` leave the table, and every held leaf stays.
#[verifier::opaque]
pub(super) open spec fn pagetable_map_remove_l3_entry_eof_transition_framing(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, l4i: L4Index,
    l3i: L3Index,
) -> bool {
    let pre_c = whole_pagetable(pre_pt, pre_lower, pagetable_ptr);
    let post_c = whole_pagetable(post_pt, post_lower, pagetable_ptr);
    &&& post_pt.perms_wf()
    &&& post_pt.unchanged_except(&pre_pt, pagetable_ptr)
    &&& post_pt.spec_index(pagetable_ptr).is_init()
    &&& post_pt.spec_index(pagetable_ptr).locking_thread() == pre_pt.spec_index(pagetable_ptr).locking_thread()
    &&& post_pt.spec_index(pagetable_ptr).being_killed() == pre_pt.spec_index(pagetable_ptr).being_killed()
    &&& post_pt.spec_index(pagetable_ptr).view_rodata() == pre_pt.spec_index(pagetable_ptr).view_rodata()
    &&& post_pt.lock_id_by_key(pagetable_ptr) == pre_pt.lock_id_by_key(pagetable_ptr)
    &&& post_pt.spec_index(pagetable_ptr).view_ghost() == post_lower.spec_index(pagetable_ptr)
    &&& post_lower == pre_lower.insert(pagetable_ptr, post_lower.spec_index(pagetable_ptr))
    &&& post_lower.dom() =~= pre_lower.dom()
    &&& forall|r: RwLockPageTableRoot| #![trigger whole_pagetable(post_pt, post_lower, r)] pre_pt.dom().contains(r) && r != pagetable_ptr ==> whole_pagetable(post_pt, post_lower, r) == whole_pagetable(pre_pt, pre_lower, r)
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index, thread_id: LockThreadId|
        #![trigger post_c.window_locked_by_thread(i4, i3, i2, thread_id)]
        #![trigger pre_c.window_locked_by_thread(i4, i3, i2, thread_id)]
        pre_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) ==> post_c.window_locked_by_thread(i4, i3, i2, thread_id) == pre_c.window_locked_by_thread(i4, i3, i2, thread_id)
    &&& post_c.wf()
    &&& post_c.kernel_l4_end() == pre_c.kernel_l4_end()
    &&& post_c.mapping_4k() == pre_c.mapping_4k()
    &&& post_c.mapping_2m() == pre_c.mapping_2m()
    &&& post_c.mapping_1g() == pre_c.mapping_1g()
    &&& post_c.lower.pagetable_window_locks == pre_c.lower.pagetable_window_locks.remove_keys(pre_c.lower.pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == l4i && spec_v2l3index(w.va) == l3i))
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger post_c.spec_held_4k_l1(i4, i3, i2, i1)] #![trigger pre_c.spec_held_4k_l1(i4, i3, i2, i1)]
        pre_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1) ==> post_c.spec_held_4k_l1(i4, i3, i2, i1) == pre_c.spec_held_4k_l1(i4, i3, i2, i1)
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger post_c.spec_held_2m_l2(i4, i3, i2)] #![trigger pre_c.spec_held_2m_l2(i4, i3, i2)]
        pre_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) ==> post_c.spec_held_2m_l2(i4, i3, i2) == pre_c.spec_held_2m_l2(i4, i3, i2)
    &&& forall|i4: L4Index, i3: L3Index| #![trigger post_c.spec_held_1g_l3(i4, i3)] #![trigger pre_c.spec_held_1g_l3(i4, i3)]
        pre_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) ==> post_c.spec_held_1g_l3(i4, i3) == pre_c.spec_held_1g_l3(i4, i3)
    &&& post_pt.spec_index(pagetable_ptr).view().table_stale_cpus == pre_pt.spec_index(pagetable_ptr).view().table_stale_cpus
}

/// EOF closure of `pagetable_map_remove_l3_entry`: the big-lock and window-half invariants after the L2 page of an unresolvable L3 entry is unlinked; every held leaf stays, so the page records keep following the held chains. The unresolvable entry had no window, so the window locks stay.
pub(super) proof fn pagetable_map_remove_l3_entry_eof(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, l4i: L4Index,
    l3i: L3Index, page_array: PageLockedArray, window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>,
    pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        pagetable_perms_wf(pre_pt),
        pre_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(pre_pt, pre_lower),
        pagetable_window_holders_hold_pagetable(pre_pt, pre_lower),
        pagetable_hidden_leaves_only_when_locked(pre_pt, pre_lower),
        pagetable_hidden_l1_only_when_locked(pre_pt, pre_lower),
        pagetable_window_stale_cpus_only_when_locked(pre_pt, pre_lower),
        pagetable_window_typed_lock_map_aligned(pre_pt, pre_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(pre_pt, pre_lower),
        pagetable_table_stale_cpus_only_when_write_locked(pre_pt),
        pre_pt.dom().contains(pagetable_ptr),
        pre_pt.spec_index(pagetable_ptr).locking_thread() is Write,
        whole_pagetable(pre_pt, pre_lower, pagetable_ptr).kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        whole_pagetable(pre_pt, pre_lower, pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i) is None,
        page_mappings_pagetable_wf(pre_pt, pre_lower, page_array),
        pagetable_map_remove_l3_entry_eof_transition_framing(pre_pt, pre_lower, post_pt, post_lower, pagetable_ptr, l4i, l3i),
    ensures
        pagetable_perms_wf(post_pt),
        post_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(post_pt, post_lower),
        pagetable_window_holders_hold_pagetable(post_pt, post_lower),
        pagetable_hidden_leaves_only_when_locked(post_pt, post_lower),
        pagetable_hidden_l1_only_when_locked(post_pt, post_lower),
        pagetable_window_stale_cpus_only_when_locked(post_pt, post_lower),
        pagetable_window_typed_lock_map_aligned(post_pt, post_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(post_pt, post_lower),
        pagetable_table_stale_cpus_only_when_write_locked(post_pt),
        page_mappings_pagetable_wf(post_pt, post_lower, page_array),
        whole_pagetable(post_pt, post_lower, pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(pre_pt, pre_lower, pagetable_ptr).lower.pagetable_window_locks,
{
    reveal(pagetable_map_remove_l3_entry_eof_transition_framing);
    let pre_c = whole_pagetable(pre_pt, pre_lower, pagetable_ptr);
    let windows = pre_c.lower.pagetable_window_locks;
    pagetable_lower_wf_at(pre_pt, pre_lower, pagetable_ptr);
    assert(windows.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == l4i && spec_v2l3index(w.va) == l3i) =~= Set::<WindowVa>::empty()) by { reveal(WholePageTable::wf_window_locks); };
    assert(windows.remove_keys(Set::<WindowVa>::empty()) =~= windows);
    assert(page_mappings_pagetable_wf(post_pt, post_lower, page_array)) by {
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_va_1g_valid_index_roundtrip;
        reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
    };
    assert(pagetable_table_stale_cpus_only_when_write_locked(post_pt)) by { reveal(pagetable_table_stale_cpus_only_when_write_locked); };
    assert(pagetable_perms_wf(post_pt)) by { reveal(pagetable_perms_wf); };
    assert(post_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id)) by {
        reveal(LockedMap::typed_lock_map_aligned);
        assert(post_pt.spec_index(pagetable_ptr).locked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).locked_by_thread(thread_id));
        assert(post_pt.spec_index(pagetable_ptr).rlocked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).rlocked_by_thread(thread_id));
        assert(post_pt.spec_index(pagetable_ptr).wlocked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).wlocked_by_thread(thread_id));
    };
    assert(pagetable_lower_wf(post_pt, post_lower)) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(post_pt, post_lower)) by { reveal(pagetable_window_holders_hold_pagetable); };
    assert(pagetable_hidden_leaves_only_when_locked(post_pt, post_lower)) by { reveal(pagetable_hidden_leaves_only_when_locked); };
    assert(pagetable_hidden_l1_only_when_locked(post_pt, post_lower)) by { reveal(pagetable_hidden_l1_only_when_locked); };
    assert(pagetable_window_stale_cpus_only_when_locked(post_pt, post_lower)) by { reveal(pagetable_window_stale_cpus_only_when_locked); };
    assert(pagetable_window_typed_lock_map_aligned(post_pt, post_lower, window_lock_map, pagetable_lock_map, thread_id)) by {
        reveal(pagetable_window_typed_lock_map_aligned);
        broadcast use spec_va_2m_valid_index_roundtrip;
    };
}
}
