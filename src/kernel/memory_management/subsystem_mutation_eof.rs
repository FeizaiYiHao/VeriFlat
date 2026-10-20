use vstd::prelude::*;
use crate::*;

verus! {
/// S of `pagetable_map_insert_4k`: only the window half of `pagetable_ptr` changes, by the present 4K leaf `target_entry` at `va`;
/// the big-lock payloads and every window lock stay.
#[verifier::opaque]
pub open spec fn pagetable_map_insert_4k_eof_transition_framing(
    pt_mp: PageTableLockedMap, pre_lower: PageTableLowerMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, va: VAddr, target_entry: MapEntry,
) -> bool {
    &&& post_lower == pre_lower.insert(pagetable_ptr, post_lower.spec_index(pagetable_ptr))
    &&& post_lower.dom() =~= pre_lower.dom()
    &&& forall|r: RwLockPageTableRoot| #![trigger pagetable_c(pt_mp, post_lower, r)] r != pagetable_ptr ==> pagetable_c(pt_mp, post_lower, r) == pagetable_c(pt_mp, pre_lower, r)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
        #![trigger pagetable_c(pt_mp, post_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        #![trigger pagetable_c(pt_mp, pre_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        pagetable_c(pt_mp, post_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(pt_mp, pre_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).wf()
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).mapping_4k() == pagetable_c(pt_mp, pre_lower, pagetable_ptr).mapping_4k().insert(va, target_entry)
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).mapping_2m() == pagetable_c(pt_mp, pre_lower, pagetable_ptr).mapping_2m()
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).mapping_1g() == pagetable_c(pt_mp, pre_lower, pagetable_ptr).mapping_1g()
}

/// EOF closure of `pagetable_map_insert_4k`: the window-half invariants after one present 4K leaf is installed under the
/// big read lock, which leaves the write-lock backup of every table valid.
pub proof fn pagetable_map_insert_4k_eof(
    pt_mp: PageTableLockedMap, pre_lower: PageTableLowerMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, va: VAddr, target_entry: MapEntry,
    window_lock_map: Map<(RwLockPageTableRoot, VAddr), TypedHeldLock>, pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        pagetable_lower_wf(pt_mp, pre_lower),
        pagetable_window_holders_hold_pagetable(pt_mp, pre_lower),
        pagetable_hidden_leaves_only_when_wlocked(pt_mp, pre_lower),
        pagetable_window_typed_lock_map_aligned(pt_mp, pre_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(pt_mp, pre_lower),
        pt_mp.dom().contains(pagetable_ptr),
        pt_mp.spec_index(pagetable_ptr).locking_thread() is Read,
        target_entry.present,
        pagetable_map_insert_4k_eof_transition_framing(pt_mp, pre_lower, post_lower, pagetable_ptr, va, target_entry),
    ensures
        pagetable_lower_wf(pt_mp, post_lower),
        pagetable_window_holders_hold_pagetable(pt_mp, post_lower),
        pagetable_hidden_leaves_only_when_wlocked(pt_mp, post_lower),
        pagetable_window_typed_lock_map_aligned(pt_mp, post_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(pt_mp, post_lower),
{
    reveal(pagetable_map_insert_4k_eof_transition_framing);
    assert(pagetable_lower_wf(pt_mp, post_lower)) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(pt_mp, post_lower)) by { reveal(pagetable_window_holders_hold_pagetable); };
    assert(pagetable_hidden_leaves_only_when_wlocked(pt_mp, post_lower)) by { reveal(pagetable_hidden_leaves_only_when_wlocked); };
    assert(pagetable_window_typed_lock_map_aligned(pt_mp, post_lower, window_lock_map, pagetable_lock_map, thread_id)) by { reveal(pagetable_window_typed_lock_map_aligned); };
}

/// S of `pagetable_map_clear_4k_present`: under the big write lock only the window half of `pagetable_ptr` changes, by clearing the
/// user present bit of the 4K leaf at `va`; the lock's ghost slot is reset to the new window half and every window lock stays.
#[verifier::opaque]
pub open spec fn pagetable_map_clear_4k_present_eof_transition_framing(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, va: VAddr,
) -> bool {
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
    &&& forall|r: RwLockPageTableRoot| #![trigger pagetable_c(post_pt, post_lower, r)] pre_pt.dom().contains(r) && r != pagetable_ptr ==> pagetable_c(post_pt, post_lower, r) == pagetable_c(pre_pt, pre_lower, r)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
        #![trigger pagetable_c(post_pt, post_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        #![trigger pagetable_c(pre_pt, pre_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        pagetable_c(post_pt, post_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(pre_pt, pre_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).wf()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).kernel_l4_end() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).kernel_l4_end()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_4k() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_4k().insert(va, MapEntry { present: false, ..pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_4k().spec_index(va) })
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_2m() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_2m()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_1g() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_1g()
}

/// EOF closure of `pagetable_map_clear_4k_present`: the big-lock and window-half invariants after a 4K leaf of the write-held table is hidden.
pub proof fn pagetable_map_clear_4k_present_eof(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, va: VAddr,
    window_lock_map: Map<(RwLockPageTableRoot, VAddr), TypedHeldLock>, pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        pagetable_perms_wf(pre_pt),
        pre_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(pre_pt, pre_lower),
        pagetable_window_holders_hold_pagetable(pre_pt, pre_lower),
        pagetable_hidden_leaves_only_when_wlocked(pre_pt, pre_lower),
        pagetable_window_typed_lock_map_aligned(pre_pt, pre_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(pre_pt, pre_lower),
        pre_pt.dom().contains(pagetable_ptr),
        pre_pt.spec_index(pagetable_ptr).locking_thread() is Write,
        pagetable_map_clear_4k_present_eof_transition_framing(pre_pt, pre_lower, post_pt, post_lower, pagetable_ptr, va),
    ensures
        pagetable_perms_wf(post_pt),
        post_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(post_pt, post_lower),
        pagetable_window_holders_hold_pagetable(post_pt, post_lower),
        pagetable_hidden_leaves_only_when_wlocked(post_pt, post_lower),
        pagetable_window_typed_lock_map_aligned(post_pt, post_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(post_pt, post_lower),
{
    reveal(pagetable_map_clear_4k_present_eof_transition_framing);
    assert(pagetable_perms_wf(post_pt)) by { reveal(pagetable_perms_wf); };
    assert(post_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id)) by {
        reveal(LockedMap::typed_lock_map_aligned);
        assert(post_pt.spec_index(pagetable_ptr).locked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).locked_by_thread(thread_id));
        assert(post_pt.spec_index(pagetable_ptr).rlocked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).rlocked_by_thread(thread_id));
        assert(post_pt.spec_index(pagetable_ptr).wlocked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).wlocked_by_thread(thread_id));
    };
    assert(pagetable_lower_wf(post_pt, post_lower)) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(post_pt, post_lower)) by { reveal(pagetable_window_holders_hold_pagetable); };
    assert(pagetable_hidden_leaves_only_when_wlocked(post_pt, post_lower)) by { reveal(pagetable_hidden_leaves_only_when_wlocked); };
    assert(pagetable_window_typed_lock_map_aligned(post_pt, post_lower, window_lock_map, pagetable_lock_map, thread_id)) by {
        reveal(pagetable_window_typed_lock_map_aligned);
    };
}

/// S of `pagetable_map_unmap_4k_kernel`: under the big write lock only the window half of `pagetable_ptr` changes, by removing the
/// hidden 4K leaf at `va`; the lock's ghost slot is reset to the new window half and every window lock stays.
#[verifier::opaque]
pub open spec fn pagetable_map_unmap_4k_kernel_eof_transition_framing(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, va: VAddr,
) -> bool {
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
    &&& forall|r: RwLockPageTableRoot| #![trigger pagetable_c(post_pt, post_lower, r)] pre_pt.dom().contains(r) && r != pagetable_ptr ==> pagetable_c(post_pt, post_lower, r) == pagetable_c(pre_pt, pre_lower, r)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
        #![trigger pagetable_c(post_pt, post_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        #![trigger pagetable_c(pre_pt, pre_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        pagetable_c(post_pt, post_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(pre_pt, pre_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).wf()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).kernel_l4_end() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).kernel_l4_end()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_4k() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_4k().remove(va)
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_2m() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_2m()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_1g() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_1g()
}

/// EOF closure of `pagetable_map_unmap_4k_kernel`: the big-lock and window-half invariants after a hidden 4K leaf is removed.
pub proof fn pagetable_map_unmap_4k_kernel_eof(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, va: VAddr,
    window_lock_map: Map<(RwLockPageTableRoot, VAddr), TypedHeldLock>, pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        pagetable_perms_wf(pre_pt),
        pre_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(pre_pt, pre_lower),
        pagetable_window_holders_hold_pagetable(pre_pt, pre_lower),
        pagetable_hidden_leaves_only_when_wlocked(pre_pt, pre_lower),
        pagetable_window_typed_lock_map_aligned(pre_pt, pre_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(pre_pt, pre_lower),
        pre_pt.dom().contains(pagetable_ptr),
        pre_pt.spec_index(pagetable_ptr).locking_thread() is Write,
        pagetable_map_unmap_4k_kernel_eof_transition_framing(pre_pt, pre_lower, post_pt, post_lower, pagetable_ptr, va),
    ensures
        pagetable_perms_wf(post_pt),
        post_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(post_pt, post_lower),
        pagetable_window_holders_hold_pagetable(post_pt, post_lower),
        pagetable_hidden_leaves_only_when_wlocked(post_pt, post_lower),
        pagetable_window_typed_lock_map_aligned(post_pt, post_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(post_pt, post_lower),
{
    reveal(pagetable_map_unmap_4k_kernel_eof_transition_framing);
    assert(pagetable_perms_wf(post_pt)) by { reveal(pagetable_perms_wf); };
    assert(post_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id)) by {
        reveal(LockedMap::typed_lock_map_aligned);
        assert(post_pt.spec_index(pagetable_ptr).locked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).locked_by_thread(thread_id));
        assert(post_pt.spec_index(pagetable_ptr).rlocked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).rlocked_by_thread(thread_id));
        assert(post_pt.spec_index(pagetable_ptr).wlocked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).wlocked_by_thread(thread_id));
    };
    assert(pagetable_lower_wf(post_pt, post_lower)) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(post_pt, post_lower)) by { reveal(pagetable_window_holders_hold_pagetable); };
    assert(pagetable_hidden_leaves_only_when_wlocked(post_pt, post_lower)) by { reveal(pagetable_hidden_leaves_only_when_wlocked); };
    assert(pagetable_window_typed_lock_map_aligned(post_pt, post_lower, window_lock_map, pagetable_lock_map, thread_id)) by {
        reveal(pagetable_window_typed_lock_map_aligned);
    };
}

/// S of `pagetable_map_remove_table_page`: under the big write lock only the entry and window half of `pagetable_ptr` change, by
/// unlinking one table page; the lock's ghost slot is reset to the new window half, and every mapping and every window lock of a
/// valid user index stay.
#[verifier::opaque]
pub open spec fn pagetable_map_remove_table_page_eof_transition_framing(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot,
) -> bool {
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
    &&& forall|r: RwLockPageTableRoot| #![trigger pagetable_c(post_pt, post_lower, r)] pre_pt.dom().contains(r) && r != pagetable_ptr ==> pagetable_c(post_pt, post_lower, r) == pagetable_c(pre_pt, pre_lower, r)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
        #![trigger pagetable_c(post_pt, post_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        #![trigger pagetable_c(pre_pt, pre_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        pagetable_c(pre_pt, pre_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
            ==> pagetable_c(post_pt, post_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(pre_pt, pre_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).wf()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).kernel_l4_end() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).kernel_l4_end()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_4k() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_4k()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_2m() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_2m()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_1g() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_1g()
}

/// EOF closure of `pagetable_map_remove_table_page`: the big-lock and window-half invariants after one table page is unlinked.
pub proof fn pagetable_map_remove_table_page_eof(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot,
    window_lock_map: Map<(RwLockPageTableRoot, VAddr), TypedHeldLock>, pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        pagetable_perms_wf(pre_pt),
        pre_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(pre_pt, pre_lower),
        pagetable_window_holders_hold_pagetable(pre_pt, pre_lower),
        pagetable_hidden_leaves_only_when_wlocked(pre_pt, pre_lower),
        pagetable_window_typed_lock_map_aligned(pre_pt, pre_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(pre_pt, pre_lower),
        pre_pt.dom().contains(pagetable_ptr),
        pre_pt.spec_index(pagetable_ptr).locking_thread() is Write,
        pagetable_map_remove_table_page_eof_transition_framing(pre_pt, pre_lower, post_pt, post_lower, pagetable_ptr),
    ensures
        pagetable_perms_wf(post_pt),
        post_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(post_pt, post_lower),
        pagetable_window_holders_hold_pagetable(post_pt, post_lower),
        pagetable_hidden_leaves_only_when_wlocked(post_pt, post_lower),
        pagetable_window_typed_lock_map_aligned(post_pt, post_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(post_pt, post_lower),
{
    reveal(pagetable_map_remove_table_page_eof_transition_framing);
    assert(pagetable_perms_wf(post_pt)) by { reveal(pagetable_perms_wf); };
    assert(post_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id)) by {
        reveal(LockedMap::typed_lock_map_aligned);
        assert(post_pt.spec_index(pagetable_ptr).locked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).locked_by_thread(thread_id));
        assert(post_pt.spec_index(pagetable_ptr).rlocked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).rlocked_by_thread(thread_id));
        assert(post_pt.spec_index(pagetable_ptr).wlocked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).wlocked_by_thread(thread_id));
    };
    assert(pagetable_lower_wf(post_pt, post_lower)) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(post_pt, post_lower)) by { reveal(pagetable_window_holders_hold_pagetable); };
    assert(pagetable_hidden_leaves_only_when_wlocked(post_pt, post_lower)) by { reveal(pagetable_hidden_leaves_only_when_wlocked); };
    assert(pagetable_window_typed_lock_map_aligned(post_pt, post_lower, window_lock_map, pagetable_lock_map, thread_id)) by {
        reveal(pagetable_window_typed_lock_map_aligned);
        broadcast use spec_va_2m_valid_index_roundtrip;
    };
}

/// S of `pagetable_map_insert_4k_wlocked`: under the big write lock only the window half of `pagetable_ptr` changes, by the present 4K
/// leaf `target_entry` at `va`; the lock's ghost slot is reset to the new window half and every window lock stays.
#[verifier::opaque]
pub open spec fn pagetable_map_insert_4k_wlocked_eof_transition_framing(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, va: VAddr,
    target_entry: MapEntry,
) -> bool {
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
    &&& forall|r: RwLockPageTableRoot| #![trigger pagetable_c(post_pt, post_lower, r)] pre_pt.dom().contains(r) && r != pagetable_ptr ==> pagetable_c(post_pt, post_lower, r) == pagetable_c(pre_pt, pre_lower, r)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
        #![trigger pagetable_c(post_pt, post_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        #![trigger pagetable_c(pre_pt, pre_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        pagetable_c(post_pt, post_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(pre_pt, pre_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).wf()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).kernel_l4_end() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).kernel_l4_end()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_4k() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_4k().insert(va, target_entry)
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_2m() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_2m()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_1g() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_1g()
}

/// EOF closure of `pagetable_map_insert_4k_wlocked`: the big-lock and window-half invariants after one 4K leaf of the write-held
/// table is installed.
pub proof fn pagetable_map_insert_4k_wlocked_eof(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, va: VAddr,
    target_entry: MapEntry, window_lock_map: Map<(RwLockPageTableRoot, VAddr), TypedHeldLock>, pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>,
    thread_id: LockThreadId,
)
    requires
        pagetable_perms_wf(pre_pt),
        pre_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(pre_pt, pre_lower),
        pagetable_window_holders_hold_pagetable(pre_pt, pre_lower),
        pagetable_hidden_leaves_only_when_wlocked(pre_pt, pre_lower),
        pagetable_window_typed_lock_map_aligned(pre_pt, pre_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(pre_pt, pre_lower),
        pre_pt.dom().contains(pagetable_ptr),
        pre_pt.spec_index(pagetable_ptr).locking_thread() is Write,
        pagetable_map_insert_4k_wlocked_eof_transition_framing(pre_pt, pre_lower, post_pt, post_lower, pagetable_ptr, va, target_entry),
    ensures
        pagetable_perms_wf(post_pt),
        post_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(post_pt, post_lower),
        pagetable_window_holders_hold_pagetable(post_pt, post_lower),
        pagetable_hidden_leaves_only_when_wlocked(post_pt, post_lower),
        pagetable_window_typed_lock_map_aligned(post_pt, post_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(post_pt, post_lower),
{
    reveal(pagetable_map_insert_4k_wlocked_eof_transition_framing);
    assert(pagetable_perms_wf(post_pt)) by { reveal(pagetable_perms_wf); };
    assert(post_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id)) by {
        reveal(LockedMap::typed_lock_map_aligned);
        assert(post_pt.spec_index(pagetable_ptr).locked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).locked_by_thread(thread_id));
        assert(post_pt.spec_index(pagetable_ptr).rlocked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).rlocked_by_thread(thread_id));
        assert(post_pt.spec_index(pagetable_ptr).wlocked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).wlocked_by_thread(thread_id));
    };
    assert(pagetable_lower_wf(post_pt, post_lower)) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(post_pt, post_lower)) by { reveal(pagetable_window_holders_hold_pagetable); };
    assert(pagetable_hidden_leaves_only_when_wlocked(post_pt, post_lower)) by { reveal(pagetable_hidden_leaves_only_when_wlocked); };
    assert(pagetable_window_typed_lock_map_aligned(post_pt, post_lower, window_lock_map, pagetable_lock_map, thread_id)) by {
        reveal(pagetable_window_typed_lock_map_aligned);
    };
}

/// S of `pagetable_map_create_entry_l2`: only the window half of `pagetable_ptr` changes, by linking one L1 page; every mapping, the
/// big-lock payloads, and every window lock stay.
#[verifier::opaque]
pub open spec fn pagetable_map_create_entry_l2_eof_transition_framing(
    pt_mp: PageTableLockedMap, pre_lower: PageTableLowerMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot,
) -> bool {
    &&& post_lower == pre_lower.insert(pagetable_ptr, post_lower.spec_index(pagetable_ptr))
    &&& post_lower.dom() =~= pre_lower.dom()
    &&& forall|r: RwLockPageTableRoot| #![trigger pagetable_c(pt_mp, post_lower, r)] r != pagetable_ptr ==> pagetable_c(pt_mp, post_lower, r) == pagetable_c(pt_mp, pre_lower, r)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
        #![trigger pagetable_c(pt_mp, post_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        #![trigger pagetable_c(pt_mp, pre_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        pagetable_c(pt_mp, post_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(pt_mp, pre_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).wf()
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).mapping_4k() == pagetable_c(pt_mp, pre_lower, pagetable_ptr).mapping_4k()
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).mapping_2m() == pagetable_c(pt_mp, pre_lower, pagetable_ptr).mapping_2m()
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).mapping_1g() == pagetable_c(pt_mp, pre_lower, pagetable_ptr).mapping_1g()
}

/// EOF closure of `pagetable_map_create_entry_l2`: the window-half invariants after one L1 page is linked under the big read lock,
/// which leaves the write-lock backup of every table valid.
pub proof fn pagetable_map_create_entry_l2_eof(
    pt_mp: PageTableLockedMap, pre_lower: PageTableLowerMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot,
    window_lock_map: Map<(RwLockPageTableRoot, VAddr), TypedHeldLock>, pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        pagetable_lower_wf(pt_mp, pre_lower),
        pagetable_window_holders_hold_pagetable(pt_mp, pre_lower),
        pagetable_hidden_leaves_only_when_wlocked(pt_mp, pre_lower),
        pagetable_window_typed_lock_map_aligned(pt_mp, pre_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(pt_mp, pre_lower),
        pt_mp.dom().contains(pagetable_ptr),
        pt_mp.spec_index(pagetable_ptr).locking_thread() is Read,
        pagetable_map_create_entry_l2_eof_transition_framing(pt_mp, pre_lower, post_lower, pagetable_ptr),
    ensures
        pagetable_lower_wf(pt_mp, post_lower),
        pagetable_window_holders_hold_pagetable(pt_mp, post_lower),
        pagetable_hidden_leaves_only_when_wlocked(pt_mp, post_lower),
        pagetable_window_typed_lock_map_aligned(pt_mp, post_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(pt_mp, post_lower),
{
    reveal(pagetable_map_create_entry_l2_eof_transition_framing);
    assert(pagetable_lower_wf(pt_mp, post_lower)) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(pt_mp, post_lower)) by { reveal(pagetable_window_holders_hold_pagetable); };
    assert(pagetable_hidden_leaves_only_when_wlocked(pt_mp, post_lower)) by { reveal(pagetable_hidden_leaves_only_when_wlocked); };
    assert(pagetable_window_typed_lock_map_aligned(pt_mp, post_lower, window_lock_map, pagetable_lock_map, thread_id)) by { reveal(pagetable_window_typed_lock_map_aligned); };
}

/// S of `pagetable_map_create_entry_l2_wlocked`: under the big write lock only the window half of `pagetable_ptr` changes, by linking
/// one L1 page; the lock's ghost slot is reset to the new window half, and every mapping and every window lock stay.
#[verifier::opaque]
pub open spec fn pagetable_map_create_entry_l2_wlocked_eof_transition_framing(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot,
) -> bool {
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
    &&& forall|r: RwLockPageTableRoot| #![trigger pagetable_c(post_pt, post_lower, r)] pre_pt.dom().contains(r) && r != pagetable_ptr ==> pagetable_c(post_pt, post_lower, r) == pagetable_c(pre_pt, pre_lower, r)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
        #![trigger pagetable_c(post_pt, post_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        #![trigger pagetable_c(pre_pt, pre_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        pagetable_c(post_pt, post_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(pre_pt, pre_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).wf()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).kernel_l4_end() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).kernel_l4_end()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_4k() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_4k()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_2m() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_2m()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_1g() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_1g()
}

/// EOF closure of `pagetable_map_create_entry_l2_wlocked`: the big-lock and window-half invariants after one L1 page of the
/// write-held table is linked.
pub proof fn pagetable_map_create_entry_l2_wlocked_eof(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot,
    window_lock_map: Map<(RwLockPageTableRoot, VAddr), TypedHeldLock>, pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        pagetable_perms_wf(pre_pt),
        pre_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(pre_pt, pre_lower),
        pagetable_window_holders_hold_pagetable(pre_pt, pre_lower),
        pagetable_hidden_leaves_only_when_wlocked(pre_pt, pre_lower),
        pagetable_window_typed_lock_map_aligned(pre_pt, pre_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(pre_pt, pre_lower),
        pre_pt.dom().contains(pagetable_ptr),
        pre_pt.spec_index(pagetable_ptr).locking_thread() is Write,
        pagetable_map_create_entry_l2_wlocked_eof_transition_framing(pre_pt, pre_lower, post_pt, post_lower, pagetable_ptr),
    ensures
        pagetable_perms_wf(post_pt),
        post_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(post_pt, post_lower),
        pagetable_window_holders_hold_pagetable(post_pt, post_lower),
        pagetable_hidden_leaves_only_when_wlocked(post_pt, post_lower),
        pagetable_window_typed_lock_map_aligned(post_pt, post_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(post_pt, post_lower),
{
    reveal(pagetable_map_create_entry_l2_wlocked_eof_transition_framing);
    assert(pagetable_perms_wf(post_pt)) by { reveal(pagetable_perms_wf); };
    assert(post_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id)) by {
        reveal(LockedMap::typed_lock_map_aligned);
        assert(post_pt.spec_index(pagetable_ptr).locked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).locked_by_thread(thread_id));
        assert(post_pt.spec_index(pagetable_ptr).rlocked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).rlocked_by_thread(thread_id));
        assert(post_pt.spec_index(pagetable_ptr).wlocked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).wlocked_by_thread(thread_id));
    };
    assert(pagetable_lower_wf(post_pt, post_lower)) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(post_pt, post_lower)) by { reveal(pagetable_window_holders_hold_pagetable); };
    assert(pagetable_hidden_leaves_only_when_wlocked(post_pt, post_lower)) by { reveal(pagetable_hidden_leaves_only_when_wlocked); };
    assert(pagetable_window_typed_lock_map_aligned(post_pt, post_lower, window_lock_map, pagetable_lock_map, thread_id)) by {
        reveal(pagetable_window_typed_lock_map_aligned);
    };
}

/// S of `pagetable_map_create_entry_l4`: under the big write lock only the big-lock payload of `pagetable_ptr` changes, by linking
/// one L3 page; the window half and its ghost-slot copy, every mapping, and every window lock of a valid user index stay.
#[verifier::opaque]
pub open spec fn pagetable_map_create_entry_l4_eof_transition_framing(
    pre_pt: PageTableLockedMap, post_pt: PageTableLockedMap, pt_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot,
) -> bool {
    &&& post_pt.perms_wf()
    &&& post_pt.unchanged_except(&pre_pt, pagetable_ptr)
    &&& post_pt.spec_index(pagetable_ptr).is_init()
    &&& post_pt.spec_index(pagetable_ptr).locking_thread() == pre_pt.spec_index(pagetable_ptr).locking_thread()
    &&& post_pt.spec_index(pagetable_ptr).being_killed() == pre_pt.spec_index(pagetable_ptr).being_killed()
    &&& post_pt.spec_index(pagetable_ptr).view_rodata() == pre_pt.spec_index(pagetable_ptr).view_rodata()
    &&& post_pt.lock_id_by_key(pagetable_ptr) == pre_pt.lock_id_by_key(pagetable_ptr)
    &&& post_pt.spec_index(pagetable_ptr).view_ghost() == pre_pt.spec_index(pagetable_ptr).view_ghost()
    &&& forall|r: RwLockPageTableRoot| #![trigger pagetable_c(post_pt, pt_lower, r)] pre_pt.dom().contains(r) && r != pagetable_ptr ==> pagetable_c(post_pt, pt_lower, r) == pagetable_c(pre_pt, pt_lower, r)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
        #![trigger pagetable_c(post_pt, pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        #![trigger pagetable_c(pre_pt, pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        pagetable_c(pre_pt, pt_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
            ==> pagetable_c(post_pt, pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(pre_pt, pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)
    &&& pagetable_c(post_pt, pt_lower, pagetable_ptr).wf()
    &&& pagetable_c(post_pt, pt_lower, pagetable_ptr).kernel_l4_end() == pagetable_c(pre_pt, pt_lower, pagetable_ptr).kernel_l4_end()
    &&& pagetable_c(post_pt, pt_lower, pagetable_ptr).mapping_4k() == pagetable_c(pre_pt, pt_lower, pagetable_ptr).mapping_4k()
    &&& pagetable_c(post_pt, pt_lower, pagetable_ptr).mapping_2m() == pagetable_c(pre_pt, pt_lower, pagetable_ptr).mapping_2m()
    &&& pagetable_c(post_pt, pt_lower, pagetable_ptr).mapping_1g() == pagetable_c(pre_pt, pt_lower, pagetable_ptr).mapping_1g()
}

/// EOF closure of `pagetable_map_create_entry_l4`: the big-lock and window-half invariants after one L3 page is linked.
pub proof fn pagetable_map_create_entry_l4_eof(
    pre_pt: PageTableLockedMap, post_pt: PageTableLockedMap, pt_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot,
    window_lock_map: Map<(RwLockPageTableRoot, VAddr), TypedHeldLock>, pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        pagetable_perms_wf(pre_pt),
        pre_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(pre_pt, pt_lower),
        pagetable_window_holders_hold_pagetable(pre_pt, pt_lower),
        pagetable_hidden_leaves_only_when_wlocked(pre_pt, pt_lower),
        pagetable_window_typed_lock_map_aligned(pre_pt, pt_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(pre_pt, pt_lower),
        pre_pt.dom().contains(pagetable_ptr),
        pre_pt.spec_index(pagetable_ptr).locking_thread() is Write,
        pagetable_map_create_entry_l4_eof_transition_framing(pre_pt, post_pt, pt_lower, pagetable_ptr),
    ensures
        pagetable_perms_wf(post_pt),
        post_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(post_pt, pt_lower),
        pagetable_window_holders_hold_pagetable(post_pt, pt_lower),
        pagetable_hidden_leaves_only_when_wlocked(post_pt, pt_lower),
        pagetable_window_typed_lock_map_aligned(post_pt, pt_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(post_pt, pt_lower),
{
    reveal(pagetable_map_create_entry_l4_eof_transition_framing);
    assert(pagetable_perms_wf(post_pt)) by { reveal(pagetable_perms_wf); };
    assert(post_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id)) by {
        reveal(LockedMap::typed_lock_map_aligned);
        assert(post_pt.spec_index(pagetable_ptr).locked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).locked_by_thread(thread_id));
        assert(post_pt.spec_index(pagetable_ptr).rlocked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).rlocked_by_thread(thread_id));
        assert(post_pt.spec_index(pagetable_ptr).wlocked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).wlocked_by_thread(thread_id));
    };
    assert(pagetable_lower_wf(post_pt, pt_lower)) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(post_pt, pt_lower)) by { reveal(pagetable_window_holders_hold_pagetable); };
    assert(pagetable_hidden_leaves_only_when_wlocked(post_pt, pt_lower)) by { reveal(pagetable_hidden_leaves_only_when_wlocked); };
    assert(pagetable_window_typed_lock_map_aligned(post_pt, pt_lower, window_lock_map, pagetable_lock_map, thread_id)) by {
        reveal(pagetable_window_typed_lock_map_aligned);
        broadcast use spec_va_2m_valid_index_roundtrip;
    };
}

/// S of `pagetable_map_create_entry_l3`: under the big write lock only the entry and window half of `pagetable_ptr` change, by
/// linking one L2 page whose windows start unlocked; the lock's ghost slot is reset to the new window half, and every mapping and
/// every window lock of a valid user index stay.
#[verifier::opaque]
pub open spec fn pagetable_map_create_entry_l3_eof_transition_framing(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot,
) -> bool {
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
    &&& forall|r: RwLockPageTableRoot| #![trigger pagetable_c(post_pt, post_lower, r)] pre_pt.dom().contains(r) && r != pagetable_ptr ==> pagetable_c(post_pt, post_lower, r) == pagetable_c(pre_pt, pre_lower, r)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
        #![trigger pagetable_c(post_pt, post_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        #![trigger pagetable_c(pre_pt, pre_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        pagetable_c(pre_pt, pre_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
            ==> pagetable_c(post_pt, post_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(pre_pt, pre_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).wf()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).kernel_l4_end() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).kernel_l4_end()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_4k() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_4k()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_2m() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_2m()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_1g() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_1g()
}

/// EOF closure of `pagetable_map_create_entry_l3`: the big-lock and window-half invariants after one L2 page is linked.
pub proof fn pagetable_map_create_entry_l3_eof(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot,
    window_lock_map: Map<(RwLockPageTableRoot, VAddr), TypedHeldLock>, pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        pagetable_perms_wf(pre_pt),
        pre_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(pre_pt, pre_lower),
        pagetable_window_holders_hold_pagetable(pre_pt, pre_lower),
        pagetable_hidden_leaves_only_when_wlocked(pre_pt, pre_lower),
        pagetable_window_typed_lock_map_aligned(pre_pt, pre_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(pre_pt, pre_lower),
        pre_pt.dom().contains(pagetable_ptr),
        pre_pt.spec_index(pagetable_ptr).locking_thread() is Write,
        pagetable_map_create_entry_l3_eof_transition_framing(pre_pt, pre_lower, post_pt, post_lower, pagetable_ptr),
    ensures
        pagetable_perms_wf(post_pt),
        post_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(post_pt, post_lower),
        pagetable_window_holders_hold_pagetable(post_pt, post_lower),
        pagetable_hidden_leaves_only_when_wlocked(post_pt, post_lower),
        pagetable_window_typed_lock_map_aligned(post_pt, post_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(post_pt, post_lower),
{
    reveal(pagetable_map_create_entry_l3_eof_transition_framing);
    assert(pagetable_perms_wf(post_pt)) by { reveal(pagetable_perms_wf); };
    assert(post_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id)) by {
        reveal(LockedMap::typed_lock_map_aligned);
        assert(post_pt.spec_index(pagetable_ptr).locked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).locked_by_thread(thread_id));
        assert(post_pt.spec_index(pagetable_ptr).rlocked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).rlocked_by_thread(thread_id));
        assert(post_pt.spec_index(pagetable_ptr).wlocked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).wlocked_by_thread(thread_id));
    };
    assert(pagetable_lower_wf(post_pt, post_lower)) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(post_pt, post_lower)) by { reveal(pagetable_window_holders_hold_pagetable); };
    assert(pagetable_hidden_leaves_only_when_wlocked(post_pt, post_lower)) by { reveal(pagetable_hidden_leaves_only_when_wlocked); };
    assert(pagetable_window_typed_lock_map_aligned(post_pt, post_lower, window_lock_map, pagetable_lock_map, thread_id)) by {
        reveal(pagetable_window_typed_lock_map_aligned);
        broadcast use spec_va_2m_valid_index_roundtrip;
    };
}

/// No window of the L2 page `l2_p` linked at `(l4i, l3i)` of the table that `thread_id` write-holds has a holder when `thread_id`
/// holds no window: a holder would hold the big lock too, so it would be `thread_id`, whose window map would list it. Stated at the
/// would-be holder `lock_state(i)`, so a caller reads off `lock_state(i) is None`.
pub proof fn pagetable_l2_windows_unlocked_when_wlocker_holds_no_windows(
    pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, window_lock_map: Map<(RwLockPageTableRoot, VAddr), TypedHeldLock>,
    pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId, pagetable_ptr: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2_p: PageMapPtr,
)
    requires
        pagetable_window_holders_hold_pagetable(pt_mp, pt_lower),
        pagetable_window_typed_lock_map_aligned(pt_mp, pt_lower, window_lock_map, pagetable_lock_map, thread_id),
        pt_mp.dom().contains(pagetable_ptr),
        pt_mp.spec_index(pagetable_ptr).wlocked_by_thread(thread_id),
        window_lock_map.dom().is_empty(),
        pagetable_c(pt_mp, pt_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i),
        pagetable_c(pt_mp, pt_lower, pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i) is Some,
        pagetable_c(pt_mp, pt_lower, pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i)->0.addr == l2_p,
    ensures
        forall|i: L2Index|
            #![trigger pt_lower.spec_index(pagetable_ptr).l2_lock_of(l2_p).lock_state(i)]
            pei_valid(i) ==> !pagetable_c(pt_mp, pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, i, pt_lower.spec_index(pagetable_ptr).l2_lock_of(l2_p).lock_state(i)->Some_thread_id),
{
    reveal(pagetable_window_holders_hold_pagetable);
    reveal(pagetable_window_typed_lock_map_aligned);
}
}
