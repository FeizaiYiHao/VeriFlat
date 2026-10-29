use vstd::prelude::*;
use crate::*;

verus! {
/// S of `pagetable_map_insert_4k`: only the window half of `pagetable_ptr` changes, by the present 4K leaf `target_entry` at `va`;
/// the big-lock payloads and every window lock stay.
#[verifier::opaque]
pub(super) open spec fn pagetable_map_insert_4k_eof_transition_framing(
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
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).lower.l2_lock == pagetable_c(pt_mp, pre_lower, pagetable_ptr).lower.l2_lock
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).lower.window_stale_cpus == pagetable_c(pt_mp, pre_lower, pagetable_ptr).lower.window_stale_cpus
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).mapping_4k() == pagetable_c(pt_mp, pre_lower, pagetable_ptr).mapping_4k().insert(va, target_entry)
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).mapping_2m() == pagetable_c(pt_mp, pre_lower, pagetable_ptr).mapping_2m()
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).mapping_1g() == pagetable_c(pt_mp, pre_lower, pagetable_ptr).mapping_1g()
}

/// EOF closure of `pagetable_map_insert_4k`: the window-half invariants after one present 4K leaf is installed under the
/// big read lock, which leaves the write-lock backup of every table valid.
pub(super) proof fn pagetable_map_insert_4k_eof(
    pt_mp: PageTableLockedMap, pre_lower: PageTableLowerMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, va: VAddr, target_entry: MapEntry,
    window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>, pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        pagetable_lower_wf(pt_mp, pre_lower),
        pagetable_window_holders_hold_pagetable(pt_mp, pre_lower),
        pagetable_hidden_leaves_only_when_locked(pt_mp, pre_lower),
        pagetable_window_stale_cpus_only_when_locked(pt_mp, pre_lower),
        pagetable_window_typed_lock_map_aligned(pt_mp, pre_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(pt_mp, pre_lower),
        pt_mp.dom().contains(pagetable_ptr),
        pt_mp.spec_index(pagetable_ptr).locking_thread() is Read,
        target_entry.present,
        pagetable_map_insert_4k_eof_transition_framing(pt_mp, pre_lower, post_lower, pagetable_ptr, va, target_entry),
    ensures
        pagetable_lower_wf(pt_mp, post_lower),
        pagetable_window_holders_hold_pagetable(pt_mp, post_lower),
        pagetable_hidden_leaves_only_when_locked(pt_mp, post_lower),
        pagetable_window_stale_cpus_only_when_locked(pt_mp, post_lower),
        pagetable_window_typed_lock_map_aligned(pt_mp, post_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(pt_mp, post_lower),
{
    reveal(pagetable_map_insert_4k_eof_transition_framing);
    assert(pagetable_lower_wf(pt_mp, post_lower)) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(pt_mp, post_lower)) by { reveal(pagetable_window_holders_hold_pagetable); };
    assert(pagetable_hidden_leaves_only_when_locked(pt_mp, post_lower)) by { reveal(pagetable_hidden_leaves_only_when_locked); };
    assert(pagetable_window_stale_cpus_only_when_locked(pt_mp, post_lower)) by { reveal(pagetable_window_stale_cpus_only_when_locked); };
    assert(pagetable_window_typed_lock_map_aligned(pt_mp, post_lower, window_lock_map, pagetable_lock_map, thread_id)) by { reveal(pagetable_window_typed_lock_map_aligned); };
}

/// S of `pagetable_map_clear_4k_present`: under the big write lock only the window half of `pagetable_ptr` changes, by clearing the
/// user present bit of the 4K leaf at `va`; the lock's ghost slot is reset to the new window half and every window lock stays.
#[verifier::opaque]
pub(super) open spec fn pagetable_map_clear_4k_present_eof_transition_framing(
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
pub(super) proof fn pagetable_map_clear_4k_present_eof(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, va: VAddr,
    window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>, pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        pagetable_perms_wf(pre_pt),
        pre_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(pre_pt, pre_lower),
        pagetable_window_holders_hold_pagetable(pre_pt, pre_lower),
        pagetable_hidden_leaves_only_when_locked(pre_pt, pre_lower),
        pagetable_window_stale_cpus_only_when_locked(pre_pt, pre_lower),
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
        pagetable_hidden_leaves_only_when_locked(post_pt, post_lower),
        pagetable_window_stale_cpus_only_when_locked(post_pt, post_lower),
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
    assert(pagetable_hidden_leaves_only_when_locked(post_pt, post_lower)) by { reveal(pagetable_hidden_leaves_only_when_locked); };
    assert(pagetable_window_stale_cpus_only_when_locked(post_pt, post_lower)) by { reveal(pagetable_window_stale_cpus_only_when_locked); };
    assert(pagetable_window_typed_lock_map_aligned(post_pt, post_lower, window_lock_map, pagetable_lock_map, thread_id)) by {
        reveal(pagetable_window_typed_lock_map_aligned);
    };
}

/// S of `pagetable_map_unmap_4k_kernel`: under the big write lock only the window half of `pagetable_ptr` changes, by removing the
/// hidden 4K leaf at `va`; the lock's ghost slot is reset to the new window half and every window lock stays.
#[verifier::opaque]
pub(super) open spec fn pagetable_map_unmap_4k_kernel_eof_transition_framing(
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
pub(super) proof fn pagetable_map_unmap_4k_kernel_eof(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, va: VAddr,
    window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>, pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        pagetable_perms_wf(pre_pt),
        pre_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(pre_pt, pre_lower),
        pagetable_window_holders_hold_pagetable(pre_pt, pre_lower),
        pagetable_hidden_leaves_only_when_locked(pre_pt, pre_lower),
        pagetable_window_stale_cpus_only_when_locked(pre_pt, pre_lower),
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
        pagetable_hidden_leaves_only_when_locked(post_pt, post_lower),
        pagetable_window_stale_cpus_only_when_locked(post_pt, post_lower),
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
    assert(pagetable_hidden_leaves_only_when_locked(post_pt, post_lower)) by { reveal(pagetable_hidden_leaves_only_when_locked); };
    assert(pagetable_window_stale_cpus_only_when_locked(post_pt, post_lower)) by { reveal(pagetable_window_stale_cpus_only_when_locked); };
    assert(pagetable_window_typed_lock_map_aligned(post_pt, post_lower, window_lock_map, pagetable_lock_map, thread_id)) by {
        reveal(pagetable_window_typed_lock_map_aligned);
    };
}

/// S of `pagetable_map_clear_4k_present_rlocked`: under the big read lock only the window half of `pagetable_ptr` changes, by
/// clearing the user present bit of the 4K leaf at `va`; the big-lock payloads and every window lock stay.
#[verifier::opaque]
pub(super) open spec fn pagetable_map_clear_4k_present_rlocked_eof_transition_framing(
    pt_mp: PageTableLockedMap, pre_lower: PageTableLowerMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, va: VAddr,
) -> bool {
    &&& post_lower == pre_lower.insert(pagetable_ptr, post_lower.spec_index(pagetable_ptr))
    &&& post_lower.dom() =~= pre_lower.dom()
    &&& forall|r: RwLockPageTableRoot| #![trigger pagetable_c(pt_mp, post_lower, r)] r != pagetable_ptr ==> pagetable_c(pt_mp, post_lower, r) == pagetable_c(pt_mp, pre_lower, r)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
        #![trigger pagetable_c(pt_mp, post_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        #![trigger pagetable_c(pt_mp, pre_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        pagetable_c(pt_mp, post_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(pt_mp, pre_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).wf()
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).lower.l2_lock == pagetable_c(pt_mp, pre_lower, pagetable_ptr).lower.l2_lock
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).lower.window_stale_cpus == pagetable_c(pt_mp, pre_lower, pagetable_ptr).lower.window_stale_cpus
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).mapping_4k() == pagetable_c(pt_mp, pre_lower, pagetable_ptr).mapping_4k().insert(va, MapEntry { present: false, ..pagetable_c(pt_mp, pre_lower, pagetable_ptr).mapping_4k().spec_index(va) })
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).mapping_2m() == pagetable_c(pt_mp, pre_lower, pagetable_ptr).mapping_2m()
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).mapping_1g() == pagetable_c(pt_mp, pre_lower, pagetable_ptr).mapping_1g()
}

/// EOF closure of `pagetable_map_clear_4k_present_rlocked`: the window-half invariants after a 4K leaf of the read-held table is
/// hidden inside a window this thread holds, which leaves the write-lock backup of every table valid.
pub(super) proof fn pagetable_map_clear_4k_present_rlocked_eof(
    pt_mp: PageTableLockedMap, pre_lower: PageTableLowerMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index),
    window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>, pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        pagetable_lower_wf(pt_mp, pre_lower),
        pagetable_window_holders_hold_pagetable(pt_mp, pre_lower),
        pagetable_hidden_leaves_only_when_locked(pt_mp, pre_lower),
        pagetable_window_stale_cpus_only_when_locked(pt_mp, pre_lower),
        pagetable_window_typed_lock_map_aligned(pt_mp, pre_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(pt_mp, pre_lower),
        pt_mp.dom().contains(pagetable_ptr),
        pt_mp.spec_index(pagetable_ptr).locking_thread() is Read,
        pei_valid(indices.0) && pei_valid(indices.1) && pei_valid(indices.2) && pei_valid(indices.3),
        pagetable_c(pt_mp, pre_lower, pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, thread_id),
        pagetable_map_clear_4k_present_rlocked_eof_transition_framing(pt_mp, pre_lower, post_lower, pagetable_ptr, spec_index2va(indices)),
    ensures
        pagetable_lower_wf(pt_mp, post_lower),
        pagetable_window_holders_hold_pagetable(pt_mp, post_lower),
        pagetable_hidden_leaves_only_when_locked(pt_mp, post_lower),
        pagetable_window_stale_cpus_only_when_locked(pt_mp, post_lower),
        pagetable_window_typed_lock_map_aligned(pt_mp, post_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(pt_mp, post_lower),
{
    reveal(pagetable_map_clear_4k_present_rlocked_eof_transition_framing);
    let (l4i, l3i, l2i, l1i) = indices;
    assert(spec_v2l4index(spec_index2va((l4i, l3i, l2i, l1i))) == l4i && spec_v2l3index(spec_index2va((l4i, l3i, l2i, l1i))) == l3i && spec_v2l2index(spec_index2va((l4i, l3i, l2i, l1i))) == l2i)
        by (bit_vector) requires l4i < 512, l3i < 512, l2i < 512, l1i < 512;
    assert(pagetable_lower_wf(pt_mp, post_lower)) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(pt_mp, post_lower)) by { reveal(pagetable_window_holders_hold_pagetable); };
    assert(pagetable_hidden_leaves_only_when_locked(pt_mp, post_lower)) by {
        reveal(pagetable_hidden_leaves_only_when_locked);
        assert(pagetable_c(pt_mp, post_lower, pagetable_ptr).window_locked(l4i, l3i, l2i));
    };
    assert(pagetable_window_stale_cpus_only_when_locked(pt_mp, post_lower)) by { reveal(pagetable_window_stale_cpus_only_when_locked); };
    assert(pagetable_window_typed_lock_map_aligned(pt_mp, post_lower, window_lock_map, pagetable_lock_map, thread_id)) by { reveal(pagetable_window_typed_lock_map_aligned); };
}

/// S of `pagetable_map_unmap_4k_kernel_rlocked`: under the big read lock only the window half of `pagetable_ptr` changes, by removing
/// the hidden 4K leaf at `va`; the big-lock payloads and every window lock stay.
#[verifier::opaque]
pub(super) open spec fn pagetable_map_unmap_4k_kernel_rlocked_eof_transition_framing(
    pt_mp: PageTableLockedMap, pre_lower: PageTableLowerMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, va: VAddr,
) -> bool {
    &&& post_lower == pre_lower.insert(pagetable_ptr, post_lower.spec_index(pagetable_ptr))
    &&& post_lower.dom() =~= pre_lower.dom()
    &&& forall|r: RwLockPageTableRoot| #![trigger pagetable_c(pt_mp, post_lower, r)] r != pagetable_ptr ==> pagetable_c(pt_mp, post_lower, r) == pagetable_c(pt_mp, pre_lower, r)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
        #![trigger pagetable_c(pt_mp, post_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        #![trigger pagetable_c(pt_mp, pre_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        pagetable_c(pt_mp, post_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(pt_mp, pre_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).wf()
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).lower.l2_lock == pagetable_c(pt_mp, pre_lower, pagetable_ptr).lower.l2_lock
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).lower.window_stale_cpus == pagetable_c(pt_mp, pre_lower, pagetable_ptr).lower.window_stale_cpus
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).mapping_4k() == pagetable_c(pt_mp, pre_lower, pagetable_ptr).mapping_4k().remove(va)
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).mapping_2m() == pagetable_c(pt_mp, pre_lower, pagetable_ptr).mapping_2m()
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).mapping_1g() == pagetable_c(pt_mp, pre_lower, pagetable_ptr).mapping_1g()
}

/// EOF closure of `pagetable_map_unmap_4k_kernel_rlocked`: the window-half invariants after a hidden 4K leaf of the read-held table
/// is removed, which leaves the write-lock backup of every table valid.
pub(super) proof fn pagetable_map_unmap_4k_kernel_rlocked_eof(
    pt_mp: PageTableLockedMap, pre_lower: PageTableLowerMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, va: VAddr,
    window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>, pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        pagetable_lower_wf(pt_mp, pre_lower),
        pagetable_window_holders_hold_pagetable(pt_mp, pre_lower),
        pagetable_hidden_leaves_only_when_locked(pt_mp, pre_lower),
        pagetable_window_stale_cpus_only_when_locked(pt_mp, pre_lower),
        pagetable_window_typed_lock_map_aligned(pt_mp, pre_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(pt_mp, pre_lower),
        pt_mp.dom().contains(pagetable_ptr),
        pt_mp.spec_index(pagetable_ptr).locking_thread() is Read,
        pagetable_map_unmap_4k_kernel_rlocked_eof_transition_framing(pt_mp, pre_lower, post_lower, pagetable_ptr, va),
    ensures
        pagetable_lower_wf(pt_mp, post_lower),
        pagetable_window_holders_hold_pagetable(pt_mp, post_lower),
        pagetable_hidden_leaves_only_when_locked(pt_mp, post_lower),
        pagetable_window_stale_cpus_only_when_locked(pt_mp, post_lower),
        pagetable_window_typed_lock_map_aligned(pt_mp, post_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(pt_mp, post_lower),
{
    reveal(pagetable_map_unmap_4k_kernel_rlocked_eof_transition_framing);
    assert(pagetable_lower_wf(pt_mp, post_lower)) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(pt_mp, post_lower)) by { reveal(pagetable_window_holders_hold_pagetable); };
    assert(pagetable_hidden_leaves_only_when_locked(pt_mp, post_lower)) by { reveal(pagetable_hidden_leaves_only_when_locked); };
    assert(pagetable_window_stale_cpus_only_when_locked(pt_mp, post_lower)) by { reveal(pagetable_window_stale_cpus_only_when_locked); };
    assert(pagetable_window_typed_lock_map_aligned(pt_mp, post_lower, window_lock_map, pagetable_lock_map, thread_id)) by { reveal(pagetable_window_typed_lock_map_aligned); };
}

/// S of `pagetable_map_remove_table_page`: under the big write lock only the entry and window half of `pagetable_ptr` change, by
/// unlinking one table page; the lock's ghost slot is reset to the new window half, and every mapping and every window lock of a
/// valid user index stay.
#[verifier::opaque]
pub(super) open spec fn pagetable_map_remove_table_page_eof_transition_framing(
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
pub(super) proof fn pagetable_map_remove_table_page_eof(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot,
    window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>, pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        pagetable_perms_wf(pre_pt),
        pre_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(pre_pt, pre_lower),
        pagetable_window_holders_hold_pagetable(pre_pt, pre_lower),
        pagetable_hidden_leaves_only_when_locked(pre_pt, pre_lower),
        pagetable_window_stale_cpus_only_when_locked(pre_pt, pre_lower),
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
        pagetable_hidden_leaves_only_when_locked(post_pt, post_lower),
        pagetable_window_stale_cpus_only_when_locked(post_pt, post_lower),
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
    assert(pagetable_hidden_leaves_only_when_locked(post_pt, post_lower)) by { reveal(pagetable_hidden_leaves_only_when_locked); };
    assert(pagetable_window_stale_cpus_only_when_locked(post_pt, post_lower)) by { reveal(pagetable_window_stale_cpus_only_when_locked); };
    assert(pagetable_window_typed_lock_map_aligned(post_pt, post_lower, window_lock_map, pagetable_lock_map, thread_id)) by {
        reveal(pagetable_window_typed_lock_map_aligned);
        broadcast use spec_va_2m_valid_index_roundtrip;
    };
}

/// S of `pagetable_map_insert_4k_wlocked`: under the big write lock only the window half of `pagetable_ptr` changes, by the present 4K
/// leaf `target_entry` at `va`; the lock's ghost slot is reset to the new window half and every window lock stays.
#[verifier::opaque]
pub(super) open spec fn pagetable_map_insert_4k_wlocked_eof_transition_framing(
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
pub(super) proof fn pagetable_map_insert_4k_wlocked_eof(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, va: VAddr,
    target_entry: MapEntry, window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>, pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>,
    thread_id: LockThreadId,
)
    requires
        pagetable_perms_wf(pre_pt),
        pre_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(pre_pt, pre_lower),
        pagetable_window_holders_hold_pagetable(pre_pt, pre_lower),
        pagetable_hidden_leaves_only_when_locked(pre_pt, pre_lower),
        pagetable_window_stale_cpus_only_when_locked(pre_pt, pre_lower),
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
        pagetable_hidden_leaves_only_when_locked(post_pt, post_lower),
        pagetable_window_stale_cpus_only_when_locked(post_pt, post_lower),
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
    assert(pagetable_hidden_leaves_only_when_locked(post_pt, post_lower)) by { reveal(pagetable_hidden_leaves_only_when_locked); };
    assert(pagetable_window_stale_cpus_only_when_locked(post_pt, post_lower)) by { reveal(pagetable_window_stale_cpus_only_when_locked); };
    assert(pagetable_window_typed_lock_map_aligned(post_pt, post_lower, window_lock_map, pagetable_lock_map, thread_id)) by {
        reveal(pagetable_window_typed_lock_map_aligned);
    };
}

/// S of `pagetable_map_create_entry_l2`: only the window half of `pagetable_ptr` changes, by linking one L1 page; every mapping, the
/// big-lock payloads, and every window lock stay.
#[verifier::opaque]
pub(super) open spec fn pagetable_map_create_entry_l2_eof_transition_framing(
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
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).lower.l2_lock == pagetable_c(pt_mp, pre_lower, pagetable_ptr).lower.l2_lock
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).lower.window_stale_cpus == pagetable_c(pt_mp, pre_lower, pagetable_ptr).lower.window_stale_cpus
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).mapping_4k() == pagetable_c(pt_mp, pre_lower, pagetable_ptr).mapping_4k()
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).mapping_2m() == pagetable_c(pt_mp, pre_lower, pagetable_ptr).mapping_2m()
    &&& pagetable_c(pt_mp, post_lower, pagetable_ptr).mapping_1g() == pagetable_c(pt_mp, pre_lower, pagetable_ptr).mapping_1g()
}

/// EOF closure of `pagetable_map_create_entry_l2`: the window-half invariants after one L1 page is linked under the big read lock,
/// which leaves the write-lock backup of every table valid.
pub(super) proof fn pagetable_map_create_entry_l2_eof(
    pt_mp: PageTableLockedMap, pre_lower: PageTableLowerMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot,
    window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>, pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        pagetable_lower_wf(pt_mp, pre_lower),
        pagetable_window_holders_hold_pagetable(pt_mp, pre_lower),
        pagetable_hidden_leaves_only_when_locked(pt_mp, pre_lower),
        pagetable_window_stale_cpus_only_when_locked(pt_mp, pre_lower),
        pagetable_window_typed_lock_map_aligned(pt_mp, pre_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(pt_mp, pre_lower),
        pt_mp.dom().contains(pagetable_ptr),
        pt_mp.spec_index(pagetable_ptr).locking_thread() is Read,
        pagetable_map_create_entry_l2_eof_transition_framing(pt_mp, pre_lower, post_lower, pagetable_ptr),
    ensures
        pagetable_lower_wf(pt_mp, post_lower),
        pagetable_window_holders_hold_pagetable(pt_mp, post_lower),
        pagetable_hidden_leaves_only_when_locked(pt_mp, post_lower),
        pagetable_window_stale_cpus_only_when_locked(pt_mp, post_lower),
        pagetable_window_typed_lock_map_aligned(pt_mp, post_lower, window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(pt_mp, post_lower),
{
    reveal(pagetable_map_create_entry_l2_eof_transition_framing);
    assert(pagetable_lower_wf(pt_mp, post_lower)) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(pt_mp, post_lower)) by { reveal(pagetable_window_holders_hold_pagetable); };
    assert(pagetable_hidden_leaves_only_when_locked(pt_mp, post_lower)) by { reveal(pagetable_hidden_leaves_only_when_locked); };
    assert(pagetable_window_stale_cpus_only_when_locked(pt_mp, post_lower)) by { reveal(pagetable_window_stale_cpus_only_when_locked); };
    assert(pagetable_window_typed_lock_map_aligned(pt_mp, post_lower, window_lock_map, pagetable_lock_map, thread_id)) by { reveal(pagetable_window_typed_lock_map_aligned); };
}

/// S of `pagetable_map_create_entry_l2_wlocked`: under the big write lock only the window half of `pagetable_ptr` changes, by linking
/// one L1 page; the lock's ghost slot is reset to the new window half, and every mapping and every window lock stay.
#[verifier::opaque]
pub(super) open spec fn pagetable_map_create_entry_l2_wlocked_eof_transition_framing(
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
pub(super) proof fn pagetable_map_create_entry_l2_wlocked_eof(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot,
    window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>, pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        pagetable_perms_wf(pre_pt),
        pre_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(pre_pt, pre_lower),
        pagetable_window_holders_hold_pagetable(pre_pt, pre_lower),
        pagetable_hidden_leaves_only_when_locked(pre_pt, pre_lower),
        pagetable_window_stale_cpus_only_when_locked(pre_pt, pre_lower),
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
        pagetable_hidden_leaves_only_when_locked(post_pt, post_lower),
        pagetable_window_stale_cpus_only_when_locked(post_pt, post_lower),
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
    assert(pagetable_hidden_leaves_only_when_locked(post_pt, post_lower)) by { reveal(pagetable_hidden_leaves_only_when_locked); };
    assert(pagetable_window_stale_cpus_only_when_locked(post_pt, post_lower)) by { reveal(pagetable_window_stale_cpus_only_when_locked); };
    assert(pagetable_window_typed_lock_map_aligned(post_pt, post_lower, window_lock_map, pagetable_lock_map, thread_id)) by {
        reveal(pagetable_window_typed_lock_map_aligned);
    };
}

/// S of `pagetable_map_create_entry_l4`: under the big write lock only the big-lock payload of `pagetable_ptr` changes, by linking
/// one L3 page; the window half and its ghost-slot copy, every mapping, and every window lock of a valid user index stay.
#[verifier::opaque]
pub(super) open spec fn pagetable_map_create_entry_l4_eof_transition_framing(
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
pub(super) proof fn pagetable_map_create_entry_l4_eof(
    pre_pt: PageTableLockedMap, post_pt: PageTableLockedMap, pt_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot,
    window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>, pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        pagetable_perms_wf(pre_pt),
        pre_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(pre_pt, pt_lower),
        pagetable_window_holders_hold_pagetable(pre_pt, pt_lower),
        pagetable_hidden_leaves_only_when_locked(pre_pt, pt_lower),
        pagetable_window_stale_cpus_only_when_locked(pre_pt, pt_lower),
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
        pagetable_hidden_leaves_only_when_locked(post_pt, pt_lower),
        pagetable_window_stale_cpus_only_when_locked(post_pt, pt_lower),
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
    assert(pagetable_hidden_leaves_only_when_locked(post_pt, pt_lower)) by { reveal(pagetable_hidden_leaves_only_when_locked); };
    assert(pagetable_window_stale_cpus_only_when_locked(post_pt, pt_lower)) by { reveal(pagetable_window_stale_cpus_only_when_locked); };
    assert(pagetable_window_typed_lock_map_aligned(post_pt, pt_lower, window_lock_map, pagetable_lock_map, thread_id)) by {
        reveal(pagetable_window_typed_lock_map_aligned);
        broadcast use spec_va_2m_valid_index_roundtrip;
    };
}

/// S of `pagetable_map_create_entry_l3`: under the big write lock only the entry and window half of `pagetable_ptr` change, by
/// linking one L2 page at `(l4i, l3i)` whose windows `lo..=hi` start held by `thread_id` and whose other windows start unlocked;
/// the lock's ghost slot is reset to the new window half, every mapping stays, and every other window lock of a valid user index
/// stays.
#[verifier::opaque]
pub(super) open spec fn pagetable_map_create_entry_l3_eof_transition_framing(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, l4i: L4Index,
    l3i: L3Index, lo: L2Index, hi: L2Index, thread_id: LockThreadId,
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
    &&& forall|a: L4Index, b: L3Index, c: L2Index, t: LockThreadId|
        #![trigger pagetable_c(post_pt, post_lower, pagetable_ptr).window_locked_by_thread(a, b, c, t)]
        #![trigger pagetable_c(pre_pt, pre_lower, pagetable_ptr).window_locked_by_thread(a, b, c, t)]
        pagetable_c(pre_pt, pre_lower, pagetable_ptr).kernel_l4_end() <= a && pei_valid(a) && pei_valid(b) && pei_valid(c)
            ==> pagetable_c(post_pt, post_lower, pagetable_ptr).window_locked_by_thread(a, b, c, t)
                == (pagetable_c(pre_pt, pre_lower, pagetable_ptr).window_locked_by_thread(a, b, c, t) || (a == l4i && b == l3i && lo <= c <= hi && t == thread_id))
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).wf()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).kernel_l4_end() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).kernel_l4_end()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_4k() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_4k()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_2m() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_2m()
    &&& pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_1g() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_1g()
}

/// EOF closure of `pagetable_map_create_entry_l3`: the big-lock and window-half invariants after one L2 page is linked with windows
/// `lo..=hi` held by `thread_id`, whose window map gains exactly those windows.
pub(super) proof fn pagetable_map_create_entry_l3_eof(
    pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot,
    pre_window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>, post_window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>,
    pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId, l4i: L4Index, l3i: L3Index, lo: L2Index, hi: L2Index,
)
    requires
        pagetable_perms_wf(pre_pt),
        pre_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(pre_pt, pre_lower),
        pagetable_window_holders_hold_pagetable(pre_pt, pre_lower),
        pagetable_hidden_leaves_only_when_locked(pre_pt, pre_lower),
        pagetable_window_stale_cpus_only_when_locked(pre_pt, pre_lower),
        pagetable_window_typed_lock_map_aligned(pre_pt, pre_lower, pre_window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(pre_pt, pre_lower),
        pre_pt.dom().contains(pagetable_ptr),
        typed_lock_map_contains_mode(pagetable_lock_map, pagetable_ptr, TypedLockMode::Write),
        pagetable_c(pre_pt, pre_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i),
        KERNEL_MEM_END_L4INDEX <= l4i,
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger post_window_lock_map.dom().contains((p, w))]
            post_window_lock_map.dom().contains((p, w)) == (pre_window_lock_map.dom().contains((p, w))
                || (p == pagetable_ptr && w.wf() && spec_v2l4index(w.va) == l4i && spec_v2l3index(w.va) == l3i && lo <= spec_v2l2index(w.va) <= hi)),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger post_window_lock_map.index((p, w))]
            pre_window_lock_map.dom().contains((p, w)) && !(p == pagetable_ptr && w.wf() && spec_v2l4index(w.va) == l4i && spec_v2l3index(w.va) == l3i && lo <= spec_v2l2index(w.va) <= hi)
                ==> post_window_lock_map.index((p, w)) == pre_window_lock_map.index((p, w)),
        forall|w: WindowVa| #![trigger post_window_lock_map.index((pagetable_ptr, w))]
            w.wf() && spec_v2l4index(w.va) == l4i && spec_v2l3index(w.va) == l3i && lo <= spec_v2l2index(w.va) <= hi
                ==> post_window_lock_map.index((pagetable_ptr, w)) == (TypedHeldLock { lock_id: window_lock_id_of(pagetable_ptr, w), mode: TypedLockMode::Write }),
        pagetable_map_create_entry_l3_eof_transition_framing(pre_pt, pre_lower, post_pt, post_lower, pagetable_ptr, l4i, l3i, lo, hi, thread_id),
    ensures
        pagetable_perms_wf(post_pt),
        post_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id),
        pagetable_lower_wf(post_pt, post_lower),
        pagetable_window_holders_hold_pagetable(post_pt, post_lower),
        pagetable_hidden_leaves_only_when_locked(post_pt, post_lower),
        pagetable_window_stale_cpus_only_when_locked(post_pt, post_lower),
        pagetable_window_typed_lock_map_aligned(post_pt, post_lower, post_window_lock_map, pagetable_lock_map, thread_id),
        pagetable_lower_backup_wf(post_pt, post_lower),
{
    reveal(pagetable_map_create_entry_l3_eof_transition_framing);
    pre_pt.typed_lock_map_aligned_write_at(pagetable_lock_map, thread_id, pagetable_ptr);
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
    assert(pagetable_window_stale_cpus_only_when_locked(post_pt, post_lower)) by { reveal(pagetable_window_stale_cpus_only_when_locked); };
    assert(pagetable_window_typed_lock_map_aligned(post_pt, post_lower, post_window_lock_map, pagetable_lock_map, thread_id)) by {
        reveal(pagetable_window_typed_lock_map_aligned);
        spec_index2va_injective();
        broadcast use spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid;
    };
}

/// No window of the L2 page `l2_p` linked at `(l4i, l3i)` of the table that `thread_id` write-holds has a holder when `thread_id`
/// holds no window: a holder would hold the big lock too, so it would be `thread_id`, whose window map would list it. Stated at the
/// would-be holder `lock_state(i)`, so a caller reads off `lock_state(i) is None`.
pub proof fn pagetable_l2_windows_unlocked_when_wlocker_holds_no_windows(
    pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>,
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

/// S of `iommu_table_map_set_did`: only the DID of the write-held IOMMU table `iommu_table_ptr` changes; its lock state stays.
#[verifier::opaque]
pub(super) open spec fn iommu_table_map_set_did_eof_transition_framing(
    pre: IommuTableLockedMap, post: IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot, did: Option<VtdDomainId>,
) -> bool {
    &&& post.perms_wf()
    &&& post.unchanged_except(&pre, iommu_table_ptr)
    &&& post.spec_index(iommu_table_ptr).is_init()
    &&& post.spec_index(iommu_table_ptr).locking_thread() == pre.spec_index(iommu_table_ptr).locking_thread()
    &&& post.spec_index(iommu_table_ptr).view() == (PageTable { did, ..pre.spec_index(iommu_table_ptr).view() })
}

/// EOF closure of `iommu_table_map_set_did` for the changed table's table levels, which do not read the DID.
proof fn iommu_table_map_set_did_eof_table_levels(pre_table: PageTable<IOMMU_TYPE>, post_table: PageTable<IOMMU_TYPE>, did: Option<VtdDomainId>)
    requires
        pre_table.wf(),
        post_table == (PageTable { did, ..pre_table }),
    ensures
        post_table.wf_l4(),
        post_table.wf_l3(),
        post_table.wf_l2(),
        post_table.wf_l1(),
{ reveal(PageTable::wf_l4); reveal(PageTable::wf_l3); reveal(PageTable::wf_l2); reveal(PageTable::wf_l1); }

/// EOF closure of `iommu_table_map_set_did` for the changed table's table disjointness, which does not read the DID.
proof fn iommu_table_map_set_did_eof_table_disjoint(pre_table: PageTable<IOMMU_TYPE>, post_table: PageTable<IOMMU_TYPE>, did: Option<VtdDomainId>)
    requires
        pre_table.wf(),
        post_table == (PageTable { did, ..pre_table }),
    ensures
        post_table.disjoint_l4(),
        post_table.disjoint_l3(),
        post_table.disjoint_l2(),
{ reveal(PageTable::disjoint_l4); reveal(PageTable::disjoint_l3); reveal(PageTable::disjoint_l2); }

/// EOF closure of `iommu_table_map_set_did` for the changed table's mappings, which do not read the DID.
proof fn iommu_table_map_set_did_eof_table_mappings(pre_table: PageTable<IOMMU_TYPE>, post_table: PageTable<IOMMU_TYPE>, did: Option<VtdDomainId>)
    requires
        pre_table.wf(),
        post_table == (PageTable { did, ..pre_table }),
    ensures
        post_table.wf_mapping_4k(),
        post_table.wf_mapping_2m(),
        post_table.wf_mapping_1g(),
{ reveal(PageTable::wf_mapping_4k); reveal(PageTable::wf_mapping_2m); reveal(PageTable::wf_mapping_1g); }

/// EOF closure of `iommu_table_map_set_did` for the changed table's entry permissions, which do not read the DID.
proof fn iommu_table_map_set_did_eof_table_permissions(pre_table: PageTable<IOMMU_TYPE>, post_table: PageTable<IOMMU_TYPE>, did: Option<VtdDomainId>)
    requires
        pre_table.wf(),
        post_table == (PageTable { did, ..pre_table }),
    ensures
        post_table.user_only(),
        post_table.rwx_upper_level_entries(),
{ reveal(PageTable::user_only); reveal(PageTable::rwx_upper_level_entries); }

/// EOF closure of `iommu_table_map_set_did` for the changed table's table pages, reachability, and kernel entries, which do not read the DID.
proof fn iommu_table_map_set_did_eof_table_table_pages(pre_table: PageTable<IOMMU_TYPE>, post_table: PageTable<IOMMU_TYPE>, did: Option<VtdDomainId>)
    requires
        pre_table.wf(),
        post_table == (PageTable { did, ..pre_table }),
    ensures
        post_table.table_pages_wf(),
        post_table.tables_reachable_wf(),
        post_table.kernel_entries_wf(),
{ reveal(PageTable::table_pages_wf); reveal(PageTable::tables_reachable_wf); reveal(PageTable::kernel_entries_wf); }

/// EOF closure of `iommu_table_map_set_did`: neither a table's well-formedness nor the hidden-leaf lock rule reads its DID.
pub(super) proof fn iommu_table_map_set_did_eof(pre: IommuTableLockedMap, post: IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot, did: Option<VtdDomainId>)
    requires
        iommu_table_perms_wf(pre),
        pre.dom().contains(iommu_table_ptr),
        pre.spec_index(iommu_table_ptr).locking_thread() is Write,
        did matches Some(d) ==> vtd_domain_id_valid(d),
        iommu_table_map_set_did_eof_transition_framing(pre, post, iommu_table_ptr, did),
    ensures iommu_table_perms_wf(post),
{
    reveal(iommu_table_map_set_did_eof_transition_framing);
    iommu_table_perms_wf_at(pre, iommu_table_ptr);
    let pre_table = pre.spec_index(iommu_table_ptr).view();
    let post_table = post.spec_index(iommu_table_ptr).view();
    iommu_table_map_set_did_eof_table_levels(pre_table, post_table, did);
    iommu_table_map_set_did_eof_table_disjoint(pre_table, post_table, did);
    iommu_table_map_set_did_eof_table_mappings(pre_table, post_table, did);
    iommu_table_map_set_did_eof_table_permissions(pre_table, post_table, did);
    iommu_table_map_set_did_eof_table_table_pages(pre_table, post_table, did);
    reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked);
}

/// S of `page_array_retype_owned_4k`: only page `page_index` changes, by retyping the owned 4K page to a kernel object; it stays well formed at its address.
#[verifier::opaque]
pub(super) open spec fn page_array_retype_owned_4k_eof_transition_framing(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex) -> bool {
    &&& post.inv()
    &&& post.entries_unchanged_except(&pre, page_index)
    &&& post.spec_index(page_index).view().inv()
    &&& post.spec_index(page_index).view().view().addr == pre.spec_index(page_index).view().view().addr
}

/// EOF closure of `page_array_retype_owned_4k`: the page array stays well formed when one page changes in place.
pub(super) proof fn page_array_retype_owned_4k_eof(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex)
    requires
        page_array_wf(pre),
        index_valid(NUM_PAGES, page_index),
        page_array_retype_owned_4k_eof_transition_framing(pre, post, page_index),
    ensures page_array_wf(post),
{ reveal(page_array_retype_owned_4k_eof_transition_framing); reveal(page_array_wf); }

/// S of `page_array_remove_4k_mapping_without_free`: only page `page_index` changes, by removing one mapping of the still-referenced 4K page; it stays well formed at its address.
#[verifier::opaque]
pub(super) open spec fn page_array_remove_4k_mapping_without_free_eof_transition_framing(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex) -> bool {
    &&& post.inv()
    &&& post.entries_unchanged_except(&pre, page_index)
    &&& post.spec_index(page_index).view().inv()
    &&& post.spec_index(page_index).view().view().addr == pre.spec_index(page_index).view().view().addr
}

/// EOF closure of `page_array_remove_4k_mapping_without_free`: the page array stays well formed when one page changes in place.
pub(super) proof fn page_array_remove_4k_mapping_without_free_eof(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex)
    requires
        page_array_wf(pre),
        index_valid(NUM_PAGES, page_index),
        page_array_remove_4k_mapping_without_free_eof_transition_framing(pre, post, page_index),
    ensures page_array_wf(post),
{ reveal(page_array_remove_4k_mapping_without_free_eof_transition_framing); reveal(page_array_wf); }

/// S of `page_array_remove_last_4k_mapping_to_cache`: only page `page_index` changes, by removing the last mapping of the 4K page and freeing it to a cpu cache; it stays well formed at its address.
#[verifier::opaque]
pub(super) open spec fn page_array_remove_last_4k_mapping_to_cache_eof_transition_framing(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex) -> bool {
    &&& post.inv()
    &&& post.entries_unchanged_except(&pre, page_index)
    &&& post.spec_index(page_index).view().inv()
    &&& post.spec_index(page_index).view().view().addr == pre.spec_index(page_index).view().view().addr
}

/// EOF closure of `page_array_remove_last_4k_mapping_to_cache`: the page array stays well formed when one page changes in place.
pub(super) proof fn page_array_remove_last_4k_mapping_to_cache_eof(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex)
    requires
        page_array_wf(pre),
        index_valid(NUM_PAGES, page_index),
        page_array_remove_last_4k_mapping_to_cache_eof_transition_framing(pre, post, page_index),
    ensures page_array_wf(post),
{ reveal(page_array_remove_last_4k_mapping_to_cache_eof_transition_framing); reveal(page_array_wf); }

/// S of `page_array_remove_4k_iommu_mapping_without_free`: only page `page_index` changes, by removing one IOMMU mapping of the still-referenced 4K page; it stays well formed at its address.
#[verifier::opaque]
pub(super) open spec fn page_array_remove_4k_iommu_mapping_without_free_eof_transition_framing(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex) -> bool {
    &&& post.inv()
    &&& post.entries_unchanged_except(&pre, page_index)
    &&& post.spec_index(page_index).view().inv()
    &&& post.spec_index(page_index).view().view().addr == pre.spec_index(page_index).view().view().addr
}

/// EOF closure of `page_array_remove_4k_iommu_mapping_without_free`: the page array stays well formed when one page changes in place.
pub(super) proof fn page_array_remove_4k_iommu_mapping_without_free_eof(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex)
    requires
        page_array_wf(pre),
        index_valid(NUM_PAGES, page_index),
        page_array_remove_4k_iommu_mapping_without_free_eof_transition_framing(pre, post, page_index),
    ensures page_array_wf(post),
{ reveal(page_array_remove_4k_iommu_mapping_without_free_eof_transition_framing); reveal(page_array_wf); }

/// S of `page_array_remove_last_4k_iommu_mapping_to_cache`: only page `page_index` changes, by removing the last IOMMU mapping of the 4K page and freeing it to a cpu cache; it stays well formed at its address.
#[verifier::opaque]
pub(super) open spec fn page_array_remove_last_4k_iommu_mapping_to_cache_eof_transition_framing(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex) -> bool {
    &&& post.inv()
    &&& post.entries_unchanged_except(&pre, page_index)
    &&& post.spec_index(page_index).view().inv()
    &&& post.spec_index(page_index).view().view().addr == pre.spec_index(page_index).view().view().addr
}

/// EOF closure of `page_array_remove_last_4k_iommu_mapping_to_cache`: the page array stays well formed when one page changes in place.
pub(super) proof fn page_array_remove_last_4k_iommu_mapping_to_cache_eof(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex)
    requires
        page_array_wf(pre),
        index_valid(NUM_PAGES, page_index),
        page_array_remove_last_4k_iommu_mapping_to_cache_eof_transition_framing(pre, post, page_index),
    ensures page_array_wf(post),
{ reveal(page_array_remove_last_4k_iommu_mapping_to_cache_eof_transition_framing); reveal(page_array_wf); }

/// S of `page_array_retire_kernel_object_4k_to_cache`: only page `page_index` changes, by retiring the 4K kernel object page to a cpu cache; it stays well formed at its address.
#[verifier::opaque]
pub(super) open spec fn page_array_retire_kernel_object_4k_to_cache_eof_transition_framing(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex) -> bool {
    &&& post.inv()
    &&& post.entries_unchanged_except(&pre, page_index)
    &&& post.spec_index(page_index).view().inv()
    &&& post.spec_index(page_index).view().view().addr == pre.spec_index(page_index).view().view().addr
}

/// EOF closure of `page_array_retire_kernel_object_4k_to_cache`: the page array stays well formed when one page changes in place.
pub(super) proof fn page_array_retire_kernel_object_4k_to_cache_eof(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex)
    requires
        page_array_wf(pre),
        index_valid(NUM_PAGES, page_index),
        page_array_retire_kernel_object_4k_to_cache_eof_transition_framing(pre, post, page_index),
    ensures page_array_wf(post),
{ reveal(page_array_retire_kernel_object_4k_to_cache_eof_transition_framing); reveal(page_array_wf); }

/// S of `page_array_retire_kernel_object_2m_to_global`: only page `page_index` changes, by retiring the 2M kernel object page to a global pool; it stays well formed at its address.
#[verifier::opaque]
pub(super) open spec fn page_array_retire_kernel_object_2m_to_global_eof_transition_framing(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex) -> bool {
    &&& post.inv()
    &&& post.entries_unchanged_except(&pre, page_index)
    &&& post.spec_index(page_index).view().inv()
    &&& post.spec_index(page_index).view().view().addr == pre.spec_index(page_index).view().view().addr
}

/// EOF closure of `page_array_retire_kernel_object_2m_to_global`: the page array stays well formed when one page changes in place.
pub(super) proof fn page_array_retire_kernel_object_2m_to_global_eof(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex)
    requires
        page_array_wf(pre),
        index_valid(NUM_PAGES, page_index),
        page_array_retire_kernel_object_2m_to_global_eof_transition_framing(pre, post, page_index),
    ensures page_array_wf(post),
{ reveal(page_array_retire_kernel_object_2m_to_global_eof_transition_framing); reveal(page_array_wf); }

/// S of `page_array_retire_kernel_object_4k_to_global`: only page `page_index` changes, by retiring the 4K kernel object page to a global pool; it stays well formed at its address.
#[verifier::opaque]
pub(super) open spec fn page_array_retire_kernel_object_4k_to_global_eof_transition_framing(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex) -> bool {
    &&& post.inv()
    &&& post.entries_unchanged_except(&pre, page_index)
    &&& post.spec_index(page_index).view().inv()
    &&& post.spec_index(page_index).view().view().addr == pre.spec_index(page_index).view().view().addr
}

/// EOF closure of `page_array_retire_kernel_object_4k_to_global`: the page array stays well formed when one page changes in place.
pub(super) proof fn page_array_retire_kernel_object_4k_to_global_eof(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex)
    requires
        page_array_wf(pre),
        index_valid(NUM_PAGES, page_index),
        page_array_retire_kernel_object_4k_to_global_eof_transition_framing(pre, post, page_index),
    ensures page_array_wf(post),
{ reveal(page_array_retire_kernel_object_4k_to_global_eof_transition_framing); reveal(page_array_wf); }

/// S of `page_array_move_free_4k_to_global_list`: only page `page_index` changes, by moving the free 4K page to a global list; it stays well formed at its address.
#[verifier::opaque]
pub(super) open spec fn page_array_move_free_4k_to_global_list_eof_transition_framing(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex) -> bool {
    &&& post.inv()
    &&& post.entries_unchanged_except(&pre, page_index)
    &&& post.spec_index(page_index).view().inv()
    &&& post.spec_index(page_index).view().view().addr == pre.spec_index(page_index).view().view().addr
}

/// EOF closure of `page_array_move_free_4k_to_global_list`: the page array stays well formed when one page changes in place.
pub(super) proof fn page_array_move_free_4k_to_global_list_eof(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex)
    requires
        page_array_wf(pre),
        index_valid(NUM_PAGES, page_index),
        page_array_move_free_4k_to_global_list_eof_transition_framing(pre, post, page_index),
    ensures page_array_wf(post),
{ reveal(page_array_move_free_4k_to_global_list_eof_transition_framing); reveal(page_array_wf); }

/// S of `page_array_move_free_4k_to_cpu_cache`: only page `page_index` changes, by moving the free 4K page to a cpu cache; it stays well formed at its address.
#[verifier::opaque]
pub(super) open spec fn page_array_move_free_4k_to_cpu_cache_eof_transition_framing(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex) -> bool {
    &&& post.inv()
    &&& post.entries_unchanged_except(&pre, page_index)
    &&& post.spec_index(page_index).view().inv()
    &&& post.spec_index(page_index).view().view().addr == pre.spec_index(page_index).view().view().addr
}

/// EOF closure of `page_array_move_free_4k_to_cpu_cache`: the page array stays well formed when one page changes in place.
pub(super) proof fn page_array_move_free_4k_to_cpu_cache_eof(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex)
    requires
        page_array_wf(pre),
        index_valid(NUM_PAGES, page_index),
        page_array_move_free_4k_to_cpu_cache_eof_transition_framing(pre, post, page_index),
    ensures page_array_wf(post),
{ reveal(page_array_move_free_4k_to_cpu_cache_eof_transition_framing); reveal(page_array_wf); }

/// S of `page_array_retype_owned_4k_for_container`: only page `page_index` changes, by retyping the owned 4K page to a kernel object of a child container; it stays well formed at its address.
#[verifier::opaque]
pub(super) open spec fn page_array_retype_owned_4k_for_container_eof_transition_framing(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex) -> bool {
    &&& post.inv()
    &&& post.entries_unchanged_except(&pre, page_index)
    &&& post.spec_index(page_index).view().inv()
    &&& post.spec_index(page_index).view().view().addr == pre.spec_index(page_index).view().view().addr
}

/// EOF closure of `page_array_retype_owned_4k_for_container`: the page array stays well formed when one page changes in place.
pub(super) proof fn page_array_retype_owned_4k_for_container_eof(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex)
    requires
        page_array_wf(pre),
        index_valid(NUM_PAGES, page_index),
        page_array_retype_owned_4k_for_container_eof_transition_framing(pre, post, page_index),
    ensures page_array_wf(post),
{ reveal(page_array_retype_owned_4k_for_container_eof_transition_framing); reveal(page_array_wf); }

/// S of `page_array_retype_owned_2m_for_container`: only page `page_index` changes, by retyping the owned 2M page to a kernel object of a child container; it stays well formed at its address.
#[verifier::opaque]
pub(super) open spec fn page_array_retype_owned_2m_for_container_eof_transition_framing(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex) -> bool {
    &&& post.inv()
    &&& post.entries_unchanged_except(&pre, page_index)
    &&& post.spec_index(page_index).view().inv()
    &&& post.spec_index(page_index).view().view().addr == pre.spec_index(page_index).view().view().addr
}

/// EOF closure of `page_array_retype_owned_2m_for_container`: the page array stays well formed when one page changes in place.
pub(super) proof fn page_array_retype_owned_2m_for_container_eof(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex)
    requires
        page_array_wf(pre),
        index_valid(NUM_PAGES, page_index),
        page_array_retype_owned_2m_for_container_eof_transition_framing(pre, post, page_index),
    ensures page_array_wf(post),
{ reveal(page_array_retype_owned_2m_for_container_eof_transition_framing); reveal(page_array_wf); }

/// S of `page_array_add_4k_mapping`: only page `page_index` changes, by recording one more mapping of the mapped 4K page; it stays well formed at its address, keeping its state and owning container.
#[verifier::opaque]
pub(super) open spec fn page_array_add_4k_mapping_eof_transition_framing(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex) -> bool {
    &&& post.inv()
    &&& post.entries_unchanged_except(&pre, page_index)
    &&& post.spec_index(page_index).view().inv()
    &&& post.spec_index(page_index).view().view().addr == pre.spec_index(page_index).view().view().addr
    &&& post.spec_index(page_index).view().view().state == pre.spec_index(page_index).view().view().state
    &&& post.spec_index(page_index).view().view().owning_container == pre.spec_index(page_index).view().view().owning_container
}

/// EOF closure of `page_array_add_4k_mapping`: the page array and the huge-page invariants after one page changes outside every page state.
pub(super) proof fn page_array_add_4k_mapping_eof(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex)
    requires
        page_array_wf(pre),
        hugepage_2m_wf(pre),
        hugepage_1g_wf(pre),
        index_valid(NUM_PAGES, page_index),
        page_array_add_4k_mapping_eof_transition_framing(pre, post, page_index),
    ensures
        page_array_wf(post),
        hugepage_2m_wf(post),
        hugepage_1g_wf(post),
{
    reveal(page_array_add_4k_mapping_eof_transition_framing); reveal(page_array_wf);
    hugepage_2m_wf_preserved_for_page_state_eq(pre, post); hugepage_1g_wf_preserved_for_page_state_eq(pre, post);
}

/// S of `page_array_add_4k_iommu_mapping`: only page `page_index` changes, by recording one more IOMMU mapping of the mapped 4K page; it stays well formed at its address, keeping its state and owning container.
#[verifier::opaque]
pub(super) open spec fn page_array_add_4k_iommu_mapping_eof_transition_framing(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex) -> bool {
    &&& post.inv()
    &&& post.entries_unchanged_except(&pre, page_index)
    &&& post.spec_index(page_index).view().inv()
    &&& post.spec_index(page_index).view().view().addr == pre.spec_index(page_index).view().view().addr
    &&& post.spec_index(page_index).view().view().state == pre.spec_index(page_index).view().view().state
    &&& post.spec_index(page_index).view().view().owning_container == pre.spec_index(page_index).view().view().owning_container
}

/// EOF closure of `page_array_add_4k_iommu_mapping`: the page array and the huge-page invariants after one page changes outside every page state.
pub(super) proof fn page_array_add_4k_iommu_mapping_eof(pre: PageLockedArray, post: PageLockedArray, page_index: PageIndex)
    requires
        page_array_wf(pre),
        hugepage_2m_wf(pre),
        hugepage_1g_wf(pre),
        index_valid(NUM_PAGES, page_index),
        page_array_add_4k_iommu_mapping_eof_transition_framing(pre, post, page_index),
    ensures
        page_array_wf(post),
        hugepage_2m_wf(post),
        hugepage_1g_wf(post),
{
    reveal(page_array_add_4k_iommu_mapping_eof_transition_framing); reveal(page_array_wf);
    hugepage_2m_wf_preserved_for_page_state_eq(pre, post); hugepage_1g_wf_preserved_for_page_state_eq(pre, post);
}

/// S of `iommu_table_map_clear_4k_present`: only the write-held IOMMU table `iommu_table_ptr` changes, by clearing the present bit of one 4K leaf; it stays well formed and keeps its lock.
#[verifier::opaque]
pub(super) open spec fn iommu_table_map_clear_4k_present_eof_transition_framing(pre: IommuTableLockedMap, post: IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot) -> bool {
    &&& post.perms_wf()
    &&& post.unchanged_except(&pre, iommu_table_ptr)
    &&& post.spec_index(iommu_table_ptr).inv()
    &&& post.spec_index(iommu_table_ptr).locking_thread() == pre.spec_index(iommu_table_ptr).locking_thread()
}

/// EOF closure of `iommu_table_map_clear_4k_present`: the changed table stays write-held, so the hidden-leaf lock rule holds.
pub(super) proof fn iommu_table_map_clear_4k_present_eof(pre: IommuTableLockedMap, post: IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot)
    requires
        iommu_table_perms_wf(pre),
        pre.spec_index(iommu_table_ptr).locking_thread() is Write,
        iommu_table_map_clear_4k_present_eof_transition_framing(pre, post, iommu_table_ptr),
    ensures iommu_table_perms_wf(post),
{ reveal(iommu_table_map_clear_4k_present_eof_transition_framing); reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); }

/// S of `iommu_table_map_unmap_4k_kernel`: only the write-held IOMMU table `iommu_table_ptr` changes, by unmapping one 4K leaf; it stays well formed and keeps its lock.
#[verifier::opaque]
pub(super) open spec fn iommu_table_map_unmap_4k_kernel_eof_transition_framing(pre: IommuTableLockedMap, post: IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot) -> bool {
    &&& post.perms_wf()
    &&& post.unchanged_except(&pre, iommu_table_ptr)
    &&& post.spec_index(iommu_table_ptr).inv()
    &&& post.spec_index(iommu_table_ptr).locking_thread() == pre.spec_index(iommu_table_ptr).locking_thread()
}

/// EOF closure of `iommu_table_map_unmap_4k_kernel`: the changed table stays write-held, so the hidden-leaf lock rule holds.
pub(super) proof fn iommu_table_map_unmap_4k_kernel_eof(pre: IommuTableLockedMap, post: IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot)
    requires
        iommu_table_perms_wf(pre),
        pre.spec_index(iommu_table_ptr).locking_thread() is Write,
        iommu_table_map_unmap_4k_kernel_eof_transition_framing(pre, post, iommu_table_ptr),
    ensures iommu_table_perms_wf(post),
{ reveal(iommu_table_map_unmap_4k_kernel_eof_transition_framing); reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); }

/// S of `iommu_table_map_insert_4k`: only the write-held IOMMU table `iommu_table_ptr` changes, by installing one 4K leaf; it stays well formed and keeps its lock.
#[verifier::opaque]
pub(super) open spec fn iommu_table_map_insert_4k_eof_transition_framing(pre: IommuTableLockedMap, post: IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot) -> bool {
    &&& post.perms_wf()
    &&& post.unchanged_except(&pre, iommu_table_ptr)
    &&& post.spec_index(iommu_table_ptr).inv()
    &&& post.spec_index(iommu_table_ptr).locking_thread() == pre.spec_index(iommu_table_ptr).locking_thread()
}

/// EOF closure of `iommu_table_map_insert_4k`: the changed table stays write-held, so the hidden-leaf lock rule holds.
pub(super) proof fn iommu_table_map_insert_4k_eof(pre: IommuTableLockedMap, post: IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot)
    requires
        iommu_table_perms_wf(pre),
        pre.spec_index(iommu_table_ptr).locking_thread() is Write,
        iommu_table_map_insert_4k_eof_transition_framing(pre, post, iommu_table_ptr),
    ensures iommu_table_perms_wf(post),
{ reveal(iommu_table_map_insert_4k_eof_transition_framing); reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); }

/// S of `iommu_table_map_create_entry_l4`: only the write-held IOMMU table `iommu_table_ptr` changes, by installing one L3 table; it stays well formed and keeps its lock.
#[verifier::opaque]
pub(super) open spec fn iommu_table_map_create_entry_l4_eof_transition_framing(pre: IommuTableLockedMap, post: IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot) -> bool {
    &&& post.perms_wf()
    &&& post.unchanged_except(&pre, iommu_table_ptr)
    &&& post.spec_index(iommu_table_ptr).inv()
    &&& post.spec_index(iommu_table_ptr).locking_thread() == pre.spec_index(iommu_table_ptr).locking_thread()
}

/// EOF closure of `iommu_table_map_create_entry_l4`: the changed table stays write-held, so the hidden-leaf lock rule holds.
pub(super) proof fn iommu_table_map_create_entry_l4_eof(pre: IommuTableLockedMap, post: IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot)
    requires
        iommu_table_perms_wf(pre),
        pre.spec_index(iommu_table_ptr).locking_thread() is Write,
        iommu_table_map_create_entry_l4_eof_transition_framing(pre, post, iommu_table_ptr),
    ensures iommu_table_perms_wf(post),
{ reveal(iommu_table_map_create_entry_l4_eof_transition_framing); reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); }

/// S of `iommu_table_map_create_entry_l3`: only the write-held IOMMU table `iommu_table_ptr` changes, by installing one L2 table; it stays well formed and keeps its lock.
#[verifier::opaque]
pub(super) open spec fn iommu_table_map_create_entry_l3_eof_transition_framing(pre: IommuTableLockedMap, post: IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot) -> bool {
    &&& post.perms_wf()
    &&& post.unchanged_except(&pre, iommu_table_ptr)
    &&& post.spec_index(iommu_table_ptr).inv()
    &&& post.spec_index(iommu_table_ptr).locking_thread() == pre.spec_index(iommu_table_ptr).locking_thread()
}

/// EOF closure of `iommu_table_map_create_entry_l3`: the changed table stays write-held, so the hidden-leaf lock rule holds.
pub(super) proof fn iommu_table_map_create_entry_l3_eof(pre: IommuTableLockedMap, post: IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot)
    requires
        iommu_table_perms_wf(pre),
        pre.spec_index(iommu_table_ptr).locking_thread() is Write,
        iommu_table_map_create_entry_l3_eof_transition_framing(pre, post, iommu_table_ptr),
    ensures iommu_table_perms_wf(post),
{ reveal(iommu_table_map_create_entry_l3_eof_transition_framing); reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); }

/// S of `iommu_table_map_create_entry_l2`: only the write-held IOMMU table `iommu_table_ptr` changes, by installing one L1 table; it stays well formed and keeps its lock.
#[verifier::opaque]
pub(super) open spec fn iommu_table_map_create_entry_l2_eof_transition_framing(pre: IommuTableLockedMap, post: IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot) -> bool {
    &&& post.perms_wf()
    &&& post.unchanged_except(&pre, iommu_table_ptr)
    &&& post.spec_index(iommu_table_ptr).inv()
    &&& post.spec_index(iommu_table_ptr).locking_thread() == pre.spec_index(iommu_table_ptr).locking_thread()
}

/// EOF closure of `iommu_table_map_create_entry_l2`: the changed table stays write-held, so the hidden-leaf lock rule holds.
pub(super) proof fn iommu_table_map_create_entry_l2_eof(pre: IommuTableLockedMap, post: IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot)
    requires
        iommu_table_perms_wf(pre),
        pre.spec_index(iommu_table_ptr).locking_thread() is Write,
        iommu_table_map_create_entry_l2_eof_transition_framing(pre, post, iommu_table_ptr),
    ensures iommu_table_perms_wf(post),
{ reveal(iommu_table_map_create_entry_l2_eof_transition_framing); reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); }

/// S of `iommu_table_map_remove_table_page`: only the write-held IOMMU table `iommu_table_ptr` changes, by removing one structure page; it stays well formed and keeps its lock.
#[verifier::opaque]
pub(super) open spec fn iommu_table_map_remove_table_page_eof_transition_framing(pre: IommuTableLockedMap, post: IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot) -> bool {
    &&& post.perms_wf()
    &&& post.unchanged_except(&pre, iommu_table_ptr)
    &&& post.spec_index(iommu_table_ptr).inv()
    &&& post.spec_index(iommu_table_ptr).locking_thread() == pre.spec_index(iommu_table_ptr).locking_thread()
}

/// EOF closure of `iommu_table_map_remove_table_page`: the changed table stays write-held, so the hidden-leaf lock rule holds.
pub(super) proof fn iommu_table_map_remove_table_page_eof(pre: IommuTableLockedMap, post: IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot)
    requires
        iommu_table_perms_wf(pre),
        pre.spec_index(iommu_table_ptr).locking_thread() is Write,
        iommu_table_map_remove_table_page_eof_transition_framing(pre, post, iommu_table_ptr),
    ensures iommu_table_perms_wf(post),
{ reveal(iommu_table_map_remove_table_page_eof_transition_framing); reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); }

/// S of `page_allocator_map_insert_new`: allocator `allocator_page` is added with value `allocator_value`; every other allocator stays.
#[verifier::opaque]
pub(super) open spec fn page_allocator_map_insert_new_eof_transition_framing<const SIZE: usize>(
    pre: PageAllocatorUnLockedMap<SIZE>, post: PageAllocatorUnLockedMap<SIZE>, allocator_page: PagePtr, allocator_value: PageAllocator<SIZE>,
) -> bool {
    &&& post.perms_wf()
    &&& post.dom() =~= pre.dom().insert(allocator_page)
    &&& post.spec_index(allocator_page) == allocator_value
    &&& forall|ptr: RwLockPageAllocatorPtr| #![trigger post.spec_index(ptr)] pre.dom().contains(ptr) ==> post.spec_index(ptr) == pre.spec_index(ptr)
}

/// EOF closure of `page_allocator_map_insert_new`: a well-formed allocator joins well-formed allocators.
pub(super) proof fn page_allocator_map_insert_new_eof<const SIZE: usize>(
    pre: PageAllocatorUnLockedMap<SIZE>, post: PageAllocatorUnLockedMap<SIZE>, allocator_page: PagePtr, allocator_value: PageAllocator<SIZE>,
)
    requires
        allocator_value.inv(),
        page_allocator_map_insert_new_eof_transition_framing(pre, post, allocator_page, allocator_value),
    ensures allocator_perms_wf(pre) ==> allocator_perms_wf(post),
{ reveal(page_allocator_map_insert_new_eof_transition_framing); reveal(allocator_perms_wf); }
}
