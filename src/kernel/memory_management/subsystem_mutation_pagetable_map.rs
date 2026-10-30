use vstd::prelude::*;
use crate::*;
use super::subsystem_mutation_eof::*;
use vstd::simple_pptr::PointsTo;

verus! {
/// Install the present 4K leaf `target_entry` in the 2M window of `indices` of page table `pagetable_ptr`: this thread holds
/// the table's big read lock and that window lock; only the window half `pt_lower[pagetable_ptr]` changes.
pub fn pagetable_map_insert_4k(
    pagetable_map: &PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index, L1Index), target_l2_ptr: PageMapPtr, target_l1_ptr: PageMapPtr, target_entry: &MapEntry,
    Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*pagetable_map),
        pagetable_lower_wf(*pagetable_map, *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *old(pt_lower)),
        pagetable_map.dom().contains(pagetable_ptr),
        pagetable_map.typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_map.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        page_table_key_4k_valid::<PT_TYPE>(spec_index2va(indices)),
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2) == (SpinLockState::Some { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_4k_l1(indices.0, indices.1, indices.2, indices.3) is None
            || !pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().dom().contains(spec_index2va(indices)),
        page_ptr_valid(target_entry.addr),
        target_entry.present,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*pagetable_map, *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *final(pt_lower)),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).page_closure() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).page_closure(),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_4k() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().insert(spec_index2va(indices), *target_entry),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_2m() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_2m(),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
            pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        forall|p: PageMapPtr, i: L2Index| #![trigger pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.map_4k_page(Tracked(lower), indices.0, indices.1, indices.2, indices.3, target_l2_ptr, target_l1_ptr, target_entry, Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        let post_c = PageTableC { higher: *pagetable, lower: *lower };
        assert(pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        let va = spec_index2va(indices);
        assert(pagetable_map.spec_index(pagetable_ptr).locking_thread() is Read) by { pagetable_map.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); };
        assert(pagetable_map_insert_4k_eof_transition_framing(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, va, *target_entry)) by {
            reveal(pagetable_map_insert_4k_eof_transition_framing);
        };
        pagetable_map_insert_4k_eof(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, va, *target_entry, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id());
    }
}

/// Install the present 4K leaf `target_entry` in the 2M window of `indices` of page table `pagetable_ptr`: this thread holds
/// the table's big write lock and that window lock; only the window half `pt_lower[pagetable_ptr]` changes, and the lock's
/// ghost slot keeps a copy of it.
pub fn pagetable_map_insert_4k_wlocked(
    pagetable_map: &mut PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index, L1Index), target_l2_ptr: PageMapPtr, target_l1_ptr: PageMapPtr, target_entry: &MapEntry,
    Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        pagetable_lower_wf(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*old(pagetable_map), *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*old(pagetable_map), *old(pt_lower)),
        old(pagetable_map).dom().contains(pagetable_ptr),
        old(pagetable_map).typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        page_table_key_4k_valid::<PT_TYPE>(spec_index2va(indices)),
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2)
            == (SpinLockState::Some { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_4k_l1(indices.0, indices.1, indices.2, indices.3) is None
            || !pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().dom().contains(spec_index2va(indices)),
        page_ptr_valid(target_entry.addr),
        target_entry.present,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        pagetable_perms_wf(*final(pagetable_map)),
        final(pagetable_map).unchanged_except(old(pagetable_map), pagetable_ptr),
        final(pagetable_map).typed_lock_map_aligned(final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        final(pagetable_map).lock_id_by_key(pagetable_ptr) == old(pagetable_map).lock_id_by_key(pagetable_ptr),
        final(pagetable_map).spec_index(pagetable_ptr).locking_thread() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread(),
        final(pagetable_map).spec_index(pagetable_ptr).being_killed() == old(pagetable_map).spec_index(pagetable_ptr).being_killed(),
        final(pagetable_map).spec_index(pagetable_ptr).view() == old(pagetable_map).spec_index(pagetable_ptr).view(),
        final(pagetable_map).spec_index(pagetable_ptr).view_ghost() == final(pt_lower).spec_index(pagetable_ptr),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*final(pagetable_map), *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().insert(spec_index2va(indices), *target_entry),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
            old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        forall|p: PageMapPtr, i: L2Index| #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.map_4k_page(Tracked(lower), indices.0, indices.1, indices.2, indices.3, target_l2_ptr, target_l1_ptr, target_entry, Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        let post_c = PageTableC { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        let va = spec_index2va(indices);
        assert(pagetable_map_insert_4k_wlocked_eof_transition_framing(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, va, *target_entry)) by {
            reveal(pagetable_map_insert_4k_wlocked_eof_transition_framing);
        };
        pagetable_map_insert_4k_wlocked_eof(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, va, *target_entry, lctx.pagetable_window_lock_map(),
            lctx.pagetable_lock_map(), lctx.thread_id());
    }
}

/// Link the empty L1 page `page_map_ptr` into the 2M window of `indices` of page table `pagetable_ptr` at L2 page `target_l2_ptr`:
/// this thread holds the table's big read lock and that window lock; only the window half `pt_lower[pagetable_ptr]` changes.
pub fn pagetable_map_create_entry_l2(
    pagetable_map: &PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index, L1Index), target_l2_ptr: PageMapPtr, page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
    Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*pagetable_map),
        pagetable_lower_wf(*pagetable_map, *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *old(pt_lower)),
        pagetable_map.dom().contains(pagetable_ptr),
        pagetable_map.typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_map.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2) == (SpinLockState::Some { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None,
        page_ptr_valid(page_map_ptr),
        !pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).page_closure().contains(page_map_ptr),
        page_map_perm.addr() == page_map_ptr,
        page_map_perm.is_init(),
        page_map_perm.value().wf(),
        forall|i: usize|
            #![trigger page_map_perm.value().spec_index(i).is_empty()]
            #![trigger page_map_perm.value().spec_index(i).perm.present]
            #![trigger page_map_perm.value().spec_index(i).perm.ps]
            #![trigger page_map_perm.value().spec_index(i).perm.kernel_present]
            pei_valid(i) ==> page_map_perm.value().spec_index(i).is_empty(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*pagetable_map, *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *final(pt_lower)),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).page_closure() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).page_closure().insert(page_map_ptr),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_4k() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k(),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_2m() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_2m(),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == page_map_ptr,
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
            pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                ==> pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        forall|p: PageMapPtr, i: L2Index| #![trigger pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.create_entry_l2(Tracked(lower), indices.0, indices.1, indices.2, target_l2_ptr, page_map_ptr, Tracked(page_map_perm), Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        let post_c = PageTableC { higher: *pagetable, lower: *lower };
        assert(pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(pagetable_map.spec_index(pagetable_ptr).locking_thread() is Read) by { pagetable_map.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); };
        assert(pagetable_map_create_entry_l2_eof_transition_framing(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr)) by {
            reveal(pagetable_map_create_entry_l2_eof_transition_framing);
        };
        pagetable_map_create_entry_l2_eof(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id());
    }
}

/// Link the empty L1 page `page_map_ptr` into the 2M window of `indices` of page table `pagetable_ptr` at L2 page `target_l2_ptr`:
/// this thread holds the table's big write lock and that window lock; only the window half `pt_lower[pagetable_ptr]` changes, and
/// the lock's ghost slot keeps a copy of it.
pub fn pagetable_map_create_entry_l2_wlocked(
    pagetable_map: &mut PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index, L1Index), target_l2_ptr: PageMapPtr, page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
    Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        pagetable_lower_wf(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*old(pagetable_map), *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*old(pagetable_map), *old(pt_lower)),
        old(pagetable_map).dom().contains(pagetable_ptr),
        old(pagetable_map).typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2)
            == (SpinLockState::Some { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None,
        page_ptr_valid(page_map_ptr),
        !pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure().contains(page_map_ptr),
        page_map_perm.addr() == page_map_ptr,
        page_map_perm.is_init(),
        page_map_perm.value().wf(),
        forall|i: usize|
            #![trigger page_map_perm.value().spec_index(i).is_empty()]
            #![trigger page_map_perm.value().spec_index(i).perm.present]
            #![trigger page_map_perm.value().spec_index(i).perm.ps]
            #![trigger page_map_perm.value().spec_index(i).perm.kernel_present]
            pei_valid(i) ==> page_map_perm.value().spec_index(i).is_empty(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        pagetable_perms_wf(*final(pagetable_map)),
        final(pagetable_map).unchanged_except(old(pagetable_map), pagetable_ptr),
        final(pagetable_map).typed_lock_map_aligned(final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        final(pagetable_map).lock_id_by_key(pagetable_ptr) == old(pagetable_map).lock_id_by_key(pagetable_ptr),
        final(pagetable_map).spec_index(pagetable_ptr).locking_thread() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread(),
        final(pagetable_map).spec_index(pagetable_ptr).being_killed() == old(pagetable_map).spec_index(pagetable_ptr).being_killed(),
        final(pagetable_map).spec_index(pagetable_ptr).view() == old(pagetable_map).spec_index(pagetable_ptr).view(),
        final(pagetable_map).spec_index(pagetable_ptr).view_ghost() == final(pt_lower).spec_index(pagetable_ptr),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*final(pagetable_map), *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure().insert(page_map_ptr),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == page_map_ptr,
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
            pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        forall|p: PageMapPtr, i: L2Index| #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.create_entry_l2(Tracked(lower), indices.0, indices.1, indices.2, target_l2_ptr, page_map_ptr, Tracked(page_map_perm), Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        let post_c = PageTableC { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(pagetable_map_create_entry_l2_wlocked_eof_transition_framing(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr)) by {
            reveal(pagetable_map_create_entry_l2_wlocked_eof_transition_framing);
        };
        pagetable_map_create_entry_l2_wlocked_eof(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(),
            lctx.thread_id());
    }
}

/// Link the empty L3 page `page_map_ptr` into root entry `indices.0` of page table `pagetable_ptr`: this thread holds the table's
/// big write lock; only the big-lock payload changes, so the window half and its ghost-slot copy stay.
pub fn pagetable_map_create_entry_l4(
    pagetable_map: &mut PageTableLockedMap, Tracked(pt_lower): Tracked<&PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index, L1Index), page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        pagetable_lower_wf(*old(pagetable_map), *pt_lower),
        pagetable_window_holders_hold_pagetable(*old(pagetable_map), *pt_lower),
        pagetable_hidden_leaves_only_when_locked(*old(pagetable_map), *pt_lower),
        pagetable_window_stale_cpus_only_when_locked(*old(pagetable_map), *pt_lower),
        pagetable_window_typed_lock_map_aligned(*old(pagetable_map), *pt_lower, old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*old(pagetable_map), *pt_lower),
        old(pagetable_map).dom().contains(pagetable_ptr),
        old(pagetable_map).typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        pagetable_c(*old(pagetable_map), *pt_lower, pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pagetable_c(*old(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l4(indices.0) is None,
        page_ptr_valid(page_map_ptr),
        !pagetable_c(*old(pagetable_map), *pt_lower, pagetable_ptr).page_closure().contains(page_map_ptr),
        page_map_perm.addr() == page_map_ptr,
        page_map_perm.is_init(),
        page_map_perm.value().wf(),
        forall|i: usize| #![trigger page_map_perm.value().spec_index(i)] pei_valid(i) ==> page_map_perm.value().spec_index(i).is_empty(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        pagetable_perms_wf(*final(pagetable_map)),
        final(pagetable_map).unchanged_except(old(pagetable_map), pagetable_ptr),
        final(pagetable_map).typed_lock_map_aligned(final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        final(pagetable_map).lock_id_by_key(pagetable_ptr) == old(pagetable_map).lock_id_by_key(pagetable_ptr),
        final(pagetable_map).spec_index(pagetable_ptr).locking_thread() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread(),
        final(pagetable_map).spec_index(pagetable_ptr).being_killed() == old(pagetable_map).spec_index(pagetable_ptr).being_killed(),
        final(pagetable_map).spec_index(pagetable_ptr).view_ghost() == old(pagetable_map).spec_index(pagetable_ptr).view_ghost(),
        pagetable_lower_wf(*final(pagetable_map), *pt_lower),
        pagetable_window_holders_hold_pagetable(*final(pagetable_map), *pt_lower),
        pagetable_hidden_leaves_only_when_locked(*final(pagetable_map), *pt_lower),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *pt_lower),
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *pt_lower, final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *pt_lower),
        pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).page_closure() == pagetable_c(*old(pagetable_map), *pt_lower, pagetable_ptr).page_closure().insert(page_map_ptr),
        pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).mapping_4k() == pagetable_c(*old(pagetable_map), *pt_lower, pagetable_ptr).mapping_4k(),
        pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).mapping_2m() == pagetable_c(*old(pagetable_map), *pt_lower, pagetable_ptr).mapping_2m(),
        pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).mapping_1g() == pagetable_c(*old(pagetable_map), *pt_lower, pagetable_ptr).mapping_1g(),
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end,
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries,
        final(pagetable_map).spec_index(pagetable_ptr).view().cr3 == old(pagetable_map).spec_index(pagetable_ptr).view().cr3,
        final(pagetable_map).spec_index(pagetable_ptr).view().pcid == old(pagetable_map).spec_index(pagetable_ptr).view().pcid,
        final(pagetable_map).spec_index(pagetable_ptr).view().did == old(pagetable_map).spec_index(pagetable_ptr).view().did,
        final(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr == old(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr,
        pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l4(indices.0) is Some,
        pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l4(indices.0)->0.addr == page_map_ptr,
        pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is None,
        pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_1g_l3(indices.0, indices.1) is None,
        forall|l4i: L4Index, l3i: L3Index| #![trigger pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i)]
            old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i)
                ==> pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i) == pagetable_c(*old(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
            pagetable_c(*old(pagetable_map), *pt_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pagetable_c(*old(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                ==> pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> pagetable_c(*final(pagetable_map), *pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(*old(pagetable_map), *pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_mut_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow(pagetable_ptr);
    pagetable.create_entry_l4(Tracked(lower), indices.0, indices.1, page_map_ptr, Tracked(page_map_perm), Tracked(&mut *lctx));
    proof {
        let post_c = PageTableC { higher: *pagetable, lower: *lower };
        assert(pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        assert(pagetable_map_create_entry_l4_eof_transition_framing(*old(pagetable_map), *pagetable_map, *pt_lower, pagetable_ptr)) by {
            reveal(pagetable_map_create_entry_l4_eof_transition_framing);
        };
        pagetable_map_create_entry_l4_eof(*old(pagetable_map), *pagetable_map, *pt_lower, pagetable_ptr, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id());
    }
}

/// Link the empty L2 page `page_map_ptr` into L3 entry `indices.1` of `target_l3_ptr` in page table `pagetable_ptr`: this thread
/// holds the table's big write lock; windows `lo..=hi` of the new page start held by this thread and their lock perms are returned,
/// the other new windows start unlocked, and the lock's ghost slot keeps a copy of the new window half.
pub fn pagetable_map_create_entry_l3(
    pagetable_map: &mut PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index, L1Index), target_l3_ptr: PageMapPtr, page_map_ptr: PageMapPtr, Tracked(page_perm): Tracked<PagePerm4k>, lo: L2Index, hi: L2Index,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
) -> (ret: Tracked<Map<L2Index, LockPerm>>)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        pagetable_lower_wf(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*old(pagetable_map), *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*old(pagetable_map), *old(pt_lower)),
        old(pagetable_map).dom().contains(pagetable_ptr),
        old(pagetable_map).typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        KERNEL_MEM_END_L4INDEX <= indices.0,
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(lo) && pei_valid(hi) && lo <= hi,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(indices.0) is Some,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(indices.0)->0.addr == target_l3_ptr,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is None,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_1g_l3(indices.0, indices.1) is None,
        page_ptr_valid(page_map_ptr),
        !pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure().contains(page_map_ptr),
        page_perm.addr() == page_map_ptr,
        page_perm.is_init(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        nonwindow_typed_lock_maps_unchanged(old(lctx), final(lctx)),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (old(lctx).pagetable_window_lock_map().dom().contains((p, w))
                || (p == pagetable_ptr && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi)),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w))
                && !(p == pagetable_ptr && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi)
                ==> final(lctx).pagetable_window_lock_map().index((p, w)) == old(lctx).pagetable_window_lock_map().index((p, w)),
        forall|w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((pagetable_ptr, w))]
            w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi
                ==> final(lctx).pagetable_window_lock_map().index((pagetable_ptr, w)) == (TypedHeldLock { lock_id: window_lock_id_of(pagetable_ptr, w), mode: TypedLockMode::Write }),
        pagetable_perms_wf(*final(pagetable_map)),
        final(pagetable_map).unchanged_except(old(pagetable_map), pagetable_ptr),
        final(pagetable_map).typed_lock_map_aligned(final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        final(pagetable_map).lock_id_by_key(pagetable_ptr) == old(pagetable_map).lock_id_by_key(pagetable_ptr),
        final(pagetable_map).spec_index(pagetable_ptr).locking_thread() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread(),
        final(pagetable_map).spec_index(pagetable_ptr).being_killed() == old(pagetable_map).spec_index(pagetable_ptr).being_killed(),
        final(pagetable_map).spec_index(pagetable_ptr).view_ghost() == final(pt_lower).spec_index(pagetable_ptr),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*final(pagetable_map), *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure().insert(page_map_ptr),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_1g() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_1g(),
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end,
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries,
        final(pagetable_map).spec_index(pagetable_ptr).view().cr3 == old(pagetable_map).spec_index(pagetable_ptr).view().cr3,
        final(pagetable_map).spec_index(pagetable_ptr).view().pcid == old(pagetable_map).spec_index(pagetable_ptr).view().pcid,
        final(pagetable_map).spec_index(pagetable_ptr).view().did == old(pagetable_map).spec_index(pagetable_ptr).view().did,
        final(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr == old(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr,
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(indices.0) == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(indices.0),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == page_map_ptr,
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_1g_l3(indices.0, indices.1) is None,
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None,
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
            pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
        forall|i: L2Index| #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(page_map_ptr, i)] pei_valid(i) && !(lo <= i <= hi) ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(page_map_ptr, i) is None,
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == Map::new(
            pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks.dom() + Set::<usize>::range(0, 512).map_by(|i: usize| WindowVa { va: spec_index2va((indices.0, indices.1, i, 0usize)) }, |w: WindowVa| spec_v2l2index(w.va)),
            |w: WindowVa| if pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks.dom().contains(w) { pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks[w] }
                else if lo <= spec_v2l2index(w.va) <= hi { LockStateU::WriteLocked } else { LockStateU::Unlocked }),
        forall|i: L2Index| #![trigger ret.view().dom().contains(i)] ret.view().dom().contains(i) == (lo <= i <= hi),
        forall|i: L2Index| #![trigger ret.view().index(i)] lo <= i <= hi ==> {
            &&& pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(page_map_ptr, i) == (SpinLockState::Some { thread_id: ret.view().index(i).thread_id(), lock_id: ret.view().index(i).lock_id() })
            &&& ret.view().index(i).state() is WriteLock
            &&& ret.view().index(i).ordering_lock_id() == window_lock_id(pagetable_ptr, indices.0, indices.1, i)
            &&& ret.view().index(i).thread_id() == final(lctx).thread_id()
        },
        forall|l4i: L4Index, l3i: L3Index| #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i)]
            old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && !(l4i == indices.0 && l3i == indices.1)
                ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i) == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)
                    == (pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)
                        || (l4i == indices.0 && l3i == indices.1 && lo <= l2i <= hi && thread_id == final(lctx).thread_id())),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_l2_page(l4i, l3i), l2i)]
            old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_exists(l4i, l3i)
                ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_l2_page(l4i, l3i), l2i)
                    == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_l2_page(l4i, l3i), l2i),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_mut_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    let ret = pagetable.create_entry_l3(Tracked(lower), indices.0, indices.1, indices.2, target_l3_ptr, page_map_ptr, Tracked(page_perm), lo, hi, Ghost(pagetable_ptr),
        Tracked(&mut *lctx));
    proof {
        let post_c = PageTableC { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(pagetable_map_create_entry_l3_eof_transition_framing(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, indices.0, indices.1, lo, hi,
            lctx.thread_id())) by {
            reveal(pagetable_map_create_entry_l3_eof_transition_framing);
        };
        pagetable_map_create_entry_l3_eof(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, old(lctx).pagetable_window_lock_map(),
            lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id(), indices.0, indices.1, lo, hi);
    }
    ret
}

/// Clear the user present bit of the 4K leaf at `indices` of page table `pagetable_ptr`: this thread holds the table's big
/// write lock, which a table with hidden leaves needs, and the 2M window lock of `indices`; the lock's ghost slot keeps a
/// copy of the new window half.
pub fn pagetable_map_clear_4k_present(
    pagetable_map: &mut PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index, L1Index), target_l2_ptr: PageMapPtr, target_l1_ptr: PageMapPtr, Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        pagetable_lower_wf(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*old(pagetable_map), *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*old(pagetable_map), *old(pt_lower)),
        old(pagetable_map).dom().contains(pagetable_ptr),
        old(pagetable_map).typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2)
            == (SpinLockState::Some { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().dom().contains(spec_index2va(indices)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        pagetable_perms_wf(*final(pagetable_map)),
        final(pagetable_map).unchanged_except(old(pagetable_map), pagetable_ptr),
        final(pagetable_map).typed_lock_map_aligned(final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        final(pagetable_map).lock_id_by_key(pagetable_ptr) == old(pagetable_map).lock_id_by_key(pagetable_ptr),
        final(pagetable_map).spec_index(pagetable_ptr).locking_thread() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread(),
        final(pagetable_map).spec_index(pagetable_ptr).being_killed() == old(pagetable_map).spec_index(pagetable_ptr).being_killed(),
        final(pagetable_map).spec_index(pagetable_ptr).view() == old(pagetable_map).spec_index(pagetable_ptr).view(),
        final(pagetable_map).spec_index(pagetable_ptr).view_ghost() == final(pt_lower).spec_index(pagetable_ptr),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*final(pagetable_map), *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().insert(spec_index2va(indices),
            MapEntry { present: false, ..pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().spec_index(spec_index2va(indices)) }),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        forall|p: PageMapPtr, i: L2Index| #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.unmap_4k_page_user_view(Tracked(lower), indices.0, indices.1, indices.2, indices.3, target_l2_ptr, target_l1_ptr, Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        let post_c = PageTableC { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        let va = spec_index2va(indices);
        assert(pagetable_map_clear_4k_present_eof_transition_framing(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, va)) by {
            reveal(pagetable_map_clear_4k_present_eof_transition_framing);
        };
        pagetable_map_clear_4k_present_eof(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, va, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id());
    }
}

/// Remove the hidden 4K leaf at `indices` of page table `pagetable_ptr` after its stale TLB entries are flushed: this thread
/// holds the table's big write lock and the 2M window lock of `indices`; the lock's ghost slot keeps a copy of the new
/// window half.
pub fn pagetable_map_unmap_4k_kernel(
    pagetable_map: &mut PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index, L1Index), target_l2_ptr: PageMapPtr, target_l1_ptr: PageMapPtr, Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        pagetable_lower_wf(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*old(pagetable_map), *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*old(pagetable_map), *old(pt_lower)),
        old(pagetable_map).dom().contains(pagetable_ptr),
        old(pagetable_map).typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2)
            == (SpinLockState::Some { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().dom().contains(spec_index2va(indices)),
        !pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().spec_index(spec_index2va(indices)).present,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        pagetable_perms_wf(*final(pagetable_map)),
        final(pagetable_map).unchanged_except(old(pagetable_map), pagetable_ptr),
        final(pagetable_map).typed_lock_map_aligned(final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        final(pagetable_map).lock_id_by_key(pagetable_ptr) == old(pagetable_map).lock_id_by_key(pagetable_ptr),
        final(pagetable_map).spec_index(pagetable_ptr).locking_thread() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread(),
        final(pagetable_map).spec_index(pagetable_ptr).being_killed() == old(pagetable_map).spec_index(pagetable_ptr).being_killed(),
        final(pagetable_map).spec_index(pagetable_ptr).view() == old(pagetable_map).spec_index(pagetable_ptr).view(),
        final(pagetable_map).spec_index(pagetable_ptr).view_ghost() == final(pt_lower).spec_index(pagetable_ptr),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*final(pagetable_map), *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().remove(spec_index2va(indices)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        forall|p: PageMapPtr, i: L2Index| #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.unmap_4k_page_kernel(Tracked(lower), indices.0, indices.1, indices.2, indices.3, target_l2_ptr, target_l1_ptr, Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        let post_c = PageTableC { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        let va = spec_index2va(indices);
        assert(pagetable_map_unmap_4k_kernel_eof_transition_framing(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, va)) by {
            reveal(pagetable_map_unmap_4k_kernel_eof_transition_framing);
        };
        pagetable_map_unmap_4k_kernel_eof(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, va, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id());
    }
}

/// Clear the user present bit of the 4K leaf at `indices` of page table `pagetable_ptr`: this thread holds the table's big
/// read lock and the 2M window lock of `indices`; only the window half `pt_lower[pagetable_ptr]` changes.
pub fn pagetable_map_clear_4k_present_rlocked(
    pagetable_map: &PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index, L1Index), target_l2_ptr: PageMapPtr, target_l1_ptr: PageMapPtr, Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*pagetable_map),
        pagetable_lower_wf(*pagetable_map, *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *old(pt_lower)),
        pagetable_map.dom().contains(pagetable_ptr),
        pagetable_map.typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_map.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2) == (SpinLockState::Some { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().dom().contains(spec_index2va(indices)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*pagetable_map, *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *final(pt_lower)),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).page_closure() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).page_closure(),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_4k() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().insert(spec_index2va(indices),
            MapEntry { present: false, ..pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().spec_index(spec_index2va(indices)) }),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_2m() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_2m(),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        forall|p: PageMapPtr, i: L2Index| #![trigger pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.unmap_4k_page_user_view(Tracked(lower), indices.0, indices.1, indices.2, indices.3, target_l2_ptr, target_l1_ptr, Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        let post_c = PageTableC { higher: *pagetable, lower: *lower };
        assert(pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(pagetable_map.spec_index(pagetable_ptr).locking_thread() is Read) by { pagetable_map.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); };
        assert(pagetable_map_clear_4k_present_rlocked_eof_transition_framing(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, spec_index2va(indices))) by {
            reveal(pagetable_map_clear_4k_present_rlocked_eof_transition_framing);
        };
        pagetable_map_clear_4k_present_rlocked_eof(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, indices, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id());
    }
}

/// Remove the hidden 4K leaf at `indices` of page table `pagetable_ptr` after its stale TLB entries are flushed: this thread
/// holds the table's big read lock and the 2M window lock of `indices`; only the window half `pt_lower[pagetable_ptr]` changes.
pub fn pagetable_map_unmap_4k_kernel_rlocked(
    pagetable_map: &PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index, L1Index), target_l2_ptr: PageMapPtr, target_l1_ptr: PageMapPtr, Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*pagetable_map),
        pagetable_lower_wf(*pagetable_map, *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *old(pt_lower)),
        pagetable_map.dom().contains(pagetable_ptr),
        pagetable_map.typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_map.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2) == (SpinLockState::Some { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().dom().contains(spec_index2va(indices)),
        !pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().spec_index(spec_index2va(indices)).present,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*pagetable_map, *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *final(pt_lower)),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).page_closure() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).page_closure(),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_4k() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().remove(spec_index2va(indices)),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_2m() == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_2m(),
        pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        forall|p: PageMapPtr, i: L2Index| #![trigger pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            pagetable_c(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == pagetable_c(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.unmap_4k_page_kernel(Tracked(lower), indices.0, indices.1, indices.2, indices.3, target_l2_ptr, target_l1_ptr, Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        let post_c = PageTableC { higher: *pagetable, lower: *lower };
        assert(pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(pagetable_map.spec_index(pagetable_ptr).locking_thread() is Read) by { pagetable_map.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); };
        assert(pagetable_map_unmap_4k_kernel_rlocked_eof_transition_framing(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, spec_index2va(indices))) by {
            reveal(pagetable_map_unmap_4k_kernel_rlocked_eof_transition_framing);
        };
        pagetable_map_unmap_4k_kernel_rlocked_eof(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, spec_index2va(indices), lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(),
            lctx.thread_id());
    }
}

/// Unlink the table page that `scan` names from the write-held page table `pagetable_ptr` and return its memory; every mapping stays.
/// Lock preconditions per branch mirror `remove_structure_page`: an L1 page needs its 2M window lock, an L2 page needs all
/// 512 of its windows unlocked.
pub fn pagetable_map_remove_table_page(
    pagetable_map: &mut PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot, scan: StructureScan,
    Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
) -> (ret: Tracked<PagePerm4k>)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        pagetable_lower_wf(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*old(pagetable_map), *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*old(pagetable_map), *old(pt_lower)),
        old(pagetable_map).dom().contains(pagetable_ptr),
        old(pagetable_map).typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_structure_scan_wf(scan),
        scan.spec_table_page() is Some,
        scan is L1 ==> pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(scan->L1_l4i, scan->L1_l3i, scan->L1_l2i, old(lctx).thread_id()),
        scan is L1 ==> pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_l2_page(scan->L1_l4i, scan->L1_l3i), scan->L1_l2i)
            == (SpinLockState::Some { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        scan is L2 ==> old(lctx).pagetable_window_lock_map().dom().is_empty(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        pagetable_perms_wf(*final(pagetable_map)),
        final(pagetable_map).unchanged_except(old(pagetable_map), pagetable_ptr),
        final(pagetable_map).typed_lock_map_aligned(final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        final(pagetable_map).lock_id_by_key(pagetable_ptr) == old(pagetable_map).lock_id_by_key(pagetable_ptr),
        final(pagetable_map).spec_index(pagetable_ptr).locking_thread() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread(),
        final(pagetable_map).spec_index(pagetable_ptr).being_killed() == old(pagetable_map).spec_index(pagetable_ptr).being_killed(),
        final(pagetable_map).spec_index(pagetable_ptr).view_ghost() == final(pt_lower).spec_index(pagetable_ptr),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*final(pagetable_map), *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        scan is L2 ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus.filter_keys(|k: (PageMapPtr, L2Index)| k.0 != scan->L2_l2_p),
        !(scan is L2) ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure().remove(scan.spec_table_page()->Some_0),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m(),
        pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_1g() == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_1g(),
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end,
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries,
        final(pagetable_map).spec_index(pagetable_ptr).view().cr3 == old(pagetable_map).spec_index(pagetable_ptr).view().cr3,
        final(pagetable_map).spec_index(pagetable_ptr).view().pcid == old(pagetable_map).spec_index(pagetable_ptr).view().pcid,
        final(pagetable_map).spec_index(pagetable_ptr).view().did == old(pagetable_map).spec_index(pagetable_ptr).view().did,
        final(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr == old(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr,
        !(scan is L2) ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        scan is L2 ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks.remove_keys(
            pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == scan->L2_l4i && spec_v2l3index(w.va) == scan->L2_l3i)),
        scan is L1 ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).higher == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).higher,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        ret.view().is_init(),
        ret.view().addr() == scan.spec_table_page()->Some_0,
        scan is L1 ==> forall|p: PageMapPtr, i: L2Index| #![trigger pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            pagetable_c(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == pagetable_c(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    proof {
        if scan is L2 {
            assert(pagetable_map.spec_index(pagetable_ptr).wlocked_by_thread(lctx.thread_id())) by {
                pagetable_map.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
            };
            wlocker_holds_no_windows_implies_l2_windows_unlocked(*pagetable_map, *pt_lower, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr,
                scan->L2_l4i, scan->L2_l3i, scan->L2_l2_p);
        }
    }
    let pagetable = pagetable_map.borrow_mut_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    let ret = pagetable.remove_structure_page(Tracked(lower), scan, Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        let post_c = PageTableC { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(pagetable_c(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(pagetable_map_remove_table_page_eof_transition_framing(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr)) by {
            reveal(pagetable_map_remove_table_page_eof_transition_framing);
        };
        pagetable_map_remove_table_page_eof(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(),
            lctx.thread_id());
    }
    ret
}
}
