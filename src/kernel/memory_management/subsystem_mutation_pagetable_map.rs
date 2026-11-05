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
        pagetable_hidden_l1_only_when_locked(*pagetable_map, *old(pt_lower)),
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
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        page_table_key_4k_valid::<PT_TYPE>(spec_index2va(indices)),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2)
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_4k_l1(indices.0, indices.1, indices.2, indices.3) is None
            || !whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().dom().contains(spec_index2va(indices)),
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
        pagetable_hidden_l1_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *final(pt_lower)),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *final(pt_lower)),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).page_closure() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).page_closure(),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_4k() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().insert(spec_index2va(indices), *target_entry),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_2m() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_2m(),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
            pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1()]
            pei_valid(i) && !whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(p, i) ==> !whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(p, i),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_perms.dom() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_perms.dom(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i)]
            whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_entry(p, i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i, l1i) != (indices.0, indices.1, indices.2, indices.3)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(indices.0, indices.1, indices.2, indices.3) is Some,
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(indices.0, indices.1, indices.2, indices.3)->0.addr == target_entry.addr,
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.map_4k_page(Tracked(lower), indices.0, indices.1, indices.2, indices.3, target_l2_ptr, target_l1_ptr, target_entry, Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        let post_c = WholePageTable { higher: *pagetable, lower: *lower };
        assert(whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        let va = spec_index2va(indices);
        assert(pagetable_map.spec_index(pagetable_ptr).locking_thread() is Read) by { pagetable_map.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); };
        assert(pagetable_map_insert_4k_eof_transition_framing(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, va, *target_entry)) by {
            reveal(pagetable_map_insert_4k_eof_transition_framing);
        };
        pagetable_map_insert_4k_eof(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, va, *target_entry, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id());
    }
}

/// Install the present 2M leaf `target_entry` in the 2M window of `indices` of page table `pagetable_ptr`: this thread holds
/// the table's big read lock and that window lock; only the window half `pt_lower[pagetable_ptr]` changes.
pub fn pagetable_map_insert_2m(
    pagetable_map: &PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index), target_l2_ptr: PageMapPtr, target_entry: &MapEntry,
    Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*pagetable_map),
        pagetable_lower_wf(*pagetable_map, *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *old(pt_lower)),
        pagetable_hidden_l1_only_when_locked(*pagetable_map, *old(pt_lower)),
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
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        page_table_key_2m_valid::<PT_TYPE>(spec_index2va((indices.0, indices.1, indices.2, 0))),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2)
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_page(target_l2_ptr).entry_lock(indices.2).l1() is None,
        !whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.window_stale_cpus.dom().contains((target_l2_ptr, indices.2)),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None
            || !whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_2m().dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0))),
        page_ptr_2m_valid(target_entry.addr),
        !whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).page_closure().contains(target_entry.addr),
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
        pagetable_hidden_l1_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *final(pt_lower)),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *final(pt_lower)),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).page_closure() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).page_closure(),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_2m() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_2m().insert(spec_index2va((indices.0, indices.1, indices.2, 0)), *target_entry),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_4k() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k(),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
            pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (indices.0, indices.1, indices.2)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(indices.0, indices.1, indices.2) is Some,
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(indices.0, indices.1, indices.2)->0.addr == target_entry.addr,
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.map_2m_page(Tracked(lower), indices.0, indices.1, indices.2, target_l2_ptr, target_entry, Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        let post_c = WholePageTable { higher: *pagetable, lower: *lower };
        assert(whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        let va = spec_index2va((indices.0, indices.1, indices.2, 0));
        assert(pagetable_map.spec_index(pagetable_ptr).locking_thread() is Read) by { pagetable_map.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); };
        assert(pagetable_map_insert_2m_eof_transition_framing(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, va, *target_entry)) by {
            reveal(pagetable_map_insert_2m_eof_transition_framing);
        };
        pagetable_map_insert_2m_eof(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, va, *target_entry, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id());
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
        pagetable_hidden_l1_only_when_locked(*old(pagetable_map), *old(pt_lower)),
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
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        page_table_key_4k_valid::<PT_TYPE>(spec_index2va(indices)),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2)
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_4k_l1(indices.0, indices.1, indices.2, indices.3) is None
            || !whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().dom().contains(spec_index2va(indices)),
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
        pagetable_hidden_l1_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows() ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().insert(spec_index2va(indices), *target_entry),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
            old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1()]
            pei_valid(i) && !whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(p, i) ==> !whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(p, i),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_perms.dom() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_perms.dom(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_entry(p, i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i, l1i) != (indices.0, indices.1, indices.2, indices.3)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(indices.0, indices.1, indices.2, indices.3) is Some,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(indices.0, indices.1, indices.2, indices.3)->0.addr == target_entry.addr,
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.map_4k_page(Tracked(lower), indices.0, indices.1, indices.2, indices.3, target_l2_ptr, target_l1_ptr, target_entry, Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        let post_c = WholePageTable { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
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
        pagetable_hidden_l1_only_when_locked(*pagetable_map, *old(pt_lower)),
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
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2)
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_page(target_l2_ptr).entry_lock(indices.2).l1() is None,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None,
        page_ptr_valid(page_map_ptr),
        !whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).page_closure().contains(page_map_ptr),
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
        pagetable_hidden_l1_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *final(pt_lower)),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *final(pt_lower)),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).page_closure() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).page_closure().insert(page_map_ptr),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_4k() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k(),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_2m() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_2m(),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == page_map_ptr,
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_perms.dom() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_perms.dom(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1()]
            !whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(p, i) ==> !whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(p, i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i) is Some
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.create_entry_l2(Tracked(lower), indices.0, indices.1, indices.2, target_l2_ptr, page_map_ptr, Tracked(page_map_perm), Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        let post_c = WholePageTable { higher: *pagetable, lower: *lower };
        assert(whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(indices.0, indices.1);
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
        pagetable_hidden_l1_only_when_locked(*old(pagetable_map), *old(pt_lower)),
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
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2)
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_page(target_l2_ptr).entry_lock(indices.2).l1() is None,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None,
        page_ptr_valid(page_map_ptr),
        !whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure().contains(page_map_ptr),
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
        pagetable_hidden_l1_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows() ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure().insert(page_map_ptr),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == page_map_ptr,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1()]
            pei_valid(i) && !whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(p, i) ==> !whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(p, i),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_perms.dom() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_perms.dom(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i) is Some
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.create_entry_l2(Tracked(lower), indices.0, indices.1, indices.2, target_l2_ptr, page_map_ptr, Tracked(page_map_perm), Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        let post_c = WholePageTable { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(indices.0, indices.1);
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
        pagetable_hidden_l1_only_when_locked(*old(pagetable_map), *pt_lower),
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
        whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).spec_held_l4(indices.0) is None,
        page_ptr_valid(page_map_ptr),
        !whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).page_closure().contains(page_map_ptr),
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
        pagetable_hidden_l1_only_when_locked(*final(pagetable_map), *pt_lower),
        whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).lower.hidden_l1_tables_in_locked_windows() ==> whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *pt_lower),
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *pt_lower, final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *pt_lower),
        whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).page_closure() == whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).page_closure().insert(page_map_ptr),
        whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).mapping_4k() == whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).mapping_4k(),
        whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).mapping_2m() == whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).mapping_2m(),
        whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).mapping_1g() == whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).mapping_1g(),
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end,
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries,
        final(pagetable_map).spec_index(pagetable_ptr).view().cr3 == old(pagetable_map).spec_index(pagetable_ptr).view().cr3,
        final(pagetable_map).spec_index(pagetable_ptr).view().pcid == old(pagetable_map).spec_index(pagetable_ptr).view().pcid,
        final(pagetable_map).spec_index(pagetable_ptr).view().did == old(pagetable_map).spec_index(pagetable_ptr).view().did,
        final(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr == old(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr,
        whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l4(indices.0) is Some,
        whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l4(indices.0)->0.addr == page_map_ptr,
        whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is None,
        whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_1g_l3(indices.0, indices.1) is None,
        forall|l4i: L4Index, l3i: L3Index| #![trigger whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i)]
            old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i)
                ==> whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i) == whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
            whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                ==> whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        final(pagetable_map).spec_index(pagetable_ptr).view().table_stale_cpus == old(pagetable_map).spec_index(pagetable_ptr).view().table_stale_cpus,
        forall|l4i: L4Index| #![trigger whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_held_l4(l4i)]
            whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).spec_held_l4(l4i) is Some
                ==> whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_held_l4(l4i) == whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).spec_held_l4(l4i),
        forall|l4i: L4Index| #![trigger whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_held_l4(l4i)]
            whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && l4i != indices.0
                ==> whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_held_l4(l4i) == whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).spec_held_l4(l4i),
        forall|l4i: L4Index, l3i: L3Index| #![trigger whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_held_l3(l4i, l3i)]
            whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i)
                ==> whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_held_l3(l4i, l3i) == whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).spec_held_l3(l4i, l3i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_held_l2(l4i, l3i, l2i)]
            whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_held_l2(l4i, l3i, l2i) == whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).spec_held_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                ==> whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) == whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i)]
            whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i) == whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_mut_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow(pagetable_ptr);
    pagetable.create_entry_l4(Tracked(lower), indices.0, indices.1, page_map_ptr, Tracked(page_map_perm), Tracked(&mut *lctx));
    proof {
        let post_c = WholePageTable { higher: *pagetable, lower: *lower };
        assert(whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
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
        pagetable_hidden_l1_only_when_locked(*old(pagetable_map), *old(pt_lower)),
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
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        KERNEL_MEM_END_L4INDEX <= indices.0,
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(lo) && pei_valid(hi) && lo <= hi,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(indices.0) is Some,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(indices.0)->0.addr == target_l3_ptr,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l3(indices.0, indices.1) is None,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_1g_l3(indices.0, indices.1) is None,
        page_ptr_valid(page_map_ptr),
        !whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure().contains(page_map_ptr),
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
        pagetable_hidden_l1_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows() ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure().insert(page_map_ptr),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_1g() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_1g(),
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end,
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries,
        final(pagetable_map).spec_index(pagetable_ptr).view().cr3 == old(pagetable_map).spec_index(pagetable_ptr).view().cr3,
        final(pagetable_map).spec_index(pagetable_ptr).view().pcid == old(pagetable_map).spec_index(pagetable_ptr).view().pcid,
        final(pagetable_map).spec_index(pagetable_ptr).view().did == old(pagetable_map).spec_index(pagetable_ptr).view().did,
        final(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr == old(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(indices.0) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(indices.0),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == page_map_ptr,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_1g_l3(indices.0, indices.1) is None,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
        forall|i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(page_map_ptr, i)] pei_valid(i) && !(lo <= i <= hi)
            ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(page_map_ptr, i) is None,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == Map::new(
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks.dom() + Set::<usize>::range(0, 512).map_by(|i: usize| WindowVa { va: spec_index2va((indices.0, indices.1, i, 0usize)) }, |w: WindowVa| spec_v2l2index(w.va)),
            |w: WindowVa| if whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks.dom().contains(w) { whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks[w] }
                else if lo <= spec_v2l2index(w.va) <= hi { LockStateU::WriteLocked { writer: final(lctx).thread_id() } } else { LockStateU::Unlocked }),
        forall|i: L2Index| #![trigger ret.view().dom().contains(i)] ret.view().dom().contains(i) == (lo <= i <= hi),
        forall|i: L2Index| #![trigger ret.view().index(i)] lo <= i <= hi ==> {
            &&& whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(page_map_ptr, i) == (RwLockState::Write { thread_id: ret.view().index(i).thread_id(), lock_id: ret.view().index(i).lock_id() })
            &&& ret.view().index(i).state() is WriteLock
            &&& ret.view().index(i).ordering_lock_id() == window_lock_id(pagetable_ptr, indices.0, indices.1, i)
            &&& ret.view().index(i).thread_id() == final(lctx).thread_id()
        },
        forall|l4i: L4Index, l3i: L3Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i)]
            old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && !(l4i == indices.0 && l3i == indices.1)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)
                    == (whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)
                        || (l4i == indices.0 && l3i == indices.1 && lo <= l2i <= hi && thread_id == final(lctx).thread_id())),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_l2_page(l4i, l3i), l2i)]
            old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_exists(l4i, l3i)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_l2_page(l4i, l3i), l2i)
                    == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_l2_page(l4i, l3i), l2i),
        final(pagetable_map).spec_index(pagetable_ptr).view().table_stale_cpus == old(pagetable_map).spec_index(pagetable_ptr).view().table_stale_cpus,
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1()]
            pei_valid(i) && !whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(p, i) ==> !whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(p, i),
        forall|i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_page(page_map_ptr).entry_lock(i).l1()]
            pei_valid(i) ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_page(page_map_ptr).entry_lock(i).l1() is None,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_perms.dom() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_perms.dom().insert(page_map_ptr),
        forall|l4i: L4Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l4(l4i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l4(l4i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l4(l4i),
        forall|l4i: L4Index, l3i: L3Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l3(l4i, l3i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l3(l4i, l3i) is Some
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l3(l4i, l3i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l3(l4i, l3i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_mut_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    let ret = pagetable.create_entry_l3(Tracked(lower), indices.0, indices.1, indices.2, target_l3_ptr, page_map_ptr, Tracked(page_perm), lo, hi, Ghost(pagetable_ptr),
        Tracked(&mut *lctx));
    proof {
        let post_c = WholePageTable { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
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
        pagetable_hidden_l1_only_when_locked(*old(pagetable_map), *old(pt_lower)),
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
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2)
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().dom().contains(spec_index2va(indices)),
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
        pagetable_hidden_l1_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows() ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().insert(spec_index2va(indices),
            MapEntry { present: false, ..whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().spec_index(spec_index2va(indices)) }),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1()]
            pei_valid(i) && !whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(p, i) ==> !whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(p, i),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_perms.dom() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_perms.dom(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_entry(p, i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i, l1i) != (indices.0, indices.1, indices.2, indices.3)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(indices.0, indices.1, indices.2, indices.3)
            == Some(PageEntry { perm: PageEntryPerm { present: false, ..whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_4k_l1(indices.0, indices.1, indices.2, indices.3)->0.perm },
                ..whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_4k_l1(indices.0, indices.1, indices.2, indices.3)->0 }),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.unmap_4k_page_user_view(Tracked(lower), indices.0, indices.1, indices.2, indices.3, target_l2_ptr, target_l1_ptr, Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).wf_mapping_4k_at(indices.0, indices.1, indices.2, indices.3);
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_4k_l1_some_implies_spec_held_4k_l1_eq(indices.0, indices.1, indices.2, indices.3);
        let post_c = WholePageTable { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        let va = spec_index2va(indices);
        assert(pagetable_map_clear_4k_present_eof_transition_framing(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, va)) by {
            reveal(pagetable_map_clear_4k_present_eof_transition_framing);
        };
        pagetable_map_clear_4k_present_eof(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, va, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id());
    }
}

/// Clear the user present bit of the 2M leaf of the window `indices` of page table `pagetable_ptr`: this thread holds the table's big
/// write lock, which a table with hidden leaves needs, and the 2M window lock of `indices`; the lock's ghost slot keeps a
/// copy of the new window half.
pub fn pagetable_map_clear_2m_present(
    pagetable_map: &mut PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index), target_l2_ptr: PageMapPtr, Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        pagetable_lower_wf(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_l1_only_when_locked(*old(pagetable_map), *old(pt_lower)),
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
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2)
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m().dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0))),
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
        pagetable_hidden_l1_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows() ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m().insert(spec_index2va((indices.0, indices.1, indices.2, 0)),
            MapEntry { present: false, ..whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m().spec_index(spec_index2va((indices.0, indices.1, indices.2, 0))) }),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (indices.0, indices.1, indices.2)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(indices.0, indices.1, indices.2) is Some,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(indices.0, indices.1, indices.2)->0.addr == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_2m_l2(indices.0, indices.1, indices.2)->0.addr,
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.unmap_2m_page_user_view(Tracked(lower), indices.0, indices.1, indices.2, target_l2_ptr, Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).wf_mapping_2m_at(indices.0, indices.1, indices.2); whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_2m_l2_some_implies_spec_held_2m_l2_eq(indices.0, indices.1, indices.2);
        let post_c = WholePageTable { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        let va = spec_index2va((indices.0, indices.1, indices.2, 0));
        assert(pagetable_map_clear_2m_present_eof_transition_framing(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, va)) by {
            reveal(pagetable_map_clear_2m_present_eof_transition_framing);
        };
        pagetable_map_clear_2m_present_eof(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, va, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id());
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
        pagetable_hidden_l1_only_when_locked(*old(pagetable_map), *old(pt_lower)),
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
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2)
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().dom().contains(spec_index2va(indices)),
        !whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().spec_index(spec_index2va(indices)).present,
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
        pagetable_hidden_l1_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows() ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().remove(spec_index2va(indices)),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1()]
            pei_valid(i) && !whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(p, i) ==> !whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(p, i),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_perms.dom() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_perms.dom(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_entry(p, i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i, l1i) != (indices.0, indices.1, indices.2, indices.3)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(indices.0, indices.1, indices.2, indices.3) is None,
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.unmap_4k_page_kernel(Tracked(lower), indices.0, indices.1, indices.2, indices.3, target_l2_ptr, target_l1_ptr, Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        let post_c = WholePageTable { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        let va = spec_index2va(indices);
        assert(pagetable_map_unmap_4k_kernel_eof_transition_framing(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, va)) by {
            reveal(pagetable_map_unmap_4k_kernel_eof_transition_framing);
        };
        pagetable_map_unmap_4k_kernel_eof(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, va, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id());
    }
}

/// Remove the hidden 2M leaf of the window `indices` of page table `pagetable_ptr` after its stale TLB entries are flushed: this thread
/// holds the table's big write lock and the 2M window lock of `indices`; the lock's ghost slot keeps a copy of the new
/// window half.
pub fn pagetable_map_unmap_2m_kernel(
    pagetable_map: &mut PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index), target_l2_ptr: PageMapPtr, Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        pagetable_lower_wf(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_l1_only_when_locked(*old(pagetable_map), *old(pt_lower)),
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
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2)
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m().dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0))),
        !whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m().spec_index(spec_index2va((indices.0, indices.1, indices.2, 0))).present,
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
        pagetable_hidden_l1_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows() ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m().remove(spec_index2va((indices.0, indices.1, indices.2, 0))),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (indices.0, indices.1, indices.2)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(indices.0, indices.1, indices.2) is None,
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.unmap_2m_page_kernel(Tracked(lower), indices.0, indices.1, indices.2, target_l2_ptr, Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        let post_c = WholePageTable { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        let va = spec_index2va((indices.0, indices.1, indices.2, 0));
        assert(pagetable_map_unmap_2m_kernel_eof_transition_framing(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, va)) by {
            reveal(pagetable_map_unmap_2m_kernel_eof_transition_framing);
        };
        pagetable_map_unmap_2m_kernel_eof(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, va, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id());
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
        pagetable_hidden_l1_only_when_locked(*pagetable_map, *old(pt_lower)),
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
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2)
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().dom().contains(spec_index2va(indices)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*pagetable_map, *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_hidden_l1_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *final(pt_lower)),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *final(pt_lower)),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).page_closure() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).page_closure(),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_4k() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().insert(spec_index2va(indices),
            MapEntry { present: false, ..whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().spec_index(spec_index2va(indices)) }),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_2m() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_2m(),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1()]
            pei_valid(i) && !whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(p, i) ==> !whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(p, i),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_perms.dom() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_perms.dom(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i)]
            whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_entry(p, i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i, l1i) != (indices.0, indices.1, indices.2, indices.3)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(indices.0, indices.1, indices.2, indices.3)
            == Some(PageEntry { perm: PageEntryPerm { present: false, ..whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_4k_l1(indices.0, indices.1, indices.2, indices.3)->0.perm },
                ..whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_4k_l1(indices.0, indices.1, indices.2, indices.3)->0 }),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.unmap_4k_page_user_view(Tracked(lower), indices.0, indices.1, indices.2, indices.3, target_l2_ptr, target_l1_ptr, Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).wf_mapping_4k_at(indices.0, indices.1, indices.2, indices.3);
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_4k_l1_some_implies_spec_held_4k_l1_eq(indices.0, indices.1, indices.2, indices.3);
        let post_c = WholePageTable { higher: *pagetable, lower: *lower };
        assert(whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(pagetable_map.spec_index(pagetable_ptr).locking_thread() is Read) by { pagetable_map.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); };
        assert(pagetable_map_clear_4k_present_rlocked_eof_transition_framing(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, spec_index2va(indices))) by {
            reveal(pagetable_map_clear_4k_present_rlocked_eof_transition_framing);
        };
        pagetable_map_clear_4k_present_rlocked_eof(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, indices, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id());
    }
}

/// Clear the user present bit of the 2M leaf of the window `indices` of page table `pagetable_ptr`: this thread holds the table's big
/// read lock and the 2M window lock of `indices`; only the window half `pt_lower[pagetable_ptr]` changes.
pub fn pagetable_map_clear_2m_present_rlocked(
    pagetable_map: &PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index), target_l2_ptr: PageMapPtr, Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*pagetable_map),
        pagetable_lower_wf(*pagetable_map, *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *old(pt_lower)),
        pagetable_hidden_l1_only_when_locked(*pagetable_map, *old(pt_lower)),
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
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2)
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_2m().dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0))),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*pagetable_map, *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_hidden_l1_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *final(pt_lower)),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *final(pt_lower)),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).page_closure() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).page_closure(),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_2m() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_2m().insert(spec_index2va((indices.0, indices.1, indices.2, 0)),
            MapEntry { present: false, ..whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_2m().spec_index(spec_index2va((indices.0, indices.1, indices.2, 0))) }),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_4k() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k(),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1()]
            pei_valid(i) && !whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(p, i) ==> !whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(p, i),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry(target_l2_ptr, indices.2)
            == (PageEntry { perm: PageEntryPerm { present: false, ..whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_entry(target_l2_ptr, indices.2).perm }, ..whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_entry(target_l2_ptr, indices.2) }),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i)]
            (p, i) != (target_l2_ptr, indices.2) ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_entry(p, i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (indices.0, indices.1, indices.2)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(indices.0, indices.1, indices.2) is Some,
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(indices.0, indices.1, indices.2) == Some(whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry(target_l2_ptr, indices.2)),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(indices.0, indices.1, indices.2)->0.addr == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_2m_l2(indices.0, indices.1, indices.2)->0.addr,
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.unmap_2m_page_user_view(Tracked(lower), indices.0, indices.1, indices.2, target_l2_ptr, Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).wf_mapping_2m_at(indices.0, indices.1, indices.2); whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_2m_l2_some_implies_spec_held_2m_l2_eq(indices.0, indices.1, indices.2);
        let post_c = WholePageTable { higher: *pagetable, lower: *lower };
        assert(whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(pagetable_map.spec_index(pagetable_ptr).locking_thread() is Read) by { pagetable_map.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); };
        assert(pagetable_map_clear_2m_present_rlocked_eof_transition_framing(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, spec_index2va((indices.0, indices.1, indices.2, 0)))) by {
            reveal(pagetable_map_clear_2m_present_rlocked_eof_transition_framing);
        };
        pagetable_map_clear_2m_present_rlocked_eof(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, indices, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id());
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
        pagetable_hidden_l1_only_when_locked(*pagetable_map, *old(pt_lower)),
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
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2)
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().dom().contains(spec_index2va(indices)),
        !whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().spec_index(spec_index2va(indices)).present,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*pagetable_map, *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_hidden_l1_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *final(pt_lower)),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *final(pt_lower)),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).page_closure() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).page_closure(),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_4k() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().remove(spec_index2va(indices)),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_2m() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_2m(),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1()]
            pei_valid(i) && !whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(p, i) ==> !whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(p, i),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_perms.dom() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_perms.dom(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i)]
            whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_entry(p, i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i, l1i) != (indices.0, indices.1, indices.2, indices.3)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(indices.0, indices.1, indices.2, indices.3) is None,
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.unmap_4k_page_kernel(Tracked(lower), indices.0, indices.1, indices.2, indices.3, target_l2_ptr, target_l1_ptr, Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        let post_c = WholePageTable { higher: *pagetable, lower: *lower };
        assert(whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(pagetable_map.spec_index(pagetable_ptr).locking_thread() is Read) by { pagetable_map.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); };
        assert(pagetable_map_unmap_4k_kernel_rlocked_eof_transition_framing(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, spec_index2va(indices))) by {
            reveal(pagetable_map_unmap_4k_kernel_rlocked_eof_transition_framing);
        };
        pagetable_map_unmap_4k_kernel_rlocked_eof(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, spec_index2va(indices), lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(),
            lctx.thread_id());
    }
}

/// Remove the hidden 2M leaf of the window `indices` of page table `pagetable_ptr` after its stale TLB entries are flushed: this thread
/// holds the table's big read lock and the 2M window lock of `indices`; only the window half `pt_lower[pagetable_ptr]` changes.
pub fn pagetable_map_unmap_2m_kernel_rlocked(
    pagetable_map: &PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot,
    indices: (L4Index, L3Index, L2Index), target_l2_ptr: PageMapPtr, Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*pagetable_map),
        pagetable_lower_wf(*pagetable_map, *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *old(pt_lower)),
        pagetable_hidden_l1_only_when_locked(*pagetable_map, *old(pt_lower)),
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
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2)
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_2m().dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0))),
        !whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_2m().spec_index(spec_index2va((indices.0, indices.1, indices.2, 0))).present,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*pagetable_map, *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_hidden_l1_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *final(pt_lower)),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *final(pt_lower)),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).page_closure() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).page_closure(),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_2m() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_2m().remove(spec_index2va((indices.0, indices.1, indices.2, 0))),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_4k() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k(),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1()]
            pei_valid(i) && !whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(p, i) ==> !whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(p, i),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i)]
            (p, i) != (target_l2_ptr, indices.2) ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_entry(p, i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (indices.0, indices.1, indices.2)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(indices.0, indices.1, indices.2) is None,
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.unmap_2m_page_kernel(Tracked(lower), indices.0, indices.1, indices.2, target_l2_ptr, Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        let post_c = WholePageTable { higher: *pagetable, lower: *lower };
        assert(whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(pagetable_map.spec_index(pagetable_ptr).locking_thread() is Read) by { pagetable_map.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); };
        assert(pagetable_map_unmap_2m_kernel_rlocked_eof_transition_framing(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, spec_index2va((indices.0, indices.1, indices.2, 0)))) by {
            reveal(pagetable_map_unmap_2m_kernel_rlocked_eof_transition_framing);
        };
        pagetable_map_unmap_2m_kernel_rlocked_eof(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, spec_index2va((indices.0, indices.1, indices.2, 0)), lctx.pagetable_window_lock_map(),
            lctx.pagetable_lock_map(), lctx.thread_id());
    }
}

/// Hide the L1 page `target_l1_ptr` that the window `indices` of page table `pagetable_ptr` links and that maps no 4K page: the
/// window's L2 entry is published with its present bit clear and the L1 address kept, and the page stays owned under the window
/// lock. This thread holds the table's big read lock and the 2M window lock of `indices`, which lists every CPU stale; only the
/// window half `pt_lower[pagetable_ptr]` changes.
pub fn pagetable_map_hide_l1_page_rlocked(
    pagetable_map: &PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index),
    target_l2_ptr: PageMapPtr, target_l1_ptr: PageMapPtr, Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*pagetable_map),
        pagetable_lower_wf(*pagetable_map, *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *old(pt_lower)),
        pagetable_hidden_l1_only_when_locked(*pagetable_map, *old(pt_lower)),
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
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2)
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == target_l1_ptr,
        forall|l1i: L1Index| #![trigger whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().dom().contains(spec_index2va((indices.0, indices.1, indices.2, l1i)))]
            pei_valid(l1i) ==> !whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k().dom().contains(spec_index2va((indices.0, indices.1, indices.2, l1i))),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*pagetable_map, *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_hidden_l1_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *final(pt_lower)),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).page_closure() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).page_closure(),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l1_rev_map == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l1_rev_map,
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_perms.dom() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_perms.dom(),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_4k() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k(),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_2m() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_2m(),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry(target_l2_ptr, indices.2)
            == (PageEntry { addr: target_l1_ptr, perm: PageEntryPerm { present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: true } }),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i)]
            (p, i) != (target_l2_ptr, indices.2) ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_entry(p, i),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1()]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_perms.dom().contains(p) && (p, i) != (target_l2_ptr, indices.2)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1(),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(target_l2_ptr, indices.2),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (indices.0, indices.1, indices.2)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (indices.0, indices.1, indices.2)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_l2(indices.0, indices.1, indices.2)
            == Some(whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry(target_l2_ptr, indices.2)),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    proof { assert(lower.mapping_4k == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k()); }
    pagetable.hide_l1_page(Tracked(lower), indices.0, indices.1, indices.2, target_l2_ptr, target_l1_ptr, Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        let post_c = WholePageTable { higher: *pagetable, lower: *lower };
        assert(whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(pagetable_map.spec_index(pagetable_ptr).locking_thread() is Read) by { pagetable_map.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); };
        assert(pagetable_map_hide_l1_page_rlocked_eof_transition_framing(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr)) by {
            reveal(pagetable_map_hide_l1_page_rlocked_eof_transition_framing);
        };
        pagetable_map_hide_l1_page_rlocked_eof(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id());
    }
}

/// Take the L1 page `target_l1_ptr` that the window `indices` of page table `pagetable_ptr` hides out of the table and return it;
/// the L2 entry is published cleared, dropping the hidden-L1 marker, and the page leaves the table. This thread holds the table's big
/// read lock and the 2M window lock of `indices`, which lists no CPU stale any more, so no usable paging-structure cache of `krnl`,
/// the state these maps belong to, names the page. Only the window half `pt_lower[pagetable_ptr]` changes.
pub fn pagetable_map_unlink_hidden_l1_page_rlocked(
    pagetable_map: &PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index),
    target_l2_ptr: PageMapPtr, target_l1_ptr: PageMapPtr, Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    Ghost(krnl): Ghost<KernelK>,
) -> (ret: Tracked<PointsTo<PageMap>>)
    requires
        krnl.inv(),
        krnl.pt_mp == *pagetable_map,
        krnl.pt_lower.view() == *old(pt_lower),
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_map.dom().contains(pagetable_ptr),
        pagetable_map.typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_map.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(indices.0, indices.1, indices.2, old(lctx).thread_id()),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2)
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == target_l2_ptr,
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_entry_hides_l1(target_l2_ptr, indices.2),
        whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_entry(target_l2_ptr, indices.2).addr == target_l1_ptr,
        !whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.window_stale_cpus.dom().contains((target_l2_ptr, indices.2)),
        old(lctx).kernel_view_locking_state() is Acquire,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*pagetable_map, *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*pagetable_map, *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_hidden_l1_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*pagetable_map, *final(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*pagetable_map, *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*pagetable_map, *final(pt_lower)),
        table_page_unreferenced_by_structure_caches(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, target_l1_ptr),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).page_closure() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).page_closure().remove(target_l1_ptr),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l1_rev_map == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l1_rev_map.remove(target_l1_ptr),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_perms.dom() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_perms.dom(),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_4k() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_4k(),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).mapping_2m() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).mapping_2m(),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry(target_l2_ptr, indices.2).is_empty(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i)]
            (p, i) != (target_l2_ptr, indices.2) ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_entry(p, i),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_page(target_l2_ptr).entry_lock(indices.2).l1() is None,
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1()]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_perms.dom().contains(p) && (p, i) != (target_l2_ptr, indices.2)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1() == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (indices.0, indices.1, indices.2)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i),
        whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_l2(indices.0, indices.1, indices.2) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i) != (indices.0, indices.1, indices.2)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i),
        forall|l1i: L1Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(indices.0, indices.1, indices.2, l1i)]
            pei_valid(l1i) ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_4k_l1(indices.0, indices.1, indices.2, l1i) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i)]
            whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*pagetable_map, *final(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i) == whole_pagetable(*pagetable_map, *old(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i),
        ret.view().addr() == target_l1_ptr,
        ret.view().is_init(),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    assert(pagetable_map.spec_index(pagetable_ptr).locking_thread() is Read) by { pagetable_map.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); };
    proof {
        pagetable_table_stale_cpus_only_when_write_locked_at(krnl.pt_mp, pagetable_ptr);
        hidden_l1_page_without_window_stale_record_implies_unreferenced_by_structure_caches(krnl, pagetable_ptr, indices.0, indices.1, indices.2, target_l1_ptr);
    }
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    let ret = pagetable.unlink_hidden_l1_page(Tracked(lower), indices.0, indices.1, indices.2, target_l2_ptr, target_l1_ptr, Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        let post_c = WholePageTable { higher: *pagetable, lower: *lower };
        assert(whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(pagetable_map_unlink_hidden_l1_page_rlocked_eof_transition_framing(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr)) by {
            reveal(pagetable_map_unlink_hidden_l1_page_rlocked_eof_transition_framing);
        };
        pagetable_map_unlink_hidden_l1_page_rlocked_eof(*pagetable_map, *old(pt_lower), *pt_lower, pagetable_ptr, old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id());
    }
    ret
}

/// Unlink the table page that `scan` names from the write-held page table `pagetable_ptr` and return its memory; every mapping stays.
/// The scan walks the held chain of a table whose user root entries no longer resolve, as `remove_structure_page` requires: an L1
/// page leaves through its unlocked L2 entry, which no CPU lists as stale, and an L2 page hides no L1 page. No page record names the
/// table, so the page records keep following the held chains. `window_perm` is unused.
pub fn pagetable_map_remove_table_page(
    pagetable_map: &mut PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot, scan: StructureScan,
    page_array: &PageLockedArray, cpu_tlb: &CpuTLB, cpu_arr: &CpuLockedArray, needflush: &PcidNeedFlushArray,
    Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
) -> (ret: Tracked<PagePerm4k>)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        pagetable_lower_wf(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_l1_only_when_locked(*old(pagetable_map), *old(pt_lower)),
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
        pagetable_table_stale_cpus_only_when_write_locked(*old(pagetable_map)),
        page_mappings_pagetable_wf(*old(pagetable_map), *old(pt_lower), *page_array),
        forall|p_i: PageIndex, va: VAddr| #![trigger page_array.spec_index(p_i).view().view().mappings().contains((pagetable_ptr, va))]
            index_valid(NUM_PAGES, p_i) && page_array.spec_index(p_i).view().view().is_mapped() ==> !page_array.spec_index(p_i).view().view().mappings().contains((pagetable_ptr, va)),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).structure_scan_wf(scan),
        scan.spec_table_page() is Some,
        scan is L1 ==> !whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus.dom().contains((scan->L1_l2_p, scan->L1_l2i)),
        scan is L2 ==> whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
        table_page_unreferenced_by_structure_caches(*cpu_tlb, *cpu_arr, *needflush, scan.spec_table_page()->Some_0),
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
        pagetable_hidden_l1_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows() ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        scan is L2 ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus.filter_keys(|k: (PageMapPtr, L2Index)| k.0 != scan->L2_l2_p),
        !(scan is L2) ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_table_stale_cpus_only_when_write_locked(*final(pagetable_map)),
        page_mappings_pagetable_wf(*final(pagetable_map), *final(pt_lower), *page_array),
        final(pagetable_map).spec_index(pagetable_ptr).view().table_stale_cpus == old(pagetable_map).spec_index(pagetable_ptr).view().table_stale_cpus,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure().remove(scan.spec_table_page()->Some_0),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_1g() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_1g(),
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end,
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries,
        final(pagetable_map).spec_index(pagetable_ptr).view().cr3 == old(pagetable_map).spec_index(pagetable_ptr).view().cr3,
        final(pagetable_map).spec_index(pagetable_ptr).view().pcid == old(pagetable_map).spec_index(pagetable_ptr).view().pcid,
        final(pagetable_map).spec_index(pagetable_ptr).view().did == old(pagetable_map).spec_index(pagetable_ptr).view().did,
        final(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr == old(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr,
        !(scan is L2) ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        scan is L2 ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks.remove_keys(
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == scan->L2_l4i && spec_v2l3index(w.va) == scan->L2_l3i)),
        scan is L1 ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).higher == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).higher,
        forall|l4i: L4Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(l4i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(l4i) is None
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(l4i) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
        ret.view().is_init(),
        ret.view().addr() == scan.spec_table_page()->Some_0,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_perms.dom().subset_of(whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_perms.dom()),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_perms.dom().contains(p)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_mut_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    let ret = pagetable.remove_structure_page(Tracked(lower), scan, cpu_tlb, cpu_arr, needflush, Tracked(window_perm), Tracked(&mut *lctx));
    proof {
        let post_c = WholePageTable { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(pagetable_map_remove_table_page_eof_transition_framing(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr)) by {
            reveal(pagetable_map_remove_table_page_eof_transition_framing);
        };
        pagetable_map_remove_table_page_eof(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, *page_array, lctx.pagetable_window_lock_map(),
            lctx.pagetable_lock_map(), lctx.thread_id());
    }
    ret
}

/// Hide the user root entry `l4i` of the write-held page table `pagetable_ptr`: publish it as a placeholder that keeps the L3 address,
/// so every mapping and every window under `l4i` leaves the table while every table page below it stays held. Every CPU is listed as
/// stale for the whole table and no window under `l4i` is locked; the lock's ghost slot keeps a copy of the new window half.
pub fn pagetable_map_hide_l4_entry(
    pagetable_map: &mut PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot, l4i: L4Index,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        pagetable_lower_wf(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_l1_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*old(pagetable_map), *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*old(pagetable_map), *old(pt_lower)),
        pagetable_table_stale_cpus_only_when_write_locked(*old(pagetable_map)),
        old(pagetable_map).dom().contains(pagetable_ptr),
        old(pagetable_map).typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(l4i) is Some,
        old(pagetable_map).spec_index(pagetable_ptr).view().table_stale_cpus.view() == Set::range(0, NUM_CPUS),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_perms.dom().contains(p) && whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).higher.l2_rev_map.view().spec_index(p).0 == l4i && pei_valid(i)
                ==> whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i) is None,
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))]
            spec_v2l4index(w.va) == l4i ==> !old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)),
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
        pagetable_hidden_l1_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows() ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_table_stale_cpus_only_when_write_locked(*final(pagetable_map)),
        final(pagetable_map).spec_index(pagetable_ptr).view().table_stale_cpus == old(pagetable_map).spec_index(pagetable_ptr).view().table_stale_cpus,
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_l4_end,
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries,
        final(pagetable_map).spec_index(pagetable_ptr).view().cr3 == old(pagetable_map).spec_index(pagetable_ptr).view().cr3,
        final(pagetable_map).spec_index(pagetable_ptr).view().pcid == old(pagetable_map).spec_index(pagetable_ptr).view().pcid,
        final(pagetable_map).spec_index(pagetable_ptr).view().did == old(pagetable_map).spec_index(pagetable_ptr).view().did,
        final(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr == old(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr,
        final(pagetable_map).spec_index(pagetable_ptr).view().l3_tables == old(pagetable_map).spec_index(pagetable_ptr).view().l3_tables,
        final(pagetable_map).spec_index(pagetable_ptr).view().l3_rev_map == old(pagetable_map).spec_index(pagetable_ptr).view().l3_rev_map,
        final(pagetable_map).spec_index(pagetable_ptr).view().l2_rev_map == old(pagetable_map).spec_index(pagetable_ptr).view().l2_rev_map,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_perms == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_perms,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l1_rev_map == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l1_rev_map,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k()
            == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().remove_keys(whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k().dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m()
            == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m().remove_keys(whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m().dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_1g()
            == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_1g().remove_keys(whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_1g().dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks
            == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks.remove_keys(whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == l4i)),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(l4i) is None,
        forall|i4: L4Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(i4)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && i4 != l4i
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(i4) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(i4),
        forall|i4: L4Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l4(i4)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && i4 != l4i
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l4(i4) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l4(i4),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l4(l4i) == Some(PageEntry { addr: whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l4(l4i)->0.addr,
            perm: PageEntryPerm { present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: true } }),
        forall|i4: L4Index, i3: L3Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l3(i4, i3)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l3(i4, i3) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l3(i4, i3),
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l2(i4, i3, i2)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l2(i4, i3, i2) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l2(i4, i3, i2),
        forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(i4, i3, i2, i1)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(i4, i3, i2, i1) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_4k_l1(i4, i3, i2, i1),
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(i4, i3, i2)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(i4, i3, i2) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_2m_l2(i4, i3, i2),
        forall|i4: L4Index, i3: L3Index, i2: L2Index, thread_id: LockThreadId| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(i4, i3, i2, thread_id)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(i4, i3, i2, thread_id) == (whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(i4, i3, i2, thread_id) && i4 != l4i),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_mut_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.hide_l4_entry(Tracked(lower), l4i, Tracked(&mut *lctx));
    proof {
        let post_c = WholePageTable { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(pagetable_map_hide_l4_entry_eof_transition_framing(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, l4i)) by {
            reveal(pagetable_map_hide_l4_entry_eof_transition_framing);
        };
        pagetable_map_hide_l4_entry_eof(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, l4i, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(),
            lctx.thread_id());
    }
}

/// The first held 4K or 2M leaf of page table `pagetable_ptr` at or after `cursor` in VA order, along the held chain with placeholders
/// included; a 2M leaf sits at L1 index 0, and `cursor.3 == 512` names the slot just past `(cursor.0, cursor.1, cursor.2, 511)`. This
/// thread holds the table's big write lock, no window of the table is locked, and no hidden L1 page sits outside a locked window.
pub fn pagetable_map_next_held_leaf_from(
    pagetable_map: &PageTableLockedMap, Tracked(pt_lower): Tracked<&PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot, cursor: (L4Index, L3Index, L2Index, L1Index),
    Tracked(lctx): Tracked<&LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
) -> (ret: Option<((L4Index, L3Index, L2Index, L1Index), bool, PageEntry)>)
    requires
        pagetable_perms_wf(*pagetable_map),
        pagetable_lower_wf(*pagetable_map, *pt_lower),
        pagetable_map.dom().contains(pagetable_ptr),
        pagetable_map.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == lctx.thread_id(),
        pagetable_lock_perm.lock_id() == pagetable_map.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).kernel_l4_end() <= cursor.0,
        pei_valid(cursor.0),
        pei_valid(cursor.1),
        pei_valid(cursor.2),
        cursor.3 <= 512,
        whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).lower.l2_perms.dom().contains(p) && pei_valid(i) ==> whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).lower.l2_owner(p, i) is None,
    ensures
        ret is Some ==> {
            let (found, is_2m, entry) = ret->Some_0;
            &&& whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).kernel_l4_end() <= found.0
            &&& pei_valid(found.0)
            &&& pei_valid(found.1)
            &&& pei_valid(found.2)
            &&& pei_valid(found.3)
            &&& spec_l4_index_path_le(cursor, found)
            &&& is_2m ==> found.3 == 0 && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).spec_held_2m_l2(found.0, found.1, found.2) == Some(entry)
            &&& !is_2m ==> whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).spec_held_4k_l1(found.0, found.1, found.2, found.3) == Some(entry)
        },
        forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).spec_held_4k_l1(i4, i3, i2, i1)]
            pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1) && spec_l4_index_path_le(cursor, (i4, i3, i2, i1)) && (ret is None || !spec_l4_index_path_le(ret->Some_0.0, (i4, i3, i2, i1)))
                ==> whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).spec_held_4k_l1(i4, i3, i2, i1) is None,
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).spec_held_2m_l2(i4, i3, i2)]
            pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && spec_l4_index_path_le(cursor, (i4, i3, i2, 0)) && (ret is None || !spec_l4_index_path_le(ret->Some_0.0, (i4, i3, i2, 0)))
                ==> whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).spec_held_2m_l2(i4, i3, i2) is None,
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow(pagetable_ptr);
    pagetable.next_held_leaf_from(Tracked(lower), cursor)
}

/// Clear the held 4K leaf `indices` of the write-held page table `pagetable_ptr` under the user root entry `indices.0`, which no longer
/// resolves; no CPU is listed as stale for the table. The leaf's L1 page publishes it cleared and stays in place, so no mapping, window,
/// or other held entry changes; the lock's ghost slot keeps a copy of the new window half.
pub fn pagetable_map_clear_held_4k_leaf(
    pagetable_map: &mut PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index),
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        pagetable_lower_wf(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_l1_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*old(pagetable_map), *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*old(pagetable_map), *old(pt_lower)),
        pagetable_table_stale_cpus_only_when_write_locked(*old(pagetable_map)),
        old(pagetable_map).dom().contains(pagetable_ptr),
        old(pagetable_map).typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(indices.0) is None,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_4k_l1(indices.0, indices.1, indices.2, indices.3) is Some,
        old(pagetable_map).spec_index(pagetable_ptr).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
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
        pagetable_hidden_l1_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows() ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_table_stale_cpus_only_when_write_locked(*final(pagetable_map)),
        final(pagetable_map).spec_index(pagetable_ptr).view() == old(pagetable_map).spec_index(pagetable_ptr).view(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_perms.dom() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_perms.dom(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l1_rev_map == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l1_rev_map,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_entry(p, i),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1()]
            (p, i) != (whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l3(indices.0, indices.1)->0.addr, indices.2)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_page(whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l3(indices.0, indices.1)->0.addr).entry_lock(indices.2).l1() is Some,
        forall|w: WindowVa| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_view(w)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(w.va) && pei_valid(spec_v2l4index(w.va)) && pei_valid(spec_v2l3index(w.va))
                && whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_exists(spec_v2l4index(w.va), spec_v2l3index(w.va))
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_view(w) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_view(w),
        forall|i4: L4Index, i3: L3Index, i2: L2Index, thread_id: LockThreadId| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(i4, i3, i2, thread_id)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(i4, i3, i2, thread_id) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(i4, i3, i2, thread_id),
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l2(i4, i3, i2)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l2(i4, i3, i2) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l2(i4, i3, i2),
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(i4, i3, i2)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(i4, i3, i2) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_2m_l2(i4, i3, i2),
        forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(i4, i3, i2, i1)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1) && (i4, i3, i2, i1) != indices
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(i4, i3, i2, i1) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_4k_l1(i4, i3, i2, i1),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(indices.0, indices.1, indices.2, indices.3) is None,
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.clear_held_4k_leaf(Tracked(lower), indices.0, indices.1, indices.2, indices.3, Tracked(&mut *lctx));
    proof {
        let post_c = WholePageTable { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(pagetable_map_clear_held_4k_leaf_eof_transition_framing(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr)) by {
            reveal(pagetable_map_clear_held_4k_leaf_eof_transition_framing);
        };
        pagetable_map_clear_held_4k_leaf_eof(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(),
            lctx.thread_id());
    }
}

/// Clear the held 2M leaf `indices` of the write-held page table `pagetable_ptr` under the user root entry `indices.0`, which no longer
/// resolves; no CPU is listed as stale for the table. The held L2 entry is published cleared and stays in its L2 page, so no mapping,
/// window, or other held entry changes; the lock's ghost slot keeps a copy of the new window half.
pub fn pagetable_map_clear_held_2m_leaf(
    pagetable_map: &mut PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index),
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        pagetable_lower_wf(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_l1_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*old(pagetable_map), *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*old(pagetable_map), *old(pt_lower)),
        pagetable_table_stale_cpus_only_when_write_locked(*old(pagetable_map)),
        old(pagetable_map).dom().contains(pagetable_ptr),
        old(pagetable_map).typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(indices.0) is None,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_2m_l2(indices.0, indices.1, indices.2) is Some,
        old(pagetable_map).spec_index(pagetable_ptr).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
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
        pagetable_hidden_l1_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows() ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_table_stale_cpus_only_when_write_locked(*final(pagetable_map)),
        final(pagetable_map).spec_index(pagetable_ptr).view() == old(pagetable_map).spec_index(pagetable_ptr).view(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_perms.dom() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_perms.dom(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l1_rev_map == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l1_rev_map,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i)]
            (p, i) != (whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l3(indices.0, indices.1)->0.addr, indices.2)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_entry(p, i),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_entry(whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l3(indices.0, indices.1)->0.addr, indices.2).is_empty(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1()]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1(),
        forall|w: WindowVa| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_view(w)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(w.va) && pei_valid(spec_v2l4index(w.va)) && pei_valid(spec_v2l3index(w.va))
                && whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_exists(spec_v2l4index(w.va), spec_v2l3index(w.va))
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_view(w) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_view(w),
        forall|i4: L4Index, i3: L3Index, i2: L2Index, thread_id: LockThreadId| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(i4, i3, i2, thread_id)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(i4, i3, i2, thread_id) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(i4, i3, i2, thread_id),
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l2(i4, i3, i2)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l2(i4, i3, i2) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l2(i4, i3, i2),
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(i4, i3, i2)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && (i4, i3, i2) != indices
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(i4, i3, i2) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_2m_l2(i4, i3, i2),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(indices.0, indices.1, indices.2) is None,
        forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(i4, i3, i2, i1)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(i4, i3, i2, i1) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_4k_l1(i4, i3, i2, i1),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    pagetable.clear_held_2m_leaf(Tracked(lower), indices.0, indices.1, indices.2, Tracked(&mut *lctx));
    proof {
        let post_c = WholePageTable { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(pagetable_map_clear_held_2m_leaf_eof_transition_framing(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr)) by {
            reveal(pagetable_map_clear_held_2m_leaf_eof_transition_framing);
        };
        pagetable_map_clear_held_2m_leaf_eof(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(),
            lctx.thread_id());
    }
}

/// The first table page of page table `pagetable_ptr` that can be unlinked, post-order along the held chain, or `Empty` once only the
/// root is left. This thread holds the table's big write lock, no user root entry resolves, no window is locked, and no hidden L1 page
/// sits outside a locked window.
pub fn pagetable_map_next_structure_page(
    pagetable_map: &PageTableLockedMap, Tracked(pt_lower): Tracked<&PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
) -> (ret: StructureScan)
    requires
        pagetable_perms_wf(*pagetable_map),
        pagetable_lower_wf(*pagetable_map, *pt_lower),
        pagetable_map.dom().contains(pagetable_ptr),
        pagetable_map.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == lctx.thread_id(),
        pagetable_lock_perm.lock_id() == pagetable_map.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        forall|i4: L4Index| #![trigger whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).spec_resolve_mapping_l4(i4)]
            whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) ==> whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).spec_resolve_mapping_l4(i4) is None,
        whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).lower.l2_perms.dom().contains(p) && pei_valid(i) ==> whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).lower.l2_owner(p, i) is None,
    ensures
        whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).structure_scan_wf(ret),
        !(ret is Blocked),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow(pagetable_ptr);
    pagetable.next_structure_page(Tracked(lower))
}

/// Take the L1 page `l1_p` that entry `l2i` of the held L2 page `l2_p` at `(l4i, l3i)` owns out of the write-held page table
/// `pagetable_ptr`, whose path to it no longer resolves, and return it: the entry is published cleared and the page leaves the table.
/// No thread holds the entry's window lock and no CPU lists the window as stale. No page record names the table, so the page records
/// keep following the held chains; the lock's ghost slot keeps a copy of the new window half.
pub fn pagetable_map_unlink_unresolvable_l1_page(
    pagetable_map: &mut PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index,
    l2i: L2Index, l2_p: PageMapPtr, l1_p: PageMapPtr, page_array: &PageLockedArray, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
) -> (ret: Tracked<PointsTo<PageMap>>)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        pagetable_lower_wf(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_holders_hold_pagetable(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_hidden_l1_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*old(pagetable_map), *old(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*old(pagetable_map), *old(pt_lower), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        pagetable_lower_backup_wf(*old(pagetable_map), *old(pt_lower)),
        pagetable_table_stale_cpus_only_when_write_locked(*old(pagetable_map)),
        old(pagetable_map).dom().contains(pagetable_ptr),
        old(pagetable_map).typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        page_mappings_pagetable_wf(*old(pagetable_map), *old(pt_lower), *page_array),
        forall|p_i: PageIndex, va: VAddr| #![trigger page_array.spec_index(p_i).view().view().mappings().contains((pagetable_ptr, va))]
            index_valid(NUM_PAGES, p_i) && page_array.spec_index(p_i).view().view().is_mapped() ==> !page_array.spec_index(p_i).view().view().mappings().contains((pagetable_ptr, va)),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i),
        pei_valid(l3i),
        pei_valid(l2i),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l3(l4i, l3i) is Some,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l3(l4i, l3i)->0.addr == l2_p,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_page(l2_p).entry_lock(l2i).l1() is Some,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_entry(l2_p, l2i).addr == l1_p,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is None,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(l2_p, l2i) is None,
        !whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus.dom().contains((l2_p, l2i)),
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
        pagetable_hidden_l1_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows() ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_table_stale_cpus_only_when_write_locked(*final(pagetable_map)),
        final(pagetable_map).spec_index(pagetable_ptr).view().table_stale_cpus == old(pagetable_map).spec_index(pagetable_ptr).view().table_stale_cpus,
        page_mappings_pagetable_wf(*final(pagetable_map), *final(pt_lower), *page_array),
        final(pagetable_map).spec_index(pagetable_ptr).view() == old(pagetable_map).spec_index(pagetable_ptr).view(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure().remove(l1_p),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l1_rev_map == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l1_rev_map.remove(l1_p),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_perms.dom() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_perms.dom(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_entry(l2_p, l2i).is_empty(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i)]
            (p, i) != (l2_p, l2i) ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_entry(p, i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_entry(p, i),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_page(l2_p).entry_lock(l2i).l1() is None,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus,
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l2(i4, i3, i2)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && (i4, i3, i2) != (l4i, l3i, l2i)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l2(i4, i3, i2) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l2(i4, i3, i2),
        forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(i4, i3, i2, i1)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1) && (i4, i3, i2) != (l4i, l3i, l2i)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(i4, i3, i2, i1) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_4k_l1(i4, i3, i2, i1),
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(i4, i3, i2)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(i4, i3, i2) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_2m_l2(i4, i3, i2),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i) is None,
        forall|i1: L1Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, i1)] pei_valid(i1) ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, i1) is None,
        forall|i4: L4Index, i3: L3Index, i2: L2Index, thread_id: LockThreadId| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(i4, i3, i2, thread_id)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(i4, i3, i2, thread_id) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(i4, i3, i2, thread_id),
        ret.view().addr() == l1_p,
        ret.view().is_init(),
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    let ret = pagetable.unlink_unresolvable_l1_page(Tracked(lower), l4i, l3i, l2i, l2_p, l1_p, Tracked(&mut *lctx));
    proof {
        let post_c = WholePageTable { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(pagetable_map_unlink_unresolvable_l1_page_eof_transition_framing(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr)) by {
            reveal(pagetable_map_unlink_unresolvable_l1_page_eof_transition_framing);
        };
        pagetable_map_unlink_unresolvable_l1_page_eof(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, *page_array, lctx.pagetable_window_lock_map(),
            lctx.pagetable_lock_map(), lctx.thread_id());
    }
    ret
}
}
