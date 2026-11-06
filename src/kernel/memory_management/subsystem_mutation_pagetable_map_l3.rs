use vstd::prelude::*;
use crate::*;
use super::subsystem_mutation_eof_l3::*;
use vstd::simple_pptr::PointsTo;

verus! {
/// Take the L1 page `l1_p` that entry `l2i` of the held L2 page `l2_p` at the unresolvable L3 entry `(l4i, l3i)` owns out of the write-held page table `pagetable_ptr` and return it: the entry is published cleared and the page leaves the table. The
/// page holds no 4K leaf, no thread holds the entry's window lock and no CPU lists the window as stale, so every held leaf and every page record stays; the lock's ghost slot keeps a copy of the new window half.
pub fn pagetable_map_unlink_hidden_l3_l1_page(
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
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i),
        pei_valid(l3i),
        pei_valid(l2i),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l3(l4i, l3i) is Some,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l3(l4i, l3i)->0.addr == l2_p,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i) is None,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_page(l2_p).entry_lock(l2i).l1() is Some,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_entry(l2_p, l2i).addr == l1_p,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(l2_p, l2i) is None,
        !whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus.dom().contains((l2_p, l2i)),
        forall|i1: L1Index| #![trigger whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, i1)] pei_valid(i1) ==> whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, i1) is None,
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
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(i4, i3, i2, i1) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_4k_l1(i4, i3, i2, i1),
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(i4, i3, i2)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(i4, i3, i2) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_2m_l2(i4, i3, i2),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l2(l4i, l3i, l2i) is None,
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
        assert(pagetable_map_unlink_hidden_l3_l1_page_eof_transition_framing(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr)) by {
            reveal(pagetable_map_unlink_hidden_l3_l1_page_eof_transition_framing);
        };
        pagetable_map_unlink_hidden_l3_l1_page_eof(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, *page_array, lctx.pagetable_window_lock_map(),
            lctx.pagetable_lock_map(), lctx.thread_id());
    }
    ret
}

/// Unlink the L2 page `l2_p` of the unresolvable L3 entry `(l4i, l3i)` of the write-held page table `pagetable_ptr` and return it as an ordinary 4K page. The page owns no L1 page and holds no 2M leaf, no thread holds one of
/// its window locks and no CPU structure cache still names it, so every held leaf, every window lock, and every page record stays; the lock's ghost slot keeps a copy of the new window half.
pub fn pagetable_map_remove_l3_entry(
    pagetable_map: &mut PageTableLockedMap, Tracked(pt_lower): Tracked<&mut PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index,
    l2_p: PageMapPtr, page_array: &PageLockedArray, cpu_tlb: &CpuTLB, cpu_arr: &CpuLockedArray, needflush: &PcidNeedFlushArray, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
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
        pagetable_table_stale_cpus_only_when_write_locked(*old(pagetable_map)),
        old(pagetable_map).dom().contains(pagetable_ptr),
        old(pagetable_map).typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        page_mappings_pagetable_wf(*old(pagetable_map), *old(pt_lower), *page_array),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i),
        pei_valid(l3i),
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l3(l4i, l3i) is Some,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l3(l4i, l3i)->0.addr == l2_p,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i) is None,
        whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
        forall|i: L2Index| #![trigger whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_page(l2_p).entry_lock(i).l1()]
            pei_valid(i) ==> whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_page(l2_p).entry_lock(i).l1() is None,
        forall|i: L2Index| #![trigger whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(l2_p, i)]
            pei_valid(i) ==> whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(l2_p, i) is None,
        forall|i: L2Index| #![trigger whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, i)]
            pei_valid(i) ==> whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_2m_l2(l4i, l3i, i) is None,
        table_page_unreferenced_by_structure_caches(*cpu_tlb, *cpu_arr, *needflush, l2_p),
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
        final(pagetable_map).spec_index(pagetable_ptr).view_rodata() == old(pagetable_map).spec_index(pagetable_ptr).view_rodata(),
        final(pagetable_map).spec_index(pagetable_ptr).view_ghost() == final(pt_lower).spec_index(pagetable_ptr),
        *final(pt_lower) == old(pt_lower).insert(pagetable_ptr, final(pt_lower).spec_index(pagetable_ptr)),
        pagetable_lower_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_holders_hold_pagetable(*final(pagetable_map), *final(pt_lower)),
        pagetable_hidden_leaves_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_hidden_l1_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *final(pt_lower)),
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *final(pt_lower), final(lctx).pagetable_window_lock_map(), final(lctx).pagetable_lock_map(), final(lctx).thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *final(pt_lower)),
        pagetable_table_stale_cpus_only_when_write_locked(*final(pagetable_map)),
        page_mappings_pagetable_wf(*final(pagetable_map), *final(pt_lower), *page_array),
        final(pagetable_map).spec_index(pagetable_ptr).view().table_stale_cpus == old(pagetable_map).spec_index(pagetable_ptr).view().table_stale_cpus,
        final(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries == old(pagetable_map).spec_index(pagetable_ptr).view().kernel_entries,
        final(pagetable_map).spec_index(pagetable_ptr).view().cr3 == old(pagetable_map).spec_index(pagetable_ptr).view().cr3,
        final(pagetable_map).spec_index(pagetable_ptr).view().pcid == old(pagetable_map).spec_index(pagetable_ptr).view().pcid,
        final(pagetable_map).spec_index(pagetable_ptr).view().did == old(pagetable_map).spec_index(pagetable_ptr).view().did,
        final(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr == old(pagetable_map).spec_index(pagetable_ptr).view().proc_ptr,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).kernel_l4_end() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).page_closure() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).page_closure().remove(l2_p),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_4k() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_4k(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_2m() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_2m(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).mapping_1g() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).mapping_1g(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.pagetable_window_locks,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.window_stale_cpus
            == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.window_stale_cpus.filter_keys(|k: (PageMapPtr, L2Index)| k.0 != l2_p),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_perms.dom() == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_perms.dom().remove(l2_p),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
            whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_perms.dom().contains(p)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i),
        forall|i4: L4Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(i4)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(i4) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_resolve_mapping_l4(i4),
        forall|i4: L4Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l4(i4)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l4(i4) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l4(i4),
        forall|i4: L4Index, i3: L3Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l3(i4, i3)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && (i4, i3) != (l4i, l3i)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l3(i4, i3) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l3(i4, i3),
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l3(l4i, l3i) is None,
        whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i) is None,
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l2(i4, i3, i2)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_l2(i4, i3, i2) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_l2(i4, i3, i2),
        forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(i4, i3, i2, i1)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_4k_l1(i4, i3, i2, i1) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_4k_l1(i4, i3, i2, i1),
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(i4, i3, i2)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_2m_l2(i4, i3, i2) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_2m_l2(i4, i3, i2),
        forall|i4: L4Index, i3: L3Index| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_1g_l3(i4, i3)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).spec_held_1g_l3(i4, i3) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).spec_held_1g_l3(i4, i3),
        forall|i4: L4Index, i3: L3Index, i2: L2Index, thread_id: LockThreadId| #![trigger whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(i4, i3, i2, thread_id)]
            whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2)
                ==> whole_pagetable(*final(pagetable_map), *final(pt_lower), pagetable_ptr).window_locked_by_thread(i4, i3, i2, thread_id) == whole_pagetable(*old(pagetable_map), *old(pt_lower), pagetable_ptr).window_locked_by_thread(i4, i3, i2, thread_id),
        ret.view().is_init(),
        ret.view().addr() == l2_p,
{
    assert(pagetable_map.perms_wf() && pagetable_map.spec_index(pagetable_ptr).is_init()) by { pagetable_perms_wf_map(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr); };
    assert(pt_lower.dom().contains(pagetable_ptr) && whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr).wf()) by { pagetable_lower_wf_at(*pagetable_map, *pt_lower, pagetable_ptr); };
    let pagetable = pagetable_map.borrow_mut_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = pt_lower.tracked_borrow_mut(pagetable_ptr);
    let l3_p = pagetable.get_held_entry_l4(l4i).unwrap().addr;
    let (_, ret) = pagetable.remove_l3_entry(Tracked(lower), l4i, l3i, l3_p, l2_p, cpu_tlb, cpu_arr, needflush, Tracked(&mut *lctx));
    proof {
        let post_c = WholePageTable { higher: *pagetable, lower: *lower };
        assert(old(pagetable_map).spec_index(pagetable_ptr).locking_thread() is Write) by {
            old(pagetable_map).typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        };
        pagetable_map.update_ghost(pagetable_ptr, pt_lower.spec_index(pagetable_ptr));
        assert(whole_pagetable(*pagetable_map, *pt_lower, pagetable_ptr) == post_c);
        assert(post_c.spec_resolve_mapping_l3(l4i, l3i) is None) by { broadcast use PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq; };
        assert(pagetable_map_remove_l3_entry_eof_transition_framing(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, l4i, l3i)) by {
            reveal(pagetable_map_remove_l3_entry_eof_transition_framing);
        };
        pagetable_map_remove_l3_entry_eof(*old(pagetable_map), *old(pt_lower), *pagetable_map, *pt_lower, pagetable_ptr, l4i, l3i, *page_array, lctx.pagetable_window_lock_map(),
            lctx.pagetable_lock_map(), lctx.thread_id());
    }
    ret
}
}
