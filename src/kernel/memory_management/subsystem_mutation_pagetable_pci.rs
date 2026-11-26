use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::subsystem_mutation_pagetable_pci_eof::*;

verus! {
/// Add (`add`) or remove the BAR mapping `m` of the function in the used entry `index` of the PCI function array of page table
/// `pagetable_ptr`, which this thread write-holds; the rest of the big-lock payload, the lock state, the ghost slot, every window
/// half, and every other table stay.
pub fn pagetable_map_update_pci_mapping(
    pagetable_map: &mut PageTableLockedMap, Tracked(pt_lower): Tracked<&PageTableLowerMap>, pagetable_ptr: RwLockPageTableRoot, index: usize, Ghost(m): Ghost<PciBarMapping>,
    add: bool, Tracked(lctx): Tracked<&LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        pagetable_perms_wf(*old(pagetable_map)),
        pagetable_lower_wf(*old(pagetable_map), *pt_lower),
        pagetable_window_holders_hold_pagetable(*old(pagetable_map), *pt_lower),
        pagetable_hidden_leaves_only_when_locked(*old(pagetable_map), *pt_lower),
        pagetable_hidden_l1_only_when_locked(*old(pagetable_map), *pt_lower),
        pagetable_window_stale_cpus_only_when_locked(*old(pagetable_map), *pt_lower),
        pagetable_window_typed_lock_map_aligned(*old(pagetable_map), *pt_lower, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id()),
        pagetable_lower_backup_wf(*old(pagetable_map), *pt_lower),
        old(pagetable_map).dom().contains(pagetable_ptr),
        old(pagetable_map).typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == lctx.thread_id(),
        pagetable_lock_perm.lock_id() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        index < PCI_FUNCTIONS_PER_PROCESS,
        old(pagetable_map).spec_index(pagetable_ptr).view().higher.pci.spec_entry(index as int).used,
        add ==> !old(pagetable_map).spec_index(pagetable_ptr).view().higher.pci.view()[old(pagetable_map).spec_index(pagetable_ptr).view().higher.pci.spec_entry(index as int).bdf].contains(m),
        add ==> old(pagetable_map).spec_index(pagetable_ptr).view().higher.pci.view()[old(pagetable_map).spec_index(pagetable_ptr).view().higher.pci.spec_entry(index as int).bdf].len() < usize::MAX,
        !add ==> old(pagetable_map).spec_index(pagetable_ptr).view().higher.pci.view()[old(pagetable_map).spec_index(pagetable_ptr).view().higher.pci.spec_entry(index as int).bdf].contains(m),
    ensures
        pagetable_perms_wf(*final(pagetable_map)),
        pagetable_lower_wf(*final(pagetable_map), *pt_lower),
        pagetable_window_holders_hold_pagetable(*final(pagetable_map), *pt_lower),
        pagetable_hidden_leaves_only_when_locked(*final(pagetable_map), *pt_lower),
        pagetable_hidden_l1_only_when_locked(*final(pagetable_map), *pt_lower),
        pagetable_window_stale_cpus_only_when_locked(*final(pagetable_map), *pt_lower),
        pagetable_window_typed_lock_map_aligned(*final(pagetable_map), *pt_lower, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id()),
        pagetable_lower_backup_wf(*final(pagetable_map), *pt_lower),
        final(pagetable_map).typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        final(pagetable_map).unchanged_except(old(pagetable_map), pagetable_ptr),
        final(pagetable_map).lock_id_by_key(pagetable_ptr) == old(pagetable_map).lock_id_by_key(pagetable_ptr),
        final(pagetable_map).spec_index(pagetable_ptr).locking_thread() == old(pagetable_map).spec_index(pagetable_ptr).locking_thread(),
        final(pagetable_map).spec_index(pagetable_ptr).being_killed() == old(pagetable_map).spec_index(pagetable_ptr).being_killed(),
        final(pagetable_map).spec_index(pagetable_ptr).view().lower_backup == old(pagetable_map).spec_index(pagetable_ptr).view().lower_backup,
        final(pagetable_map).spec_index(pagetable_ptr).view().higher
            == (PageTableHigher { pci: final(pagetable_map).spec_index(pagetable_ptr).view().higher.pci, ..old(pagetable_map).spec_index(pagetable_ptr).view().higher }),
        ({
            let old_c = whole_pagetable(*old(pagetable_map), *pt_lower, pagetable_ptr);
            let new_c = whole_pagetable(*final(pagetable_map), *pt_lower, pagetable_ptr);
            &&& new_c.kernel_l4_end() == old_c.kernel_l4_end() && new_c.page_closure() == old_c.page_closure()
            &&& new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_2m() == old_c.mapping_2m() && new_c.mapping_1g() == old_c.mapping_1g()
            &&& forall|l4i: L4Index| #![trigger new_c.higher.spec_nonempty_l4(l4i)] new_c.higher.spec_nonempty_l4(l4i) == old_c.higher.spec_nonempty_l4(l4i)
            &&& forall|l4i: L4Index| #![trigger new_c.higher.spec_resolve_mapping_l4(l4i)] new_c.higher.spec_resolve_mapping_l4(l4i) == old_c.higher.spec_resolve_mapping_l4(l4i)
            &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.higher.spec_nonempty_l3(l4i, l3i)] new_c.higher.spec_nonempty_l3(l4i, l3i) == old_c.higher.spec_nonempty_l3(l4i, l3i)
            &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.higher.spec_resolve_mapping_l3(l4i, l3i)]
                new_c.higher.spec_resolve_mapping_l3(l4i, l3i) == old_c.higher.spec_resolve_mapping_l3(l4i, l3i)
            &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.higher.spec_nonempty_1g_l3(l4i, l3i)] new_c.higher.spec_nonempty_1g_l3(l4i, l3i) == old_c.higher.spec_nonempty_1g_l3(l4i, l3i)
            &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.higher.spec_resolve_mapping_1g_l3(l4i, l3i)]
                new_c.higher.spec_resolve_mapping_1g_l3(l4i, l3i) == old_c.higher.spec_resolve_mapping_1g_l3(l4i, l3i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_nonempty_l2(l4i, l3i, l2i)] new_c.spec_nonempty_l2(l4i, l3i, l2i) == old_c.spec_nonempty_l2(l4i, l3i, l2i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_nonempty_2m_l2(l4i, l3i, l2i)] new_c.spec_nonempty_2m_l2(l4i, l3i, l2i) == old_c.spec_nonempty_2m_l2(l4i, l3i, l2i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_nonempty_4k_l1(l4i, l3i, l2i, l1i)]
                new_c.spec_nonempty_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_nonempty_4k_l1(l4i, l3i, l2i, l1i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId| #![trigger new_c.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                new_c.window_locked_by_thread(l4i, l3i, l2i, thread_id) == old_c.window_locked_by_thread(l4i, l3i, l2i, thread_id)
        }),
        ({
            let old_pci = old(pagetable_map).spec_index(pagetable_ptr).view().higher.pci;
            let new_pci = final(pagetable_map).spec_index(pagetable_ptr).view().higher.pci;
            let f = old_pci.spec_entry(index as int).bdf;
            &&& new_pci.view() == old_pci.view().insert(f, if add { old_pci.view()[f].insert(m) } else { old_pci.view()[f].remove(m) })
            &&& new_pci.view().dom() == old_pci.view().dom()
            &&& forall|g: PciBdf, n: PciBarMapping| #![trigger new_pci.view()[g].contains(n)] new_pci.view().dom().contains(g)
                ==> new_pci.view()[g].contains(n) == if g == f { if add { old_pci.view()[g].contains(n) || n == m } else { old_pci.view()[g].contains(n) && n != m } } else { old_pci.view()[g].contains(n) }
            &&& new_pci.mapping_counts() == old_pci.mapping_counts().insert(f, if add { (old_pci.mapping_counts()[f] + 1) as nat } else { (old_pci.mapping_counts()[f] - 1) as nat })
            &&& forall|j: int| #![trigger new_pci.spec_entry(j)] new_pci.spec_entry(j).used == old_pci.spec_entry(j).used && new_pci.spec_entry(j).bdf == old_pci.spec_entry(j).bdf
            &&& forall|g: PciBdf| #![trigger new_pci.index_of(g)] new_pci.index_of(g) == old_pci.index_of(g)
        }),
{
    proof {
        pagetable_perms_wf_implies_map_perms_wf(*pagetable_map); pagetable_perms_wf_at(*pagetable_map, pagetable_ptr);
        pagetable_map.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
    }
    let pagetable = pagetable_map.borrow_mut_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(lctx), Tracked(pagetable_lock_perm));
    if add { pagetable.higher.pci.add_mapping(index, Ghost(m)); } else { pagetable.higher.pci.remove_mapping(index, Ghost(m)); }
    proof {
        assert(pagetable_map_update_pci_mapping_eof_transition_framing(*old(pagetable_map), *pagetable_map, *pt_lower, pagetable_ptr)) by {
            reveal(pagetable_map_update_pci_mapping_eof_transition_framing);
        };
        pagetable_map_update_pci_mapping_eof(*old(pagetable_map), *pagetable_map, *pt_lower, pagetable_ptr, lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id());
    }
}
}
