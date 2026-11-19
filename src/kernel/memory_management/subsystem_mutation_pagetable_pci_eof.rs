use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use crate::kernel::iommu_tlb_management::pci_ownership_mutation_eof::update_pci_entry_eof_table_wf;

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
    update_pci_entry_eof_table_wf(whole_pagetable(pre_pt, pt_lower, pagetable_ptr), whole_pagetable(post_pt, pt_lower, pagetable_ptr));
    assert(pagetable_perms_wf(post_pt)) by { lock_op_implies_pagetable_perms_wf_preserved_forall(); };
    assert(post_pt.typed_lock_map_aligned(pagetable_lock_map, thread_id)) by {
        reveal(LockedMap::typed_lock_map_aligned);
        assert(post_pt.spec_index(pagetable_ptr).locked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).locked_by_thread(thread_id));
        assert(post_pt.spec_index(pagetable_ptr).rlocked_by_thread(thread_id) == pre_pt.spec_index(pagetable_ptr).rlocked_by_thread(thread_id));
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
