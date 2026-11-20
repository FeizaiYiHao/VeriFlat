use vstd::prelude::*;
use crate::*;

verus! {
/// Whether no 1G, 2M, or 4K leaf of the write-held page table `pagetable_ptr` covers the 4K page `va`. No krnl or LocalContext state
/// changes.
pub(super) fn pci_bar_va_4k_free(krnl: &KernelK, pagetable_ptr: RwLockPageTableRoot, va: VAddr, Tracked(lctx): Tracked<&LocalContext>, Tracked(pagetable_perm): Tracked<&LockPerm>)
    -> (ret: bool)
    requires
        krnl.inv(),
        krnl.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        krnl.pt_mp.dom().contains(pagetable_ptr),
        krnl.pt_mp.spec_index(pagetable_ptr).view().higher.kernel_l4_end == KERNEL_MEM_END_L4INDEX,
        va_4k_valid(va),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_perm.state() is WriteLock,
        pagetable_perm.thread_id() == lctx.thread_id(),
        pagetable_perm.lock_id() == krnl.pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
    ensures
        ({
            let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
            let idx = spec_va2index(va);
            ret == (!table.mapping_1g().dom().contains(spec_index2va((idx.0, idx.1, 0, 0))) && !table.mapping_2m().dom().contains(spec_index2va((idx.0, idx.1, idx.2, 0)))
                && !table.mapping_4k().dom().contains(va))
        }),
{
    let indices = va2index(va);
    proof {
        let c = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
        spec_va_4k_index_roundtrip_at(va, indices.0, indices.1, indices.2, indices.3);
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
        c.wf_mapping_4k_at(indices.0, indices.1, indices.2, indices.3); c.wf_mapping_2m_at(indices.0, indices.1, indices.2); c.higher.wf_mapping_1g_at(indices.0, indices.1);
    }
    let pt = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(lctx), Tracked(pagetable_perm));
    let tracked lower = krnl.pt_lower.borrow().tracked_borrow(pagetable_ptr);
    let l4 = match pt.higher.get_entry_l4(indices.0) { Some(e) => e, None => { return true; } };
    if pt.higher.get_entry_1g_l3(indices.0, indices.1, &l4).is_some() { return false; }
    let l3 = match pt.higher.get_entry_l3(indices.0, indices.1, &l4) { Some(e) => e, None => { return true; } };
    if pt.higher.get_entry_2m_l2(Tracked(lower), indices.0, indices.1, indices.2, &l3).is_some() { return false; }
    let l2 = match pt.higher.get_entry_l2(Tracked(lower), indices.0, indices.1, indices.2, &l3) { Some(e) => e, None => { return true; } };
    pt.higher.get_entry_l1(Tracked(lower), indices.0, indices.1, indices.2, indices.3, &l3, &l2).is_none()
}

/// The entry of the PCI function array of the write-held page table `pagetable_ptr` that holds function `bdf`, or None when the
/// table's process does not own it. No krnl or LocalContext state changes.
pub(super) fn pci_bar_owner_entry(krnl: &KernelK, pagetable_ptr: RwLockPageTableRoot, bdf: PciBdf, Tracked(lctx): Tracked<&LocalContext>, Tracked(pagetable_perm): Tracked<&LockPerm>)
    -> (ret: Option<usize>)
    requires
        krnl.inv(),
        krnl.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        krnl.pt_mp.dom().contains(pagetable_ptr),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_perm.state() is WriteLock,
        pagetable_perm.thread_id() == lctx.thread_id(),
        pagetable_perm.lock_id() == krnl.pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
    ensures
        (ret is Some) == krnl.pt_mp.spec_index(pagetable_ptr).view().higher.pci.view().dom().contains(bdf),
        ret matches Some(i) ==> i < PCI_FUNCTIONS_PER_PROCESS && krnl.pt_mp.spec_index(pagetable_ptr).view().higher.pci.spec_entry(i as int).used
            && krnl.pt_mp.spec_index(pagetable_ptr).view().higher.pci.spec_entry(i as int).bdf == bdf,
{
    assert(krnl.pt_mp.perms_wf() && krnl.pt_mp.spec_index(pagetable_ptr).inv()) by { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); };
    let pt = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(lctx), Tracked(pagetable_perm));
    let ret = pt.higher.pci.find(bdf.0, bdf.1, bdf.2);
    proof { if ret is Some { pt.higher.pci.wf_function_at(bdf); } }
    ret
}

/// Whether no 1G or 2M leaf covers the 2M window `va` of the write-held page table `pagetable_ptr` and no 4K leaf maps a VA inside it,
/// and whether the window's L2 entry links an L1 page. No krnl or LocalContext state changes.
pub(super) fn pci_bar_va_2m_free(krnl: &KernelK, pagetable_ptr: RwLockPageTableRoot, va: VAddr, Tracked(lctx): Tracked<&LocalContext>, Tracked(pagetable_perm): Tracked<&LockPerm>)
    -> (ret: (bool, bool))
    requires
        krnl.inv(),
        krnl.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        krnl.pt_mp.dom().contains(pagetable_ptr),
        krnl.pt_mp.spec_index(pagetable_ptr).view().higher.kernel_l4_end == KERNEL_MEM_END_L4INDEX,
        va_2m_valid(va),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_perm.state() is WriteLock,
        pagetable_perm.thread_id() == lctx.thread_id(),
        pagetable_perm.lock_id() == krnl.pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
    ensures
        ({
            let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
            let idx = spec_va2index(va);
            &&& ret.0 == (!table.mapping_1g().dom().contains(spec_index2va((idx.0, idx.1, 0, 0))) && !table.mapping_2m().dom().contains(va)
                && forall|l1i: L1Index| #![trigger table.mapping_4k().dom().contains(spec_index2va((idx.0, idx.1, idx.2, l1i)))] pei_valid(l1i)
                    ==> !table.mapping_4k().dom().contains(spec_index2va((idx.0, idx.1, idx.2, l1i))))
            &&& ret.1 == (table.spec_resolve_mapping_l2(idx.0, idx.1, idx.2) is Some)
        }),
{
    let indices = va2index(va);
    let ghost table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
    proof {
        assert(indices.0 == spec_v2l4index(va) && indices.1 == spec_v2l3index(va) && indices.2 == spec_v2l2index(va) && spec_index2va((indices.0, indices.1, indices.2, 0usize)) == va) by {
            broadcast use spec_va_2m_valid_index_roundtrip;
        };
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
        table.wf_mapping_2m_at(indices.0, indices.1, indices.2); table.higher.wf_mapping_1g_at(indices.0, indices.1);
    }
    let pt = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(lctx), Tracked(pagetable_perm));
    let tracked lower = krnl.pt_lower.borrow().tracked_borrow(pagetable_ptr);
    let mut linked = false;
    if let Some(l4) = pt.higher.get_entry_l4(indices.0) {
        if pt.higher.get_entry_1g_l3(indices.0, indices.1, &l4).is_some() { return (false, false); }
        if let Some(l3) = pt.higher.get_entry_l3(indices.0, indices.1, &l4) {
            if pt.higher.get_entry_2m_l2(Tracked(lower), indices.0, indices.1, indices.2, &l3).is_some() { return (false, false); }
            linked = pt.higher.get_entry_l2(Tracked(lower), indices.0, indices.1, indices.2, &l3).is_some();
        }
    }
    let end_va = index2va((indices.0, indices.1, indices.2, 511));
    proof {
        let (l4i, l3i, l2i) = (indices.0, indices.1, indices.2);
        spec_va_4k_index_roundtrip_at(va, l4i, l3i, l2i, 0usize); spec_va_4k_index_roundtrip_at(end_va, l4i, l3i, l2i, 511usize);
        assert((l4i << 39 | l3i << 30 | l2i << 21 | 0usize << 12) <= (l4i << 39 | l3i << 30 | l2i << 21 | 511usize << 12)) by (bit_vector) requires l4i < 512, l3i < 512, l2i < 512;
    }
    (pt.higher.mapping_4k_va_range_empty(Tracked(lower), va, end_va), linked)
}
} // verus!
