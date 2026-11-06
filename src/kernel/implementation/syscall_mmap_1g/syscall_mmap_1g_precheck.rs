use vstd::prelude::*;
use crate::*;

verus! {
/// Whether no 1G, 2M, or 4K leaf of the pagetable `pagetable_ptr` maps inside a 1G slot of `range`, read under this thread's write lock on it. When one does, `ret.1` is the first such page, with the 2M leaf `ret.2` or the 4K leaf `ret.3` of its slot as the witness, or its 1G leaf when
/// both are None. No krnl or LocalContext state changes.
pub(super) fn mmap_1g_precheck(krnl: &KernelK, range: &VaRange1G, pagetable_ptr: RwLockPageTableRoot, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(pagetable_lock_perm): Tracked<&LockPerm>) -> (ret: (bool, Ghost<int>, Ghost<Option<L2Index>>, Ghost<Option<(L4Index, L3Index, L2Index, L1Index)>>))
    requires
        krnl.inv(),
        range.wf(),
        krnl.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        krnl.pt_mp.dom().contains(pagetable_ptr),
        krnl.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end == KERNEL_MEM_END_L4INDEX,
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == lctx.thread_id(),
        pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
    ensures
        ret.0 ==> forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len ==> {
            let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
            let idx = spec_va2index(range.view()[j]);
            &&& !table.mapping_1g().dom().contains(range.view()[j])
            &&& forall|l2i: L2Index| #![trigger table.mapping_2m().dom().contains(spec_index2va((idx.0, idx.1, l2i, 0)))] pei_valid(l2i)
                ==> !table.mapping_2m().dom().contains(spec_index2va((idx.0, idx.1, l2i, 0)))
            &&& forall|l2i: L2Index, l1i: L1Index| #![trigger table.mapping_4k().dom().contains(spec_index2va((idx.0, idx.1, l2i, l1i)))] pei_valid(l2i) && pei_valid(l1i)
                ==> !table.mapping_4k().dom().contains(spec_index2va((idx.0, idx.1, l2i, l1i)))
        },
        !ret.0 ==> {
            let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
            let at_va = range.view()[ret.1@];
            let idx = spec_va2index(at_va);
            &&& 0 <= ret.1@ < range.len
            &&& ret.2@ is Some ==> pei_valid(ret.2@->Some_0) && table.mapping_2m().dom().contains(spec_index2va((idx.0, idx.1, ret.2@->Some_0, 0)))
            &&& ret.3@ is Some ==> {
                let f = ret.3@->Some_0;
                &&& f.0 == idx.0 && f.1 == idx.1 && pei_valid(f.2) && pei_valid(f.3)
                &&& table.mapping_4k().dom().contains(spec_index2va(f))
            }
            &&& ret.2@ is None && ret.3@ is None ==> table.mapping_1g().dom().contains(at_va)
        },
{
    proof {
        assert(krnl.pt_mp.perms_wf() && krnl.pt_mp.spec_index(pagetable_ptr).inv()) by { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); };
        assert(krnl.pt_lower.view().dom().contains(pagetable_ptr) && whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).wf()) by {
            pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
        };
    }
    let pagetable = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = krnl.pt_lower.borrow().tracked_borrow(pagetable_ptr);
    let ghost table = WholePageTable { higher: *pagetable, lower: *lower };
    let mut i: usize = 0;
    while i < range.len
        invariant
            table == whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr),
            table.higher == *pagetable,
            table.lower == *lower,
            table.wf(),
            range.wf(),
            i <= range.len,
            pagetable.kernel_l4_end == KERNEL_MEM_END_L4INDEX,
            forall|j: int| #![trigger range.view()[j]] 0 <= j < i ==> {
                let idx = spec_va2index(range.view()[j]);
                &&& !table.mapping_1g().dom().contains(range.view()[j])
                &&& forall|l2i: L2Index| #![trigger table.mapping_2m().dom().contains(spec_index2va((idx.0, idx.1, l2i, 0)))] pei_valid(l2i)
                    ==> !table.mapping_2m().dom().contains(spec_index2va((idx.0, idx.1, l2i, 0)))
                &&& forall|l2i: L2Index, l1i: L1Index| #![trigger table.mapping_4k().dom().contains(spec_index2va((idx.0, idx.1, l2i, l1i)))] pei_valid(l2i) && pei_valid(l1i)
                    ==> !table.mapping_4k().dom().contains(spec_index2va((idx.0, idx.1, l2i, l1i)))
            },
        decreases range.len - i,
    {
        let va = range.index(i);
        let (l4i, l3i, _, _) = va2index(va);
        proof { spec_va_1g_valid_index_roundtrip(va); spec_va_4k_index_roundtrip_at(va, l4i, l3i, 0usize, 0usize); pagetable.wf_mapping_1g_at(l4i, l3i); }
        let mut l3_entry: Option<PageEntry> = None;
        if let Some(l4_entry) = pagetable.get_entry_l4(l4i) {
            if pagetable.get_entry_1g_l3(l4i, l3i, &l4_entry).is_some() { return (false, Ghost(i as int), Ghost(None), Ghost(None)); }
            l3_entry = pagetable.get_entry_l3(l4i, l3i, &l4_entry);
        }
        let mut l2i: usize = 0;
        while l2i < 512
            invariant
                table == whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr),
                table.higher == *pagetable,
                table.lower == *lower,
                table.wf(),
                range.wf(),
                i < range.len,
                va == range.view()[i as int],
                spec_va2index(va) == (l4i, l3i, 0usize, 0usize),
                KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i),
                pagetable.kernel_l4_end == KERNEL_MEM_END_L4INDEX,
                l3_entry == pagetable.spec_resolve_mapping_l3(l4i, l3i),
                l2i <= 512,
                forall|k: L2Index| #![trigger table.mapping_2m().dom().contains(spec_index2va((l4i, l3i, k, 0)))] pei_valid(k) && k < l2i ==> !table.mapping_2m().dom().contains(spec_index2va((l4i, l3i, k, 0))),
            decreases 512 - l2i,
        {
            proof { table.wf_mapping_2m_at(l4i, l3i, l2i); }
            if let Some(l3e) = &l3_entry {
                if pagetable.get_entry_2m_l2(Tracked(lower), l4i, l3i, l2i, l3e).is_some() { return (false, Ghost(i as int), Ghost(Some(l2i)), Ghost(None)); }
            }
            l2i = l2i + 1;
        }
        let end_va = index2va((l4i, l3i, 511, 511));
        proof {
            spec_va_4k_index_roundtrip_at(end_va, l4i, l3i, 511usize, 511usize);
            assert(((l4i as usize) << 39 | (l3i as usize) << 30 | (0usize) << 21 | (0usize) << 12) <= ((l4i as usize) << 39 | (l3i as usize) << 30 | (511usize) << 21 | (511usize) << 12))
                by (bit_vector) requires l4i < 512, l3i < 512;
        }
        if !pagetable.mapping_4k_va_range_empty(Tracked(lower), va, end_va) {
            let found = pagetable.next_mapped_4k_from(Tracked(lower), (l4i, l3i, 0, 0));
            return (false, Ghost(i as int), Ghost(None), Ghost(found));
        }
        i = i + 1;
    }
    (true, Ghost(0), Ghost(None), Ghost(None))
}
} // verus!
