use vstd::prelude::*;

use crate::*;

verus! {
/// Result of the PageTable checks that precede construction for mmap(2M).
pub(super) enum Mmap2mPrecheck {
    Ready,
    Invalid,
    InUse,
}

/// Check each page of the 2M range for a covering 1G leaf, a 2M leaf, or a 4K leaf in its 2M window, under a read or write lock
/// on the pagetable; under a read lock the caller holds the range's 2M windows. A free range is also stated per 2M window of its
/// covering 4K range `cover`. The first page found in use is returned as `at`, with the first 4K leaf of its window as the
/// witness when the window holds one. No krnl or LocalContext state changes.
pub(super) fn mmap_2m_precheck(krnl: &KernelK, range: &VaRange2M, cover: &VaRange4K, pagetable_ptr: RwLockPageTableRoot, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(pagetable_lock_perm): Tracked<&LockPerm>) -> (ret: (Mmap2mPrecheck, Ghost<Option<(L4Index, L3Index, L2Index, L1Index)>>, Ghost<int>))
    requires
        krnl.inv(),
        krnl.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        range.wf(),
        range.len > 0,
        *cover == range.covering_4k_range(),
        cover.wf(),
        krnl.pt_mp.dom().contains(pagetable_ptr),
        pagetable_lock_perm.thread_id() == lctx.thread_id(),
        pagetable_lock_perm.state() is WriteLock || pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.state() is WriteLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock ==> pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        pagetable_lock_perm.state() is ReadLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        pagetable_lock_perm.state() is ReadLock ==> krnl.pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), pagetable_lock_perm.lock_id()),
    ensures
        (ret.0 is Invalid) == (spec_v2l4index(range.start) < whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).kernel_l4_end()),
        ret.0 is Ready ==> forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len ==> {
            let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
            let idx = spec_va2index(range.view()[j]);
            &&& !table.mapping_1g().dom().contains(spec_index2va((idx.0, idx.1, 0, 0)))
            &&& !table.mapping_2m().dom().contains(range.view()[j])
            &&& forall|l1i: L1Index| #![trigger table.mapping_4k().dom().contains(spec_index2va((idx.0, idx.1, idx.2, l1i)))] pei_valid(l1i)
                ==> !table.mapping_4k().dom().contains(spec_index2va((idx.0, idx.1, idx.2, l1i)))
        },
        ret.0 is Ready ==> forall|w: WindowVa| #![trigger va_range_2m_windows(range.covering_4k_range()).contains(w)] va_range_2m_windows(range.covering_4k_range()).contains(w) ==> {
            let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
            &&& !table.mapping_2m().dom().contains(w.va)
            &&& forall|l1i: L1Index| #![trigger table.mapping_4k().dom().contains(spec_index2va((spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va), l1i)))]
                pei_valid(l1i) ==> !table.mapping_4k().dom().contains(spec_index2va((spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va), l1i)))
        },
        ret.0 is InUse ==> {
            let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
            let at_va = range.view()[ret.2.view()];
            let at_idx = spec_va2index(at_va);
            &&& 0 <= ret.2.view() < range.len
            &&& ret.1.view() is Some ==> {
                let f = ret.1.view()->Some_0;
                &&& f.0 == at_idx.0 && f.1 == at_idx.1 && f.2 == at_idx.2 && pei_valid(f.3)
                &&& table.mapping_4k().dom().contains(spec_index2va(f))
            }
            &&& ret.1.view() is None ==> table.mapping_2m().dom().contains(at_va) || table.mapping_1g().dom().contains(spec_index2va((at_idx.0, at_idx.1, 0, 0)))
        },
{
    let range_len = range.len;
    let range_start = range.start;
    proof {
        assert(krnl.pt_mp.perms_wf() && krnl.pt_mp.spec_index(pagetable_ptr).inv()) by { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); };
        assert(krnl.pt_lower.view().dom().contains(pagetable_ptr) && whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).wf()) by {
            pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
        };
    }
    let pagetable = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = krnl.pt_lower.borrow().tracked_borrow(pagetable_ptr);
    let start_indices = va2index(range_start);
    if start_indices.0 < pagetable.kernel_l4_end { return (Mmap2mPrecheck::Invalid, Ghost(None), Ghost(0)); }
    proof {
        broadcast use spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid;
        spec_va_4k_index_roundtrip_at(range_start, start_indices.0, start_indices.1, start_indices.2, 0usize);
    }
    let mut i: usize = 0;
    while i < range_len
        invariant
            (WholePageTable { higher: *pagetable, lower: *lower }) == whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr),
            (WholePageTable { higher: *pagetable, lower: *lower }).wf(),
            range.wf(),
            range_len == range.len,
            range_start == range.start,
            i <= range_len,
            spec_va_4k_valid(range_start),
            pagetable.kernel_l4_end <= spec_v2l4index(range_start),
            forall|j: int| #![trigger range.view()[j]] 0 <= j < i ==> {
                let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
                let idx = spec_va2index(range.view()[j]);
                &&& !table.mapping_1g().dom().contains(spec_index2va((idx.0, idx.1, 0, 0)))
                &&& !table.mapping_2m().dom().contains(range.view()[j])
                &&& forall|l1i: L1Index| #![trigger table.mapping_4k().dom().contains(spec_index2va((idx.0, idx.1, idx.2, l1i)))] pei_valid(l1i)
                    ==> !table.mapping_4k().dom().contains(spec_index2va((idx.0, idx.1, idx.2, l1i)))
            },
            forall|w: WindowVa| #![trigger va_range_2m_windows(range.covering_4k_range()).contains(w)]
                va_range_2m_windows(range.covering_4k_range()).contains(w) && 0 < i && spec_l4_index_path_le(spec_va2index(w.va), spec_va2index(range.view()[i - 1])) ==> {
                let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
                &&& !table.mapping_2m().dom().contains(w.va)
                &&& forall|l1i: L1Index| #![trigger table.mapping_4k().dom().contains(spec_index2va((spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va), l1i)))]
                    pei_valid(l1i) ==> !table.mapping_4k().dom().contains(spec_index2va((spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va), l1i)))
            },
        decreases range_len - i,
    {
        let va = range.index(i);
        let (l4i, l3i, l2i, _) = va2index(va);
        proof {
            broadcast use spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid;
            range.wf_implies_view_index_is_start_plus_offset();
            spec_va_4k_index_roundtrip_at(va, l4i, l3i, l2i, 0usize);
            spec_v2l4index_monotonic(range_start, va);
            if 0 < i {
                let prev_va = range.view()[i - 1];
                assert((spec_v2l4index(va) == spec_v2l4index(prev_va) && spec_v2l3index(va) == spec_v2l3index(prev_va) && spec_v2l2index(va) == add(spec_v2l2index(prev_va), 1usize))
                    || (spec_v2l4index(va) == spec_v2l4index(prev_va) && spec_v2l3index(va) == add(spec_v2l3index(prev_va), 1usize) && spec_v2l2index(va) == 0 && spec_v2l2index(prev_va) == 511)
                    || (spec_v2l4index(va) == add(spec_v2l4index(prev_va), 1usize) && spec_v2l3index(va) == 0 && spec_v2l2index(va) == 0 && spec_v2l3index(prev_va) == 511
                        && spec_v2l2index(prev_va) == 511)) by (bit_vector)
                    requires
                        spec_va_2m_valid(prev_va),
                        spec_va_2m_valid(va),
                        va == add(prev_va, 0x200000usize);
            }
        }
        if let Some(l4_entry) = pagetable.get_entry_l4(l4i) {
            if pagetable.get_entry_1g_l3(l4i, l3i, &l4_entry).is_some() {
                proof { pagetable.wf_mapping_1g_at(l4i, l3i); }
                return (Mmap2mPrecheck::InUse, Ghost(None), Ghost(i as int));
            }
            if let Some(l3_entry) = pagetable.get_entry_l3(l4i, l3i, &l4_entry) {
                if pagetable.get_entry_2m_l2(Tracked(lower), l4i, l3i, l2i, &l3_entry).is_some() {
                    proof { (WholePageTable { higher: *pagetable, lower: *lower }).wf_mapping_2m_at(l4i, l3i, l2i); }
                    return (Mmap2mPrecheck::InUse, Ghost(None), Ghost(i as int));
                }
            }
        }
        let end_va = index2va((l4i, l3i, l2i, 511));
        proof {
            pagetable.wf_mapping_1g_at(l4i, l3i); (WholePageTable { higher: *pagetable, lower: *lower }).wf_mapping_2m_at(l4i, l3i, l2i);
            spec_va_4k_index_roundtrip_at(end_va, l4i, l3i, l2i, 511usize);
            assert(((l4i as usize) << 39 | (l3i as usize) << 30 | (l2i as usize) << 21 | (0usize) << 12) <= ((l4i as usize) << 39 | (l3i as usize) << 30 | (l2i as usize) << 21 | (511usize) << 12))
                by (bit_vector) requires l4i < 512, l3i < 512, l2i < 512;
        }
        if !pagetable.mapping_4k_va_range_empty(Tracked(lower), va, end_va) {
            let found = pagetable.next_mapped_4k_from(Tracked(lower), (l4i, l3i, l2i, 0));
            return (Mmap2mPrecheck::InUse, Ghost(found), Ghost(i as int));
        }
        i = i + 1;
    }
    proof {
        broadcast use spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid;
        range.wf_implies_view_index_is_start_plus_offset(); cover.wf_implies_view_index_is_start_plus_offset();
        let last = range.view()[range_len - 1];
        assert(cover.view()[cover.len - 1] == add(last, 0x1ff000usize)) by (nonlinear_arith)
            requires
                cover.view()[cover.len - 1] == spec_va_add_range(range_start, (cover.len - 1) as usize),
                last == spec_va_add_range_2m(range_start, (range_len - 1) as usize),
                cover.len == range_len * 512,
                0 < range_len <= usize::MAX / 0x200000,
                range_start < usize::MAX - range_len * 0x200000;
        assert(spec_v2l4index(add(last, 0x1ff000usize)) == spec_v2l4index(last) && spec_v2l3index(add(last, 0x1ff000usize)) == spec_v2l3index(last)
            && spec_v2l2index(add(last, 0x1ff000usize)) == spec_v2l2index(last)) by (bit_vector) requires spec_va_2m_valid(last);
    }
    (Mmap2mPrecheck::Ready, Ghost(None), Ghost(0))
}
} // verus!
