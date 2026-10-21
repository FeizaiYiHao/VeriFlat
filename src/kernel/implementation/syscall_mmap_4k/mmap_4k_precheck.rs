use vstd::prelude::*;

use crate::*;

verus! {
/// Result of the PageTable checks that precede construction for mmap(4K).
pub(super) enum Mmap4kPrecheck {
    Ready,
    Invalid,
    InUse,
}

    /// Check the range's inclusive index interval for 4K leaves and each of its pages for a covering 2M or 1G leaf, under a
    /// read or write lock on the pagetable; under a read lock the caller holds the range's 2M windows. Only an interval known
    /// to hold a 4K leaf is scanned for its first leaf, which is returned as the witness, so every read entry lies in the
    /// interval. No krnl or LocalContext state changes.
    pub(super) fn mmap_4k_precheck(krnl: &KernelK, range: &VaRange4K, pagetable_ptr: RwLockPageTableRoot, Tracked(lctx): Tracked<&LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>)
        -> (ret: (Mmap4kPrecheck, Ghost<Option<(L4Index, L3Index, L2Index, L1Index)>>))
        requires
            krnl.inv(),
            krnl.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
            range.wf(),
            range.len > 0,
            krnl.pt_mp.dom().contains(pagetable_ptr),
            pagetable_lock_perm.thread_id() == lctx.thread_id(),
            pagetable_lock_perm.state() is WriteLock || pagetable_lock_perm.state() is ReadLock,
            pagetable_lock_perm.state() is WriteLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_lock_perm.state() is WriteLock ==> pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            pagetable_lock_perm.state() is ReadLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
            pagetable_lock_perm.state() is ReadLock ==> krnl.pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), pagetable_lock_perm.lock_id()),
        ensures
            ret.0 is Ready ==> {
                let pagetable = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
                let end_va = range.view().spec_index((range.len - 1) as int);
                &&& pagetable.kernel_l4_end() <= spec_v2l4index(range.start)
                &&& pagetable.spec_mapping_4k_va_range_empty(range.start, end_va)
                &&& pagetable.spec_mapping_4k_va_range_buildable(range)
                &&& forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < range.len ==> {
                    let indices = spec_va2index(range.view().spec_index(j));
                    &&& !pagetable.mapping_1g().dom().contains(spec_index2va((indices.0, indices.1, 0, 0)))
                    &&& !pagetable.mapping_2m().dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0)))
                }
            },
            (ret.0 is Invalid) == (spec_va2index(range.start).0 < krnl.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end),
            !(ret.0 is Invalid) ==> {
                let pagetable = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
                let end_va = range.view().spec_index((range.len - 1) as int);
                (ret.0 is InUse) == !(pagetable.spec_mapping_4k_range_empty(spec_va2index(range.start), spec_va2index(end_va))
                    && forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < range.len ==> {
                        let indices = spec_va2index(range.view().spec_index(j));
                        &&& !pagetable.mapping_1g().dom().contains(spec_index2va((indices.0, indices.1, 0, 0)))
                        &&& !pagetable.mapping_2m().dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0)))
                        &&& !pagetable.mapping_4k().dom().contains(range.view().spec_index(j))
                    })
            },
            ret.1@ is Some ==> {
                let found = ret.1@->Some_0;
                &&& ret.0 is InUse
                &&& pei_valid(found.0) && pei_valid(found.1) && pei_valid(found.2) && pei_valid(found.3)
                &&& spec_l4_index_path_le(spec_va2index(range.start), found)
                &&& spec_l4_index_path_le(found, spec_va2index(range.view().spec_index((range.len - 1) as int)))
                &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(spec_index2va(found))
            },
            ret.0 is InUse && ret.1@ is None ==> pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).spec_mapping_4k_range_empty(spec_va2index(range.start),
                spec_va2index(range.view().spec_index((range.len - 1) as int))),
    {
        let range_len = range.len;
        let range_start = range.start;
        let end_index = range_len - 1;
        let end_va = range.index(end_index);
        assert(end_va == spec_va_add_range(range_start, end_index)) by { range.va_range_lemma(); };
        let start_indices = va2index(range_start);
        proof {
            assert(krnl.pt_mp.perms_wf() && krnl.pt_mp.spec_index(pagetable_ptr).inv()) by { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); };
            assert(krnl.pt_lower.view().dom().contains(pagetable_ptr) && pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).wf()) by {
                pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
            };
        }
        let pagetable = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
        let tracked lower = krnl.pt_lower.borrow().tracked_borrow(pagetable_ptr);
        if start_indices.0 < pagetable.kernel_l4_end { return (Mmap4kPrecheck::Invalid, Ghost(None)); }
        if !pagetable.mapping_4k_va_range_empty(Tracked(lower), range_start, end_va) {
            proof { broadcast use spec_va_4k_valid_index_roundtrip; }
            let found = pagetable.next_mapped_4k_from(Tracked(lower), start_indices);
            return (Mmap4kPrecheck::InUse, Ghost(found));
        }
        if !pagetable.mapping_4k_va_range_buildable(Tracked(lower), range) { return (Mmap4kPrecheck::InUse, Ghost(None)); }
        (Mmap4kPrecheck::Ready, Ghost(None))
    }
}
