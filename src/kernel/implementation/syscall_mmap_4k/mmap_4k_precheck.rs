use vstd::prelude::*;

use crate::*;

verus! {

/// Result of the PageTable checks that precede construction for mmap(4K).
pub(super) enum Mmap4kPrecheck {
    Ready,
    Invalid,
    InUse,
}

    /// Check the entire inclusive VA interval for existing abstract 4K
    /// mappings. No krnl or LocalContext state changes.
    pub(super) fn mmap_4k_precheck(
        krnl: &KernelK,
        range: &VaRange4K,
        pagetable_ptr: RwLockPageTableRoot,
        Tracked(lctx): Tracked<&LocalContext>,
        Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: Mmap4kPrecheck)
        requires
            krnl.inv(),
            krnl.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
            range.wf(),
            range.len > 0,
            krnl.pt_mp.dom().contains(pagetable_ptr),
            typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_lock_perm.state() is WriteLock,
            pagetable_lock_perm.thread_id() == lctx.thread_id(),
            pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        ensures
            ret is Ready ==> { let end_va = range.view().spec_index((range.len - 1) as int); &&& krnl.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(range.start) &&& krnl.pt_mp.spec_index(pagetable_ptr).view().spec_mapping_4k_va_range_empty(range.start, end_va) &&& krnl.pt_mp.spec_index(pagetable_ptr).view().spec_mapping_4k_va_range_buildable(range) },
            ret is Invalid ==> spec_va2index(range.start).0 < krnl.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end,
            ret is InUse ==> { let end_va = range.view().spec_index((range.len - 1) as int); &&& krnl.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= spec_va2index(range.start).0 &&& (!krnl.pt_mp.spec_index(pagetable_ptr).view().spec_mapping_4k_range_empty(spec_va2index(range.start), spec_va2index(end_va)) || !krnl.pt_mp.spec_index(pagetable_ptr).view().spec_mapping_4k_va_range_buildable(range)) },
    {
        let range_len = range.len;
        let range_start = range.start;
        let end_index = range_len - 1;
        let end_va = range.index(end_index);
        assert(end_va == spec_va_add_range(range_start, end_index)) by { range.va_range_lemma(); };
        assert(range_start <= end_va) by { range.va_range_lemma(); };
        let start_indices = va2index(range_start);
        proof {
            assert(
                krnl.pt_mp.perms_wf()
                    && krnl.pt_mp.spec_index(pagetable_ptr).inv()
            ) by { reveal(pagetable_perms_wf); };
        }
        let pagetable = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
        if start_indices.0 < pagetable.kernel_l4_end {
            return Mmap4kPrecheck::Invalid;
        }
        if !pagetable.mapping_4k_va_range_empty(range_start, end_va) {
            return Mmap4kPrecheck::InUse;
        }
        if !pagetable.mapping_4k_va_range_buildable(range) {
            return Mmap4kPrecheck::InUse;
        }
        Mmap4kPrecheck::Ready
    }

}
