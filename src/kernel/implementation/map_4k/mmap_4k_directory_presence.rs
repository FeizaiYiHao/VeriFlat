use vstd::prelude::*;

use crate::*;

verus! {
    /// Read which directory levels above the 4K leaf of `indices` are present.
    pub(super) fn mmap_4k_directory_presence(
        krnl: &KernelK, pagetable_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index), Tracked(lctx): Tracked<&LocalContext>,
        Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (bool, bool, bool))
        requires
            typed_lock_maps_aligned(krnl, lctx),
            krnl.pt_mp.perms_wf(),
            krnl.pt_mp.dom().contains(pagetable_ptr),
            krnl.pt_mp.spec_index(pagetable_ptr).inv(),
            typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_lock_perm.state() is WriteLock,
            pagetable_lock_perm.thread_id() == lctx.thread_id(),
            pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            krnl.pt_mp.spec_index(pagetable_ptr).view().wf(),
            krnl.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= indices.0 && pei_valid(indices.0),
            pei_valid(indices.1),
            pei_valid(indices.2),
        ensures
            ret.0 == (krnl.pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l4(indices.0) is Some),
            ret.1 == (ret.0 && krnl.pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) is Some),
            ret.2 == (ret.1 && krnl.pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some),
    {
        let pagetable = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(lctx), Tracked(pagetable_lock_perm));
        match pagetable.get_entry_l4(indices.0) {
            None => (false, false, false),
            Some(l4_entry) => match pagetable.get_entry_l3(indices.0, indices.1, &l4_entry) {
                None => (true, false, false),
                Some(l3_entry) => (true, true, pagetable.get_entry_l2(indices.0, indices.1, indices.2, &l3_entry).is_some()),
            },
        }
    }
} // verus!
