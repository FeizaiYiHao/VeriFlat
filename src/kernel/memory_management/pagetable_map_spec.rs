use vstd::prelude::*;
use crate::*;
use super::*;
verus! {
    /// The whole page table rooted at `root`: the big-lock payload in `pt_mp` and its window half in `pt_lower`.
    pub open spec fn pagetable_c(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, root: RwLockPageTableRoot) -> PageTableC<PT_TYPE> {
        PageTableC { higher: pt_mp.spec_index(root).view(), lower: pt_lower.spec_index(root) }
    }

    #[verifier::opaque]
    pub open spec fn pagetable_perms_wf(pagetable_perms: PageTableLockedMap) -> bool {
        &&& pagetable_perms.perms_wf()
        &&& pagetables_inv(pagetable_perms)
    }

    /// A page table that is not write-locked hides 4K leaves only inside locked 2M windows and hides no 2M or 1G leaf:
    /// unmap clears present bits and reclaims those leaves under the table's write lock or the leaf's window lock.
    #[verifier::opaque]
    pub open spec fn pagetable_hidden_leaves_only_when_locked(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap) -> bool {
        forall|pagetable_p: RwLockPageTableRoot|
            #![trigger pt_mp.spec_index(pagetable_p).locking_thread()]
            pt_mp.dom().contains(pagetable_p) && !(pt_mp.spec_index(pagetable_p).locking_thread() is Write) ==> pagetable_c(pt_mp, pt_lower, pagetable_p).hidden_leaves_in_locked_windows()
    }

    pub proof fn pagetable_hidden_leaves_only_when_locked_at(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot)
        requires
            pagetable_hidden_leaves_only_when_locked(pt_mp, pt_lower),
            pt_mp.dom().contains(pagetable_ptr),
        ensures !(pt_mp.spec_index(pagetable_ptr).locking_thread() is Write) ==> pagetable_c(pt_mp, pt_lower, pagetable_ptr).hidden_leaves_in_locked_windows(),
    { reveal(pagetable_hidden_leaves_only_when_locked); }

    /// A page table that is not write-locked lists stale CPUs only for locked 2M windows of its own L2 pages: unmap lists a
    /// window before it hides a leaf there and drops the entry before it releases the window.
    #[verifier::opaque]
    pub open spec fn pagetable_window_stale_cpus_only_when_locked(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap) -> bool {
        forall|pagetable_p: RwLockPageTableRoot|
            #![trigger pt_mp.spec_index(pagetable_p).locking_thread()]
            pt_mp.dom().contains(pagetable_p) && !(pt_mp.spec_index(pagetable_p).locking_thread() is Write) ==> forall|p: PageMapPtr, i: L2Index|
                #![trigger pagetable_c(pt_mp, pt_lower, pagetable_p).lower.window_stale_cpus.dom().contains((p, i))]
                pagetable_c(pt_mp, pt_lower, pagetable_p).lower.window_stale_cpus.dom().contains((p, i)) ==> {
                    &&& pagetable_c(pt_mp, pt_lower, pagetable_p).lower.l2_lock.dom().contains(p)
                    &&& pei_valid(i)
                    &&& pagetable_c(pt_mp, pt_lower, pagetable_p).lower.l2_lock_of(p).locked(i)
                }
    }

    pub proof fn pagetable_window_stale_cpus_only_when_locked_at(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, p: PageMapPtr, i: L2Index)
        requires pagetable_window_stale_cpus_only_when_locked(pt_mp, pt_lower), pt_mp.dom().contains(pagetable_ptr),
        ensures
            !(pt_mp.spec_index(pagetable_ptr).locking_thread() is Write) && pagetable_c(pt_mp, pt_lower, pagetable_ptr).lower.window_stale_cpus.dom().contains((p, i)) ==> {
                &&& pagetable_c(pt_mp, pt_lower, pagetable_ptr).lower.l2_lock.dom().contains(p)
                &&& pei_valid(i)
                &&& pagetable_c(pt_mp, pt_lower, pagetable_ptr).lower.l2_lock_of(p).locked(i)
            },
    { reveal(pagetable_window_stale_cpus_only_when_locked); }

    /// Every page table has its window half, and the two halves together form a well-formed table.
    #[verifier::opaque]
    pub open spec fn pagetable_lower_wf(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap) -> bool {
        &&& pt_lower.dom() == pt_mp.dom()
        &&& forall|pagetable_ptr: RwLockPageTableRoot|
            #![trigger pagetable_c(pt_mp, pt_lower, pagetable_ptr)]
            pt_mp.dom().contains(pagetable_ptr) ==> pagetable_c(pt_mp, pt_lower, pagetable_ptr).wf()
    }

    pub proof fn pagetable_lower_wf_at(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot)
        requires
            pagetable_lower_wf(pt_mp, pt_lower),
            pt_mp.dom().contains(pagetable_ptr),
        ensures
            pt_lower.dom().contains(pagetable_ptr),
            pagetable_c(pt_mp, pt_lower, pagetable_ptr).wf(),
    { reveal(pagetable_lower_wf); }

    /// A thread that holds a 2M window of a page table holds that table's big lock.
    #[verifier::opaque]
    pub open spec fn pagetable_window_holders_hold_pagetable(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap) -> bool {
        forall|pagetable_ptr: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger pagetable_c(pt_mp, pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            pt_mp.dom().contains(pagetable_ptr) && pagetable_c(pt_mp, pt_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                && pagetable_c(pt_mp, pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) ==> pt_mp.spec_index(pagetable_ptr).locked_by_thread(thread_id)
    }

    pub proof fn pagetable_window_holders_hold_pagetable_at(
        pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId,
    )
        requires
            pagetable_window_holders_hold_pagetable(pt_mp, pt_lower),
            pt_mp.dom().contains(pagetable_ptr),
        ensures
            pagetable_c(pt_mp, pt_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                && pagetable_c(pt_mp, pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) ==> pt_mp.spec_index(pagetable_ptr).locked_by_thread(thread_id),
    { reveal(pagetable_window_holders_hold_pagetable); }

    /// The ghost slot of a write-locked page table's big lock holds a copy of its window half.
    pub open spec fn pagetable_lower_backup_wf(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap) -> bool {
        forall|pagetable_ptr: RwLockPageTableRoot|
            #![trigger pt_mp.spec_index(pagetable_ptr)]
            pt_mp.dom().contains(pagetable_ptr) && pt_mp.spec_index(pagetable_ptr).wlocked() ==> pt_mp.spec_index(pagetable_ptr).view_ghost() == pt_lower.spec_index(pagetable_ptr)
    }

    pub proof fn pagetable_lower_backup_wf_at(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot)
        requires
            pagetable_lower_backup_wf(pt_mp, pt_lower),
            pt_mp.dom().contains(pagetable_ptr),
            pt_mp.spec_index(pagetable_ptr).wlocked(),
        ensures pt_mp.spec_index(pagetable_ptr).view_ghost() == pt_lower.spec_index(pagetable_ptr),
    {}

    /// The held 2M windows of `thread_id` and its typed window map agree: every entry names a well-formed window of a held
    /// page table that `thread_id` has locked, with its exact ordering id, and every window `thread_id` has locked is held.
    #[verifier::opaque]
    pub open spec fn pagetable_window_typed_lock_map_aligned(
        pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>,
        pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId,
    ) -> bool {
        &&& forall|pagetable_ptr: RwLockPageTableRoot, w: WindowVa|
            #![trigger window_lock_map.dom().contains((pagetable_ptr, w))]
            window_lock_map.dom().contains((pagetable_ptr, w)) ==> {
                &&& pt_mp.dom().contains(pagetable_ptr)
                &&& pagetable_lock_map.dom().contains(pagetable_ptr)
                &&& w.wf()
                &&& pagetable_c(pt_mp, pt_lower, pagetable_ptr).kernel_l4_end() <= spec_v2l4index(w.va)
                &&& pagetable_c(pt_mp, pt_lower, pagetable_ptr).window_locked_by_thread(spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va), thread_id)
                &&& window_lock_map.index((pagetable_ptr, w)) == (TypedHeldLock { lock_id: window_lock_id_at(pagetable_ptr, w), mode: TypedLockMode::Write })
            }
        &&& forall|pagetable_ptr: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger pagetable_c(pt_mp, pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            pt_mp.dom().contains(pagetable_ptr) && pagetable_c(pt_mp, pt_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                && pagetable_c(pt_mp, pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) ==> window_lock_map.dom().contains((pagetable_ptr, WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) }))
    }

    pub proof fn pagetable_window_typed_lock_map_aligned_at(
        pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>,
        pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId, pagetable_ptr: RwLockPageTableRoot, w: WindowVa,
    )
        requires
            pagetable_window_typed_lock_map_aligned(pt_mp, pt_lower, window_lock_map, pagetable_lock_map, thread_id),
            window_lock_map.dom().contains((pagetable_ptr, w)),
        ensures
            pt_mp.dom().contains(pagetable_ptr),
            pagetable_lock_map.dom().contains(pagetable_ptr),
            w.wf(),
            pagetable_c(pt_mp, pt_lower, pagetable_ptr).kernel_l4_end() <= spec_v2l4index(w.va),
            pagetable_c(pt_mp, pt_lower, pagetable_ptr).window_locked_by_thread(spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va), thread_id),
            window_lock_map.index((pagetable_ptr, w)) == (TypedHeldLock { lock_id: window_lock_id_at(pagetable_ptr, w), mode: TypedLockMode::Write }),
    { reveal(pagetable_window_typed_lock_map_aligned); }

    pub proof fn pagetable_window_typed_lock_map_aligned_locked_at(
        pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>,
        pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId, pagetable_ptr: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index,
    )
        requires
            pagetable_window_typed_lock_map_aligned(pt_mp, pt_lower, window_lock_map, pagetable_lock_map, thread_id),
            pt_mp.dom().contains(pagetable_ptr),
        ensures
            pagetable_c(pt_mp, pt_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                && pagetable_c(pt_mp, pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) ==> window_lock_map.dom().contains((pagetable_ptr, WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) })),
    { reveal(pagetable_window_typed_lock_map_aligned); }

    pub proof fn pagetable_perms_wf_map(pagetable_perms: PageTableLockedMap)
        requires pagetable_perms_wf(pagetable_perms)
        ensures pagetable_perms.perms_wf()
    { reveal(pagetable_perms_wf); }

    pub open spec fn pagetables_inv<T: LockInvTrait, GhostT>(pagetable_perms: LockedMap<RwLockPageTableRoot, T, (), GhostT, PAGE_TABLE_HAS_KILL_STATE>) -> bool {
        &&& forall|pagetable_p:RwLockPageTableRoot| #![auto] pagetable_perms.dom().contains(pagetable_p) ==> pagetable_perms.spec_index(pagetable_p).inv()
    }

    pub proof fn pagetable_perms_wf_at(pagetable_perms: PageTableLockedMap, pagetable_ptr: RwLockPageTableRoot)
        requires
            pagetable_perms_wf(pagetable_perms),
            pagetable_perms.dom().contains(pagetable_ptr),
        ensures
            pagetable_perms.view().spec_index(pagetable_ptr).is_init(),
            pagetable_perms.view().spec_index(pagetable_ptr).addr() == pagetable_ptr,
            pagetable_perms.spec_index(pagetable_ptr).inv(),
            pagetable_perms.spec_index(pagetable_ptr).is_init(),
            pagetable_perms.spec_index(pagetable_ptr).view().inv(),
    { reveal(pagetable_perms_wf); }
}
