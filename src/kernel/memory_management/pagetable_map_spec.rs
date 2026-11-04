use vstd::prelude::*;
use crate::*;
use super::*;
verus! {
    /// The whole page table rooted at `root`: the big-lock payload in `pt_mp` and its window half in `pt_lower`.
    pub open spec fn whole_pagetable(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, root: RwLockPageTableRoot) -> WholePageTable<PT_TYPE> {
        WholePageTable { higher: pt_mp.spec_index(root).view(), lower: pt_lower.spec_index(root) }
    }

    #[verifier::opaque]
    pub open spec fn pagetable_perms_wf(pagetable_perms: PageTableLockedMap) -> bool {
        &&& pagetable_perms.perms_wf()
        &&& pagetables_inv(pagetable_perms)
    }

    /// A page table that is not write-locked hides 4K and 2M leaves only inside locked 2M windows and hides no 1G leaf:
    /// unmap clears present bits and reclaims those leaves under the table's write lock or the leaf's window lock.
    #[verifier::opaque]
    pub open spec fn pagetable_hidden_leaves_only_when_locked(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap) -> bool {
        forall|pagetable_p: RwLockPageTableRoot|
            #![trigger pt_mp.spec_index(pagetable_p).locking_thread()]
            pt_mp.dom().contains(pagetable_p) && !(pt_mp.spec_index(pagetable_p).locking_thread() is Write) ==> whole_pagetable(pt_mp, pt_lower, pagetable_p).hidden_leaves_in_locked_windows()
    }

    pub proof fn pagetable_hidden_leaves_only_when_locked_at(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot)
        requires
            pagetable_hidden_leaves_only_when_locked(pt_mp, pt_lower),
            pt_mp.dom().contains(pagetable_ptr),
        ensures !(pt_mp.spec_index(pagetable_ptr).locking_thread() is Write) ==> whole_pagetable(pt_mp, pt_lower, pagetable_ptr).hidden_leaves_in_locked_windows(),
    { reveal(pagetable_hidden_leaves_only_when_locked); }

    /// A page table that is not write-locked hides L1 pages only inside locked 2M windows: an L2 entry that clears its
    /// present bit keeps its L1 page only while its window is held, and the page is unlinked before the window is released.
    #[verifier::opaque]
    pub open spec fn pagetable_hidden_l1_only_when_locked(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap) -> bool {
        forall|pagetable_p: RwLockPageTableRoot|
            #![trigger pt_mp.spec_index(pagetable_p).locking_thread()]
            pt_mp.dom().contains(pagetable_p) && !(pt_mp.spec_index(pagetable_p).locking_thread() is Write) ==> whole_pagetable(pt_mp, pt_lower, pagetable_p).lower.hidden_l1_tables_in_locked_windows()
    }

    pub proof fn pagetable_hidden_l1_only_when_locked_at(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot)
        requires
            pagetable_hidden_l1_only_when_locked(pt_mp, pt_lower),
            pt_mp.dom().contains(pagetable_ptr),
        ensures !(pt_mp.spec_index(pagetable_ptr).locking_thread() is Write) ==> whole_pagetable(pt_mp, pt_lower, pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
    { reveal(pagetable_hidden_l1_only_when_locked); }

    /// A page table that is not write-locked lists stale CPUs only for locked 2M windows of its own L2 pages: unmap lists a
    /// window before it hides a leaf there and drops the entry before it releases the window.
    #[verifier::opaque]
    pub open spec fn pagetable_window_stale_cpus_only_when_locked(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap) -> bool {
        forall|pagetable_p: RwLockPageTableRoot|
            #![trigger pt_mp.spec_index(pagetable_p).locking_thread()]
            pt_mp.dom().contains(pagetable_p) && !(pt_mp.spec_index(pagetable_p).locking_thread() is Write) ==> forall|p: PageMapPtr, i: L2Index|
                #![trigger whole_pagetable(pt_mp, pt_lower, pagetable_p).lower.window_stale_cpus.dom().contains((p, i))]
                whole_pagetable(pt_mp, pt_lower, pagetable_p).lower.window_stale_cpus.dom().contains((p, i)) ==> {
                    &&& whole_pagetable(pt_mp, pt_lower, pagetable_p).lower.l2_perms.dom().contains(p)
                    &&& pei_valid(i)
                    &&& whole_pagetable(pt_mp, pt_lower, pagetable_p).lower.l2_owner(p, i) is Write
                }
    }

    pub proof fn pagetable_window_stale_cpus_only_when_locked_at(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, p: PageMapPtr, i: L2Index)
        requires
            pagetable_window_stale_cpus_only_when_locked(pt_mp, pt_lower),
            pt_mp.dom().contains(pagetable_ptr),
        ensures
            !(pt_mp.spec_index(pagetable_ptr).locking_thread() is Write) && whole_pagetable(pt_mp, pt_lower, pagetable_ptr).lower.window_stale_cpus.dom().contains((p, i)) ==> {
                &&& whole_pagetable(pt_mp, pt_lower, pagetable_ptr).lower.l2_perms.dom().contains(p)
                &&& pei_valid(i)
                &&& whole_pagetable(pt_mp, pt_lower, pagetable_ptr).lower.l2_owner(p, i) is Write
            },
    { reveal(pagetable_window_stale_cpus_only_when_locked); }

    /// A page table that is not write-locked lists no CPU as stale for the whole table: kill and thread_exit list every CPU
    /// under the write lock and drop each one, by a flush or by the drop obligation, before they release it.
    #[verifier::opaque]
    pub open spec fn pagetable_table_stale_cpus_only_when_write_held(pt_mp: PageTableLockedMap) -> bool {
        forall|pagetable_p: RwLockPageTableRoot|
            #![trigger pt_mp.spec_index(pagetable_p).locking_thread()]
            pt_mp.dom().contains(pagetable_p) && !(pt_mp.spec_index(pagetable_p).locking_thread() is Write) ==> pt_mp.spec_index(pagetable_p).view().table_stale_cpus.view() == Set::<CpuId>::empty()
    }

    pub proof fn pagetable_table_stale_cpus_only_when_write_held_at(pt_mp: PageTableLockedMap, pagetable_ptr: RwLockPageTableRoot)
        requires
            pagetable_table_stale_cpus_only_when_write_held(pt_mp),
            pt_mp.dom().contains(pagetable_ptr),
        ensures
            !(pt_mp.spec_index(pagetable_ptr).locking_thread() is Write) ==> pt_mp.spec_index(pagetable_ptr).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
    { reveal(pagetable_table_stale_cpus_only_when_write_held); }

    /// A page table that is not write-locked hides a user root entry only once its process has emptied its tables: every
    /// held user L4 entry and every held L3 entry under a user L4 entry of a live process's table resolves. Kill and
    /// thread_exit hide the roots under the write lock.
    // Proof dependency (for process-state changes): process_pagetable_match.
    #[verifier::opaque]
    pub open spec fn pagetable_hidden_roots_only_when_write_held_or_emptied(pt_mp: PageTableLockedMap, prc_mp: ProcessLockedMap) -> bool {
        forall|pagetable_p: RwLockPageTableRoot|
            #![trigger pt_mp.spec_index(pagetable_p).locking_thread()]
            pt_mp.dom().contains(pagetable_p) && !(pt_mp.spec_index(pagetable_p).locking_thread() is Write)
                && !(prc_mp.spec_index(pt_mp.spec_index(pagetable_p).view().proc_ptr).view().state.view() is TablesEmptied)
                && !(prc_mp.spec_index(pt_mp.spec_index(pagetable_p).view().proc_ptr).view().state.view() is Zombie) ==> {
                &&& forall|l4i: L4Index|
                    #![trigger pt_mp.spec_index(pagetable_p).view().spec_held_l4(l4i)]
                    pt_mp.spec_index(pagetable_p).view().kernel_l4_end <= l4i && pei_valid(l4i) && pt_mp.spec_index(pagetable_p).view().spec_held_l4(l4i) is Some
                        ==> pt_mp.spec_index(pagetable_p).view().spec_resolve_mapping_l4(l4i) is Some
                &&& forall|l4i: L4Index, l3i: L3Index|
                    #![trigger pt_mp.spec_index(pagetable_p).view().spec_held_l3(l4i, l3i)]
                    pt_mp.spec_index(pagetable_p).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pt_mp.spec_index(pagetable_p).view().spec_held_l3(l4i, l3i) is Some
                        ==> pt_mp.spec_index(pagetable_p).view().spec_resolve_mapping_l3(l4i, l3i) is Some
            }
    }

    pub proof fn pagetable_hidden_roots_only_when_write_held_or_emptied_at(pt_mp: PageTableLockedMap, prc_mp: ProcessLockedMap, pagetable_ptr: RwLockPageTableRoot)
        requires
            pagetable_hidden_roots_only_when_write_held_or_emptied(pt_mp, prc_mp),
            pt_mp.dom().contains(pagetable_ptr),
        ensures
            !(pt_mp.spec_index(pagetable_ptr).locking_thread() is Write)
                && !(prc_mp.spec_index(pt_mp.spec_index(pagetable_ptr).view().proc_ptr).view().state.view() is TablesEmptied)
                && !(prc_mp.spec_index(pt_mp.spec_index(pagetable_ptr).view().proc_ptr).view().state.view() is Zombie) ==> forall|l4i: L4Index|
                #![trigger pt_mp.spec_index(pagetable_ptr).view().spec_held_l4(l4i)]
                pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pt_mp.spec_index(pagetable_ptr).view().spec_held_l4(l4i) is Some
                    ==> pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l4(l4i) is Some,
            !(pt_mp.spec_index(pagetable_ptr).locking_thread() is Write)
                && !(prc_mp.spec_index(pt_mp.spec_index(pagetable_ptr).view().proc_ptr).view().state.view() is TablesEmptied)
                && !(prc_mp.spec_index(pt_mp.spec_index(pagetable_ptr).view().proc_ptr).view().state.view() is Zombie) ==> forall|l4i: L4Index, l3i: L3Index|
                #![trigger pt_mp.spec_index(pagetable_ptr).view().spec_held_l3(l4i, l3i)]
                pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pt_mp.spec_index(pagetable_ptr).view().spec_held_l3(l4i, l3i) is Some
                    ==> pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(l4i, l3i) is Some,
    { reveal(pagetable_hidden_roots_only_when_write_held_or_emptied); }

    /// Every page table has its window half, and the two halves together form a well-formed table.
    #[verifier::opaque]
    pub open spec fn pagetable_lower_wf(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap) -> bool {
        &&& pt_lower.dom() == pt_mp.dom()
        &&& forall|pagetable_ptr: RwLockPageTableRoot| #![trigger whole_pagetable(pt_mp, pt_lower, pagetable_ptr)] pt_mp.dom().contains(pagetable_ptr) ==> whole_pagetable(pt_mp, pt_lower, pagetable_ptr).wf()
    }

    pub proof fn pagetable_lower_wf_at(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot)
        requires
            pagetable_lower_wf(pt_mp, pt_lower),
            pt_mp.dom().contains(pagetable_ptr),
        ensures
            pt_lower.dom().contains(pagetable_ptr),
            whole_pagetable(pt_mp, pt_lower, pagetable_ptr).wf(),
    { reveal(pagetable_lower_wf); }

    /// A thread that holds a 2M window of a page table holds that table's big lock.
    #[verifier::opaque]
    pub open spec fn pagetable_window_holders_hold_pagetable(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap) -> bool {
        forall|pagetable_ptr: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
            #![trigger whole_pagetable(pt_mp, pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            pt_mp.dom().contains(pagetable_ptr) && whole_pagetable(pt_mp, pt_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                && whole_pagetable(pt_mp, pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) ==> pt_mp.spec_index(pagetable_ptr).locked_by_thread(thread_id)
    }

    pub proof fn pagetable_window_holders_hold_pagetable_at(
        pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId,
    )
        requires
            pagetable_window_holders_hold_pagetable(pt_mp, pt_lower),
            pt_mp.dom().contains(pagetable_ptr),
        ensures
            whole_pagetable(pt_mp, pt_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                && whole_pagetable(pt_mp, pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) ==> pt_mp.spec_index(pagetable_ptr).locked_by_thread(thread_id),
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
                &&& whole_pagetable(pt_mp, pt_lower, pagetable_ptr).kernel_l4_end() <= spec_v2l4index(w.va)
                &&& whole_pagetable(pt_mp, pt_lower, pagetable_ptr).window_locked_by_thread(spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va), thread_id)
                &&& window_lock_map.index((pagetable_ptr, w)) == (TypedHeldLock { lock_id: window_lock_id_of(pagetable_ptr, w), mode: TypedLockMode::Write })
            }
        &&& forall|pagetable_ptr: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger whole_pagetable(pt_mp, pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            pt_mp.dom().contains(pagetable_ptr) && whole_pagetable(pt_mp, pt_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                && whole_pagetable(pt_mp, pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) ==> window_lock_map.dom().contains((pagetable_ptr, WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) }))
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
            whole_pagetable(pt_mp, pt_lower, pagetable_ptr).kernel_l4_end() <= spec_v2l4index(w.va),
            whole_pagetable(pt_mp, pt_lower, pagetable_ptr).window_locked_by_thread(spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va), thread_id),
            window_lock_map.index((pagetable_ptr, w)) == (TypedHeldLock { lock_id: window_lock_id_of(pagetable_ptr, w), mode: TypedLockMode::Write }),
    { reveal(pagetable_window_typed_lock_map_aligned); }

    pub proof fn pagetable_window_typed_lock_map_aligned_locked_at(
        pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>,
        pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId, pagetable_ptr: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index,
    )
        requires
            pagetable_window_typed_lock_map_aligned(pt_mp, pt_lower, window_lock_map, pagetable_lock_map, thread_id),
            pt_mp.dom().contains(pagetable_ptr),
        ensures
            whole_pagetable(pt_mp, pt_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                && whole_pagetable(pt_mp, pt_lower, pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) ==> window_lock_map.dom().contains((pagetable_ptr, WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) })),
    { reveal(pagetable_window_typed_lock_map_aligned); }

    pub proof fn pagetable_perms_wf_map(pagetable_perms: PageTableLockedMap)
        requires pagetable_perms_wf(pagetable_perms)
        ensures pagetable_perms.perms_wf()
    { reveal(pagetable_perms_wf); }

    pub open spec fn pagetables_inv<T: LockInvTrait, GhostT, I>(pagetable_perms: LockedMap<RwLockPageTableRoot, T, (), GhostT, PAGE_TABLE_HAS_KILL_STATE, I>) -> bool {
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
