use vstd::prelude::*;
use crate::*;
use super::*;
verus! {
/// The whole page table rooted at `root`: the part under the big lock (`pt_mp`) and the L2/L1 part under the small
/// (window) locks (`pt_lower`).
pub open spec fn whole_pagetable(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, root: RwLockPageTableRoot) -> WholePageTable<PT_TYPE> {
    WholePageTable { higher: pt_mp.spec_index(root).view(), lower: pt_lower.spec_index(root) }
}

/// The page-table lock map is well-formed and every page table satisfies inv().
#[verifier::opaque]
pub open spec fn pagetable_perms_wf(pt_mp: PageTableLockedMap) -> bool {
    &&& pt_mp.perms_wf()
    &&& pagetables_inv(pt_mp)
}

/// Every CPU or IOMMU table lock satisfies inv().
pub open spec fn pagetables_inv<T: LockInvTrait, GhostT, I>(table_mp: LockedMap<RwLockPageTableRoot, T, (), GhostT, PAGE_TABLE_HAS_KILL_STATE, I>) -> bool {
    &&& forall|pt: RwLockPageTableRoot|
        #![auto]
        table_mp.dom().contains(pt) ==> table_mp.spec_index(pt).inv()
}

pub proof fn pagetable_perms_wf_map(pt_mp: PageTableLockedMap)
    requires pagetable_perms_wf(pt_mp)
    ensures pt_mp.perms_wf()
{ reveal(pagetable_perms_wf); }

pub proof fn pagetable_perms_wf_at(pt_mp: PageTableLockedMap, pt_ptr: RwLockPageTableRoot)
    requires
        pagetable_perms_wf(pt_mp),
        pt_mp.dom().contains(pt_ptr),
    ensures
        pt_mp.view().spec_index(pt_ptr).is_init(),
        pt_mp.view().spec_index(pt_ptr).addr() == pt_ptr,
        pt_mp.spec_index(pt_ptr).inv(),
        pt_mp.spec_index(pt_ptr).is_init(),
        pt_mp.spec_index(pt_ptr).view().inv(),
{ reveal(pagetable_perms_wf); }

/// A page table that is not write-locked hides 4K and 2M leaves only inside locked 2M windows and hides no 1G leaf:
/// unmap clears present bits and reclaims those leaves under the table's write lock or the leaf's window lock.
#[verifier::opaque]
pub open spec fn pagetable_hidden_leaves_only_when_locked(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap) -> bool {
    forall|pt: RwLockPageTableRoot|
        #![trigger pt_mp.spec_index(pt).locking_thread()]
        pt_mp.dom().contains(pt)
            && !(pt_mp.spec_index(pt).locking_thread() is Write)
            ==>
            whole_pagetable(pt_mp, pt_lower, pt).hidden_leaves_in_locked_windows()
}

pub proof fn pagetable_hidden_leaves_only_when_locked_at(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pt_ptr: RwLockPageTableRoot)
    requires
        pagetable_hidden_leaves_only_when_locked(pt_mp, pt_lower),
        pt_mp.dom().contains(pt_ptr),
    ensures !(pt_mp.spec_index(pt_ptr).locking_thread() is Write) ==> whole_pagetable(pt_mp, pt_lower, pt_ptr).hidden_leaves_in_locked_windows(),
{ reveal(pagetable_hidden_leaves_only_when_locked); }

/// A page table that is not write-locked hides L1 pages only inside locked 2M windows: an L2 entry that clears its
/// present bit keeps its L1 page only while its window is locked, and the page is unlinked before the window is released.
#[verifier::opaque]
pub open spec fn pagetable_hidden_l1_only_when_locked(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap) -> bool {
    forall|pt: RwLockPageTableRoot|
        #![trigger pt_mp.spec_index(pt).locking_thread()]
        pt_mp.dom().contains(pt)
            && !(pt_mp.spec_index(pt).locking_thread() is Write)
            ==>
            whole_pagetable(pt_mp, pt_lower, pt).lower.hidden_l1_tables_in_locked_windows()
}

pub proof fn pagetable_hidden_l1_only_when_locked_at(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pt_ptr: RwLockPageTableRoot)
    requires
        pagetable_hidden_l1_only_when_locked(pt_mp, pt_lower),
        pt_mp.dom().contains(pt_ptr),
    ensures !(pt_mp.spec_index(pt_ptr).locking_thread() is Write) ==> whole_pagetable(pt_mp, pt_lower, pt_ptr).lower.hidden_l1_tables_in_locked_windows(),
{ reveal(pagetable_hidden_l1_only_when_locked); }

/// A page table that is not write-locked lists stale CPUs only for locked 2M windows of its own L2 pages: unmap lists a
/// window before it hides a leaf there and drops the entry before it releases the window.
#[verifier::opaque]
pub open spec fn pagetable_window_stale_cpus_only_when_locked(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap) -> bool {
    forall|pt: RwLockPageTableRoot|
        #![trigger pt_mp.spec_index(pt).locking_thread()]
        pt_mp.dom().contains(pt)
            && !(pt_mp.spec_index(pt).locking_thread() is Write)
            ==>
            forall|p: PageMapPtr, i: L2Index|
                #![trigger whole_pagetable(pt_mp, pt_lower, pt).lower.window_stale_cpus.dom().contains((p, i))]
                whole_pagetable(pt_mp, pt_lower, pt).lower.window_stale_cpus.dom().contains((p, i)) ==> {
                    &&& whole_pagetable(pt_mp, pt_lower, pt).lower.l2_perms.dom().contains(p)
                    &&& pei_valid(i)
                    &&& whole_pagetable(pt_mp, pt_lower, pt).lower.l2_owner(p, i) is Write
                }
}

pub proof fn pagetable_window_stale_cpus_only_when_locked_at(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pt_ptr: RwLockPageTableRoot, p: PageMapPtr, i: L2Index)
    requires
        pagetable_window_stale_cpus_only_when_locked(pt_mp, pt_lower),
        pt_mp.dom().contains(pt_ptr),
    ensures
        !(pt_mp.spec_index(pt_ptr).locking_thread() is Write)
            && whole_pagetable(pt_mp, pt_lower, pt_ptr).lower.window_stale_cpus.dom().contains((p, i))
            ==> {
                &&& whole_pagetable(pt_mp, pt_lower, pt_ptr).lower.l2_perms.dom().contains(p)
                &&& pei_valid(i)
                &&& whole_pagetable(pt_mp, pt_lower, pt_ptr).lower.l2_owner(p, i) is Write
            },
{ reveal(pagetable_window_stale_cpus_only_when_locked); }

/// A page table that is not write-locked lists no CPU as stale for the whole table: kill and thread_exit list every CPU
/// under the write lock and drop each one, by a flush or by the drop obligation, before they release it.
#[verifier::opaque]
pub open spec fn pagetable_table_stale_cpus_only_when_write_locked(pt_mp: PageTableLockedMap) -> bool {
    forall|pt: RwLockPageTableRoot|
        #![trigger pt_mp.spec_index(pt).locking_thread()]
        pt_mp.dom().contains(pt)
            && !(pt_mp.spec_index(pt).locking_thread() is Write)
            ==>
            pt_mp.spec_index(pt).view().table_stale_cpus.view() == Set::<CpuId>::empty()
}

pub proof fn pagetable_table_stale_cpus_only_when_write_locked_at(pt_mp: PageTableLockedMap, pt_ptr: RwLockPageTableRoot)
    requires
        pagetable_table_stale_cpus_only_when_write_locked(pt_mp),
        pt_mp.dom().contains(pt_ptr),
    ensures
        !(pt_mp.spec_index(pt_ptr).locking_thread() is Write) ==> pt_mp.spec_index(pt_ptr).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
{ reveal(pagetable_table_stale_cpus_only_when_write_locked); }

/// A page table that is not write-locked hides no user L4 entry, and no L3 entry under one, unless its process has
/// emptied its tables: every such entry with the present or kernel_present bit set has its present bit set. Kill and
/// thread_exit hide these entries under the write lock.
#[verifier::opaque]
pub open spec fn pagetable_hidden_roots_only_when_write_locked_or_emptied(pt_mp: PageTableLockedMap, prc_mp: ProcessLockedMap) -> bool {
    forall|pt: RwLockPageTableRoot|
        #![trigger pt_mp.spec_index(pt).locking_thread()]
        pt_mp.dom().contains(pt)
            && !(pt_mp.spec_index(pt).locking_thread() is Write)
            && !(prc_mp.spec_index(pt_mp.spec_index(pt).view().proc_ptr).view().state.view() is TablesEmptied)
            && !(prc_mp.spec_index(pt_mp.spec_index(pt).view().proc_ptr).view().state.view() is Zombie)
            ==> {
                // User L4 entries.
                &&& forall|l4i: L4Index|
                    #![trigger pt_mp.spec_index(pt).view().spec_held_l4(l4i)]
                    pt_mp.spec_index(pt).view().kernel_l4_end <= l4i
                        && pei_valid(l4i)
                        && pt_mp.spec_index(pt).view().spec_held_l4(l4i) is Some
                        ==>
                        pt_mp.spec_index(pt).view().spec_resolve_mapping_l4(l4i) is Some
                // L3 entries under user L4 entries.
                &&& forall|l4i: L4Index, l3i: L3Index|
                    #![trigger pt_mp.spec_index(pt).view().spec_held_l3(l4i, l3i)]
                    pt_mp.spec_index(pt).view().kernel_l4_end <= l4i
                        && pei_valid(l4i)
                        && pei_valid(l3i)
                        && pt_mp.spec_index(pt).view().spec_held_l3(l4i, l3i) is Some
                        ==>
                        pt_mp.spec_index(pt).view().spec_resolve_mapping_l3(l4i, l3i) is Some
            }
}

pub proof fn pagetable_hidden_roots_only_when_write_locked_or_emptied_at(pt_mp: PageTableLockedMap, prc_mp: ProcessLockedMap, pt_ptr: RwLockPageTableRoot)
    requires
        pagetable_hidden_roots_only_when_write_locked_or_emptied(pt_mp, prc_mp),
        pt_mp.dom().contains(pt_ptr),
    ensures
        !(pt_mp.spec_index(pt_ptr).locking_thread() is Write)
            && !(prc_mp.spec_index(pt_mp.spec_index(pt_ptr).view().proc_ptr).view().state.view() is TablesEmptied)
            && !(prc_mp.spec_index(pt_mp.spec_index(pt_ptr).view().proc_ptr).view().state.view() is Zombie)
            ==>
            forall|l4i: L4Index|
                #![trigger pt_mp.spec_index(pt_ptr).view().spec_held_l4(l4i)]
                pt_mp.spec_index(pt_ptr).view().kernel_l4_end <= l4i
                    && pei_valid(l4i)
                    && pt_mp.spec_index(pt_ptr).view().spec_held_l4(l4i) is Some
                    ==>
                    pt_mp.spec_index(pt_ptr).view().spec_resolve_mapping_l4(l4i) is Some,
        !(pt_mp.spec_index(pt_ptr).locking_thread() is Write)
            && !(prc_mp.spec_index(pt_mp.spec_index(pt_ptr).view().proc_ptr).view().state.view() is TablesEmptied)
            && !(prc_mp.spec_index(pt_mp.spec_index(pt_ptr).view().proc_ptr).view().state.view() is Zombie)
            ==>
            forall|l4i: L4Index, l3i: L3Index|
                #![trigger pt_mp.spec_index(pt_ptr).view().spec_held_l3(l4i, l3i)]
                pt_mp.spec_index(pt_ptr).view().kernel_l4_end <= l4i
                    && pei_valid(l4i)
                    && pei_valid(l3i)
                    && pt_mp.spec_index(pt_ptr).view().spec_held_l3(l4i, l3i) is Some
                    ==>
                    pt_mp.spec_index(pt_ptr).view().spec_resolve_mapping_l3(l4i, l3i) is Some,
{ reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); }

/// Every page table has its L2/L1 part, and the two parts together form a well-formed table.
#[verifier::opaque]
pub open spec fn pagetable_lower_wf(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap) -> bool {
    &&& pt_lower.dom() == pt_mp.dom()
    &&& forall|pt: RwLockPageTableRoot|
        #![trigger whole_pagetable(pt_mp, pt_lower, pt)]
        pt_mp.dom().contains(pt) ==> whole_pagetable(pt_mp, pt_lower, pt).wf()
}

pub proof fn pagetable_lower_wf_at(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pt_ptr: RwLockPageTableRoot)
    requires
        pagetable_lower_wf(pt_mp, pt_lower),
        pt_mp.dom().contains(pt_ptr),
    ensures
        pt_lower.dom().contains(pt_ptr),
        whole_pagetable(pt_mp, pt_lower, pt_ptr).wf(),
{ reveal(pagetable_lower_wf); }

/// A thread that locks a 2M window (small lock) of a page table also locks that table's big lock.
#[verifier::opaque]
pub open spec fn pagetable_window_holders_hold_pagetable(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap) -> bool {
    forall|pt: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
        #![trigger whole_pagetable(pt_mp, pt_lower, pt).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        pt_mp.dom().contains(pt)
            && whole_pagetable(pt_mp, pt_lower, pt).kernel_l4_end() <= l4i
            && pei_valid(l4i)
            && pei_valid(l3i)
            && pei_valid(l2i)
            && whole_pagetable(pt_mp, pt_lower, pt).window_locked_by_thread(l4i, l3i, l2i, thread_id)
            ==>
            pt_mp.spec_index(pt).locked_by_thread(thread_id)
}

pub proof fn pagetable_window_holders_hold_pagetable_at(
    pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pt_ptr: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId,
)
    requires
        pagetable_window_holders_hold_pagetable(pt_mp, pt_lower),
        pt_mp.dom().contains(pt_ptr),
    ensures
        whole_pagetable(pt_mp, pt_lower, pt_ptr).kernel_l4_end() <= l4i
            && pei_valid(l4i)
            && pei_valid(l3i)
            && pei_valid(l2i)
            && whole_pagetable(pt_mp, pt_lower, pt_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)
            ==>
            pt_mp.spec_index(pt_ptr).locked_by_thread(thread_id),
{ reveal(pagetable_window_holders_hold_pagetable); }

/// While a page table is write-locked, its big lock's ghost value equals its L2/L1 part (`pt_lower`).
pub open spec fn pagetable_lower_backup_wf(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap) -> bool {
    forall|pt: RwLockPageTableRoot|
        #![trigger pt_mp.spec_index(pt)]
        pt_mp.dom().contains(pt)
            && pt_mp.spec_index(pt).wlocked()
            ==>
            pt_mp.spec_index(pt).view_ghost() == pt_lower.spec_index(pt)
}

pub proof fn pagetable_lower_backup_wf_at(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pt_ptr: RwLockPageTableRoot)
    requires
        pagetable_lower_backup_wf(pt_mp, pt_lower),
        pt_mp.dom().contains(pt_ptr),
        pt_mp.spec_index(pt_ptr).wlocked(),
    ensures pt_mp.spec_index(pt_ptr).view_ghost() == pt_lower.spec_index(pt_ptr),
{}

/// The 2M windows `thread_id` has locked and its typed window map agree: every map entry names a well-formed window,
/// locked by `thread_id`, of a page table whose big lock is in `pagetable_lock_map`, with the window's exact lock id;
/// and every window `thread_id` has locked is in the map.
#[verifier::opaque]
pub open spec fn pagetable_window_typed_lock_map_aligned(
    pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>,
    pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId,
) -> bool {
    &&& forall|pt: RwLockPageTableRoot, w: WindowVa|
        #![trigger window_lock_map.dom().contains((pt, w))]
        window_lock_map.dom().contains((pt, w)) ==> {
            &&& pt_mp.dom().contains(pt)
            &&& pagetable_lock_map.dom().contains(pt)
            &&& w.wf()
            &&& whole_pagetable(pt_mp, pt_lower, pt).kernel_l4_end() <= spec_v2l4index(w.va)
            &&& whole_pagetable(pt_mp, pt_lower, pt).window_locked_by_thread(spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va), thread_id)
            &&& window_lock_map.index((pt, w)) == (TypedHeldLock { lock_id: window_lock_id_of(pt, w), mode: TypedLockMode::Write })
        }
    &&& forall|pt: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index|
        #![trigger whole_pagetable(pt_mp, pt_lower, pt).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        pt_mp.dom().contains(pt)
            && whole_pagetable(pt_mp, pt_lower, pt).kernel_l4_end() <= l4i
            && pei_valid(l4i)
            && pei_valid(l3i)
            && pei_valid(l2i)
            && whole_pagetable(pt_mp, pt_lower, pt).window_locked_by_thread(l4i, l3i, l2i, thread_id)
            ==>
            window_lock_map.dom().contains((pt, WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) }))
}

pub proof fn pagetable_window_typed_lock_map_aligned_at(
    pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>,
    pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId, pt_ptr: RwLockPageTableRoot, w: WindowVa,
)
    requires
        pagetable_window_typed_lock_map_aligned(pt_mp, pt_lower, window_lock_map, pagetable_lock_map, thread_id),
        window_lock_map.dom().contains((pt_ptr, w)),
    ensures
        pt_mp.dom().contains(pt_ptr),
        pagetable_lock_map.dom().contains(pt_ptr),
        w.wf(),
        whole_pagetable(pt_mp, pt_lower, pt_ptr).kernel_l4_end() <= spec_v2l4index(w.va),
        whole_pagetable(pt_mp, pt_lower, pt_ptr).window_locked_by_thread(spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va), thread_id),
        window_lock_map.index((pt_ptr, w)) == (TypedHeldLock { lock_id: window_lock_id_of(pt_ptr, w), mode: TypedLockMode::Write }),
{ reveal(pagetable_window_typed_lock_map_aligned); }

pub proof fn pagetable_window_typed_lock_map_aligned_locked_at(
    pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>,
    pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>, thread_id: LockThreadId, pt_ptr: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index,
)
    requires
        pagetable_window_typed_lock_map_aligned(pt_mp, pt_lower, window_lock_map, pagetable_lock_map, thread_id),
        pt_mp.dom().contains(pt_ptr),
    ensures
        whole_pagetable(pt_mp, pt_lower, pt_ptr).kernel_l4_end() <= l4i
            && pei_valid(l4i)
            && pei_valid(l3i)
            && pei_valid(l2i)
            && whole_pagetable(pt_mp, pt_lower, pt_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)
            ==>
            window_lock_map.dom().contains((pt_ptr, WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) })),
{ reveal(pagetable_window_typed_lock_map_aligned); }
}
