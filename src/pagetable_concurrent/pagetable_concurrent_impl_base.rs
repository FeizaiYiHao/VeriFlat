use vstd::prelude::*;
verus! {
use crate::*;
use vstd::simple_pptr::*;
use super::l2_page_map::*;

impl<const TABLE_TYPE: PTType> PageTableHigher<TABLE_TYPE> {
    /// Link the empty L3 page `page_map_ptr` into root entry `target_l4i`. Writes only the big-lock payload, so the
    /// caller holds the big lock in write mode.
    pub fn create_entry_l4(&mut self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, page_map_ptr: PageMapPtr,
        Tracked(page_map_perm): Tracked<PointsTo<PageMap>>, Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            (PageTableC { higher: *old(self), lower: *lower }).wf(),
            old(self).kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            old(self).spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            (PageTableC { higher: *old(self), lower: *lower }).page_closure().contains(page_map_ptr) == false,
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i: usize| #![trigger page_map_perm.value().spec_index(i)] pei_valid(i) ==> page_map_perm.value().spec_index(i).is_empty(),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (PageTableC { higher: *final(self), lower: *lower }).wf(),
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).pcid == old(self).pcid,
            final(self).cr3 == old(self).cr3,
            final(self).proc_ptr == old(self).proc_ptr,
            (PageTableC { higher: *final(self), lower: *lower }).page_closure() =~= (PageTableC { higher: *old(self), lower: *lower }).page_closure().insert(page_map_ptr),
            final(self).mapping_1g.view() =~= old(self).mapping_1g.view(),
            final(self).spec_resolve_mapping_l4(target_l4i) is Some,
            final(self).spec_resolve_mapping_l4(target_l4i)->0.addr == page_map_ptr,
            final(self).spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            final(self).spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            final(self).kernel_entries =~= old(self).kernel_entries,
            forall|l4i: L4Index, l3i: L3Index| #![trigger final(self).spec_resolve_mapping_l3(l4i, l3i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> final(self).spec_resolve_mapping_l3(l4i, l3i) == old(self).spec_resolve_mapping_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
                #![trigger (PageTableC { higher: *final(self), lower: *lower }).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (PageTableC { higher: *final(self), lower: *lower }).window_locked_by_thread(l4i, l3i, l2i, thread_id)
                    == (PageTableC { higher: *old(self), lower: *lower }).window_locked_by_thread(l4i, l3i, l2i, thread_id),
    {
        proof { self.wf_l4_cr3_at(); page_ptr_valid_imply_mem_valid(page_map_ptr); }
        page_map_set_published_in_map(self.cr3, Tracked(self.l4_table.borrow_mut()), target_l4i,
            PageEntry { addr: page_map_ptr, perm: PageEntryPerm { present: true, ps: false, write: true, execute_disable: false, user: true, kernel_present: false } },
            Tracked(&mut *lctx));
        proof { self.l3_tables.borrow_mut().tracked_insert(page_map_ptr, page_map_perm); self.l3_rev_map = Ghost(self.l3_rev_map.view().insert(page_map_ptr, target_l4i)); }
        proof {
            let pre = PageTableC { higher: *old(self), lower: *lower };
            let post = PageTableC { higher: *self, lower: *lower };
            assert(PageTableC::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr)) by { reveal(PageTableC::create_entry_l4_eof_transition_framing); };
            PageTableC::create_entry_l4_eof(pre, post, target_l4i, page_map_ptr);
            PageTableC::create_entry_l4_eof_window_locks_unchanged(pre, post, target_l4i, page_map_ptr);
        }
    }

    /// Retype the free page `page_map_ptr` into an empty L2 page and link it into L3 entry `target_l3i` of `target_l3_p`. Writes the
    /// big-lock payload, so the caller holds the big lock in write mode. Windows `lo..=hi` of the new page start locked by this thread
    /// and their lock perms are returned; the other new windows start unlocked.
    pub fn create_entry_l3(&mut self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index,
        target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr, Tracked(page_perm): Tracked<PagePerm4k>, lo: L2Index, hi: L2Index, Ghost(root): Ghost<RwLockPageTableRoot>,
        Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<Map<L2Index, LockPerm>>)
        requires
            TABLE_TYPE == PT_TYPE,
            (PageTableC { higher: *old(self), lower: *old(lower) }).wf(),
            old(self).kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            KERNEL_MEM_END_L4INDEX <= target_l4i,
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(lo) && pei_valid(hi) && lo <= hi,
            old(self).spec_resolve_mapping_l4(target_l4i) is Some,
            old(self).spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            old(self).spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            old(self).spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            (PageTableC { higher: *old(self), lower: *old(lower) }).page_closure().contains(page_map_ptr) == false,
            page_perm.addr() == page_map_ptr,
            page_perm.is_init(),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            nonwindow_typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (old(lctx).pagetable_window_lock_map().dom().contains((p, w))
                    || (p == root && w.wf() && spec_v2l4index(w.va) == target_l4i && spec_v2l3index(w.va) == target_l3i && lo <= spec_v2l2index(w.va) <= hi)),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((p, w))]
                old(lctx).pagetable_window_lock_map().dom().contains((p, w))
                    && !(p == root && w.wf() && spec_v2l4index(w.va) == target_l4i && spec_v2l3index(w.va) == target_l3i && lo <= spec_v2l2index(w.va) <= hi)
                    ==> final(lctx).pagetable_window_lock_map().index((p, w)) == old(lctx).pagetable_window_lock_map().index((p, w)),
            forall|w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((root, w))]
                w.wf() && spec_v2l4index(w.va) == target_l4i && spec_v2l3index(w.va) == target_l3i && lo <= spec_v2l2index(w.va) <= hi
                    ==> final(lctx).pagetable_window_lock_map().index((root, w)) == (TypedHeldLock { lock_id: window_lock_id_at(root, w), mode: TypedLockMode::Write }),
            (PageTableC { higher: *final(self), lower: *final(lower) }).wf(),
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).pcid == old(self).pcid,
            final(self).cr3 == old(self).cr3,
            final(self).proc_ptr == old(self).proc_ptr,
            (PageTableC { higher: *final(self), lower: *final(lower) }).page_closure() =~= (PageTableC { higher: *old(self), lower: *old(lower) }).page_closure().insert(page_map_ptr),
            final(lower).mapping_4k =~= old(lower).mapping_4k,
            final(lower).mapping_2m =~= old(lower).mapping_2m,
            final(self).mapping_1g.view() =~= old(self).mapping_1g.view(),
            final(self).spec_resolve_mapping_l4(target_l4i) == old(self).spec_resolve_mapping_l4(target_l4i),
            final(self).spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            final(self).spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == page_map_ptr,
            final(self).spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            (PageTableC { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            (PageTableC { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            final(self).kernel_entries =~= old(self).kernel_entries,
            final(lower).l2_lock == old(lower).l2_lock.insert(page_map_ptr, final(lower).l2_lock_of(page_map_ptr)),
            forall|i: L2Index| #![trigger final(lower).l2_lock_of(page_map_ptr).lock_state(i)] pei_valid(i) && !(lo <= i <= hi) ==> final(lower).l2_lock_of(page_map_ptr).lock_state(i) is None,
            forall|i: L2Index| #![trigger ret.view().dom().contains(i)] ret.view().dom().contains(i) == (lo <= i <= hi),
            forall|i: L2Index| #![trigger ret.view().index(i)] lo <= i <= hi ==> {
                &&& final(lower).l2_lock_of(page_map_ptr).lock_perm_match(i, &ret.view().index(i))
                &&& ret.view().index(i).state() is WriteLock
                &&& ret.view().index(i).ordering_lock_id() == window_lock_id(root, target_l4i, target_l3i, i)
                &&& ret.view().index(i).thread_id() == final(lctx).thread_id()
            },
            final(lower).window_stale_cpus == old(lower).window_stale_cpus,
            forall|l4i: L4Index, l3i: L3Index| #![trigger final(self).spec_resolve_mapping_l3(l4i, l3i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && !(l4i == target_l4i && l3i == target_l3i) ==> final(self).spec_resolve_mapping_l3(l4i, l3i) == old(self).spec_resolve_mapping_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
                #![trigger (PageTableC { higher: *final(self), lower: *final(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (PageTableC { higher: *final(self), lower: *final(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id)
                    == ((PageTableC { higher: *old(self), lower: *old(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id)
                        || (l4i == target_l4i && l3i == target_l3i && lo <= l2i <= hi && thread_id == final(lctx).thread_id())),
            forall|l4i: L4Index, l3i: L3Index| #![trigger final(lower).l2_lock_of((PageTableC { higher: *final(self), lower: *final(lower) }).window_l2_page(l4i, l3i))]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && old(self).spec_resolve_mapping_l3(l4i, l3i) is Some
                    ==> final(lower).l2_lock_of((PageTableC { higher: *final(self), lower: *final(lower) }).window_l2_page(l4i, l3i))
                        == old(lower).l2_lock_of((PageTableC { higher: *old(self), lower: *old(lower) }).window_l2_page(l4i, l3i)),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (PageTableC { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i)]
                (PageTableC { higher: *old(self), lower: *old(lower) }).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (PageTableC { higher: *old(self), lower: *old(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                    ==> (PageTableC { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
    {
        proof {
            self.wf_l4_at(target_l4i);
            self.wf_l3_at(target_l3_p);
            page_ptr_valid_imply_mem_valid(page_map_ptr);
        }
        let (_, Tracked(l2_perm), Tracked(l2_ghost), Tracked(l2_lock), Tracked(window_perms)) = page_perm_to_l2_page_map(page_map_ptr, Tracked(page_perm), lo, hi, Tracked(&mut *lctx),
            Ghost(root), Ghost(target_l4i), Ghost(target_l3i));
        page_map_set_published_in_map(target_l3_p, Tracked(self.l3_tables.borrow_mut()), target_l3i,
            PageEntry { addr: page_map_ptr, perm: PageEntryPerm { present: true, ps: false, write: true, execute_disable: false, user: true, kernel_present: true } },
            Tracked(&mut *lctx));
        proof {
            self.l2_rev_map = Ghost(self.l2_rev_map.view().insert(page_map_ptr, (target_l4i, target_l3i)));
            lower.l2_perms.tracked_insert(page_map_ptr, l2_perm);
            lower.l2_ghost.tracked_insert(page_map_ptr, l2_ghost);
            lower.l2_lock.tracked_insert(page_map_ptr, l2_lock);
            lower.locked_windows = lower.locked_windows.union(Set::<usize>::range_inclusive(lo, hi).map_by(|i: usize| WindowVa { va: spec_index2va((target_l4i, target_l3i, i, 0usize)) },
                |w: WindowVa| spec_v2l2index(w.va)));
        }
        proof {
            let pre = PageTableC { higher: *old(self), lower: *old(lower) };
            let post = PageTableC { higher: *self, lower: *lower };
            assert(PageTableC::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, lctx.thread_id())) by {
                reveal(PageTableC::create_entry_l3_eof_transition_framing);
            };
            PageTableC::create_entry_l3_eof(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, lctx.thread_id());
            PageTableC::create_entry_l3_eof_window_locks_unchanged(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, lctx.thread_id());
        }
        Tracked(window_perms)
    }

    /// Link the empty L1 page `page_map_ptr` into window `target_l2i` of L2 page `target_l2_p`. The entry is the window's spin lock
    /// word, so this thread must hold that window lock; the published word keeps the lock bit. The big-lock payload is unchanged.
    pub fn create_entry_l2(&self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index,
        target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<PointsTo<PageMap>>, Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            (PageTableC { higher: *self, lower: *old(lower) }).wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            self.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            self.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            (PageTableC { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            (PageTableC { higher: *self, lower: *old(lower) }).spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            (PageTableC { higher: *self, lower: *old(lower) }).window_locked_by_thread(target_l4i, target_l3i, target_l2i, old(lctx).thread_id()),
            page_ptr_valid(page_map_ptr),
            (PageTableC { higher: *self, lower: *old(lower) }).page_closure().contains(page_map_ptr) == false,
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i: usize|
                #![trigger page_map_perm.value().spec_index(i).is_empty()]
                #![trigger page_map_perm.value().spec_index(i).perm.present]
                #![trigger page_map_perm.value().spec_index(i).perm.ps]
                #![trigger page_map_perm.value().spec_index(i).perm.kernel_present]
                pei_valid(i) ==> page_map_perm.value().spec_index(i).is_empty(),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (PageTableC { higher: *self, lower: *final(lower) }).wf(),
            (PageTableC { higher: *self, lower: *final(lower) }).page_closure() =~= (PageTableC { higher: *self, lower: *old(lower) }).page_closure().insert(page_map_ptr),
            final(lower).mapping_4k =~= old(lower).mapping_4k,
            final(lower).mapping_2m =~= old(lower).mapping_2m,
            (PageTableC { higher: *self, lower: *final(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            (PageTableC { higher: *self, lower: *final(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == page_map_ptr,
            (PageTableC { higher: *self, lower: *final(lower) }).spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (PageTableC { higher: *self, lower: *final(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i)]
                (PageTableC { higher: *self, lower: *old(lower) }).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (PageTableC { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                    ==> (PageTableC { higher: *self, lower: *final(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
            final(lower).l2_lock == old(lower).l2_lock,
            final(lower).locked_windows == old(lower).locked_windows,
            final(lower).window_stale_cpus == old(lower).window_stale_cpus,
    {
        proof {
            let c = PageTableC { higher: *self, lower: *lower };
            self.wf_l4_at(target_l4i);
            c.wf_l3_at(self.spec_resolve_mapping_l4(target_l4i)->0.addr, target_l3i);
            c.l2_tokens_paired_at(target_l2_p);
            page_ptr_valid_imply_mem_valid(page_map_ptr);
        }
        let tracked l2_perm = lower.l2_perms.tracked_borrow(target_l2_p);
        let tracked l2_lock = lower.l2_lock.tracked_borrow(target_l2_p);
        let tracked mut l2_ghost = lower.l2_ghost.tracked_remove(target_l2_p);
        let l2_tbl: &L2PageMap = PPtr::<L2PageMap>::from_usize(target_l2_p).borrow(Tracked(l2_perm));
        l2_tbl.set_published_locked(Tracked(&mut l2_ghost), Tracked(l2_lock), target_l2i,
            PageEntry { addr: page_map_ptr, perm: PageEntryPerm { present: true, ps: false, write: true, execute_disable: false, user: true, kernel_present: true } },
            Tracked(&mut *lctx));
        proof {
            lower.l2_ghost.tracked_insert(target_l2_p, l2_ghost);
            lower.l1_tables.tracked_insert(page_map_ptr, page_map_perm);
            lower.l1_rev_map = lower.l1_rev_map.insert(page_map_ptr, (target_l4i, target_l3i, target_l2i));
        }
        proof {
            let pre = PageTableC { higher: *self, lower: *old(lower) };
            let post = PageTableC { higher: *self, lower: *lower };
            assert(PageTableC::create_entry_l2_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr)) by {
                reveal(PageTableC::create_entry_l2_eof_transition_framing);
            };
            PageTableC::create_entry_l2_eof(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
            PageTableC::create_entry_l2_eof_resolved_l2_kept(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        }
    }
}
} // verus!
