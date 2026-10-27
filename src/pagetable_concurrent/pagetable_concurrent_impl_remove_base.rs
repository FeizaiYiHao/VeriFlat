use vstd::prelude::*;
verus! {
use crate::*;
use vstd::simple_pptr::*;

impl<const TABLE_TYPE: PTType> PageTableHigher<TABLE_TYPE> {
    /// First half of 4K unmap under the window lock: make future page walks miss while retaining the kernel mapping
    /// record that backs any stale TLB entry. A caller must flush those entries before invoking `unmap_4k_page_kernel`.
    pub fn unmap_4k_page_user_view(&self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index,
        target_l1i: L1Index, target_l1_p: PageMapPtr, Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            (PageTableC { higher: *self, lower: *old(lower) }).wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            (PageTableC { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            (PageTableC { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            (PageTableC { higher: *self, lower: *old(lower) }).spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is Some
                || old(lower).mapping_4k.dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            (PageTableC { higher: *self, lower: *old(lower) }).window_locked_by_thread(target_l4i, target_l3i, target_l2i, old(lctx).thread_id()),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (PageTableC { higher: *self, lower: *final(lower) }).wf(),
            (PageTableC { higher: *self, lower: *final(lower) }).page_closure() =~= (PageTableC { higher: *self, lower: *old(lower) }).page_closure(),
            final(lower).mapping_4k == old(lower).mapping_4k.insert(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
                MapEntry { present: false, ..old(lower).mapping_4k.spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) }),
            final(lower).mapping_2m == old(lower).mapping_2m,
            final(lower).l2_ghost == old(lower).l2_ghost,
            final(lower).l2_lock == old(lower).l2_lock,
            final(lower).locked_windows == old(lower).locked_windows,
            final(lower).window_stale_cpus == old(lower).window_stale_cpus,
    {
        proof {
            let c = PageTableC { higher: *self, lower: *lower };
            self.wf_l4_at(target_l4i);
            c.wf_l3_at(self.spec_resolve_mapping_l4(target_l4i)->0.addr, target_l3i);
            c.wf_l2_at(self.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, target_l2i);
            c.wf_l1_at(target_l1_p);
            c.wf_mapping_4k_at(target_l4i, target_l3i, target_l2i, target_l1i);
        }
        let tracked l1_perm = lower.l1_tables.tracked_borrow(target_l1_p);
        let l1_tbl: &PageMap = PPtr::<PageMap>::from_usize(target_l1_p).borrow(Tracked(l1_perm));
        let mut l1_entry = l1_tbl.get(target_l1i);
        l1_entry.perm.present = false;
        page_map_set_published_in_map(target_l1_p, Tracked(&mut lower.l1_tables), target_l1i, l1_entry, Tracked(&mut *lctx));
        proof {
            let va = spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i));
            lower.mapping_4k = lower.mapping_4k.insert(va, MapEntry { present: false, ..old(lower).mapping_4k.spec_index(va) });
            let pre = PageTableC { higher: *self, lower: *old(lower) };
            let post = PageTableC { higher: *self, lower: *lower };
            assert(PageTableC::unmap_4k_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p)) by {
                reveal(PageTableC::unmap_4k_page_user_view_eof_transition_framing);
            };
            PageTableC::unmap_4k_page_user_view_eof(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        }
    }

    /// Final half of 4K unmap under the window lock: remove the kernel mapping only after its user present bit is
    /// already clear. Kernel-level callers must additionally establish that no stale TLB entry remains.
    pub fn unmap_4k_page_kernel(&self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index,
        target_l1i: L1Index, target_l1_p: PageMapPtr, Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            (PageTableC { higher: *self, lower: *old(lower) }).wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            (PageTableC { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            (PageTableC { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            old(lower).mapping_4k.dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            old(lower).mapping_4k.spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))).present == false,
            (PageTableC { higher: *self, lower: *old(lower) }).window_locked_by_thread(target_l4i, target_l3i, target_l2i, old(lctx).thread_id()),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (PageTableC { higher: *self, lower: *final(lower) }).wf(),
            (PageTableC { higher: *self, lower: *final(lower) }).page_closure() =~= (PageTableC { higher: *self, lower: *old(lower) }).page_closure(),
            final(lower).mapping_4k == old(lower).mapping_4k.remove(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            (PageTableC { higher: *self, lower: *final(lower) }).spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None,
            final(lower).mapping_2m == old(lower).mapping_2m,
            final(lower).l2_ghost == old(lower).l2_ghost,
            final(lower).l2_lock == old(lower).l2_lock,
            final(lower).locked_windows == old(lower).locked_windows,
            final(lower).window_stale_cpus == old(lower).window_stale_cpus,
    {
        proof {
            let c = PageTableC { higher: *self, lower: *lower };
            self.wf_l4_at(target_l4i);
            c.wf_l3_at(self.spec_resolve_mapping_l4(target_l4i)->0.addr, target_l3i);
            c.wf_l2_at(self.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, target_l2i);
            c.wf_l1_at(target_l1_p);
            mem_valid_zero();
        }
        page_map_set_published_in_map(target_l1_p, Tracked(&mut lower.l1_tables), target_l1i, PageEntry::empty(), Tracked(&mut *lctx));
        proof {
            lower.mapping_4k = lower.mapping_4k.remove(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)));
            let pre = PageTableC { higher: *self, lower: *old(lower) };
            let post = PageTableC { higher: *self, lower: *lower };
            assert(PageTableC::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p)) by {
                reveal(PageTableC::unmap_4k_page_kernel_eof_transition_framing);
            };
            PageTableC::unmap_4k_page_kernel_eof(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        }
    }

    /// Unlink the L1 page of window `(target_l4i, target_l3i, target_l2i)` and return it. The cleared L2 entry is the window's
    /// spin lock word, so this thread must hold that window lock; the published word keeps the lock bit.
    pub fn remove_l2_entry(&self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index,
        target_l2_p: PageMapPtr, target_l1_p: PageMapPtr, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: (PageMapPtr, Tracked<PointsTo<PageMap>>))
        requires
            (PageTableC { higher: *self, lower: *old(lower) }).wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            self.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            self.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            (PageTableC { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            (PageTableC { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            forall|i: L1Index|
                #![trigger (PageTableC { higher: *self, lower: *old(lower) }).spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, i)]
                pei_valid(i) ==> (PageTableC { higher: *self, lower: *old(lower) }).spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, i) is None,
            (PageTableC { higher: *self, lower: *old(lower) }).window_locked_by_thread(target_l4i, target_l3i, target_l2i, old(lctx).thread_id()),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (PageTableC { higher: *self, lower: *final(lower) }).wf(),
            (PageTableC { higher: *self, lower: *final(lower) }).page_closure() =~= (PageTableC { higher: *self, lower: *old(lower) }).page_closure().remove(target_l1_p),
            final(lower).mapping_4k == old(lower).mapping_4k,
            final(lower).mapping_2m == old(lower).mapping_2m,
            final(lower).l2_lock == old(lower).l2_lock,
            final(lower).locked_windows == old(lower).locked_windows,
            final(lower).window_stale_cpus == old(lower).window_stale_cpus,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
                #![trigger (PageTableC { higher: *self, lower: *final(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                #![trigger (PageTableC { higher: *self, lower: *old(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    ==> (PageTableC { higher: *self, lower: *final(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id) == (PageTableC { higher: *self, lower: *old(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id),
            ret.0 == target_l1_p,
            ret.1.view().is_init(),
            ret.1.view().addr() == target_l1_p,
    {
        proof {
            let c = PageTableC { higher: *self, lower: *lower };
            self.wf_l4_at(target_l4i);
            c.wf_l3_at(self.spec_resolve_mapping_l4(target_l4i)->0.addr, target_l3i);
            c.l2_tokens_paired_at(target_l2_p);
            c.wf_l2_at(target_l2_p, target_l2i);
            c.wf_l1_at(target_l1_p);
            mem_valid_zero();
        }
        let tracked l2_perm = lower.l2_perms.tracked_borrow(target_l2_p);
        let tracked l2_lk = lower.l2_lock.tracked_borrow(target_l2_p);
        let tracked l2_g = lower.l2_ghost.tracked_borrow_mut(target_l2_p);
        let l2_tbl: &L2PageMap = PPtr::<L2PageMap>::from_usize(target_l2_p).borrow(Tracked(l2_perm));
        l2_tbl.set_published_locked(Tracked(l2_g), Tracked(l2_lk), target_l2i, PageEntry::empty(), Tracked(&mut *lctx));
        let tracked l1_perm = lower.l1_tables.tracked_remove(target_l1_p);
        proof {
            lower.l1_rev_map = lower.l1_rev_map.remove(target_l1_p);
            let pre = PageTableC { higher: *self, lower: *old(lower) };
            let post = PageTableC { higher: *self, lower: *lower };
            assert(PageTableC::remove_l2_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p)) by {
                reveal(PageTableC::remove_l2_entry_eof_transition_framing);
            };
            PageTableC::remove_l2_entry_eof(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        }
        (target_l1_p, Tracked(l1_perm))
    }

    /// Unlink the L2 page, which links no L1 page and no 2M leaf, under L3 entry `(target_l4i, target_l3i)` and return it as an ordinary 4K page. No
    /// window of that page may be locked.
    pub fn remove_l3_entry(&mut self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr,
        target_l2_p: PageMapPtr, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: (PageMapPtr, Tracked<PagePerm4k>))
        requires
            (PageTableC { higher: *old(self), lower: *old(lower) }).wf(),
            old(self).kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            old(self).spec_resolve_mapping_l4(target_l4i) is Some,
            old(self).spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            old(self).spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            old(self).spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            forall|i: L2Index|
                #![trigger (PageTableC { higher: *old(self), lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, i)]
                pei_valid(i) ==> (PageTableC { higher: *old(self), lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index|
                #![trigger (PageTableC { higher: *old(self), lower: *old(lower) }).spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i)]
                pei_valid(i) ==> (PageTableC { higher: *old(self), lower: *old(lower) }).spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index| #![trigger old(lower).l2_lock_of(target_l2_p).lock_state(i)] pei_valid(i) ==> old(lower).l2_lock_of(target_l2_p).lock_state(i) is None,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (PageTableC { higher: *final(self), lower: *final(lower) }).wf(),
            (PageTableC { higher: *final(self), lower: *final(lower) }).page_closure() =~= (PageTableC { higher: *old(self), lower: *old(lower) }).page_closure().remove(target_l2_p),
            final(lower).mapping_4k == old(lower).mapping_4k,
            final(lower).mapping_2m == old(lower).mapping_2m,
            final(self).mapping_1g == old(self).mapping_1g,
            final(self).kernel_entries == old(self).kernel_entries,
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).cr3 == old(self).cr3,
            final(self).pcid == old(self).pcid,
            final(self).did == old(self).did,
            final(self).proc_ptr == old(self).proc_ptr,
            final(lower).l2_lock == old(lower).l2_lock.remove(target_l2_p),
            final(lower).locked_windows == old(lower).locked_windows,
            final(lower).window_stale_cpus == old(lower).window_stale_cpus.filter_keys(|k: (PageMapPtr, L2Index)| k.0 != target_l2_p),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
                #![trigger (PageTableC { higher: *final(self), lower: *final(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                #![trigger (PageTableC { higher: *old(self), lower: *old(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    ==> (PageTableC { higher: *final(self), lower: *final(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id) == (PageTableC { higher: *old(self), lower: *old(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id),
            ret.0 == target_l2_p,
            ret.1.view().is_init(),
            ret.1.view().addr() == target_l2_p,
    {
        proof {
            let c = PageTableC { higher: *self, lower: *lower };
            self.wf_l4_at(target_l4i);
            self.wf_l3_at(target_l3_p);
            c.wf_l3_at(target_l3_p, target_l3i);
            c.l2_tokens_paired_at(target_l2_p);
            mem_valid_zero();
        }
        page_map_set_published_in_map(target_l3_p, Tracked(self.l3_tables.borrow_mut()), target_l3i, PageEntry::empty(), Tracked(&mut *lctx));
        proof { self.l2_rev_map = Ghost(self.l2_rev_map.view().remove(target_l2_p)); }
        let tracked l2_perm = lower.l2_perms.tracked_remove(target_l2_p);
        let tracked l2_g = lower.l2_ghost.tracked_remove(target_l2_p);
        let tracked l2_lk = lower.l2_lock.tracked_remove(target_l2_p);
        let page_perm = l2_page_map_to_page_perm(target_l2_p, Tracked(l2_perm), Tracked(l2_g), Tracked(l2_lk));
        proof {
            lower.window_stale_cpus = lower.window_stale_cpus.filter_keys(|k: (PageMapPtr, L2Index)| k.0 != target_l2_p);
            let pre = PageTableC { higher: *old(self), lower: *old(lower) };
            let post = PageTableC { higher: *self, lower: *lower };
            assert(PageTableC::remove_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p)) by {
                reveal(PageTableC::remove_l3_entry_eof_transition_framing);
            };
            PageTableC::remove_l3_entry_eof(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p);
        }
        (target_l2_p, page_perm)
    }

    /// Unlink the L3 page under user root entry `target_l4i` and return it. The window half is untouched: no L2 page
    /// hangs under that entry.
    pub fn remove_l4_entry(&mut self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3_p: PageMapPtr,
        Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: (PageMapPtr, Tracked<PointsTo<PageMap>>))
        requires
            (PageTableC { higher: *old(self), lower: *lower }).wf(),
            old(self).kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            old(self).spec_resolve_mapping_l4(target_l4i) is Some,
            old(self).spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![trigger old(self).spec_resolve_mapping_l3(target_l4i, i)] pei_valid(i) ==> old(self).spec_resolve_mapping_l3(target_l4i, i) is None,
            forall|i: L3Index| #![trigger old(self).spec_resolve_mapping_1g_l3(target_l4i, i)] pei_valid(i) ==> old(self).spec_resolve_mapping_1g_l3(target_l4i, i) is None,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (PageTableC { higher: *final(self), lower: *lower }).wf(),
            (PageTableC { higher: *final(self), lower: *lower }).page_closure() =~= (PageTableC { higher: *old(self), lower: *lower }).page_closure().remove(target_l3_p),
            final(self).mapping_1g == old(self).mapping_1g,
            final(self).kernel_entries == old(self).kernel_entries,
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).cr3 == old(self).cr3,
            final(self).pcid == old(self).pcid,
            final(self).did == old(self).did,
            final(self).proc_ptr == old(self).proc_ptr,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
                #![trigger (PageTableC { higher: *final(self), lower: *lower }).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                #![trigger (PageTableC { higher: *old(self), lower: *lower }).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    ==> (PageTableC { higher: *final(self), lower: *lower }).window_locked_by_thread(l4i, l3i, l2i, thread_id) == (PageTableC { higher: *old(self), lower: *lower }).window_locked_by_thread(l4i, l3i, l2i, thread_id),
            ret.0 == target_l3_p,
            ret.1.view().is_init(),
            ret.1.view().addr() == target_l3_p,
    {
        proof {
            self.wf_l4_cr3_at();
            self.wf_l4_at(target_l4i);
            self.wf_l3_at(target_l3_p);
            mem_valid_zero();
        }
        page_map_set_published_in_map(self.cr3, Tracked(self.l4_table.borrow_mut()), target_l4i, PageEntry::empty(), Tracked(&mut *lctx));
        proof { self.l3_rev_map = Ghost(self.l3_rev_map.view().remove(target_l3_p)); }
        let tracked l3_perm = self.l3_tables.borrow_mut().tracked_remove(target_l3_p);
        proof {
            let pre = PageTableC { higher: *old(self), lower: *lower };
            let post = PageTableC { higher: *self, lower: *lower };
            assert(PageTableC::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p)) by { reveal(PageTableC::remove_l4_entry_eof_transition_framing); };
            PageTableC::remove_l4_entry_eof(pre, post, target_l4i, target_l3_p);
        }
        (target_l3_p, Tracked(l3_perm))
    }
}
} // verus!
