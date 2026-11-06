use vstd::prelude::*;
verus! {
use crate::*;
use vstd::simple_pptr::*;

impl<const TABLE_TYPE: PTType> PageTableHigher<TABLE_TYPE> {
    /// First half of 4K unmap under the window lock: make future page walks miss while retaining the kernel mapping
    /// record that backs any stale TLB entry. A caller must flush those entries before invoking `unmap_4k_page_kernel`.
    pub fn unmap_4k_page_user_view(&self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index,
        target_l1i: L1Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr, Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            (WholePageTable { higher: *self, lower: *old(lower) }).wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            (WholePageTable { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            (WholePageTable { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            (WholePageTable { higher: *self, lower: *old(lower) }).spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is Some
                || old(lower).mapping_4k.dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            (WholePageTable { higher: *self, lower: *old(lower) }).window_locked_by_thread(target_l4i, target_l3i, target_l2i, old(lctx).thread_id()),
            self.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            self.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            old(lower).l2_owner(target_l2_p, target_l2i) == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (WholePageTable { higher: *self, lower: *final(lower) }).wf(),
            (WholePageTable { higher: *self, lower: *final(lower) }).page_closure() =~= (WholePageTable { higher: *self, lower: *old(lower) }).page_closure(),
            final(lower).mapping_4k == old(lower).mapping_4k.insert(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
                MapEntry { present: false, ..old(lower).mapping_4k.spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) }),
            final(lower).mapping_2m == old(lower).mapping_2m,
            final(lower).l2_perms.dom() == old(lower).l2_perms.dom(),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_entry(p, i)] final(lower).l2_entry(p, i) == old(lower).l2_entry(p, i),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_owner(p, i)] final(lower).l2_owner(p, i) == old(lower).l2_owner(p, i),
            final(lower).pagetable_window_locks == old(lower).pagetable_window_locks,
            final(lower).window_stale_cpus == old(lower).window_stale_cpus,
            old(lower).hidden_l1_tables_in_locked_windows() ==> final(lower).hidden_l1_tables_in_locked_windows(),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_page(p).entry_lock(i).l1()] pei_valid(i) && !old(lower).l2_entry_hides_l1(p, i) ==> !final(lower).l2_entry_hides_l1(p, i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_2m_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i, l1i) != (target_l4i, target_l3i, target_l2i, target_l1i)
                    ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i),
            (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i)
                == Some(PageEntry { perm: PageEntryPerm { present: false, ..old(lower).l1_page(target_l2_p, target_l2i).spec_index(target_l1i).perm }, ..old(lower).l1_page(target_l2_p, target_l2i).spec_index(target_l1i) }),
    {
        proof {
            let c = WholePageTable { higher: *self, lower: *lower };
            self.wf_l4_at(target_l4i);
            c.l3_links_l2_wf_at(self.spec_resolve_mapping_l4(target_l4i)->0.addr, target_l3i);
            c.wf_l2_at(target_l2_p, target_l2i);
            c.wf_l1_at(target_l2_p, target_l2i);
            c.wf_mapping_4k_at(target_l4i, target_l3i, target_l2i, target_l1i);
        }
        let tracked mut l2_perm = lower.l2_perms.tracked_remove(target_l2_p);
        let tracked mut l1_perm = l2_entry_take_l1(&mut l2_perm, target_l2i, window_perm);
        let l1_tbl: &PageMap = PPtr::<PageMap>::from_usize(target_l1_p).borrow(Tracked(&l1_perm));
        let mut l1_entry = l1_tbl.get(target_l1i);
        l1_entry.perm.present = false;
        page_map_set_published(target_l1_p, Tracked(&mut l1_perm), target_l1i, l1_entry, Tracked(&mut *lctx));
        proof {
            l2_entry_put_l1(&mut l2_perm, target_l2i, window_perm, l1_perm);
            lower.l2_perms.tracked_insert(target_l2_p, l2_perm);
            let va = spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i));
            lower.mapping_4k = lower.mapping_4k.insert(va, MapEntry { present: false, ..old(lower).mapping_4k.spec_index(va) });
            let pre = WholePageTable { higher: *self, lower: *old(lower) };
            let post = WholePageTable { higher: *self, lower: *lower };
            assert(WholePageTable::unmap_4k_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p)) by {
                reveal(WholePageTable::unmap_4k_page_user_view_eof_transition_framing);
            };
            WholePageTable::unmap_4k_page_user_view_eof(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
            WholePageTable::unmap_4k_page_user_view_eof_held_chain(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l2_p, target_l1_p);
        }
    }

    /// Final half of 4K unmap under the window lock: remove the kernel mapping only after its user present bit is
    /// already clear. Kernel-level callers must additionally establish that no stale TLB entry remains.
    pub fn unmap_4k_page_kernel(&self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index,
        target_l1i: L1Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr, Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            (WholePageTable { higher: *self, lower: *old(lower) }).wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            (WholePageTable { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            (WholePageTable { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            old(lower).mapping_4k.dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            old(lower).mapping_4k.spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))).present == false,
            (WholePageTable { higher: *self, lower: *old(lower) }).window_locked_by_thread(target_l4i, target_l3i, target_l2i, old(lctx).thread_id()),
            self.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            self.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            old(lower).l2_owner(target_l2_p, target_l2i) == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (WholePageTable { higher: *self, lower: *final(lower) }).wf(),
            (WholePageTable { higher: *self, lower: *final(lower) }).page_closure() =~= (WholePageTable { higher: *self, lower: *old(lower) }).page_closure(),
            final(lower).mapping_4k == old(lower).mapping_4k.remove(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            (WholePageTable { higher: *self, lower: *final(lower) }).spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None,
            final(lower).mapping_2m == old(lower).mapping_2m,
            final(lower).l2_perms.dom() == old(lower).l2_perms.dom(),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_entry(p, i)] final(lower).l2_entry(p, i) == old(lower).l2_entry(p, i),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_owner(p, i)] final(lower).l2_owner(p, i) == old(lower).l2_owner(p, i),
            final(lower).pagetable_window_locks == old(lower).pagetable_window_locks,
            final(lower).window_stale_cpus == old(lower).window_stale_cpus,
            old(lower).hidden_l1_tables_in_locked_windows() ==> final(lower).hidden_l1_tables_in_locked_windows(),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_page(p).entry_lock(i).l1()] pei_valid(i) && !old(lower).l2_entry_hides_l1(p, i) ==> !final(lower).l2_entry_hides_l1(p, i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_2m_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i, l1i) != (target_l4i, target_l3i, target_l2i, target_l1i)
                    ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i),
            (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None,
    {
        proof {
            let c = WholePageTable { higher: *self, lower: *lower };
            self.wf_l4_at(target_l4i);
            c.l3_links_l2_wf_at(self.spec_resolve_mapping_l4(target_l4i)->0.addr, target_l3i);
            c.wf_l2_at(target_l2_p, target_l2i);
            c.wf_l1_at(target_l2_p, target_l2i);
            mem_valid_zero();
        }
        let tracked mut l2_perm = lower.l2_perms.tracked_remove(target_l2_p);
        let tracked mut l1_perm = l2_entry_take_l1(&mut l2_perm, target_l2i, window_perm);
        page_map_set_published(target_l1_p, Tracked(&mut l1_perm), target_l1i, PageEntry::empty(), Tracked(&mut *lctx));
        proof {
            l2_entry_put_l1(&mut l2_perm, target_l2i, window_perm, l1_perm);
            lower.l2_perms.tracked_insert(target_l2_p, l2_perm);
            lower.mapping_4k = lower.mapping_4k.remove(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)));
            let pre = WholePageTable { higher: *self, lower: *old(lower) };
            let post = WholePageTable { higher: *self, lower: *lower };
            assert(WholePageTable::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p)) by {
                reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
            };
            WholePageTable::unmap_4k_page_kernel_eof(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
            WholePageTable::unmap_4k_page_kernel_eof_held_chain(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l2_p, target_l1_p);
        }
    }

    /// First half of 2M unmap under the window lock: clear the user present bit of the 2M leaf in L2 entry `target_l2i` of
    /// the L2 page `target_l2_p` while keeping `kernel_present`, so future page walks miss and the kernel mapping record that
    /// backs any stale TLB entry stays. The entry is the window's spin lock word; the published word keeps the lock bit.
    /// A caller must flush those entries before invoking `unmap_2m_page_kernel`.
    pub fn unmap_2m_page_user_view(&self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr,
        Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            (WholePageTable { higher: *self, lower: *old(lower) }).wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            self.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            self.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            (WholePageTable { higher: *self, lower: *old(lower) }).spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is Some
                || old(lower).mapping_2m.dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, 0))),
            (WholePageTable { higher: *self, lower: *old(lower) }).window_locked_by_thread(target_l4i, target_l3i, target_l2i, old(lctx).thread_id()),
            old(lower).l2_owner(target_l2_p, target_l2i) == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (WholePageTable { higher: *self, lower: *final(lower) }).wf(),
            (WholePageTable { higher: *self, lower: *final(lower) }).page_closure() =~= (WholePageTable { higher: *self, lower: *old(lower) }).page_closure(),
            final(lower).mapping_2m == old(lower).mapping_2m.insert(spec_index2va((target_l4i, target_l3i, target_l2i, 0)),
                MapEntry { present: false, ..old(lower).mapping_2m.spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, 0))) }),
            final(lower).mapping_4k == old(lower).mapping_4k,
            final(lower).l2_perms.dom() == old(lower).l2_perms.dom(),
            final(lower).l2_entry(target_l2_p, target_l2i) == (PageEntry { perm: PageEntryPerm { present: false, ..old(lower).l2_entry(target_l2_p, target_l2i).perm }, ..old(lower).l2_entry(target_l2_p, target_l2i) }),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_entry(p, i)] (p, i) != (target_l2_p, target_l2i) ==> final(lower).l2_entry(p, i) == old(lower).l2_entry(p, i),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_owner(p, i)] final(lower).l2_owner(p, i) == old(lower).l2_owner(p, i),
            final(lower).pagetable_window_locks == old(lower).pagetable_window_locks,
            final(lower).window_stale_cpus == old(lower).window_stale_cpus,
            old(lower).hidden_l1_tables_in_locked_windows() ==> final(lower).hidden_l1_tables_in_locked_windows(),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                    ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (target_l4i, target_l3i, target_l2i)
                    ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_2m_l2(l4i, l3i, l2i),
            (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(target_l4i, target_l3i, target_l2i) == Some(final(lower).l2_entry(target_l2_p, target_l2i)),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_page(p).entry_lock(i).l1()] pei_valid(i) && !old(lower).l2_entry_hides_l1(p, i) ==> !final(lower).l2_entry_hides_l1(p, i),
    {
        proof {
            let c = WholePageTable { higher: *self, lower: *lower };
            self.wf_l4_at(target_l4i);
            c.l3_links_l2_wf_at(self.spec_resolve_mapping_l4(target_l4i)->0.addr, target_l3i);
            c.wf_l2_at(target_l2_p, target_l2i);
            c.wf_mapping_2m_at(target_l4i, target_l3i, target_l2i);
        }
        let tracked mut l2_perm = lower.l2_perms.tracked_remove(target_l2_p);
        let l2_tbl: &L2PageMap = PPtr::<L2PageMap>::from_usize(target_l2_p).borrow(Tracked(&l2_perm));
        let mut l2_entry = l2_tbl.borrow_entry_lock(target_l2i).get();
        l2_entry.perm.present = false;
        l2_entry_set_published_locked(&PPtr::<L2PageMap>::from_usize(target_l2_p), Tracked(&mut l2_perm), target_l2i, Tracked(window_perm), l2_entry, Tracked(&mut *lctx));
        proof {
            lower.l2_perms.tracked_insert(target_l2_p, l2_perm);
            let va = spec_index2va((target_l4i, target_l3i, target_l2i, 0));
            lower.mapping_2m = lower.mapping_2m.insert(va, MapEntry { present: false, ..old(lower).mapping_2m.spec_index(va) });
            let pre = WholePageTable { higher: *self, lower: *old(lower) };
            let post = WholePageTable { higher: *self, lower: *lower };
            assert(WholePageTable::unmap_2m_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p)) by {
                reveal(WholePageTable::unmap_2m_page_user_view_eof_transition_framing);
            };
            WholePageTable::unmap_2m_page_user_view_eof(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p);
            WholePageTable::unmap_2m_page_user_view_eof_held_chain(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p);
        }
    }

    /// Final half of 2M unmap under the window lock: clear L2 entry `target_l2i` of the L2 page `target_l2_p`, whose 2M leaf's
    /// user present bit is already clear, keeping the lock bit of the published word. Kernel-level callers must additionally
    /// establish that no stale TLB entry remains.
    pub fn unmap_2m_page_kernel(&self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr,
        Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            (WholePageTable { higher: *self, lower: *old(lower) }).wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            self.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            self.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            old(lower).mapping_2m.dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, 0))),
            old(lower).mapping_2m.spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, 0))).present == false,
            (WholePageTable { higher: *self, lower: *old(lower) }).window_locked_by_thread(target_l4i, target_l3i, target_l2i, old(lctx).thread_id()),
            old(lower).l2_owner(target_l2_p, target_l2i) == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (WholePageTable { higher: *self, lower: *final(lower) }).wf(),
            (WholePageTable { higher: *self, lower: *final(lower) }).page_closure() =~= (WholePageTable { higher: *self, lower: *old(lower) }).page_closure(),
            final(lower).mapping_2m == old(lower).mapping_2m.remove(spec_index2va((target_l4i, target_l3i, target_l2i, 0))),
            (WholePageTable { higher: *self, lower: *final(lower) }).spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            (WholePageTable { higher: *self, lower: *final(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            final(lower).mapping_4k == old(lower).mapping_4k,
            final(lower).l2_perms.dom() == old(lower).l2_perms.dom(),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_entry(p, i)] (p, i) != (target_l2_p, target_l2i) ==> final(lower).l2_entry(p, i) == old(lower).l2_entry(p, i),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_owner(p, i)] final(lower).l2_owner(p, i) == old(lower).l2_owner(p, i),
            final(lower).pagetable_window_locks == old(lower).pagetable_window_locks,
            final(lower).window_stale_cpus == old(lower).window_stale_cpus,
            old(lower).hidden_l1_tables_in_locked_windows() ==> final(lower).hidden_l1_tables_in_locked_windows(),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                    ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (target_l4i, target_l3i, target_l2i)
                    ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_2m_l2(l4i, l3i, l2i),
            (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_page(p).entry_lock(i).l1()] pei_valid(i) && !old(lower).l2_entry_hides_l1(p, i) ==> !final(lower).l2_entry_hides_l1(p, i),
    {
        proof {
            let c = WholePageTable { higher: *self, lower: *lower };
            self.wf_l4_at(target_l4i);
            c.l3_links_l2_wf_at(self.spec_resolve_mapping_l4(target_l4i)->0.addr, target_l3i);
            c.wf_l2_at(target_l2_p, target_l2i);
            c.wf_mapping_2m_at(target_l4i, target_l3i, target_l2i);
            mem_valid_zero();
        }
        let tracked mut l2_perm = lower.l2_perms.tracked_remove(target_l2_p);
        l2_entry_set_published_locked(&PPtr::<L2PageMap>::from_usize(target_l2_p), Tracked(&mut l2_perm), target_l2i, Tracked(window_perm), PageEntry::empty(), Tracked(&mut *lctx));
        proof {
            lower.l2_perms.tracked_insert(target_l2_p, l2_perm);
            lower.mapping_2m = lower.mapping_2m.remove(spec_index2va((target_l4i, target_l3i, target_l2i, 0)));
            let pre = WholePageTable { higher: *self, lower: *old(lower) };
            let post = WholePageTable { higher: *self, lower: *lower };
            assert(WholePageTable::unmap_2m_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p)) by {
                reveal(WholePageTable::unmap_2m_page_kernel_eof_transition_framing);
            };
            WholePageTable::unmap_2m_page_kernel_eof(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p);
            WholePageTable::unmap_2m_page_kernel_eof_held_chain(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p);
        }
    }

    /// Hide the L1 page `target_l1_p` that window `(target_l4i, target_l3i, target_l2i)` links and that maps no 4K page:
    /// publish the window's L2 entry with every permission bit clear but the L1 address kept, so future page walks miss; the
    /// L1 page stays in the window lock, its reverse index, and the page closure. The entry is the window's spin lock word, so
    /// this thread must hold that window lock; the published word keeps the lock bit. A caller must flush the cached L2 entries
    /// before `unlink_hidden_l1_page` takes the page out.
    pub fn hide_l1_page(&self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr,
        target_l1_p: PageMapPtr, Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            (WholePageTable { higher: *self, lower: *old(lower) }).wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            self.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            self.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            (WholePageTable { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            (WholePageTable { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            forall|l1i: L1Index| #![trigger old(lower).mapping_4k.dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, l1i)))]
                pei_valid(l1i) ==> !old(lower).mapping_4k.dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, l1i))),
            (WholePageTable { higher: *self, lower: *old(lower) }).window_locked_by_thread(target_l4i, target_l3i, target_l2i, old(lctx).thread_id()),
            old(lower).l2_owner(target_l2_p, target_l2i) == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (WholePageTable { higher: *self, lower: *final(lower) }).wf(),
            (WholePageTable { higher: *self, lower: *final(lower) }).page_closure() =~= (WholePageTable { higher: *self, lower: *old(lower) }).page_closure(),
            final(lower).mapping_4k == old(lower).mapping_4k,
            final(lower).mapping_2m == old(lower).mapping_2m,
            final(lower).l1_rev_map == old(lower).l1_rev_map,
            final(lower).l2_perms.dom() == old(lower).l2_perms.dom(),
            final(lower).l2_entry(target_l2_p, target_l2i) == (PageEntry { addr: target_l1_p, perm: PageEntryPerm { present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: true } }),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_entry(p, i)] (p, i) != (target_l2_p, target_l2i) ==> final(lower).l2_entry(p, i) == old(lower).l2_entry(p, i),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_owner(p, i)] final(lower).l2_owner(p, i) == old(lower).l2_owner(p, i),
            final(lower).l2_page(target_l2_p).entry_lock(target_l2i).l1() == old(lower).l2_page(target_l2_p).entry_lock(target_l2i).l1(),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_page(p).entry_lock(i).l1()]
                old(lower).l2_perms.dom().contains(p) && (p, i) != (target_l2_p, target_l2i) ==> final(lower).l2_page(p).entry_lock(i).l1() == old(lower).l2_page(p).entry_lock(i).l1(),
            final(lower).l2_entry_hides_l1(target_l2_p, target_l2i),
            final(lower).l1_perm(target_l2_p, target_l2i).addr() == target_l1_p,
            (WholePageTable { higher: *self, lower: *final(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (target_l4i, target_l3i, target_l2i)
                    ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i),
            final(lower).pagetable_window_locks == old(lower).pagetable_window_locks,
            final(lower).window_stale_cpus == old(lower).window_stale_cpus,
            old(lower).hidden_l1_tables_in_locked_windows() ==> final(lower).hidden_l1_tables_in_locked_windows(),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (target_l4i, target_l3i, target_l2i)
                    ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                    ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_2m_l2(l4i, l3i, l2i),
            (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(target_l4i, target_l3i, target_l2i) == Some(final(lower).l2_entry(target_l2_p, target_l2i)),
    {
        proof {
            let c = WholePageTable { higher: *self, lower: *lower };
            self.wf_l4_at(target_l4i);
            c.l3_links_l2_wf_at(self.spec_resolve_mapping_l4(target_l4i)->0.addr, target_l3i);
            c.wf_l2_at(target_l2_p, target_l2i);
            c.table_pages_wf_l1_at(target_l1_p);
            page_ptr_valid_imply_mem_valid(target_l1_p);
        }
        let tracked mut l2_perm = lower.l2_perms.tracked_remove(target_l2_p);
        l2_entry_set_published_locked(&PPtr::<L2PageMap>::from_usize(target_l2_p), Tracked(&mut l2_perm), target_l2i, Tracked(window_perm),
            PageEntry { addr: target_l1_p, perm: PageEntryPerm { present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: true } }, Tracked(&mut *lctx));
        proof {
            lower.l2_perms.tracked_insert(target_l2_p, l2_perm);
            let pre = WholePageTable { higher: *self, lower: *old(lower) };
            let post = WholePageTable { higher: *self, lower: *lower };
            assert(WholePageTable::hide_l1_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p)) by {
                reveal(WholePageTable::hide_l1_page_eof_transition_framing);
            };
            WholePageTable::hide_l1_page_eof(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
            WholePageTable::hide_l1_page_eof_held_chain(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        }
    }

    /// Take the hidden L1 page `target_l1_p` out of window `(target_l4i, target_l3i, target_l2i)` and return it: publish the entry
    /// cleared, dropping the hidden-L1 marker `hide_l1_page` published, then move the page out; it leaves its reverse index and the
    /// page closure. The caller holds that window lock under `window_perm`, so the published word keeps the lock bit, and no CPU is
    /// still listed as caching the window's entries.
    pub fn unlink_hidden_l1_page(&self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index,
        target_l2_p: PageMapPtr, target_l1_p: PageMapPtr, Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<PointsTo<PageMap>>)
        requires
            (WholePageTable { higher: *self, lower: *old(lower) }).wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            self.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            self.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            old(lower).l2_entry_hides_l1(target_l2_p, target_l2i),
            old(lower).l2_entry(target_l2_p, target_l2i).addr == target_l1_p,
            old(lower).l2_owner(target_l2_p, target_l2i) == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
            !old(lower).window_stale_cpus.dom().contains((target_l2_p, target_l2i)),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (WholePageTable { higher: *self, lower: *final(lower) }).wf(),
            (WholePageTable { higher: *self, lower: *final(lower) }).page_closure() =~= (WholePageTable { higher: *self, lower: *old(lower) }).page_closure().remove(target_l1_p),
            final(lower).l1_rev_map == old(lower).l1_rev_map.remove(target_l1_p),
            final(lower).mapping_4k == old(lower).mapping_4k,
            final(lower).mapping_2m == old(lower).mapping_2m,
            final(lower).l2_perms.dom() == old(lower).l2_perms.dom(),
            final(lower).l2_entry(target_l2_p, target_l2i).is_empty(),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_entry(p, i)] (p, i) != (target_l2_p, target_l2i) ==> final(lower).l2_entry(p, i) == old(lower).l2_entry(p, i),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_owner(p, i)] final(lower).l2_owner(p, i) == old(lower).l2_owner(p, i),
            final(lower).l2_page(target_l2_p).entry_lock(target_l2i).l1() is None,
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_page(p).entry_lock(i).l1()]
                old(lower).l2_perms.dom().contains(p) && (p, i) != (target_l2_p, target_l2i) ==> final(lower).l2_page(p).entry_lock(i).l1() == old(lower).l2_page(p).entry_lock(i).l1(),
            final(lower).pagetable_window_locks == old(lower).pagetable_window_locks,
            final(lower).window_stale_cpus == old(lower).window_stale_cpus,
            old(lower).hidden_l1_tables_in_locked_windows() ==> final(lower).hidden_l1_tables_in_locked_windows(),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (target_l4i, target_l3i, target_l2i)
                    ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i) != (target_l4i, target_l3i, target_l2i)
                    ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_2m_l2(l4i, l3i, l2i),
            (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(target_l4i, target_l3i, target_l2i) is None,
            forall|l1i: L1Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(target_l4i, target_l3i, target_l2i, l1i)]
                pei_valid(l1i) ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(target_l4i, target_l3i, target_l2i, l1i) is None,
            ret.view().addr() == target_l1_p,
            ret.view().is_init(),
    {
        proof {
            let c = WholePageTable { higher: *self, lower: *lower };
            self.wf_l4_at(target_l4i);
            c.l3_links_l2_wf_at(self.spec_resolve_mapping_l4(target_l4i)->0.addr, target_l3i);
            c.wf_l2_at(target_l2_p, target_l2i);
            c.wf_l1_at(target_l2_p, target_l2i);
            mem_valid_zero();
        }
        let tracked mut l2_perm = lower.l2_perms.tracked_remove(target_l2_p);
        l2_entry_set_published_locked(&PPtr::<L2PageMap>::from_usize(target_l2_p), Tracked(&mut l2_perm), target_l2i, Tracked(window_perm), PageEntry::empty(), Tracked(&mut *lctx));
        let tracked l1_perm = l2_entry_take_l1(&mut l2_perm, target_l2i, window_perm);
        proof {
            lower.l2_perms.tracked_insert(target_l2_p, l2_perm);
            lower.l1_rev_map = lower.l1_rev_map.remove(target_l1_p);
            let pre = WholePageTable { higher: *self, lower: *old(lower) };
            let post = WholePageTable { higher: *self, lower: *lower };
            assert(WholePageTable::unlink_hidden_l1_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p)) by {
                reveal(WholePageTable::unlink_hidden_l1_page_eof_transition_framing);
            };
            WholePageTable::unlink_hidden_l1_page_eof(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
            WholePageTable::unlink_hidden_l1_page_eof_held_chain(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        }
        Tracked(l1_perm)
    }

    /// Take the L1 page `target_l1_p` that entry `target_l2i` of the held L2 page `target_l2_p` owns out of a path that no longer
    /// resolves, and return it: publish the entry cleared, then move the page out; it leaves its reverse index and the page closure.
    /// No thread holds the entry's window lock, so the published word keeps the lock bit clear; the caller holds the table's big lock
    /// in write mode, and no CPU is still listed as caching the window's entries.
    pub fn unlink_unresolvable_l1_page(&self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index,
        target_l2_p: PageMapPtr, target_l1_p: PageMapPtr, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<PointsTo<PageMap>>)
        requires
            (WholePageTable { higher: *self, lower: *old(lower) }).wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            self.spec_held_l3(target_l4i, target_l3i) is Some,
            self.spec_held_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            old(lower).l2_page(target_l2_p).entry_lock(target_l2i).l1() is Some,
            old(lower).l2_entry(target_l2_p, target_l2i).addr == target_l1_p,
            (WholePageTable { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            old(lower).l2_owner(target_l2_p, target_l2i) is None,
            !old(lower).window_stale_cpus.dom().contains((target_l2_p, target_l2i)),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (WholePageTable { higher: *self, lower: *final(lower) }).wf(),
            (WholePageTable { higher: *self, lower: *final(lower) }).page_closure() =~= (WholePageTable { higher: *self, lower: *old(lower) }).page_closure().remove(target_l1_p),
            final(lower).l1_rev_map == old(lower).l1_rev_map.remove(target_l1_p),
            final(lower).mapping_4k == old(lower).mapping_4k,
            final(lower).mapping_2m == old(lower).mapping_2m,
            final(lower).l2_perms.dom() == old(lower).l2_perms.dom(),
            final(lower).l2_entry(target_l2_p, target_l2i).is_empty(),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_entry(p, i)] (p, i) != (target_l2_p, target_l2i) ==> final(lower).l2_entry(p, i) == old(lower).l2_entry(p, i),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_owner(p, i)] final(lower).l2_owner(p, i) == old(lower).l2_owner(p, i),
            final(lower).l2_page(target_l2_p).entry_lock(target_l2i).l1() is None,
            final(lower).pagetable_window_locks == old(lower).pagetable_window_locks,
            final(lower).window_stale_cpus == old(lower).window_stale_cpus,
            old(lower).hidden_l1_tables_in_locked_windows() ==> final(lower).hidden_l1_tables_in_locked_windows(),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (target_l4i, target_l3i, target_l2i)
                    ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i) != (target_l4i, target_l3i, target_l2i)
                    ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_2m_l2(l4i, l3i, l2i),
            (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(target_l4i, target_l3i, target_l2i) is None,
            forall|l1i: L1Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(target_l4i, target_l3i, target_l2i, l1i)]
                pei_valid(l1i) ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(target_l4i, target_l3i, target_l2i, l1i) is None,
            ret.view().addr() == target_l1_p,
            ret.view().is_init(),
    {
        proof {
            let c = WholePageTable { higher: *self, lower: *lower };
            self.wf_l4_at(target_l4i);
            c.l3_links_l2_wf_at(self.spec_held_l4(target_l4i)->0.addr, target_l3i);
            c.wf_l2_at(target_l2_p, target_l2i);
            c.wf_l1_at(target_l2_p, target_l2i);
            mem_valid_zero();
        }
        let tracked mut l2_perm = lower.l2_perms.tracked_remove(target_l2_p);
        l2_entry_set_published_unlocked(&PPtr::<L2PageMap>::from_usize(target_l2_p), Tracked(&mut l2_perm), target_l2i, PageEntry::empty(), Tracked(&mut *lctx));
        let tracked l1_perm = l2_entry_take_l1_unlocked(&mut l2_perm, target_l2i);
        proof {
            lower.l2_perms.tracked_insert(target_l2_p, l2_perm);
            lower.l1_rev_map = lower.l1_rev_map.remove(target_l1_p);
            let pre = WholePageTable { higher: *self, lower: *old(lower) };
            let post = WholePageTable { higher: *self, lower: *lower };
            assert(WholePageTable::unlink_unresolvable_l1_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p)) by {
                reveal(WholePageTable::unlink_unresolvable_l1_page_eof_transition_framing);
            };
            WholePageTable::unlink_unresolvable_l1_page_eof(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
            WholePageTable::unlink_unresolvable_l1_page_eof_held_chain(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        }
        Tracked(l1_perm)
    }

    /// Clear the held 4K leaf `(target_l4i, target_l3i, target_l2i, target_l1i)` under the user root entry `target_l4i`, which no longer
    /// resolves: the L1 page that the held L2 entry owns publishes the leaf cleared and stays in place, so no mapping changes. No path to
    /// the leaf resolves, so the entry's window lock is free; the caller holds the table's big lock in write mode, which every window lock
    /// follows, and the L1 token moves through the unlocked slot.
    pub fn clear_held_4k_leaf(&self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index,
        target_l1i: L1Index, Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            (WholePageTable { higher: *self, lower: *old(lower) }).wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            self.spec_resolve_mapping_l4(target_l4i) is None,
            (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is Some,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (WholePageTable { higher: *self, lower: *final(lower) }).wf(),
            (WholePageTable { higher: *self, lower: *final(lower) }).page_closure() =~= (WholePageTable { higher: *self, lower: *old(lower) }).page_closure(),
            final(lower).l1_rev_map == old(lower).l1_rev_map,
            final(lower).mapping_4k == old(lower).mapping_4k,
            final(lower).mapping_2m == old(lower).mapping_2m,
            final(lower).l2_perms.dom() == old(lower).l2_perms.dom(),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_entry(p, i)] final(lower).l2_entry(p, i) == old(lower).l2_entry(p, i),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_owner(p, i)] final(lower).l2_owner(p, i) == old(lower).l2_owner(p, i),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_page(p).entry_lock(i).l1()]
                (p, i) != (self.spec_held_l3(target_l4i, target_l3i)->0.addr, target_l2i) ==> final(lower).l2_page(p).entry_lock(i).l1() == old(lower).l2_page(p).entry_lock(i).l1(),
            final(lower).l2_page(self.spec_held_l3(target_l4i, target_l3i)->0.addr).entry_lock(target_l2i).l1() is Some,
            forall|w: WindowVa| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).window_view(w)]
                self.kernel_l4_end <= spec_v2l4index(w.va) && pei_valid(spec_v2l4index(w.va)) && pei_valid(spec_v2l3index(w.va))
                    && (WholePageTable { higher: *self, lower: *old(lower) }).window_exists(spec_v2l4index(w.va), spec_v2l3index(w.va))
                    ==> (WholePageTable { higher: *self, lower: *final(lower) }).window_view(w) == (WholePageTable { higher: *self, lower: *old(lower) }).window_view(w),
            final(lower).pagetable_window_locks == old(lower).pagetable_window_locks,
            final(lower).window_stale_cpus == old(lower).window_stale_cpus,
            old(lower).hidden_l1_tables_in_locked_windows() ==> final(lower).hidden_l1_tables_in_locked_windows(),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_2m_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i, l1i) != (target_l4i, target_l3i, target_l2i, target_l1i)
                    ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i),
            (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None,
    {
        let ghost pre = WholePageTable { higher: *self, lower: *lower };
        if let Some(l4_entry) = self.get_held_entry_l4(target_l4i) {
            if let Some(l3_entry) = self.get_held_entry_l3(target_l4i, target_l3i, &l4_entry) {
                let target_l2_p = l3_entry.addr;
                proof {
                    self.wf_l4_at(target_l4i);
                    pre.l3_links_l2_wf_at(l4_entry.addr, target_l3i);
                    pre.wf_l2_at(target_l2_p, target_l2i);
                    pre.wf_l1_at(target_l2_p, target_l2i);
                    pre.tables_reachable_wf_l2_at(target_l2_p);
                    self.disjoint_l4_l3_implies_held_l3_addr_unique_at(target_l4i, target_l3i, self.l2_rev_map.view().spec_index(target_l2_p).0, self.l2_rev_map.view().spec_index(target_l2_p).1);
                    pre.wf_window_locks_l2_entry_at(target_l2_p, target_l2i);
                    mem_valid_zero();
                }
                let tracked l2_perm_ref = lower.l2_perms.tracked_borrow(target_l2_p);
                let l2_tbl: &L2PageMap = PPtr::<L2PageMap>::from_usize(target_l2_p).borrow(Tracked(l2_perm_ref));
                let target_l1_p = l2_tbl.borrow_entry_lock(target_l2i).get().addr;
                let tracked mut l2_perm = lower.l2_perms.tracked_remove(target_l2_p);
                let tracked mut l1_perm = l2_entry_take_l1_unlocked(&mut l2_perm, target_l2i);
                page_map_set_published(target_l1_p, Tracked(&mut l1_perm), target_l1i, PageEntry::empty(), Tracked(&mut *lctx));
                proof {
                    l2_entry_put_l1_unlocked(&mut l2_perm, target_l2i, l1_perm);
                    lower.l2_perms.tracked_insert(target_l2_p, l2_perm);
                    let post = WholePageTable { higher: *self, lower: *lower };
                    assert(WholePageTable::clear_held_4k_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i)) by {
                        reveal(WholePageTable::clear_held_4k_leaf_eof_transition_framing);
                    };
                    WholePageTable::clear_held_4k_leaf_eof(pre, post, target_l4i, target_l3i, target_l2i, target_l1i);
                    WholePageTable::clear_held_4k_leaf_eof_held_chain(pre, post, target_l4i, target_l3i, target_l2i, target_l1i);
                }
            }
        }
    }

    /// Clear the held 2M leaf `(target_l4i, target_l3i, target_l2i)` under the user root entry `target_l4i`, which no longer resolves:
    /// the held L2 entry is published cleared and stays in its L2 page, so no mapping changes. No path to the leaf resolves, so the
    /// entry's window lock is free; the caller holds the table's big lock in write mode, which every window lock follows. A 2M leaf
    /// owns no L1 page, so no L1 token moves.
    pub fn clear_held_2m_leaf(&self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index,
        Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            (WholePageTable { higher: *self, lower: *old(lower) }).wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            self.spec_resolve_mapping_l4(target_l4i) is None,
            (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_2m_l2(target_l4i, target_l3i, target_l2i) is Some,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (WholePageTable { higher: *self, lower: *final(lower) }).wf(),
            (WholePageTable { higher: *self, lower: *final(lower) }).page_closure() =~= (WholePageTable { higher: *self, lower: *old(lower) }).page_closure(),
            final(lower).l1_rev_map == old(lower).l1_rev_map,
            final(lower).mapping_4k == old(lower).mapping_4k,
            final(lower).mapping_2m == old(lower).mapping_2m,
            final(lower).l2_perms.dom() == old(lower).l2_perms.dom(),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_entry(p, i)]
                (p, i) != (self.spec_held_l3(target_l4i, target_l3i)->0.addr, target_l2i) ==> final(lower).l2_entry(p, i) == old(lower).l2_entry(p, i),
            final(lower).l2_entry(self.spec_held_l3(target_l4i, target_l3i)->0.addr, target_l2i).is_empty(),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_owner(p, i)] final(lower).l2_owner(p, i) == old(lower).l2_owner(p, i),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_page(p).entry_lock(i).l1()] final(lower).l2_page(p).entry_lock(i).l1() == old(lower).l2_page(p).entry_lock(i).l1(),
            forall|w: WindowVa| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).window_view(w)]
                self.kernel_l4_end <= spec_v2l4index(w.va) && pei_valid(spec_v2l4index(w.va)) && pei_valid(spec_v2l3index(w.va))
                    && (WholePageTable { higher: *self, lower: *old(lower) }).window_exists(spec_v2l4index(w.va), spec_v2l3index(w.va))
                    ==> (WholePageTable { higher: *self, lower: *final(lower) }).window_view(w) == (WholePageTable { higher: *self, lower: *old(lower) }).window_view(w),
            final(lower).pagetable_window_locks == old(lower).pagetable_window_locks,
            final(lower).window_stale_cpus == old(lower).window_stale_cpus,
            old(lower).hidden_l1_tables_in_locked_windows() ==> final(lower).hidden_l1_tables_in_locked_windows(),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                    ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (target_l4i, target_l3i, target_l2i)
                    ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_2m_l2(l4i, l3i, l2i),
            (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(target_l4i, target_l3i, target_l2i) is None,
    {
        let ghost pre = WholePageTable { higher: *self, lower: *lower };
        if let Some(l4_entry) = self.get_held_entry_l4(target_l4i) {
            if let Some(l3_entry) = self.get_held_entry_l3(target_l4i, target_l3i, &l4_entry) {
                let target_l2_p = l3_entry.addr;
                proof {
                    self.wf_l4_at(target_l4i);
                    pre.l3_links_l2_wf_at(l4_entry.addr, target_l3i);
                    pre.wf_l2_at(target_l2_p, target_l2i);
                    pre.tables_reachable_wf_l2_at(target_l2_p);
                    self.disjoint_l4_l3_implies_held_l3_addr_unique_at(target_l4i, target_l3i, self.l2_rev_map.view().spec_index(target_l2_p).0, self.l2_rev_map.view().spec_index(target_l2_p).1);
                    pre.wf_window_locks_l2_entry_at(target_l2_p, target_l2i);
                    mem_valid_zero();
                }
                let tracked mut l2_perm = lower.l2_perms.tracked_remove(target_l2_p);
                l2_entry_set_published_unlocked(&PPtr::<L2PageMap>::from_usize(target_l2_p), Tracked(&mut l2_perm), target_l2i, PageEntry::empty(), Tracked(&mut *lctx));
                proof {
                    lower.l2_perms.tracked_insert(target_l2_p, l2_perm);
                    let post = WholePageTable { higher: *self, lower: *lower };
                    assert(WholePageTable::clear_held_2m_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i)) by {
                        reveal(WholePageTable::clear_held_2m_leaf_eof_transition_framing);
                    };
                    WholePageTable::clear_held_2m_leaf_eof(pre, post, target_l4i, target_l3i, target_l2i);
                    WholePageTable::clear_held_2m_leaf_eof_held_chain(pre, post, target_l4i, target_l3i, target_l2i);
                }
            }
        }
    }

    /// Unlink the L1 page of window `(target_l4i, target_l3i, target_l2i)` and return it. The cleared L2 entry is the window's
    /// spin lock word, so this thread must hold that window lock; the published word keeps the lock bit.
    pub fn remove_l2_entry(&self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index,
        target_l2_p: PageMapPtr, target_l1_p: PageMapPtr, Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>)
        -> (ret: (PageMapPtr, Tracked<PointsTo<PageMap>>))
        requires
            (WholePageTable { higher: *self, lower: *old(lower) }).wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            self.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            self.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            (WholePageTable { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            (WholePageTable { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            forall|i: L1Index|
                #![trigger (WholePageTable { higher: *self, lower: *old(lower) }).spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, i)]
                pei_valid(i) ==> (WholePageTable { higher: *self, lower: *old(lower) }).spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, i) is None,
            (WholePageTable { higher: *self, lower: *old(lower) }).window_locked_by_thread(target_l4i, target_l3i, target_l2i, old(lctx).thread_id()),
            old(lower).l2_owner(target_l2_p, target_l2i) == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (WholePageTable { higher: *self, lower: *final(lower) }).wf(),
            (WholePageTable { higher: *self, lower: *final(lower) }).page_closure() =~= (WholePageTable { higher: *self, lower: *old(lower) }).page_closure().remove(target_l1_p),
            final(lower).mapping_4k == old(lower).mapping_4k,
            final(lower).mapping_2m == old(lower).mapping_2m,
            final(lower).l2_perms.dom() == old(lower).l2_perms.dom(),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_owner(p, i)] final(lower).l2_owner(p, i) == old(lower).l2_owner(p, i),
            final(lower).pagetable_window_locks == old(lower).pagetable_window_locks,
            final(lower).window_stale_cpus == old(lower).window_stale_cpus,
            old(lower).hidden_l1_tables_in_locked_windows() ==> final(lower).hidden_l1_tables_in_locked_windows(),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (target_l4i, target_l3i, target_l2i)
                    ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i) != (target_l4i, target_l3i, target_l2i)
                    ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_held_2m_l2(l4i, l3i, l2i),
            (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_l2(target_l4i, target_l3i, target_l2i) is None,
            forall|l1i: L1Index| #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(target_l4i, target_l3i, target_l2i, l1i)]
                pei_valid(l1i) ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(target_l4i, target_l3i, target_l2i, l1i) is None,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
                #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                #![trigger (WholePageTable { higher: *self, lower: *old(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    ==> (WholePageTable { higher: *self, lower: *final(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id) == (WholePageTable { higher: *self, lower: *old(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id),
            ret.0 == target_l1_p,
            ret.1.view().is_init(),
            ret.1.view().addr() == target_l1_p,
    {
        proof {
            let c = WholePageTable { higher: *self, lower: *lower };
            self.wf_l4_at(target_l4i);
            c.l3_links_l2_wf_at(self.spec_resolve_mapping_l4(target_l4i)->0.addr, target_l3i);
            c.wf_l2_at(target_l2_p, target_l2i);
            c.wf_l1_at(target_l2_p, target_l2i);
            mem_valid_zero();
        }
        let tracked mut l2_perm = lower.l2_perms.tracked_remove(target_l2_p);
        l2_entry_set_published_locked(&PPtr::<L2PageMap>::from_usize(target_l2_p), Tracked(&mut l2_perm), target_l2i, Tracked(window_perm), PageEntry::empty(), Tracked(&mut *lctx));
        let tracked l1_perm = l2_entry_take_l1(&mut l2_perm, target_l2i, window_perm);
        proof {
            lower.l2_perms.tracked_insert(target_l2_p, l2_perm);
            lower.l1_rev_map = lower.l1_rev_map.remove(target_l1_p);
            let pre = WholePageTable { higher: *self, lower: *old(lower) };
            let post = WholePageTable { higher: *self, lower: *lower };
            assert(WholePageTable::remove_l2_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p)) by {
                reveal(WholePageTable::remove_l2_entry_eof_transition_framing);
            };
            WholePageTable::remove_l2_entry_eof(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
            WholePageTable::remove_l2_entry_eof_held_chain(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        }
        (target_l1_p, Tracked(l1_perm))
    }

    /// Unlink the L2 page, which owns no L1 page and has no resolving 2M leaf, under the held L3 entry `(target_l4i, target_l3i)`
    /// and return it as an ordinary 4K page. No window of that page may be locked.
    pub fn remove_l3_entry(&mut self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr,
        target_l2_p: PageMapPtr, cpu_tlb: &CpuTLB, cpu_arr: &CpuLockedArray, needflush: &PcidNeedFlushArray, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: (PageMapPtr, Tracked<PagePerm4k>))
        requires
            (WholePageTable { higher: *old(self), lower: *old(lower) }).wf(),
            old(self).kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            old(self).spec_held_l4(target_l4i) is Some,
            old(self).spec_held_l4(target_l4i)->0.addr == target_l3_p,
            old(self).spec_held_l3(target_l4i, target_l3i) is Some,
            old(self).spec_held_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            forall|i: L2Index|
                #![trigger old(lower).l2_page(target_l2_p).entry_lock(i).l1()]
                #![trigger old(lower).l2_entry(target_l2_p, i)]
                pei_valid(i) ==> old(lower).l2_page(target_l2_p).entry_lock(i).l1() is None,
            forall|i: L2Index|
                #![trigger (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i)]
                pei_valid(i) ==> (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index| #![trigger old(lower).l2_owner(target_l2_p, i)] pei_valid(i) ==> old(lower).l2_owner(target_l2_p, i) is None,
            old(lower).hidden_l1_tables_in_locked_windows(),
            table_page_unreferenced_by_structure_caches(*cpu_tlb, *cpu_arr, *needflush, target_l2_p),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (WholePageTable { higher: *final(self), lower: *final(lower) }).wf(),
            (WholePageTable { higher: *final(self), lower: *final(lower) }).page_closure() =~= (WholePageTable { higher: *old(self), lower: *old(lower) }).page_closure().remove(target_l2_p),
            final(lower).mapping_4k == old(lower).mapping_4k,
            final(lower).mapping_2m == old(lower).mapping_2m,
            final(self).mapping_1g == old(self).mapping_1g,
            final(self).kernel_entries == old(self).kernel_entries,
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).cr3 == old(self).cr3,
            final(self).pcid == old(self).pcid,
            final(self).did == old(self).did,
            final(self).proc_ptr == old(self).proc_ptr,
            final(self).table_stale_cpus == old(self).table_stale_cpus,
            final(lower).pagetable_window_locks
                == old(lower).pagetable_window_locks.remove_keys(old(lower).pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == target_l4i && spec_v2l3index(w.va) == target_l3i)),
            final(lower).window_stale_cpus == old(lower).window_stale_cpus.filter_keys(|k: (PageMapPtr, L2Index)| k.0 != target_l2_p),
            final(lower).hidden_l1_tables_in_locked_windows(),
            final(lower).l2_perms.dom() == old(lower).l2_perms.dom().remove(target_l2_p),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_owner(p, i)] final(lower).l2_perms.dom().contains(p) ==> final(lower).l2_owner(p, i) == old(lower).l2_owner(p, i),
            forall|l4i: L4Index| #![trigger final(self).spec_resolve_mapping_l4(l4i)] old(self).kernel_l4_end <= l4i && pei_valid(l4i) ==> final(self).spec_resolve_mapping_l4(l4i) == old(self).spec_resolve_mapping_l4(l4i),
            forall|l4i: L4Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_l4(l4i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_l4(l4i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_held_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_l3(l4i, l3i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (target_l4i, target_l3i)
                    ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_l3(l4i, l3i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_held_l3(l4i, l3i),
            (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_l3(target_l4i, target_l3i) is None,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                    ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i) != (target_l4i, target_l3i)
                    ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_held_2m_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_1g_l3(l4i, l3i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (target_l4i, target_l3i)
                    ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_1g_l3(l4i, l3i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_held_1g_l3(l4i, l3i),
            (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_1g_l3(target_l4i, target_l3i) is None,
            forall|l2i: L2Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_2m_l2(target_l4i, target_l3i, l2i)] pei_valid(l2i) ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_2m_l2(target_l4i, target_l3i, l2i) is None,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
                #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                #![trigger (WholePageTable { higher: *old(self), lower: *old(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id) == (WholePageTable { higher: *old(self), lower: *old(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id),
            ret.0 == target_l2_p,
            ret.1.view().is_init(),
            ret.1.view().addr() == target_l2_p,
    {
        proof {
            let c = WholePageTable { higher: *self, lower: *lower };
            self.wf_l4_at(target_l4i);
            self.wf_l3_at(target_l3_p);
            c.l3_links_l2_wf_at(target_l3_p, target_l3i);
            c.wf_l2_at(target_l2_p, 0);
            mem_valid_zero();
        }
        page_map_set_published_in_map(target_l3_p, Tracked(self.l3_tables.borrow_mut()), target_l3i, PageEntry::empty(), Tracked(&mut *lctx));
        proof { self.l2_rev_map = Ghost(self.l2_rev_map.view().remove(target_l2_p)); }
        let tracked l2_perm = lower.l2_perms.tracked_remove(target_l2_p);
        let page_perm = l2_page_map_to_page_perm(Tracked(l2_perm), cpu_tlb, cpu_arr, needflush);
        proof {
            lower.pagetable_window_locks = lower.pagetable_window_locks.remove_keys(lower.pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == target_l4i && spec_v2l3index(w.va) == target_l3i));
            lower.window_stale_cpus = lower.window_stale_cpus.filter_keys(|k: (PageMapPtr, L2Index)| k.0 != target_l2_p);
            let pre = WholePageTable { higher: *old(self), lower: *old(lower) };
            let post = WholePageTable { higher: *self, lower: *lower };
            assert(WholePageTable::remove_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p)) by {
                reveal(WholePageTable::remove_l3_entry_eof_transition_framing);
            };
            WholePageTable::remove_l3_entry_eof(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p);
            WholePageTable::remove_l3_entry_eof_held_chain(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p);
        }
        (target_l2_p, page_perm)
    }

    /// Unlink the L3 page under the held user root entry `target_l4i`, present or a placeholder, and return it. The window half
    /// is untouched: no L2 page hangs under that entry.
    pub fn remove_l4_entry(&mut self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3_p: PageMapPtr,
        Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: (PageMapPtr, Tracked<PointsTo<PageMap>>))
        requires
            (WholePageTable { higher: *old(self), lower: *lower }).wf(),
            old(self).kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            old(self).spec_held_l4(target_l4i) is Some,
            old(self).spec_held_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![trigger old(self).spec_held_l3(target_l4i, i)] pei_valid(i) ==> old(self).spec_held_l3(target_l4i, i) is None,
            forall|i: L3Index| #![trigger old(self).spec_resolve_mapping_1g_l3(target_l4i, i)] pei_valid(i) ==> old(self).spec_resolve_mapping_1g_l3(target_l4i, i) is None,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (WholePageTable { higher: *final(self), lower: *lower }).wf(),
            (WholePageTable { higher: *final(self), lower: *lower }).page_closure() =~= (WholePageTable { higher: *old(self), lower: *lower }).page_closure().remove(target_l3_p),
            final(self).mapping_1g == old(self).mapping_1g,
            final(self).kernel_entries == old(self).kernel_entries,
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).cr3 == old(self).cr3,
            final(self).pcid == old(self).pcid,
            final(self).did == old(self).did,
            final(self).proc_ptr == old(self).proc_ptr,
            final(self).table_stale_cpus == old(self).table_stale_cpus,
            forall|l4i: L4Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_held_l4(l4i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && l4i != target_l4i ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_held_l4(l4i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_held_l4(l4i),
            (WholePageTable { higher: *final(self), lower: *lower }).spec_held_l4(target_l4i) is None,
            forall|l4i: L4Index| #![trigger final(self).spec_resolve_mapping_l4(l4i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && l4i != target_l4i ==> final(self).spec_resolve_mapping_l4(l4i) == old(self).spec_resolve_mapping_l4(l4i),
            final(self).spec_resolve_mapping_l4(target_l4i) is None,
            forall|l4i: L4Index, l3i: L3Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_held_l3(l4i, l3i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_held_l3(l4i, l3i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_held_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_held_l2(l4i, l3i, l2i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_held_l2(l4i, l3i, l2i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                    ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_held_4k_l1(l4i, l3i, l2i, l1i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_held_2m_l2(l4i, l3i, l2i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_held_2m_l2(l4i, l3i, l2i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_held_2m_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_held_1g_l3(l4i, l3i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && (WholePageTable { higher: *final(self), lower: *lower }).spec_held_1g_l3(l4i, l3i) is Some
                    ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_held_1g_l3(l4i, l3i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_held_1g_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
                #![trigger (WholePageTable { higher: *final(self), lower: *lower }).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                #![trigger (WholePageTable { higher: *old(self), lower: *lower }).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    ==> (WholePageTable { higher: *final(self), lower: *lower }).window_locked_by_thread(l4i, l3i, l2i, thread_id) == (WholePageTable { higher: *old(self), lower: *lower }).window_locked_by_thread(l4i, l3i, l2i, thread_id),
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
            let pre = WholePageTable { higher: *old(self), lower: *lower };
            let post = WholePageTable { higher: *self, lower: *lower };
            assert(WholePageTable::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p)) by { reveal(WholePageTable::remove_l4_entry_eof_transition_framing); };
            WholePageTable::remove_l4_entry_eof(pre, post, target_l4i, target_l3_p);
            WholePageTable::remove_l4_entry_eof_held_chain(pre, post, target_l4i, target_l3_p);
        }
        (target_l3_p, Tracked(l3_perm))
    }

    /// Hide the user root entry `target_l4i`: publish it as a placeholder, every permission bit clear but `kernel_present`, with the
    /// L3 address kept. Page walks stop there, so every 4K, 2M and 1G mapping and every window under `target_l4i` disappears, while
    /// the table keeps holding every table page below it. No window under the entry may be locked.
    pub fn hide_l4_entry(&mut self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            (WholePageTable { higher: *old(self), lower: *old(lower) }).wf(),
            old(self).kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            old(self).spec_resolve_mapping_l4(target_l4i) is Some,
            forall|p: PageMapPtr, i: L2Index| #![trigger old(lower).l2_owner(p, i)]
                old(lower).l2_perms.dom().contains(p) && old(self).l2_rev_map.view().spec_index(p).0 == target_l4i && pei_valid(i) ==> old(lower).l2_owner(p, i) is None,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (WholePageTable { higher: *final(self), lower: *final(lower) }).wf(),
            (WholePageTable { higher: *final(self), lower: *final(lower) }).page_closure() =~= (WholePageTable { higher: *old(self), lower: *old(lower) }).page_closure(),
            final(self).l3_tables == old(self).l3_tables,
            final(self).l3_rev_map == old(self).l3_rev_map,
            final(self).l2_rev_map == old(self).l2_rev_map,
            final(self).kernel_entries == old(self).kernel_entries,
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).cr3 == old(self).cr3,
            final(self).pcid == old(self).pcid,
            final(self).did == old(self).did,
            final(self).proc_ptr == old(self).proc_ptr,
            final(self).table_stale_cpus == old(self).table_stale_cpus,
            final(self).mapping_1g.view() == old(self).mapping_1g.view().remove_keys(old(self).mapping_1g.view().dom().filter(|va: VAddr| spec_v2l4index(va) == target_l4i)),
            final(lower).l2_perms == old(lower).l2_perms,
            final(lower).l1_rev_map == old(lower).l1_rev_map,
            final(lower).mapping_4k == old(lower).mapping_4k.remove_keys(old(lower).mapping_4k.dom().filter(|va: VAddr| spec_v2l4index(va) == target_l4i)),
            final(lower).mapping_2m == old(lower).mapping_2m.remove_keys(old(lower).mapping_2m.dom().filter(|va: VAddr| spec_v2l4index(va) == target_l4i)),
            final(lower).pagetable_window_locks == old(lower).pagetable_window_locks.remove_keys(old(lower).pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == target_l4i)),
            final(lower).window_stale_cpus == old(lower).window_stale_cpus,
            old(lower).hidden_l1_tables_in_locked_windows() ==> final(lower).hidden_l1_tables_in_locked_windows(),
            final(self).spec_resolve_mapping_l4(target_l4i) is None,
            forall|l4i: L4Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_l4(l4i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && l4i != target_l4i ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_l4(l4i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_resolve_mapping_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_l3(l4i, l3i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && l4i != target_l4i
                    ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_l3(l4i, l3i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_resolve_mapping_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_1g_l3(l4i, l3i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && l4i != target_l4i
                    ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_1g_l3(l4i, l3i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_resolve_mapping_1g_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && l4i != target_l4i
                    ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_2m_l2(l4i, l3i, l2i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && l4i != target_l4i
                    ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_resolve_mapping_2m_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && l4i != target_l4i
                    ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_l4(l4i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && l4i != target_l4i ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_l4(l4i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_held_l4(l4i),
            (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_l4(target_l4i) == Some(PageEntry { addr: (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_held_l4(target_l4i)->0.addr,
                perm: PageEntryPerm { present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: true } }),
            forall|l4i: L4Index, l3i: L3Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_l3(l4i, l3i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_l3(l4i, l3i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_held_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                    ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_held_2m_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_1g_l3(l4i, l3i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i)
                    ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_1g_l3(l4i, l3i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_held_1g_l3(l4i, l3i),
    {
        proof {
            self.wf_l4_cr3_at();
            self.wf_l4_at(target_l4i);
            self.table_pages_wf_l3_at(self.spec_resolve_mapping_l4(target_l4i)->0.addr);
            page_ptr_valid_imply_mem_valid(self.spec_resolve_mapping_l4(target_l4i)->0.addr);
        }
        let l4_entry = self.get_entry_l4(target_l4i).unwrap();
        page_map_set_published_in_map(self.cr3, Tracked(self.l4_table.borrow_mut()), target_l4i,
            PageEntry { addr: l4_entry.addr, perm: PageEntryPerm { present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: true } },
            Tracked(&mut *lctx));
        proof {
            self.mapping_1g = Ghost(self.mapping_1g.view().remove_keys(self.mapping_1g.view().dom().filter(|va: VAddr| spec_v2l4index(va) == target_l4i)));
            lower.mapping_4k = lower.mapping_4k.remove_keys(lower.mapping_4k.dom().filter(|va: VAddr| spec_v2l4index(va) == target_l4i));
            lower.mapping_2m = lower.mapping_2m.remove_keys(lower.mapping_2m.dom().filter(|va: VAddr| spec_v2l4index(va) == target_l4i));
            lower.pagetable_window_locks = lower.pagetable_window_locks.remove_keys(lower.pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == target_l4i));
            let pre = WholePageTable { higher: *old(self), lower: *old(lower) };
            let post = WholePageTable { higher: *self, lower: *lower };
            assert(WholePageTable::hide_l4_entry_eof_transition_framing(pre, post, target_l4i)) by { reveal(WholePageTable::hide_l4_entry_eof_transition_framing); };
            WholePageTable::hide_l4_entry_eof(pre, post, target_l4i);
            WholePageTable::hide_l4_entry_eof_resolve(pre, post, target_l4i);
            WholePageTable::hide_l4_entry_eof_held_chain(pre, post, target_l4i);
        }
    }

    /// Hide the 1G leaf `(target_l4i, target_l3i)` under the present root entry `target_l4i`: clear its user present bit while keeping
    /// `kernel_present`, so future page walks miss and the kernel mapping record that backs any stale TLB entry stays. Writes only the
    /// big-lock payload, so the caller holds the big lock in write mode; it must flush before `clear_held_1g_leaf`.
    pub fn hide_1g_leaf(&mut self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            (WholePageTable { higher: *old(self), lower: *lower }).wf(),
            old(self).kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            old(self).spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is Some || old(self).mapping_1g.view().dom().contains(spec_index2va((target_l4i, target_l3i, 0, 0))),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (WholePageTable { higher: *final(self), lower: *lower }).wf(),
            (WholePageTable { higher: *final(self), lower: *lower }).page_closure() == (WholePageTable { higher: *old(self), lower: *lower }).page_closure(),
            final(self).mapping_1g.view() == old(self).mapping_1g.view().insert(spec_index2va((target_l4i, target_l3i, 0, 0)), MapEntry { present: false, ..old(self).mapping_1g.view().spec_index(spec_index2va((target_l4i, target_l3i, 0, 0))) }),
            final(self).l4_table == old(self).l4_table,
            final(self).l3_rev_map == old(self).l3_rev_map,
            final(self).l2_rev_map == old(self).l2_rev_map,
            final(self).kernel_entries == old(self).kernel_entries,
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).cr3 == old(self).cr3,
            final(self).pcid == old(self).pcid,
            final(self).did == old(self).did,
            final(self).proc_ptr == old(self).proc_ptr,
            final(self).table_stale_cpus == old(self).table_stale_cpus,
            forall|l4i: L4Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_l4(l4i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_l4(l4i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_resolve_mapping_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_l3(l4i, l3i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_l3(l4i, l3i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_resolve_mapping_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_1g_l3(l4i, l3i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (target_l4i, target_l3i)
                    ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_1g_l3(l4i, l3i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_resolve_mapping_1g_l3(l4i, l3i),
            (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_1g_l3(target_l4i, target_l3i)
                == Some(PageEntry { perm: PageEntryPerm { present: false, ..old(self).spec_resolve_mapping_1g_l3(target_l4i, target_l3i)->0.perm }, ..old(self).spec_resolve_mapping_1g_l3(target_l4i, target_l3i)->0 }),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_l2(l4i, l3i, l2i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_l2(l4i, l3i, l2i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_resolve_mapping_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_2m_l2(l4i, l3i, l2i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_resolve_mapping_2m_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                    ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    ==> (WholePageTable { higher: *final(self), lower: *lower }).window_locked_by_thread(l4i, l3i, l2i, thread_id) == (WholePageTable { higher: *old(self), lower: *lower }).window_locked_by_thread(l4i, l3i, l2i, thread_id),
            forall|l4i: L4Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_held_l4(l4i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_held_l4(l4i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_held_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_held_l3(l4i, l3i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_held_l3(l4i, l3i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_held_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_held_1g_l3(l4i, l3i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (target_l4i, target_l3i)
                    ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_held_1g_l3(l4i, l3i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_held_1g_l3(l4i, l3i),
            (WholePageTable { higher: *final(self), lower: *lower }).spec_held_1g_l3(target_l4i, target_l3i)
                == Some(PageEntry { perm: PageEntryPerm { present: false, ..old(self).spec_resolve_mapping_1g_l3(target_l4i, target_l3i)->0.perm }, ..old(self).spec_resolve_mapping_1g_l3(target_l4i, target_l3i)->0 }),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_held_l2(l4i, l3i, l2i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_held_l2(l4i, l3i, l2i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                    ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_held_4k_l1(l4i, l3i, l2i, l1i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_held_2m_l2(l4i, l3i, l2i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_held_2m_l2(l4i, l3i, l2i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_held_2m_l2(l4i, l3i, l2i),
    {
        proof {
            self.wf_l4_at(target_l4i);
            self.wf_mapping_1g_at(target_l4i, target_l3i);
        }
        let l4_entry = self.get_entry_l4(target_l4i).unwrap();
        let mut l3_entry = self.get_entry_1g_l3(target_l4i, target_l3i, &l4_entry).unwrap();
        proof {
            self.wf_l3_at(l4_entry.addr);
            page_ptr_valid_imply_mem_valid(l3_entry.addr);
        }
        l3_entry.perm.present = false;
        page_map_set_published_in_map(l4_entry.addr, Tracked(self.l3_tables.borrow_mut()), target_l3i, l3_entry, Tracked(&mut *lctx));
        proof {
            self.mapping_1g = Ghost(self.mapping_1g.view().insert(spec_index2va((target_l4i, target_l3i, 0, 0)), MapEntry { present: false, ..self.mapping_1g.view().spec_index(spec_index2va((target_l4i, target_l3i, 0, 0))) }));
            let pre = (WholePageTable { higher: *old(self), lower: *lower });
            let post = WholePageTable { higher: *self, lower: *lower };
            assert(WholePageTable::hide_1g_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, l4_entry.addr)) by { reveal(WholePageTable::hide_1g_leaf_eof_transition_framing); };
            WholePageTable::hide_1g_leaf_eof(pre, post, target_l4i, target_l3i, l4_entry.addr);
            WholePageTable::hide_1g_leaf_eof_resolve(pre, post, target_l4i, target_l3i, l4_entry.addr);
            WholePageTable::hide_1g_leaf_eof_held_chain(pre, post, target_l4i, target_l3i, l4_entry.addr);
        }
    }

    /// Clear the held 1G leaf `(target_l4i, target_l3i)`, which no longer resolves or is hidden, and return it: its L3 entry is published
    /// empty, and a hidden leaf under a present root entry leaves `mapping_1g`. Writes only the big-lock payload, so the caller holds
    /// the big lock in write mode.
    pub fn clear_held_1g_leaf(&mut self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, Tracked(lctx): Tracked<&mut LocalContext>)
        -> (ret: PageEntry)
        requires
            (WholePageTable { higher: *old(self), lower: *lower }).wf(),
            old(self).kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            old(self).spec_held_1g_l3(target_l4i, target_l3i) is Some,
            old(self).spec_resolve_mapping_l4(target_l4i) is None || !old(self).spec_held_1g_l3(target_l4i, target_l3i)->0.perm.present,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (WholePageTable { higher: *final(self), lower: *lower }).wf(),
            (WholePageTable { higher: *final(self), lower: *lower }).page_closure() == (WholePageTable { higher: *old(self), lower: *lower }).page_closure(),
            ret == old(self).spec_held_1g_l3(target_l4i, target_l3i)->0,
            final(self).mapping_1g.view() == old(self).mapping_1g.view().remove(spec_index2va((target_l4i, target_l3i, 0, 0))),
            final(self).l4_table == old(self).l4_table,
            final(self).l3_rev_map == old(self).l3_rev_map,
            final(self).l2_rev_map == old(self).l2_rev_map,
            final(self).kernel_entries == old(self).kernel_entries,
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).cr3 == old(self).cr3,
            final(self).pcid == old(self).pcid,
            final(self).did == old(self).did,
            final(self).proc_ptr == old(self).proc_ptr,
            final(self).table_stale_cpus == old(self).table_stale_cpus,
            forall|l4i: L4Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_l4(l4i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_l4(l4i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_resolve_mapping_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_l3(l4i, l3i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_l3(l4i, l3i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_resolve_mapping_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_1g_l3(l4i, l3i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (target_l4i, target_l3i)
                    ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_1g_l3(l4i, l3i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_resolve_mapping_1g_l3(l4i, l3i),
            (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_l2(l4i, l3i, l2i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_l2(l4i, l3i, l2i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_resolve_mapping_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_2m_l2(l4i, l3i, l2i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_resolve_mapping_2m_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                    ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    ==> (WholePageTable { higher: *final(self), lower: *lower }).window_locked_by_thread(l4i, l3i, l2i, thread_id) == (WholePageTable { higher: *old(self), lower: *lower }).window_locked_by_thread(l4i, l3i, l2i, thread_id),
            forall|l4i: L4Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_held_l4(l4i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_held_l4(l4i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_held_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_held_l3(l4i, l3i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_held_l3(l4i, l3i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_held_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_held_1g_l3(l4i, l3i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (target_l4i, target_l3i)
                    ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_held_1g_l3(l4i, l3i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_held_1g_l3(l4i, l3i),
            (WholePageTable { higher: *final(self), lower: *lower }).spec_held_1g_l3(target_l4i, target_l3i) is None,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_held_l2(l4i, l3i, l2i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_held_l2(l4i, l3i, l2i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                    ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_held_4k_l1(l4i, l3i, l2i, l1i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *final(self), lower: *lower }).spec_held_2m_l2(l4i, l3i, l2i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (WholePageTable { higher: *final(self), lower: *lower }).spec_held_2m_l2(l4i, l3i, l2i) == (WholePageTable { higher: *old(self), lower: *lower }).spec_held_2m_l2(l4i, l3i, l2i),
    {
        proof { self.wf_l4_at(target_l4i); mem_valid_zero(); }
        let l4_entry = self.get_held_entry_l4(target_l4i).unwrap();
        let l3_entry = self.get_l3_entry_word(target_l4i, target_l3i, &l4_entry);
        proof { self.wf_l3_at(l4_entry.addr); }
        page_map_set_published_in_map(l4_entry.addr, Tracked(self.l3_tables.borrow_mut()), target_l3i, PageEntry::empty(), Tracked(&mut *lctx));
        proof {
            self.mapping_1g = Ghost(self.mapping_1g.view().remove(spec_index2va((target_l4i, target_l3i, 0, 0))));
            let pre = (WholePageTable { higher: *old(self), lower: *lower });
            let post = WholePageTable { higher: *self, lower: *lower };
            assert(WholePageTable::clear_held_1g_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, l4_entry.addr)) by { reveal(WholePageTable::clear_held_1g_leaf_eof_transition_framing); };
            WholePageTable::clear_held_1g_leaf_eof(pre, post, target_l4i, target_l3i, l4_entry.addr);
            WholePageTable::clear_held_1g_leaf_eof_resolve(pre, post, target_l4i, target_l3i, l4_entry.addr);
            WholePageTable::clear_held_1g_leaf_eof_held_chain(pre, post, target_l4i, target_l3i, l4_entry.addr);
        }
        l3_entry
    }

    /// Hide the non-huge L3 entry `(target_l4i, target_l3i)` under the present root entry `target_l4i`: publish it as a placeholder, every
    /// permission bit clear but `kernel_present`, with the L2 address kept. Page walks stop there, so its 512 windows leave the window lock
    /// map, while the table keeps holding the L2 page and every L1 page below it. No window under the entry is locked and no 4K or 2M leaf
    /// under it resolves, so no mapping changes.
    pub fn hide_l3_entry(&mut self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            (WholePageTable { higher: *old(self), lower: *old(lower) }).wf(),
            old(self).kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            old(self).spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            forall|i: L2Index| #![trigger old(lower).l2_owner(old(self).spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, i)]
                pei_valid(i) ==> old(lower).l2_owner(old(self).spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, i) is None,
            forall|i: L2Index| #![trigger (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i)]
                pei_valid(i) ==> (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index, j: L1Index| #![trigger (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_resolve_mapping_4k_l1(target_l4i, target_l3i, i, j)]
                pei_valid(i) && pei_valid(j) ==> (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_resolve_mapping_4k_l1(target_l4i, target_l3i, i, j) is None,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (WholePageTable { higher: *final(self), lower: *final(lower) }).wf(),
            (WholePageTable { higher: *final(self), lower: *final(lower) }).page_closure() == (WholePageTable { higher: *old(self), lower: *old(lower) }).page_closure(),
            final(self).l4_table == old(self).l4_table,
            final(self).l3_rev_map == old(self).l3_rev_map,
            final(self).l2_rev_map == old(self).l2_rev_map,
            final(self).mapping_1g == old(self).mapping_1g,
            final(self).kernel_entries == old(self).kernel_entries,
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).cr3 == old(self).cr3,
            final(self).pcid == old(self).pcid,
            final(self).did == old(self).did,
            final(self).proc_ptr == old(self).proc_ptr,
            final(self).table_stale_cpus == old(self).table_stale_cpus,
            final(lower).l2_perms == old(lower).l2_perms,
            final(lower).l1_rev_map == old(lower).l1_rev_map,
            final(lower).mapping_4k == old(lower).mapping_4k,
            final(lower).mapping_2m == old(lower).mapping_2m,
            final(lower).pagetable_window_locks
                == old(lower).pagetable_window_locks.remove_keys(old(lower).pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == target_l4i && spec_v2l3index(w.va) == target_l3i)),
            final(lower).window_stale_cpus == old(lower).window_stale_cpus,
            old(lower).hidden_l1_tables_in_locked_windows() ==> final(lower).hidden_l1_tables_in_locked_windows(),
            forall|l4i: L4Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_l4(l4i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_l4(l4i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_resolve_mapping_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_l3(l4i, l3i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (target_l4i, target_l3i)
                    ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_l3(l4i, l3i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_resolve_mapping_l3(l4i, l3i),
            (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            forall|l4i: L4Index, l3i: L3Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_1g_l3(l4i, l3i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_1g_l3(l4i, l3i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_resolve_mapping_1g_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i) != (target_l4i, target_l3i)
                    ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i),
            forall|l2i: L2Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, l2i)]
                pei_valid(l2i) ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, l2i) is None,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_2m_l2(l4i, l3i, l2i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_resolve_mapping_2m_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                    ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id) == (WholePageTable { higher: *old(self), lower: *old(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id),
            forall|l4i: L4Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_l4(l4i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_l4(l4i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_held_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_l3(l4i, l3i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (target_l4i, target_l3i)
                    ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_l3(l4i, l3i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_held_l3(l4i, l3i),
            (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_l3(target_l4i, target_l3i) == Some(PageEntry { addr: old(self).spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr,
                perm: PageEntryPerm { present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: true } }),
            forall|l4i: L4Index, l3i: L3Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_1g_l3(l4i, l3i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_1g_l3(l4i, l3i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_held_1g_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_l2(l4i, l3i, l2i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                    ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_2m_l2(l4i, l3i, l2i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_held_2m_l2(l4i, l3i, l2i),
    {
        proof { self.wf_l4_at(target_l4i); }
        let l4_entry = self.get_entry_l4(target_l4i).unwrap();
        let l3_entry = self.get_entry_l3(target_l4i, target_l3i, &l4_entry).unwrap();
        proof {
            let c = WholePageTable { higher: *self, lower: *lower };
            self.wf_l3_at(l4_entry.addr);
            c.l3_links_l2_wf_at(l4_entry.addr, target_l3i);
            c.table_pages_wf_l2_at(l3_entry.addr);
            page_ptr_valid_imply_mem_valid(l3_entry.addr);
        }
        page_map_set_published_in_map(l4_entry.addr, Tracked(self.l3_tables.borrow_mut()), target_l3i,
            PageEntry { addr: l3_entry.addr, perm: PageEntryPerm { present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: true } }, Tracked(&mut *lctx));
        proof {
            lower.pagetable_window_locks = lower.pagetable_window_locks.remove_keys(lower.pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == target_l4i && spec_v2l3index(w.va) == target_l3i));
            let pre = (WholePageTable { higher: *old(self), lower: *old(lower) });
            let post = WholePageTable { higher: *self, lower: *lower };
            assert(WholePageTable::hide_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, l4_entry.addr)) by { reveal(WholePageTable::hide_l3_entry_eof_transition_framing); };
            WholePageTable::hide_l3_entry_eof(pre, post, target_l4i, target_l3i, l4_entry.addr);
            WholePageTable::hide_l3_entry_eof_resolve(pre, post, target_l4i, target_l3i, l4_entry.addr);
            WholePageTable::hide_l3_entry_eof_held_chain(pre, post, target_l4i, target_l3i, l4_entry.addr);
        }
    }
}
} // verus!
