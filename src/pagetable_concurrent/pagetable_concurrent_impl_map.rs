use vstd::prelude::*;
verus! {
use crate::*;
use vstd::simple_pptr::*;

impl<const TABLE_TYPE: PTType> PageTableHigher<TABLE_TYPE> {
    /// Install a 4K leaf at entry `target_l1i` of the existing L1 page `target_l1_p`. The lower half changes only under its window
    /// lock, so this thread must hold the lock of window `(target_l4i, target_l3i, target_l2i)` that links `target_l1_p`.
    pub fn map_4k_page(&self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index,
        target_l2_p: PageMapPtr, target_l1_p: PageMapPtr, target_entry: &MapEntry, Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            (WholePageTable { higher: *self, lower: *old(lower) }).wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            page_table_key_4k_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            (WholePageTable { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            (WholePageTable { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            (WholePageTable { higher: *self, lower: *old(lower) }).spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None
                || old(lower).mapping_4k.dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            target_entry.present,
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
            (WholePageTable { higher: *self, lower: *final(lower) }).page_closure() == (WholePageTable { higher: *self, lower: *old(lower) }).page_closure(),
            final(lower).mapping_4k == old(lower).mapping_4k.insert(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)), *target_entry),
            (WholePageTable { higher: *self, lower: *final(lower) }).spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) == Some(PageEntry { addr: target_entry.addr,
                perm: PageEntryPerm { present: true, ps: false, write: target_entry.write, execute_disable: target_entry.execute_disable, user: true, kernel_present: true } }),
            final(lower).mapping_2m == old(lower).mapping_2m,
            forall|l4i: L4Index|
                #![trigger pei_valid(l4i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) ==> forall|l3i: L3Index|
                    #![trigger pei_valid(l3i)]
                    pei_valid(l3i) ==> forall|l2i: L2Index|
                        #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i)]
                        pei_valid(l2i) ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i)
                            == (WholePageTable { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i),
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
            (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) == Some(PageEntry { addr: target_entry.addr,
                perm: PageEntryPerm { present: true, ps: false, write: target_entry.write, execute_disable: target_entry.execute_disable, user: true, kernel_present: true } }),
    {
        proof {
            let c = WholePageTable { higher: *self, lower: *lower };
            self.wf_l4_at(target_l4i);
            c.l3_links_l2_wf_at(self.spec_resolve_mapping_l4(target_l4i)->0.addr, target_l3i);
            c.wf_l2_at(target_l2_p, target_l2i);
            c.wf_l1_at(target_l2_p, target_l2i);
            page_ptr_valid_imply_mem_valid(target_entry.addr);
        }
        let tracked mut l2_perm = lower.l2_perms.tracked_remove(target_l2_p);
        let tracked mut l1_perm = l2_entry_take_l1(&mut l2_perm, target_l2i, window_perm);
        page_map_set_published(target_l1_p, Tracked(&mut l1_perm), target_l1i,
            PageEntry { addr: target_entry.addr, perm: PageEntryPerm { present: true, ps: false, write: target_entry.write, execute_disable: target_entry.execute_disable, user: true, kernel_present: true } },
            Tracked(&mut *lctx));
        proof {
            l2_entry_put_l1(&mut l2_perm, target_l2i, window_perm, l1_perm);
            lower.l2_perms.tracked_insert(target_l2_p, l2_perm);
            lower.mapping_4k = lower.mapping_4k.insert(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)), *target_entry);
            let pre = WholePageTable { higher: *self, lower: *old(lower) };
            let post = WholePageTable { higher: *self, lower: *lower };
            assert(WholePageTable::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, *target_entry)) by {
                reveal(WholePageTable::map_4k_page_eof_transition_framing);
            };
            WholePageTable::map_4k_page_eof(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, *target_entry);
            WholePageTable::map_4k_page_eof_held_chain(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, *target_entry);
        }
    }

    /// Install a 2M leaf at entry `target_l2i` of the L2 page `target_l2_p`. The entry is the window's spin lock word, so this
    /// thread must hold that window lock; the published word keeps the lock bit.
    pub fn map_2m_page(&self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr,
        target_entry: &MapEntry, Tracked(window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            (WholePageTable { higher: *self, lower: *old(lower) }).wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            self.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            self.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            (WholePageTable { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            (WholePageTable { higher: *self, lower: *old(lower) }).spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None
                || old(lower).mapping_2m.dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, 0))) == false,
            (WholePageTable { higher: *self, lower: *old(lower) }).page_closure().contains(target_entry.addr) == false,
            page_ptr_2m_valid(target_entry.addr),
            page_table_key_2m_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, 0))),
            target_entry.present,
            (WholePageTable { higher: *self, lower: *old(lower) }).window_locked_by_thread(target_l4i, target_l3i, target_l2i, old(lctx).thread_id()),
            old(lower).l2_owner(target_l2_p, target_l2i) == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
            old(lower).l2_page(target_l2_p).entry_lock(target_l2i).l1() is None,
            !old(lower).window_stale_cpus.dom().contains((target_l2_p, target_l2i)),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (WholePageTable { higher: *self, lower: *final(lower) }).wf(),
            (WholePageTable { higher: *self, lower: *final(lower) }).page_closure() == (WholePageTable { higher: *self, lower: *old(lower) }).page_closure(),
            final(lower).mapping_2m == old(lower).mapping_2m.insert(spec_index2va((target_l4i, target_l3i, target_l2i, 0)), *target_entry),
            final(lower).mapping_4k == old(lower).mapping_4k,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger (WholePageTable { higher: *self, lower: *final(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    ==> (WholePageTable { higher: *self, lower: *final(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i) == (WholePageTable { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i),
            final(lower).l2_perms.dom() == old(lower).l2_perms.dom(),
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
            (WholePageTable { higher: *self, lower: *final(lower) }).spec_held_2m_l2(target_l4i, target_l3i, target_l2i) == Some(PageEntry { addr: target_entry.addr,
                perm: PageEntryPerm { present: true, ps: true, write: target_entry.write, execute_disable: target_entry.execute_disable, user: true, kernel_present: true } }),
    {
        proof {
            let c = WholePageTable { higher: *self, lower: *lower };
            self.wf_l4_at(target_l4i);
            c.l3_links_l2_wf_at(self.spec_resolve_mapping_l4(target_l4i)->0.addr, target_l3i);
            c.wf_l2_at(target_l2_p, target_l2i);
            page_ptr_valid_imply_mem_valid(target_entry.addr);
        }
        let tracked mut l2_perm = lower.l2_perms.tracked_remove(target_l2_p);
        l2_entry_set_published_locked(&PPtr::<L2PageMap>::from_usize(target_l2_p), Tracked(&mut l2_perm), target_l2i, Tracked(window_perm),
            PageEntry { addr: target_entry.addr, perm: PageEntryPerm { present: true, ps: true, write: target_entry.write, execute_disable: target_entry.execute_disable, user: true, kernel_present: true } },
            Tracked(&mut *lctx));
        proof {
            lower.l2_perms.tracked_insert(target_l2_p, l2_perm);
            lower.mapping_2m = lower.mapping_2m.insert(spec_index2va((target_l4i, target_l3i, target_l2i, 0)), *target_entry);
            let pre = WholePageTable { higher: *self, lower: *old(lower) };
            let post = WholePageTable { higher: *self, lower: *lower };
            assert(WholePageTable::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, *target_entry)) by {
                reveal(WholePageTable::map_2m_page_eof_transition_framing);
            };
            WholePageTable::map_2m_page_eof(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, *target_entry);
            WholePageTable::map_2m_page_eof_held_chain(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, *target_entry);
        }
    }

    /// Install a 1G leaf at the empty entry `target_l3i` of the L3 page `target_l3_p` that the present root entry `target_l4i` links.
    /// Writes only the big-lock payload, so the caller holds the big lock in write mode.
    pub fn map_1g_page(&mut self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_entry: &MapEntry,
        Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            (WholePageTable { higher: *old(self), lower: *lower }).wf(),
            old(self).kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            old(self).spec_resolve_mapping_l4(target_l4i) is Some,
            old(self).spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            old(self).spec_held_l3(target_l4i, target_l3i) is None,
            old(self).spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None || old(self).mapping_1g.view().dom().contains(spec_index2va((target_l4i, target_l3i, 0, 0))) == false,
            (WholePageTable { higher: *old(self), lower: *lower }).page_closure().contains(target_entry.addr) == false,
            page_ptr_1g_valid(target_entry.addr),
            page_table_key_1g_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, 0, 0))),
            target_entry.present,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (WholePageTable { higher: *final(self), lower: *lower }).wf(),
            (WholePageTable { higher: *final(self), lower: *lower }).page_closure() == (WholePageTable { higher: *old(self), lower: *lower }).page_closure(),
            final(self).mapping_1g.view() == old(self).mapping_1g.view().insert(spec_index2va((target_l4i, target_l3i, 0, 0)), *target_entry),
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
                == Some(PageEntry { addr: target_entry.addr, perm: PageEntryPerm { present: true, ps: true, write: target_entry.write, execute_disable: target_entry.execute_disable, user: true, kernel_present: true } }),
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
                == Some(PageEntry { addr: target_entry.addr, perm: PageEntryPerm { present: true, ps: true, write: target_entry.write, execute_disable: target_entry.execute_disable, user: true, kernel_present: true } }),
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
            self.wf_l3_at(target_l3_p);
            self.wf_mapping_1g_at(target_l4i, target_l3i);
            page_ptr_valid_imply_mem_valid(target_entry.addr);
        }
        page_map_set_published_in_map(target_l3_p, Tracked(self.l3_tables.borrow_mut()), target_l3i,
            PageEntry { addr: target_entry.addr, perm: PageEntryPerm { present: true, ps: true, write: target_entry.write, execute_disable: target_entry.execute_disable, user: true, kernel_present: true } }, Tracked(&mut *lctx));
        proof {
            self.mapping_1g = Ghost(self.mapping_1g.view().insert(spec_index2va((target_l4i, target_l3i, 0, 0)), *target_entry));
            let pre = (WholePageTable { higher: *old(self), lower: *lower });
            let post = WholePageTable { higher: *self, lower: *lower };
            assert(WholePageTable::map_1g_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, *target_entry)) by {
                reveal(WholePageTable::map_1g_page_eof_transition_framing);
            };
            WholePageTable::map_1g_page_eof(pre, post, target_l4i, target_l3i, target_l3_p, *target_entry);
            WholePageTable::map_1g_page_eof_resolve(pre, post, target_l4i, target_l3i, target_l3_p, *target_entry);
            WholePageTable::map_1g_page_eof_held_chain(pre, post, target_l4i, target_l3i, target_l3_p, *target_entry);
        }
    }
}
} // verus!
