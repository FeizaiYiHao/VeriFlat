use vstd::prelude::*;
verus! {
use crate::*;
use vstd::simple_pptr::*;

impl<const TABLE_TYPE: PTType> PageTableHigher<TABLE_TYPE> {
    /// Install a 4K leaf at entry `target_l1i` of the existing L1 page `target_l1_p`. The lower half changes only under its window
    /// lock, so this thread must hold the lock of window `(target_l4i, target_l3i, target_l2i)` that links `target_l1_p`.
    pub fn map_4k_page(&self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index,
        target_l1_p: PageMapPtr, target_entry: &MapEntry, Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            (PageTableC { higher: *self, lower: *old(lower) }).wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            page_table_key_4k_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            (PageTableC { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            (PageTableC { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            (PageTableC { higher: *self, lower: *old(lower) }).spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None
                || old(lower).mapping_4k.dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            target_entry.present,
            (PageTableC { higher: *self, lower: *old(lower) }).window_locked_by_thread(target_l4i, target_l3i, target_l2i, old(lctx).thread_id()),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (PageTableC { higher: *self, lower: *final(lower) }).wf(),
            (PageTableC { higher: *self, lower: *final(lower) }).page_closure() == (PageTableC { higher: *self, lower: *old(lower) }).page_closure(),
            final(lower).mapping_4k == old(lower).mapping_4k.insert(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)), *target_entry),
            (PageTableC { higher: *self, lower: *final(lower) }).spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) == Some(PageEntry { addr: target_entry.addr,
                perm: PageEntryPerm { present: true, ps: false, write: target_entry.write, execute_disable: target_entry.execute_disable, user: true, kernel_present: true } }),
            final(lower).mapping_2m == old(lower).mapping_2m,
            forall|l4i: L4Index|
                #![trigger pei_valid(l4i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) ==> forall|l3i: L3Index|
                    #![trigger pei_valid(l3i)]
                    pei_valid(l3i) ==> forall|l2i: L2Index|
                        #![trigger (PageTableC { higher: *self, lower: *final(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i)]
                        pei_valid(l2i) ==> (PageTableC { higher: *self, lower: *final(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i)
                            == (PageTableC { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(l4i, l3i, l2i),
            final(lower).l2_perms == old(lower).l2_perms,
            final(lower).l2_lock == old(lower).l2_lock,
            final(lower).locked_windows == old(lower).locked_windows,
    {
        proof {
            let c = PageTableC { higher: *self, lower: *lower };
            c.resolve_l2_target_exists(target_l4i, target_l3i, target_l2i);
            c.wf_l1_at(target_l1_p);
            page_ptr_valid_imply_mem_valid(target_entry.addr);
        }
        page_map_set_published_in_map(target_l1_p, Tracked(&mut lower.l1_tables), target_l1i,
            PageEntry { addr: target_entry.addr, perm: PageEntryPerm { present: true, ps: false, write: target_entry.write, execute_disable: target_entry.execute_disable, user: true, kernel_present: true } },
            Tracked(&mut *lctx));
        proof {
            lower.mapping_4k = lower.mapping_4k.insert(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)), *target_entry);
            let pre = PageTableC { higher: *self, lower: *old(lower) };
            let post = PageTableC { higher: *self, lower: *lower };
            assert(PageTableC::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, *target_entry)) by {
                reveal(PageTableC::map_4k_page_eof_transition_framing);
            };
            PageTableC::map_4k_page_eof(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, *target_entry);
        }
    }

    /// Install a 2M leaf at entry `target_l2i` of the L2 page `target_l2_p`. The entry is the window's spin lock word, so this
    /// thread must hold that window lock; the published word keeps the lock bit.
    pub fn map_2m_page(&self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr,
        target_entry: &MapEntry, Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            (PageTableC { higher: *self, lower: *old(lower) }).wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            self.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            self.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            (PageTableC { higher: *self, lower: *old(lower) }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            (PageTableC { higher: *self, lower: *old(lower) }).spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None
                || old(lower).mapping_2m.dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, 0))) == false,
            (PageTableC { higher: *self, lower: *old(lower) }).page_closure().contains(target_entry.addr) == false,
            page_ptr_2m_valid(target_entry.addr),
            page_table_key_2m_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, 0))),
            target_entry.present,
            (PageTableC { higher: *self, lower: *old(lower) }).window_locked_by_thread(target_l4i, target_l3i, target_l2i, old(lctx).thread_id()),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (PageTableC { higher: *self, lower: *final(lower) }).wf(),
            (PageTableC { higher: *self, lower: *final(lower) }).page_closure() == (PageTableC { higher: *self, lower: *old(lower) }).page_closure(),
            final(lower).mapping_2m == old(lower).mapping_2m.insert(spec_index2va((target_l4i, target_l3i, target_l2i, 0)), *target_entry),
            final(lower).mapping_4k == old(lower).mapping_4k,
            final(lower).l2_perms == old(lower).l2_perms,
            final(lower).l2_lock == old(lower).l2_lock,
            final(lower).locked_windows == old(lower).locked_windows,
    {
        proof {
            let c = PageTableC { higher: *self, lower: *lower };
            self.wf_l4_at(target_l4i);
            c.wf_l3_at(self.spec_resolve_mapping_l4(target_l4i)->0.addr, target_l3i);
            c.l2_tokens_paired_at(target_l2_p);
            page_ptr_valid_imply_mem_valid(target_entry.addr);
        }
        let tracked l2_perm = lower.l2_perms.tracked_borrow(target_l2_p);
        let tracked l2_lock = lower.l2_lock.tracked_borrow(target_l2_p);
        let tracked mut l2_ghost = lower.l2_ghost.tracked_remove(target_l2_p);
        let l2_tbl: &L2PageMap = PPtr::<L2PageMap>::from_usize(target_l2_p).borrow(Tracked(l2_perm));
        l2_tbl.set_published_locked(Tracked(&mut l2_ghost), Tracked(l2_lock), target_l2i,
            PageEntry { addr: target_entry.addr, perm: PageEntryPerm { present: true, ps: true, write: target_entry.write, execute_disable: target_entry.execute_disable, user: true, kernel_present: true } },
            Tracked(&mut *lctx));
        proof {
            lower.l2_ghost.tracked_insert(target_l2_p, l2_ghost);
            lower.mapping_2m = lower.mapping_2m.insert(spec_index2va((target_l4i, target_l3i, target_l2i, 0)), *target_entry);
            let pre = PageTableC { higher: *self, lower: *old(lower) };
            let post = PageTableC { higher: *self, lower: *lower };
            assert(PageTableC::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, *target_entry)) by {
                reveal(PageTableC::map_2m_page_eof_transition_framing);
            };
            PageTableC::map_2m_page_eof(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, *target_entry);
        }
    }
}
} // verus!
