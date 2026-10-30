use vstd::prelude::*;
verus! {
use crate::*;
use vstd::simple_pptr::*;
use super::pagetable_concurrent_lock_eof::*;

impl PageTableHigher<PT_TYPE> {
    /// Take the lock of 2M window `(l4i, l3i, l2i)` of the table whose big lock lives at `root`; the spin lock waits
    /// out any other holder.
    pub fn lock_window(&self, Tracked(lower): Tracked<&mut PageTableLower<PT_TYPE>>, Ghost(root): Ghost<RwLockPageTableRoot>, l4i: L4Index, l3i: L3Index, l2i: L2Index,
        Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            (PageTableC { higher: *self, lower: *old(lower) }).wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            page_table_key_2m_valid::<PT_TYPE>(spec_index2va((l4i, l3i, l2i, 0))),
            (PageTableC { higher: *self, lower: *old(lower) }).window_exists(l4i, l3i),
            !(PageTableC { higher: *self, lower: *old(lower) }).window_locked_by_thread(l4i, l3i, l2i, old(lctx).thread_id()),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).lock_id_acyclic(window_lock_id(root, l4i, l3i, l2i)),
        ensures
            (PageTableC { higher: *self, lower: *final(lower) }).wf(),
            lock_window_eof_transition_framing(PageTableC { higher: *self, lower: *old(lower) }, PageTableC { higher: *self, lower: *final(lower) }, l4i, l3i, l2i,
                final(lctx).thread_id(), ret.view().lock_id()),
            (PageTableC { higher: *self, lower: *final(lower) }).window_locked_by_thread(l4i, l3i, l2i, final(lctx).thread_id()),
            final(lower).l2_owner((PageTableC { higher: *self, lower: *final(lower) }).window_l2_page(l4i, l3i), l2i) == (SpinLockState::Some { thread_id: ret.view().thread_id(), lock_id: ret.view().lock_id() }),
            ret.view().state() is WriteLock,
            ret.view().ordering_lock_id() == window_lock_id(root, l4i, l3i, l2i),
            ret.view().thread_id() == final(lctx).thread_id(),
            lock_ensures(old(lctx), final(lctx), window_lock_id(root, l4i, l3i, l2i), window_obj_id(root, l4i, l3i, l2i)),
    {
        let ghost pre = PageTableC { higher: *self, lower: *lower };
        let l4_entry = self.get_entry_l4(l4i).unwrap();
        let l3_entry = self.get_entry_l3(l4i, l3i, &l4_entry).unwrap();
        proof {
            self.wf_l4_at(l4i);
            pre.wf_l3_at(l4_entry.addr, l3i);
            pre.wf_l2_at(l3_entry.addr, l2i);
        }
        let tracked mut l2_perm = lower.l2_perms.tracked_remove(l3_entry.addr);
        let l2_tbl: &mut L2PageMap = PPtr::<L2PageMap>::from_usize(l3_entry.addr).borrow_mut(Tracked(&mut l2_perm));
        let ret = l2_tbl.borrow_entry_lock_mut(l2i).lock(Tracked(&mut *lctx), Ghost(window_lock_id(root, l4i, l3i, l2i)), Ghost(window_obj_id(root, l4i, l3i, l2i)));
        proof {
            lower.l2_perms.tracked_insert(l3_entry.addr, l2_perm);
            lower.pagetable_window_locks = lower.pagetable_window_locks.insert(WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) }, LockStateU::WriteLocked);
            lock_window_eof(pre, PageTableC { higher: *self, lower: *lower }, l4i, l3i, l2i, lctx.thread_id(), ret.view().lock_id());
        }
        ret
    }

    /// Release the lock of 2M window `(l4i, l3i, l2i)` of the table whose big lock lives at `root`.
    pub fn unlock_window(&self, Tracked(lower): Tracked<&mut PageTableLower<PT_TYPE>>, Ghost(root): Ghost<RwLockPageTableRoot>, l4i: L4Index, l3i: L3Index, l2i: L2Index,
        Tracked(lctx): Tracked<&mut LocalContext>, lp: Tracked<LockPerm>)
        requires
            (PageTableC { higher: *self, lower: *old(lower) }).wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            (PageTableC { higher: *self, lower: *old(lower) }).window_locked_by_thread(l4i, l3i, l2i, old(lctx).thread_id()),
            lp.view().state() is WriteLock,
            lp.view().thread_id() == old(lctx).thread_id(),
            old(lower).l2_owner((PageTableC { higher: *self, lower: *old(lower) }).window_l2_page(l4i, l3i), l2i) == (SpinLockState::Some { thread_id: lp.view().thread_id(), lock_id: lp.view().lock_id() }),
            old(lctx).lock_entry_contains(window_lock_id(root, l4i, l3i, l2i), window_obj_id(root, l4i, l3i, l2i)),
        ensures
            (PageTableC { higher: *self, lower: *final(lower) }).wf(),
            unlock_window_eof_transition_framing(PageTableC { higher: *self, lower: *old(lower) }, PageTableC { higher: *self, lower: *final(lower) }, l4i, l3i, l2i),
            unlock_ensures(old(lctx), final(lctx), window_obj_id(root, l4i, l3i, l2i), window_lock_id(root, l4i, l3i, l2i)),
    {
        let ghost pre = PageTableC { higher: *self, lower: *lower };
        let l4_entry = self.get_entry_l4(l4i).unwrap();
        let l3_entry = self.get_entry_l3(l4i, l3i, &l4_entry).unwrap();
        proof {
            self.wf_l4_at(l4i);
            pre.wf_l3_at(l4_entry.addr, l3i);
            pre.wf_l2_at(l3_entry.addr, l2i);
        }
        let tracked mut l2_perm = lower.l2_perms.tracked_remove(l3_entry.addr);
        let l2_tbl: &mut L2PageMap = PPtr::<L2PageMap>::from_usize(l3_entry.addr).borrow_mut(Tracked(&mut l2_perm));
        l2_tbl.borrow_entry_lock_mut(l2i).unlock(Tracked(&mut *lctx), lp, Ghost(window_lock_id(root, l4i, l3i, l2i)), Ghost(window_obj_id(root, l4i, l3i, l2i)));
        proof {
            lower.l2_perms.tracked_insert(l3_entry.addr, l2_perm);
            lower.pagetable_window_locks = lower.pagetable_window_locks.insert(WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) }, LockStateU::Unlocked);
            unlock_window_eof(pre, PageTableC { higher: *self, lower: *lower }, l4i, l3i, l2i);
        }
    }
}
} // verus!
