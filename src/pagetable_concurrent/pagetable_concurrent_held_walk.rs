use vstd::prelude::*;

verus! {
use crate::*;

impl<const TABLE_TYPE: PTType> PageTableHigher<TABLE_TYPE> {
    /// The first held 4K leaf of the L1 page that the held L2 entry `l2_entry` holds, at or after `start_l1i`; `start_l1i == 512`
    /// scans nothing.
    fn next_held_4k_l1_from(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, l4i: L4Index, l3i: L3Index, l2i: L2Index, l3_entry: &PageEntry, l2_entry: &PageEntry,
        start_l1i: L1Index) -> (ret: Option<(L1Index, PageEntry)>)
        requires
            (WholePageTable { higher: *self, lower: *lower }).wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            start_l1i <= 512,
            self.spec_held_l3(l4i, l3i) =~= Some(*l3_entry),
            (WholePageTable { higher: *self, lower: *lower }).spec_held_l2(l4i, l3i, l2i) =~= Some(*l2_entry),
        ensures
            ret is Some ==> {
                let (found, entry) = ret->Some_0;
                &&& start_l1i <= found
                &&& pei_valid(found)
                &&& (WholePageTable { higher: *self, lower: *lower }).spec_held_4k_l1(l4i, l3i, l2i, found) == Some(entry)
            },
            forall|l1i: L1Index| #![trigger (WholePageTable { higher: *self, lower: *lower }).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                pei_valid(l1i) && start_l1i <= l1i && (ret is None || l1i < ret->Some_0.0) ==> (WholePageTable { higher: *self, lower: *lower }).spec_held_4k_l1(l4i, l3i, l2i, l1i) is None,
    {
        let ghost c = WholePageTable { higher: *self, lower: *lower };
        let mut l1i = start_l1i;
        while l1i < 512
            invariant
                c == (WholePageTable { higher: *self, lower: *lower }),
                c.wf(),
                self.kernel_l4_end <= l4i && pei_valid(l4i),
                pei_valid(l3i),
                pei_valid(l2i),
                start_l1i <= l1i <= 512,
                self.spec_held_l3(l4i, l3i) =~= Some(*l3_entry),
                c.spec_held_l2(l4i, l3i, l2i) =~= Some(*l2_entry),
                forall|done_l1i: L1Index| #![trigger c.spec_held_4k_l1(l4i, l3i, l2i, done_l1i)] start_l1i <= done_l1i < l1i ==> c.spec_held_4k_l1(l4i, l3i, l2i, done_l1i) is None,
            decreases 512 - l1i,
        {
            if let Some(entry) = self.get_held_entry_l1(Tracked(lower), l4i, l3i, l2i, l1i, l3_entry, l2_entry) { return Some((l1i, entry)); }
            l1i = l1i + 1;
        }
        None
    }

    /// The first held 4K or 2M leaf under the held L3 entry `l3_entry` at or after `start` in (L2, L1) order; a 2M leaf sits at L1
    /// index 0. No entry of the L2 page is locked.
    fn next_held_leaf_l2_from(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, l4i: L4Index, l3i: L3Index, l3_entry: &PageEntry, start: (L2Index, L1Index))
        -> (ret: Option<((L2Index, L1Index), bool, PageEntry)>)
        requires
            (WholePageTable { higher: *self, lower: *lower }).wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(start.0),
            start.1 <= 512,
            self.spec_held_l3(l4i, l3i) =~= Some(*l3_entry),
            lower.hidden_l1_tables_in_locked_windows(),
            forall|i: L2Index| #![trigger lower.l2_owner(l3_entry.addr, i)] pei_valid(i) ==> lower.l2_owner(l3_entry.addr, i) is None,
        ensures
            ret is Some ==> {
                let (found, is_2m, entry) = ret->Some_0;
                &&& pei_valid(found.0)
                &&& pei_valid(found.1)
                &&& spec_l2_index_path_le(start, found)
                &&& is_2m ==> found.1 == 0 && (WholePageTable { higher: *self, lower: *lower }).spec_held_2m_l2(l4i, l3i, found.0) == Some(entry)
                &&& !is_2m ==> (WholePageTable { higher: *self, lower: *lower }).spec_held_4k_l1(l4i, l3i, found.0, found.1) == Some(entry)
            },
            forall|l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *self, lower: *lower }).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                pei_valid(l2i) && pei_valid(l1i) && spec_l2_index_path_le(start, (l2i, l1i)) && (ret is None || !spec_l2_index_path_le(ret->Some_0.0, (l2i, l1i))) ==> (WholePageTable { higher: *self, lower: *lower }).spec_held_4k_l1(l4i, l3i, l2i, l1i) is None,
            forall|l2i: L2Index| #![trigger (WholePageTable { higher: *self, lower: *lower }).spec_held_2m_l2(l4i, l3i, l2i)]
                pei_valid(l2i) && spec_l2_index_path_le(start, (l2i, 0)) && (ret is None || !spec_l2_index_path_le(ret->Some_0.0, (l2i, 0))) ==> (WholePageTable { higher: *self, lower: *lower }).spec_held_2m_l2(l4i, l3i, l2i) is None,
    {
        let ghost c = WholePageTable { higher: *self, lower: *lower };
        let mut l2i = start.0;
        while l2i < 512
            invariant
                c == (WholePageTable { higher: *self, lower: *lower }),
                c.wf(),
                self.kernel_l4_end <= l4i && pei_valid(l4i),
                pei_valid(l3i),
                pei_valid(start.0),
                start.1 <= 512,
                start.0 <= l2i <= 512,
                self.spec_held_l3(l4i, l3i) =~= Some(*l3_entry),
                lower.hidden_l1_tables_in_locked_windows(),
                forall|i: L2Index| #![trigger lower.l2_owner(l3_entry.addr, i)] pei_valid(i) ==> lower.l2_owner(l3_entry.addr, i) is None,
                forall|done_l2i: L2Index, done_l1i: L1Index| #![trigger c.spec_held_4k_l1(l4i, l3i, done_l2i, done_l1i)]
                    pei_valid(done_l2i) && pei_valid(done_l1i) && spec_l2_index_path_le(start, (done_l2i, done_l1i)) && done_l2i < l2i ==> c.spec_held_4k_l1(l4i, l3i, done_l2i, done_l1i) is None,
                forall|done_l2i: L2Index| #![trigger c.spec_held_2m_l2(l4i, l3i, done_l2i)] pei_valid(done_l2i) && spec_l2_index_path_le(start, (done_l2i, 0)) && done_l2i < l2i ==> c.spec_held_2m_l2(l4i, l3i, done_l2i) is None,
            decreases 512 - l2i,
        {
            let l2_entry = self.get_l2_entry_word(Tracked(lower), l4i, l3i, l2i, l3_entry);
            if l2_entry.perm.kernel_present && l2_entry.perm.ps {
                if l2i != start.0 || start.1 == 0 { return Some(((l2i, 0), true, l2_entry)); }
            } else if l2_entry.perm.present && !l2_entry.perm.ps {
                if let Some((l1i, entry)) = self.next_held_4k_l1_from(Tracked(lower), l4i, l3i, l2i, l3_entry, &l2_entry, if l2i == start.0 { start.1 } else { 0 }) {
                    return Some(((l2i, l1i), false, entry));
                }
            }
            l2i = l2i + 1;
        }
        None
    }

    /// The first held 4K or 2M leaf under the held root entry `l4_entry` at or after `start` in (L3, L2, L1) order.
    fn next_held_leaf_l3_from(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, l4i: L4Index, l4_entry: &PageEntry, start: (L3Index, L2Index, L1Index))
        -> (ret: Option<((L3Index, L2Index, L1Index), bool, PageEntry)>)
        requires
            (WholePageTable { higher: *self, lower: *lower }).wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(start.0),
            pei_valid(start.1),
            start.2 <= 512,
            self.spec_held_l4(l4i) =~= Some(*l4_entry),
            lower.hidden_l1_tables_in_locked_windows(),
            forall|p: PageMapPtr, i: L2Index| #![trigger lower.l2_owner(p, i)] lower.l2_perms.dom().contains(p) && pei_valid(i) ==> lower.l2_owner(p, i) is None,
        ensures
            ret is Some ==> {
                let (found, is_2m, entry) = ret->Some_0;
                &&& pei_valid(found.0)
                &&& pei_valid(found.1)
                &&& pei_valid(found.2)
                &&& spec_l3_index_path_le(start, found)
                &&& is_2m ==> found.2 == 0 && (WholePageTable { higher: *self, lower: *lower }).spec_held_2m_l2(l4i, found.0, found.1) == Some(entry)
                &&& !is_2m ==> (WholePageTable { higher: *self, lower: *lower }).spec_held_4k_l1(l4i, found.0, found.1, found.2) == Some(entry)
            },
            forall|l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *self, lower: *lower }).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l3_index_path_le(start, (l3i, l2i, l1i)) && (ret is None || !spec_l3_index_path_le(ret->Some_0.0, (l3i, l2i, l1i))) ==> (WholePageTable { higher: *self, lower: *lower }).spec_held_4k_l1(l4i, l3i, l2i, l1i) is None,
            forall|l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *self, lower: *lower }).spec_held_2m_l2(l4i, l3i, l2i)]
                pei_valid(l3i) && pei_valid(l2i) && spec_l3_index_path_le(start, (l3i, l2i, 0)) && (ret is None || !spec_l3_index_path_le(ret->Some_0.0, (l3i, l2i, 0))) ==> (WholePageTable { higher: *self, lower: *lower }).spec_held_2m_l2(l4i, l3i, l2i) is None,
    {
        let ghost c = WholePageTable { higher: *self, lower: *lower };
        let mut l3i = start.0;
        while l3i < 512
            invariant
                c == (WholePageTable { higher: *self, lower: *lower }),
                c.wf(),
                self.kernel_l4_end <= l4i && pei_valid(l4i),
                pei_valid(start.0),
                pei_valid(start.1),
                start.2 <= 512,
                start.0 <= l3i <= 512,
                self.spec_held_l4(l4i) =~= Some(*l4_entry),
                lower.hidden_l1_tables_in_locked_windows(),
                forall|p: PageMapPtr, i: L2Index| #![trigger lower.l2_owner(p, i)] lower.l2_perms.dom().contains(p) && pei_valid(i) ==> lower.l2_owner(p, i) is None,
                forall|done_l3i: L3Index, done_l2i: L2Index, done_l1i: L1Index| #![trigger c.spec_held_4k_l1(l4i, done_l3i, done_l2i, done_l1i)]
                    pei_valid(done_l3i) && pei_valid(done_l2i) && pei_valid(done_l1i) && spec_l3_index_path_le(start, (done_l3i, done_l2i, done_l1i)) && done_l3i < l3i ==> c.spec_held_4k_l1(l4i, done_l3i, done_l2i, done_l1i) is None,
                forall|done_l3i: L3Index, done_l2i: L2Index| #![trigger c.spec_held_2m_l2(l4i, done_l3i, done_l2i)]
                    pei_valid(done_l3i) && pei_valid(done_l2i) && spec_l3_index_path_le(start, (done_l3i, done_l2i, 0)) && done_l3i < l3i ==> c.spec_held_2m_l2(l4i, done_l3i, done_l2i) is None,
            decreases 512 - l3i,
        {
            if let Some(l3_entry) = self.get_held_entry_l3(l4i, l3i, l4_entry) {
                proof {
                    self.wf_l4_at(l4i);
                    c.wf_l3_at(l4_entry.addr, l3i);
                }
                if let Some((found, is_2m, entry)) = self.next_held_leaf_l2_from(Tracked(lower), l4i, l3i, &l3_entry, if l3i == start.0 { (start.1, start.2) } else { (0, 0) }) {
                    return Some(((l3i, found.0, found.1), is_2m, entry));
                }
            }
            l3i = l3i + 1;
        }
        None
    }

    /// The first held 4K or 2M leaf at or after `cursor` in (L4, L3, L2, L1) order, which is VA order; a 2M leaf sits at L1 index
    /// 0. `cursor.3 == 512` names the slot just past `(cursor.0, cursor.1, cursor.2, 511)`, so a caller steps past a found 4K leaf
    /// `f` with `(f.0, f.1, f.2, f.3 + 1)` and past a found 2M leaf with `(f.0, f.1, f.2, 512)`. The walk follows the held chain,
    /// placeholders included, and skips every absent subtree whole. No window is locked and no hidden L1 page sits outside a
    /// locked window, so each L2 word tells whether it holds an L1 page.
    pub fn next_held_leaf_from(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, cursor: (L4Index, L3Index, L2Index, L1Index))
        -> (ret: Option<((L4Index, L3Index, L2Index, L1Index), bool, PageEntry)>)
        requires
            (WholePageTable { higher: *self, lower: *lower }).wf(),
            self.kernel_l4_end <= cursor.0,
            pei_valid(cursor.0),
            pei_valid(cursor.1),
            pei_valid(cursor.2),
            cursor.3 <= 512,
            lower.hidden_l1_tables_in_locked_windows(),
            forall|p: PageMapPtr, i: L2Index| #![trigger lower.l2_owner(p, i)] lower.l2_perms.dom().contains(p) && pei_valid(i) ==> lower.l2_owner(p, i) is None,
        ensures
            ret is Some ==> {
                let (found, is_2m, entry) = ret->Some_0;
                &&& self.kernel_l4_end <= found.0
                &&& pei_valid(found.0)
                &&& pei_valid(found.1)
                &&& pei_valid(found.2)
                &&& pei_valid(found.3)
                &&& spec_l4_index_path_le(cursor, found)
                &&& is_2m ==> found.3 == 0 && (WholePageTable { higher: *self, lower: *lower }).spec_held_2m_l2(found.0, found.1, found.2) == Some(entry)
                &&& !is_2m ==> (WholePageTable { higher: *self, lower: *lower }).spec_held_4k_l1(found.0, found.1, found.2, found.3) == Some(entry)
            },
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *self, lower: *lower }).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i)) && (ret is None || !spec_l4_index_path_le(ret->Some_0.0, (l4i, l3i, l2i, l1i)))
                    ==> (WholePageTable { higher: *self, lower: *lower }).spec_held_4k_l1(l4i, l3i, l2i, l1i) is None,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger (WholePageTable { higher: *self, lower: *lower }).spec_held_2m_l2(l4i, l3i, l2i)]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && spec_l4_index_path_le(cursor, (l4i, l3i, l2i, 0)) && (ret is None || !spec_l4_index_path_le(ret->Some_0.0, (l4i, l3i, l2i, 0)))
                    ==> (WholePageTable { higher: *self, lower: *lower }).spec_held_2m_l2(l4i, l3i, l2i) is None,
    {
        let ghost c = WholePageTable { higher: *self, lower: *lower };
        let mut l4i = cursor.0;
        while l4i < 512
            invariant
                c == (WholePageTable { higher: *self, lower: *lower }),
                c.wf(),
                self.kernel_l4_end <= cursor.0 <= l4i <= 512,
                pei_valid(cursor.0),
                pei_valid(cursor.1),
                pei_valid(cursor.2),
                cursor.3 <= 512,
                lower.hidden_l1_tables_in_locked_windows(),
                forall|p: PageMapPtr, i: L2Index| #![trigger lower.l2_owner(p, i)] lower.l2_perms.dom().contains(p) && pei_valid(i) ==> lower.l2_owner(p, i) is None,
                forall|done_l4i: L4Index, done_l3i: L3Index, done_l2i: L2Index, done_l1i: L1Index| #![trigger c.spec_held_4k_l1(done_l4i, done_l3i, done_l2i, done_l1i)]
                    pei_valid(done_l4i) && pei_valid(done_l3i) && pei_valid(done_l2i) && pei_valid(done_l1i) && spec_l4_index_path_le(cursor, (done_l4i, done_l3i, done_l2i, done_l1i)) && done_l4i < l4i ==> c.spec_held_4k_l1(done_l4i, done_l3i, done_l2i, done_l1i) is None,
                forall|done_l4i: L4Index, done_l3i: L3Index, done_l2i: L2Index| #![trigger c.spec_held_2m_l2(done_l4i, done_l3i, done_l2i)]
                    pei_valid(done_l4i) && pei_valid(done_l3i) && pei_valid(done_l2i) && spec_l4_index_path_le(cursor, (done_l4i, done_l3i, done_l2i, 0)) && done_l4i < l4i ==> c.spec_held_2m_l2(done_l4i, done_l3i, done_l2i) is None,
            decreases 512 - l4i,
        {
            if let Some(l4_entry) = self.get_held_entry_l4(l4i) {
                if let Some((found, is_2m, entry)) = self.next_held_leaf_l3_from(Tracked(lower), l4i, &l4_entry, if l4i == cursor.0 { (cursor.1, cursor.2, cursor.3) } else { (0, 0, 0) }) {
                    return Some(((l4i, found.0, found.1, found.2), is_2m, entry));
                }
            }
            l4i = l4i + 1;
        }
        None
    }
}
} // verus!
