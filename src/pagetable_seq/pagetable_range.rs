use vstd::prelude::*;

verus! {
use super::entry::*;
use super::pagetable_spec::*;
use crate::*;

pub open spec fn spec_l2_index_path_le(lhs: (L2Index, L1Index), rhs: (L2Index, L1Index)) -> bool { lhs.0 < rhs.0 || (lhs.0 == rhs.0 && lhs.1 <= rhs.1) }

pub open spec fn spec_l3_index_path_le(lhs: (L3Index, L2Index, L1Index), rhs: (L3Index, L2Index, L1Index)) -> bool {
    lhs.0 < rhs.0 || (lhs.0 == rhs.0 && spec_l2_index_path_le((lhs.1, lhs.2), (rhs.1, rhs.2)))
}

pub open spec fn spec_l4_index_path_le(lhs: (L4Index, L3Index, L2Index, L1Index), rhs: (L4Index, L3Index, L2Index, L1Index)) -> bool {
    lhs.0 < rhs.0 || (lhs.0 == rhs.0 && spec_l3_index_path_le((lhs.1, lhs.2, lhs.3), (rhs.1, rhs.2, rhs.3)))
}

/// An index path strictly below the L1 successor `succ` of `n` is `n` itself or strictly below `n`.
pub proof fn lemma_l4_index_path_le_successor(n: (L4Index, L3Index, L2Index, L1Index), succ: (L4Index, L3Index, L2Index, L1Index))
    requires
        n.3 < 512,
        succ == (n.0, n.1, n.2, (n.3 + 1) as usize),
    ensures
        forall|idx: (L4Index, L3Index, L2Index, L1Index)| #![trigger spec_l4_index_path_le(succ, idx)] !spec_l4_index_path_le(succ, idx) ==> idx == n || !spec_l4_index_path_le(n, idx),
{
}

impl<const TABLE_TYPE: PTType> PageTable<TABLE_TYPE> {
    /// No abstract 4K mapping exists in the inclusive L1 interval under one
    /// fixed L4/L3/L2 path.
    pub open spec fn spec_mapping_4k_l1_range_empty(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index, start_l1i: L1Index, end_l1i: L1Index) -> bool {
        forall|l1i: L1Index| #![trigger self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))] start_l1i <= l1i <= end_l1i ==> !self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
    }

    /// No abstract 4K mapping exists in the inclusive (L2, L1) interval
    /// under one fixed L4/L3 path.
    pub open spec fn spec_mapping_4k_l2_range_empty(&self, l4i: L4Index, l3i: L3Index, start: (L2Index, L1Index), end: (L2Index, L1Index)) -> bool {
        forall|l2i: L2Index, l1i: L1Index|
            #![trigger self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l2i) && pei_valid(l1i) && spec_l2_index_path_le(start, (l2i, l1i)) && spec_l2_index_path_le((l2i, l1i), end) ==> !self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
    }

    /// No abstract 4K mapping exists in the inclusive (L3, L2, L1)
    /// interval under one fixed L4 path.
    pub open spec fn spec_mapping_4k_l3_range_empty(&self, l4i: L4Index, start: (L3Index, L2Index, L1Index), end: (L3Index, L2Index, L1Index)) -> bool {
        forall|l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l3_index_path_le(start, (l3i, l2i, l1i)) && spec_l3_index_path_le((l3i, l2i, l1i), end) ==> !self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
    }

    /// No abstract 4K mapping exists between two inclusive four-level index
    /// boundaries. The tuple order is (L4, L3, L2, L1).
    pub open spec fn spec_mapping_4k_range_empty(&self, start: (L4Index, L3Index, L2Index, L1Index), end: (L4Index, L3Index, L2Index, L1Index)) -> bool {
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l4_index_path_le(start, (l4i, l3i, l2i, l1i)) && spec_l4_index_path_le((l4i, l3i, l2i, l1i), end)
                ==> !self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
    }

    /// Every address in the 4K range resolves to a user-present concrete leaf
    /// whose abstract mapping carries a valid physical page pointer.
    pub open spec fn spec_mapping_4k_va_range_present(&self, range: &VaRange4K) -> bool
        recommends
            self.wf(),
            range.wf(),
            self.kernel_l4_end <= spec_va2index(range.start).0,
    {
        forall|i: int|
            #![trigger self.mapping_4k().dom().contains(range.view().spec_index(i))]
            #![trigger self.spec_resolve_mapping_4k_l1(spec_va2index(range.view().spec_index(i)).0, spec_va2index(range.view().spec_index(i)).1, spec_va2index(range.view().spec_index(i)).2, spec_va2index(range.view().spec_index(i)).3)]
            0 <= i < range.len ==> {
                let va = range.view().spec_index(i);
                let indices = spec_va2index(va);
                &&& self.kernel_l4_end <= indices.0
                &&& pei_valid(indices.0)
                &&& pei_valid(indices.1)
                &&& pei_valid(indices.2)
                &&& pei_valid(indices.3)
                &&& self.mapping_4k().dom().contains(va)
                &&& self.mapping_4k().spec_index(va).present
                &&& page_ptr_valid(self.mapping_4k().spec_index(va).addr)
                &&& {
                    let resolved = self.spec_resolve_mapping_4k_l1(indices.0, indices.1, indices.2, indices.3);
                    &&& resolved is Some
                    &&& resolved->0.perm.kernel_present
                    &&& resolved->0.perm.present
                }
            }
    }

    fn mapping_4k_l1_range_empty(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index, l2_entry: &PageEntry, start_l1i: L1Index, end_l1i: L1Index) -> (ret: bool)
        requires
            self.wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            pei_valid(start_l1i),
            pei_valid(end_l1i),
            start_l1i <= end_l1i,
            self.spec_resolve_mapping_l2(l4i, l3i, l2i) =~= Some(*l2_entry),
        ensures
            ret == self.spec_mapping_4k_l1_range_empty(l4i, l3i, l2i, start_l1i, end_l1i),
    {
        let mut l1i = start_l1i;
        while l1i <= end_l1i
            invariant
                self.wf(),
                self.kernel_l4_end <= l4i && pei_valid(l4i),
                pei_valid(l3i),
                pei_valid(l2i),
                pei_valid(start_l1i),
                pei_valid(end_l1i),
                start_l1i <= l1i <= end_l1i + 1,
                self.spec_resolve_mapping_l2(l4i, l3i, l2i) =~= Some(*l2_entry),
                forall|done_l1i: L1Index| #![trigger self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, done_l1i)))] start_l1i <= done_l1i < l1i ==> !self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, done_l1i))),
            decreases end_l1i + 1 - l1i,
        {
            let entry = self.get_entry_l1(l4i, l3i, l2i, l1i, l2_entry);
            match entry {
                Some(_) => return false,
                None => {},
            }
            l1i = l1i + 1;
        }
        true
    }

    fn mapping_4k_l2_range_empty(&self, l4i: L4Index, l3i: L3Index, l3_entry: &PageEntry, start: (L2Index, L1Index), end: (L2Index, L1Index)) -> (ret: bool)
        requires
            self.wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(start.0),
            pei_valid(start.1),
            pei_valid(end.0),
            pei_valid(end.1),
            spec_l2_index_path_le(start, end),
            self.spec_resolve_mapping_l3(l4i, l3i) =~= Some(*l3_entry),
        ensures
            ret == self.spec_mapping_4k_l2_range_empty(l4i, l3i, start, end),
    {
        let mut l2i = start.0;
        while l2i <= end.0
            invariant
                self.wf(),
                self.kernel_l4_end <= l4i && pei_valid(l4i),
                pei_valid(l3i),
                pei_valid(start.0),
                pei_valid(start.1),
                pei_valid(end.0),
                pei_valid(end.1),
                spec_l2_index_path_le(start, end),
                start.0 <= l2i <= end.0 + 1,
                self.spec_resolve_mapping_l3(l4i, l3i) =~= Some(*l3_entry),
                forall|done_l2i: L2Index, done_l1i: L1Index|
                    #![trigger self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, done_l2i, done_l1i)))]
                    pei_valid(done_l2i) && pei_valid(done_l1i) && spec_l2_index_path_le(start, (done_l2i, done_l1i)) && spec_l2_index_path_le((done_l2i, done_l1i), end) && done_l2i < l2i
                        ==> !self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, done_l2i, done_l1i))),
            decreases end.0 + 1 - l2i,
        {
            let l2_entry = self.get_entry_l2(l4i, l3i, l2i, l3_entry);
            if let Some(l2_entry) = l2_entry {
                if !self.mapping_4k_l1_range_empty(l4i, l3i, l2i, &l2_entry, if l2i == start.0 { start.1 } else { 0 }, if l2i == end.0 { end.1 } else { 511 }) {
                    return false;
                }
            }
            l2i = l2i + 1;
        }
        true
    }

    fn mapping_4k_l3_range_empty(&self, l4i: L4Index, l4_entry: &PageEntry, start: (L3Index, L2Index, L1Index), end: (L3Index, L2Index, L1Index)) -> (ret: bool)
        requires
            self.wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(start.0),
            pei_valid(start.1),
            pei_valid(start.2),
            pei_valid(end.0),
            pei_valid(end.1),
            pei_valid(end.2),
            spec_l3_index_path_le(start, end),
            self.spec_resolve_mapping_l4(l4i) =~= Some(*l4_entry),
        ensures
            ret == self.spec_mapping_4k_l3_range_empty(l4i, start, end),
    {
        let mut l3i = start.0;
        while l3i <= end.0
            invariant
                self.wf(),
                self.kernel_l4_end <= l4i && pei_valid(l4i),
                pei_valid(start.0),
                pei_valid(start.1),
                pei_valid(start.2),
                pei_valid(end.0),
                pei_valid(end.1),
                pei_valid(end.2),
                spec_l3_index_path_le(start, end),
                start.0 <= l3i <= end.0 + 1,
                self.spec_resolve_mapping_l4(l4i) =~= Some(*l4_entry),
                forall|done_l3i: L3Index, done_l2i: L2Index, done_l1i: L1Index|
                    #![trigger self.mapping_4k().dom().contains(spec_index2va((l4i, done_l3i, done_l2i, done_l1i)))]
                    pei_valid(done_l3i) && pei_valid(done_l2i) && pei_valid(done_l1i) && spec_l3_index_path_le(start, (done_l3i, done_l2i, done_l1i)) && spec_l3_index_path_le((done_l3i, done_l2i, done_l1i), end) && done_l3i < l3i
                        ==> !self.mapping_4k().dom().contains(spec_index2va((l4i, done_l3i, done_l2i, done_l1i))),
            decreases end.0 + 1 - l3i,
        {
            let l3_entry = self.get_entry_l3(l4i, l3i, l4_entry);
            if let Some(l3_entry) = l3_entry {
                if !self.mapping_4k_l2_range_empty(l4i, l3i, &l3_entry, if l3i == start.0 { (start.1, start.2) } else { (0, 0) }, if l3i == end.0 { (end.1, end.2) } else { (511, 511) }) {
                    return false;
                }
            }
            l3i = l3i + 1;
        }
        true
    }

    /// Check whether the abstract 4K mapping is empty between two inclusive
    /// page-table index boundaries. Missing directory levels and huge-page
    /// entries skip their complete 4K subtrees.
    pub fn mapping_4k_range_empty(&self, start: (L4Index, L3Index, L2Index, L1Index), end: (L4Index, L3Index, L2Index, L1Index)) -> (ret: bool)
        requires
            self.wf(),
            self.kernel_l4_end <= start.0,
            pei_valid(start.0),
            pei_valid(start.1),
            pei_valid(start.2),
            pei_valid(start.3),
            pei_valid(end.0),
            pei_valid(end.1),
            pei_valid(end.2),
            pei_valid(end.3),
            spec_l4_index_path_le(start, end),
        ensures
            ret == self.spec_mapping_4k_range_empty(start, end),
    {
        let mut l4i = start.0;
        while l4i <= end.0
            invariant
                self.wf(),
                self.kernel_l4_end <= start.0 <= l4i,
                pei_valid(start.0),
                pei_valid(start.1),
                pei_valid(start.2),
                pei_valid(start.3),
                pei_valid(end.0),
                pei_valid(end.1),
                pei_valid(end.2),
                pei_valid(end.3),
                spec_l4_index_path_le(start, end),
                l4i <= end.0 + 1,
                forall|done_l4i: L4Index, done_l3i: L3Index, done_l2i: L2Index, done_l1i: L1Index|
                    #![trigger self.mapping_4k().dom().contains(spec_index2va((done_l4i, done_l3i, done_l2i, done_l1i)))]
                    pei_valid(done_l4i) && pei_valid(done_l3i) && pei_valid(done_l2i) && pei_valid(done_l1i) && spec_l4_index_path_le(start, (done_l4i, done_l3i, done_l2i, done_l1i)) && spec_l4_index_path_le((done_l4i, done_l3i, done_l2i, done_l1i), end) && done_l4i < l4i
                            ==> !self.mapping_4k().dom().contains(spec_index2va((done_l4i, done_l3i, done_l2i, done_l1i))),
            decreases end.0 + 1 - l4i,
        {
            let l4_entry = self.get_entry_l4(l4i);
            if let Some(l4_entry) = l4_entry {
                if !self.mapping_4k_l3_range_empty(l4i, &l4_entry, if l4i == start.0 { (start.1, start.2, start.3) } else { (0, 0, 0) }, if l4i == end.0 { (end.1, end.2, end.3) } else { (511, 511, 511) }) {
                    return false;
                }
            }
            l4i = l4i + 1;
        }
        true
    }

    /// The first 4K mapping under one fixed L4/L3/L2 path at or after `start_l1i`; `start_l1i == 512` scans nothing.
    fn next_mapped_4k_l1_from(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index, l2_entry: &PageEntry, start_l1i: L1Index) -> (ret: Option<L1Index>)
        requires
            self.wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            start_l1i <= 512,
            self.spec_resolve_mapping_l2(l4i, l3i, l2i) =~= Some(*l2_entry),
        ensures
            ret is Some ==> {
                let found = ret->Some_0;
                &&& start_l1i <= found
                &&& pei_valid(found)
                &&& self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, found)))
            },
            forall|l1i: L1Index|
                #![trigger self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l1i) && start_l1i <= l1i && (ret is None || l1i < ret->Some_0) ==> !self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
    {
        let mut l1i = start_l1i;
        while l1i < 512
            invariant
                self.wf(),
                self.kernel_l4_end <= l4i && pei_valid(l4i),
                pei_valid(l3i),
                pei_valid(l2i),
                start_l1i <= l1i <= 512,
                self.spec_resolve_mapping_l2(l4i, l3i, l2i) =~= Some(*l2_entry),
                forall|done_l1i: L1Index| #![trigger self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, done_l1i)))] start_l1i <= done_l1i < l1i ==> !self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, done_l1i))),
            decreases 512 - l1i,
        {
            let entry = self.get_entry_l1(l4i, l3i, l2i, l1i, l2_entry);
            if let Some(_) = entry {
                return Some(l1i);
            }
            l1i = l1i + 1;
        }
        None
    }

    /// The first 4K mapping under one fixed L4/L3 path at or after `start` in (L2, L1) order.
    fn next_mapped_4k_l2_from(&self, l4i: L4Index, l3i: L3Index, l3_entry: &PageEntry, start: (L2Index, L1Index)) -> (ret: Option<(L2Index, L1Index)>)
        requires
            self.wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(start.0),
            start.1 <= 512,
            self.spec_resolve_mapping_l3(l4i, l3i) =~= Some(*l3_entry),
        ensures
            ret is Some ==> {
                let found = ret->Some_0;
                &&& pei_valid(found.0)
                &&& pei_valid(found.1)
                &&& spec_l2_index_path_le(start, found)
                &&& self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, found.0, found.1)))
            },
            forall|l2i: L2Index, l1i: L1Index|
                #![trigger self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l2i) && pei_valid(l1i) && spec_l2_index_path_le(start, (l2i, l1i)) && (ret is None || !spec_l2_index_path_le(ret->Some_0, (l2i, l1i)))
                    ==> !self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
    {
        let mut l2i = start.0;
        while l2i < 512
            invariant
                self.wf(),
                self.kernel_l4_end <= l4i && pei_valid(l4i),
                pei_valid(l3i),
                pei_valid(start.0),
                start.1 <= 512,
                start.0 <= l2i <= 512,
                self.spec_resolve_mapping_l3(l4i, l3i) =~= Some(*l3_entry),
                forall|done_l2i: L2Index, done_l1i: L1Index|
                    #![trigger self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, done_l2i, done_l1i)))]
                    pei_valid(done_l2i) && pei_valid(done_l1i) && spec_l2_index_path_le(start, (done_l2i, done_l1i)) && done_l2i < l2i
                        ==> !self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, done_l2i, done_l1i))),
            decreases 512 - l2i,
        {
            let l2_entry = self.get_entry_l2(l4i, l3i, l2i, l3_entry);
            if let Some(l2_entry) = l2_entry {
                if let Some(l1i) = self.next_mapped_4k_l1_from(l4i, l3i, l2i, &l2_entry, if l2i == start.0 { start.1 } else { 0 }) {
                    return Some((l2i, l1i));
                }
            }
            l2i = l2i + 1;
        }
        None
    }

    /// The first 4K mapping under one fixed L4 path at or after `start` in (L3, L2, L1) order.
    fn next_mapped_4k_l3_from(&self, l4i: L4Index, l4_entry: &PageEntry, start: (L3Index, L2Index, L1Index)) -> (ret: Option<(L3Index, L2Index, L1Index)>)
        requires
            self.wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(start.0),
            pei_valid(start.1),
            start.2 <= 512,
            self.spec_resolve_mapping_l4(l4i) =~= Some(*l4_entry),
        ensures
            ret is Some ==> {
                let found = ret->Some_0;
                &&& pei_valid(found.0)
                &&& pei_valid(found.1)
                &&& pei_valid(found.2)
                &&& spec_l3_index_path_le(start, found)
                &&& self.mapping_4k().dom().contains(spec_index2va((l4i, found.0, found.1, found.2)))
            },
            forall|l3i: L3Index, l2i: L2Index, l1i: L1Index|
                #![trigger self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l3_index_path_le(start, (l3i, l2i, l1i)) && (ret is None || !spec_l3_index_path_le(ret->Some_0, (l3i, l2i, l1i)))
                    ==> !self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
    {
        let mut l3i = start.0;
        while l3i < 512
            invariant
                self.wf(),
                self.kernel_l4_end <= l4i && pei_valid(l4i),
                pei_valid(start.0),
                pei_valid(start.1),
                start.2 <= 512,
                start.0 <= l3i <= 512,
                self.spec_resolve_mapping_l4(l4i) =~= Some(*l4_entry),
                forall|done_l3i: L3Index, done_l2i: L2Index, done_l1i: L1Index|
                    #![trigger self.mapping_4k().dom().contains(spec_index2va((l4i, done_l3i, done_l2i, done_l1i)))]
                    pei_valid(done_l3i) && pei_valid(done_l2i) && pei_valid(done_l1i) && spec_l3_index_path_le(start, (done_l3i, done_l2i, done_l1i)) && done_l3i < l3i
                        ==> !self.mapping_4k().dom().contains(spec_index2va((l4i, done_l3i, done_l2i, done_l1i))),
            decreases 512 - l3i,
        {
            let l3_entry = self.get_entry_l3(l4i, l3i, l4_entry);
            if let Some(l3_entry) = l3_entry {
                if let Some(found) = self.next_mapped_4k_l2_from(l4i, l3i, &l3_entry, if l3i == start.0 { (start.1, start.2) } else { (0, 0) }) {
                    return Some((l3i, found.0, found.1));
                }
            }
            l3i = l3i + 1;
        }
        None
    }

    /// The first 4K mapping at or after `cursor` in (L4, L3, L2, L1) order. `cursor.3 == 512` names the slot just past
    /// `(cursor.0, cursor.1, cursor.2, 511)`, so a caller steps past a found leaf `f` with `(f.0, f.1, f.2, f.3 + 1)`.
    /// Missing directory levels and huge-page entries skip their complete 4K subtrees.
    pub fn next_mapped_4k_from(&self, cursor: (L4Index, L3Index, L2Index, L1Index)) -> (ret: Option<(L4Index, L3Index, L2Index, L1Index)>)
        requires
            self.wf(),
            self.kernel_l4_end <= cursor.0,
            pei_valid(cursor.0),
            pei_valid(cursor.1),
            pei_valid(cursor.2),
            cursor.3 <= 512,
        ensures
            ret is Some ==> {
                let found = ret->Some_0;
                &&& self.kernel_l4_end <= found.0
                &&& pei_valid(found.0)
                &&& pei_valid(found.1)
                &&& pei_valid(found.2)
                &&& pei_valid(found.3)
                &&& spec_l4_index_path_le(cursor, found)
                &&& self.mapping_4k().dom().contains(spec_index2va(found))
            },
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
                #![trigger self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i))
                    && (ret is None || !spec_l4_index_path_le(ret->Some_0, (l4i, l3i, l2i, l1i)))
                    ==> !self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
    {
        let mut l4i = cursor.0;
        while l4i < 512
            invariant
                self.wf(),
                self.kernel_l4_end <= cursor.0 <= l4i <= 512,
                pei_valid(cursor.0),
                pei_valid(cursor.1),
                pei_valid(cursor.2),
                cursor.3 <= 512,
                forall|done_l4i: L4Index, done_l3i: L3Index, done_l2i: L2Index, done_l1i: L1Index|
                    #![trigger self.mapping_4k().dom().contains(spec_index2va((done_l4i, done_l3i, done_l2i, done_l1i)))]
                    pei_valid(done_l4i) && pei_valid(done_l3i) && pei_valid(done_l2i) && pei_valid(done_l1i) && spec_l4_index_path_le(cursor, (done_l4i, done_l3i, done_l2i, done_l1i)) && done_l4i < l4i
                        ==> !self.mapping_4k().dom().contains(spec_index2va((done_l4i, done_l3i, done_l2i, done_l1i))),
            decreases 512 - l4i,
        {
            let l4_entry = self.get_entry_l4(l4i);
            if let Some(l4_entry) = l4_entry {
                if let Some(found) = self.next_mapped_4k_l3_from(l4i, &l4_entry, if l4i == cursor.0 { (cursor.1, cursor.2, cursor.3) } else { (0, 0, 0) }) {
                    return Some((l4i, found.0, found.1, found.2));
                }
            }
            l4i = l4i + 1;
        }
        None
    }

    /// Check whether every address in a 4K range has a user-present leaf.
    ///
    /// This scans only the page table and does not mutate any page-table state.
    pub fn mapping_4k_va_range_present(&self, range: &VaRange4K) -> (ret: bool)
        requires
            self.wf(),
            range.wf(),
            self.kernel_l4_end <= spec_va2index(range.start).0,
        ensures
            ret == self.spec_mapping_4k_va_range_present(range),
            ret == forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < range.len
                ==> self.mapping_4k().dom().contains(range.view().spec_index(j)) && self.mapping_4k().spec_index(range.view().spec_index(j)).present,
    {
        let range_start = range.start;
        let range_len = range.len;
        let mut i: usize = 0;
        while i < range_len
            invariant
                self.wf(),
                range.wf(),
                range_start == range.start,
                range_len == range.len,
                self.kernel_l4_end <= spec_va2index(range.start).0,
                0 <= i <= range_len,
                forall|done: int|
                    #![trigger self.mapping_4k().dom().contains(range.view().spec_index(done))]
                    #![trigger self.spec_resolve_mapping_4k_l1(spec_va2index(range.view().spec_index(done)).0, spec_va2index(range.view().spec_index(done)).1,
                        spec_va2index(range.view().spec_index(done)).2, spec_va2index(range.view().spec_index(done)).3)]
                    0 <= done < i ==> {
                        let va = range.view().spec_index(done);
                        let indices = spec_va2index(va);
                        &&& self.kernel_l4_end <= indices.0
                        &&& pei_valid(indices.0)
                        &&& pei_valid(indices.1)
                        &&& pei_valid(indices.2)
                        &&& pei_valid(indices.3)
                        &&& self.mapping_4k().dom().contains(va)
                        &&& self.mapping_4k().spec_index(va).present
                        &&& page_ptr_valid(self.mapping_4k().spec_index(va).addr)
                        &&& {
                            let resolved = self.spec_resolve_mapping_4k_l1(indices.0, indices.1, indices.2, indices.3);
                            &&& resolved is Some
                            &&& resolved->0.perm.kernel_present
                            &&& resolved->0.perm.present
                        }
                    },
            decreases range_len - i,
        {
            let va = va_add_range(range_start, i);
            proof { assert(va_4k_valid(va)) by { range.va_range_lemma(); }; }
            let (l4i, l3i, l2i, l1i) = va2index(va);
            proof { assert(self.kernel_l4_end <= l4i) by { assert(spec_va_4k_valid(range_start) && spec_va_4k_valid(va) && range_start <= va) by { range.va_range_lemma(); }; spec_v2l4index_monotonic(range_start, va); }; }
            let resolved = self.resolve_mapping_4k_l1(l4i, l3i, l2i, l1i);
            if resolved.2.is_none() {
                proof { assert(!self.mapping_4k().dom().contains(range.view().spec_index(i as int))) by { range.va_range_lemma(); reveal(PageTable::wf_mapping_4k); spec_va_4k_index_roundtrip_at(va, l4i, l3i, l2i, l1i); }; }
                return false;
            }
            let entry = resolved.2.unwrap();
            if !entry.present {
                proof {
                    assert(!self.spec_mapping_4k_va_range_present(range)) by { range.va_range_lemma(); assert(spec_index2va((l4i, l3i, l2i, l1i)) == va) by { spec_va_4k_index_roundtrip_at(va, l4i, l3i, l2i, l1i); }; };
                    assert(!self.mapping_4k().spec_index(range.view().spec_index(i as int)).present) by { range.va_range_lemma(); reveal(PageTable::wf_mapping_4k); spec_va_4k_index_roundtrip_at(va, l4i, l3i, l2i, l1i); };
                }
                return false;
            }
            proof {
                assert({
                    let checked_va = range.view().spec_index(i as int);
                    let checked_indices = spec_va2index(checked_va);
                    &&& self.kernel_l4_end <= checked_indices.0
                    &&& pei_valid(checked_indices.0)
                    &&& pei_valid(checked_indices.1)
                    &&& pei_valid(checked_indices.2)
                    &&& pei_valid(checked_indices.3)
                    &&& self.mapping_4k().dom().contains(checked_va)
                    &&& self.mapping_4k().spec_index(checked_va).present
                    &&& page_ptr_valid(self.mapping_4k().spec_index(checked_va).addr)
                    &&& {
                        let spec_resolved = self.spec_resolve_mapping_4k_l1(checked_indices.0, checked_indices.1, checked_indices.2, checked_indices.3);
                        &&& spec_resolved is Some
                        &&& spec_resolved->0.perm.kernel_present
                        &&& spec_resolved->0.perm.present
                    }
                }) by { range.va_range_lemma(); assert(spec_index2va((l4i, l3i, l2i, l1i)) == va) by { spec_va_4k_index_roundtrip_at(va, l4i, l3i, l2i, l1i); }; reveal(PageTable::wf_mapping_4k); };
            }
            i = i + 1;
        }
        true
    }

    /// Check whether no address in a 4K range has an abstract 4K mapping.
    ///
    /// This scans only the page table and does not mutate any page-table state.
    pub fn mapping_4k_va_range_absent(&self, range: &VaRange4K) -> (ret: bool)
        requires
            self.wf(),
            range.wf(),
            self.kernel_l4_end <= spec_va2index(range.start).0,
        ensures
            ret == forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < range.len ==> !self.mapping_4k().dom().contains(range.view().spec_index(j)),
    {
        let range_start = range.start;
        let range_len = range.len;
        let mut i: usize = 0;
        while i < range_len
            invariant
                self.wf(),
                range.wf(),
                range_start == range.start,
                range_len == range.len,
                self.kernel_l4_end <= spec_va2index(range.start).0,
                0 <= i <= range_len,
                forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < i ==> !self.mapping_4k().dom().contains(range.view().spec_index(j)),
            decreases range_len - i,
        {
            let va = va_add_range(range_start, i);
            proof { assert(va_4k_valid(va)) by { range.va_range_lemma(); }; }
            let (l4i, l3i, l2i, l1i) = va2index(va);
            proof { assert(self.kernel_l4_end <= l4i) by { assert(spec_va_4k_valid(range_start) && spec_va_4k_valid(va) && range_start <= va) by { range.va_range_lemma(); }; spec_v2l4index_monotonic(range_start, va); }; }
            let resolved = self.resolve_mapping_4k_l1(l4i, l3i, l2i, l1i);
            if resolved.2.is_some() {
                proof { assert(self.mapping_4k().dom().contains(range.view().spec_index(i as int))) by { range.va_range_lemma(); reveal(PageTable::wf_mapping_4k); spec_va_4k_index_roundtrip_at(va, l4i, l3i, l2i, l1i); }; }
                return false;
            }
            proof { assert(!self.mapping_4k().dom().contains(range.view().spec_index(i as int))) by { range.va_range_lemma(); reveal(PageTable::wf_mapping_4k); spec_va_4k_index_roundtrip_at(va, l4i, l3i, l2i, l1i); }; }
            i = i + 1;
        }
        true
    }

    /// Every 4K slot in the range is available for a new leaf. Missing
    /// directory levels are allowed; existing 1G, 2M, and 4K leaves are not.
    pub open spec fn spec_mapping_4k_va_range_buildable(&self, range: &VaRange4K) -> bool {
        forall|i: int|
            #![trigger self.spec_resolve_mapping_4k_l1(spec_va2index(range.view().spec_index(i)).0, spec_va2index(range.view().spec_index(i)).1, spec_va2index(range.view().spec_index(i)).2, spec_va2index(range.view().spec_index(i)).3)]
            0 <= i < range.len ==> self.spec_4k_entry_usable(spec_va2index(range.view().spec_index(i)).0, spec_va2index(range.view().spec_index(i)).1, spec_va2index(range.view().spec_index(i)).2, spec_va2index(range.view().spec_index(i)).3)
    }

    pub fn mapping_4k_va_range_buildable(&self, range: &VaRange4K) -> (ret: bool)
        requires
            self.wf(),
            range.wf(),
            range.len > 0,
            self.kernel_l4_end <= spec_va2index(range.start).0,
        ensures
            ret == self.spec_mapping_4k_va_range_buildable(range),
            ret == forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < range.len ==> {
                let indices = spec_va2index(range.view().spec_index(j));
                &&& !self.mapping_1g().dom().contains(spec_index2va((indices.0, indices.1, 0, 0)))
                &&& !self.mapping_2m().dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0)))
                &&& !self.mapping_4k().dom().contains(range.view().spec_index(j))
            },
    {
        let range_start = range.start;
        let range_len = range.len;
        let mut i: usize = 0;
        while i < range.len
            invariant
                self.wf(),
                range.wf(),
                range_start == range.start,
                range_len == range.len,
                range.len > 0,
                self.kernel_l4_end <= spec_va2index(range.start).0,
                0 <= i <= range.len,
                forall|j: int|
                    #![trigger range.view().spec_index(j)]
                    0 <= j < i ==> {
                        let indices = spec_va2index(range.view().spec_index(j));
                        &&& self.kernel_l4_end <= indices.0
                        &&& pei_valid(indices.0)
                        &&& pei_valid(indices.1)
                        &&& pei_valid(indices.2)
                        &&& pei_valid(indices.3)
                        &&& !self.mapping_1g().dom().contains(spec_index2va((indices.0, indices.1, 0, 0)))
                        &&& !self.mapping_2m().dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0)))
                        &&& !self.mapping_4k().dom().contains(range.view().spec_index(j))
                    },
                forall|j: int|
                    #![trigger self.spec_resolve_mapping_4k_l1(spec_va2index(range.view().spec_index(j)).0, spec_va2index(range.view().spec_index(j)).1,
                        spec_va2index(range.view().spec_index(j)).2, spec_va2index(range.view().spec_index(j)).3)]
                    0 <= j < i ==> {
                        let indices = spec_va2index(range.view().spec_index(j));
                        self.spec_4k_entry_usable(indices.0, indices.1, indices.2, indices.3)
                    },
            decreases range.len - i,
        {
            let va = va_add_range(range_start, i);
            proof { assert(va_4k_valid(va)) by { range.va_range_lemma(); }; }
            let (l4i, l3i, l2i, l1i) = va2index(va);
            proof { assert(self.kernel_l4_end <= l4i) by { assert(spec_va_4k_valid(range_start) && spec_va_4k_valid(va) && range_start <= va) by { range.va_range_lemma(); }; spec_v2l4index_monotonic(range_start, va); }; }
            let resolved = self.resolve_mapping_4k_l1(l4i, l3i, l2i, l1i);
            match resolved.1 {
                PageTableErrorCode::NoError | PageTableErrorCode::EntryTakenBy4k | PageTableErrorCode::EntryTakenBy1g | PageTableErrorCode::EntryTakenBy2m => {
                    proof {
                        assert(!self.spec_mapping_4k_va_range_buildable(range)) by { range.va_range_lemma(); spec_va_4k_valid_imply_indices_valid(); };
                        assert({
                            let indices = spec_va2index(range.view().spec_index(i as int));
                            ||| self.mapping_1g().dom().contains(spec_index2va((indices.0, indices.1, 0, 0)))
                            ||| self.mapping_2m().dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0)))
                            ||| self.mapping_4k().dom().contains(range.view().spec_index(i as int))
                        }) by {
                            range.va_range_lemma(); spec_va_4k_valid_imply_indices_valid(); spec_va_4k_index_roundtrip_at(va, l4i, l3i, l2i, l1i);
                            reveal(PageTable::wf_mapping_1g); reveal(PageTable::wf_mapping_2m); reveal(PageTable::wf_mapping_4k);
                        };
                    }
                    return false;
                },
                PageTableErrorCode::L4EntryNotExist | PageTableErrorCode::L3EntryNotExist | PageTableErrorCode::L2EntryNotExist | PageTableErrorCode::L1EntryNotExist => {},
            }
            proof {
                assert({
                    let checked_indices = spec_va2index(range.view().spec_index(i as int));
                    &&& self.kernel_l4_end <= checked_indices.0
                    &&& pei_valid(checked_indices.0)
                    &&& pei_valid(checked_indices.1)
                    &&& pei_valid(checked_indices.2)
                    &&& pei_valid(checked_indices.3)
                    &&& self.spec_4k_entry_usable(checked_indices.0, checked_indices.1, checked_indices.2, checked_indices.3)
                    &&& !self.mapping_1g().dom().contains(spec_index2va((checked_indices.0, checked_indices.1, 0, 0)))
                    &&& !self.mapping_2m().dom().contains(spec_index2va((checked_indices.0, checked_indices.1, checked_indices.2, 0)))
                    &&& !self.mapping_4k().dom().contains(range.view().spec_index(i as int))
                }) by {
                    range.va_range_lemma(); spec_va_4k_valid_imply_indices_valid();
                    assert(spec_index2va((l4i, l3i, l2i, l1i)) == va) by { spec_va_4k_index_roundtrip_at(va, l4i, l3i, l2i, l1i); };
                    reveal(PageTable::wf_mapping_1g); reveal(PageTable::wf_mapping_2m); reveal(PageTable::wf_mapping_4k);
                };
            }
            i = i + 1;
        }
        true
    }
}
} // verus!
