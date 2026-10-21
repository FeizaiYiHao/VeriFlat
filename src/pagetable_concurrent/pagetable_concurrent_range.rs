use vstd::prelude::*;

verus! {
use crate::*;

impl<const TABLE_TYPE: PTType> PageTableC<TABLE_TYPE> {
    /// No 4K leaf resolves in the inclusive L1 interval under one fixed L4/L3/L2 path.
    pub open spec fn spec_resolve_4k_l1_range_empty(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index, start_l1i: L1Index, end_l1i: L1Index) -> bool {
        forall|l1i: L1Index|
            #![trigger self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
            start_l1i <= l1i <= end_l1i ==> self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is None
    }

    /// No 4K leaf resolves in the inclusive (L2, L1) interval under one fixed L4/L3 path.
    pub open spec fn spec_resolve_4k_l2_range_empty(&self, l4i: L4Index, l3i: L3Index, start: (L2Index, L1Index), end: (L2Index, L1Index)) -> bool {
        forall|l2i: L2Index, l1i: L1Index|
            #![trigger self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
            pei_valid(l2i) && pei_valid(l1i) && spec_l2_index_path_le(start, (l2i, l1i)) && spec_l2_index_path_le((l2i, l1i), end) ==> self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is None
    }

    /// No 4K leaf resolves in the inclusive (L3, L2, L1) interval under one fixed L4 path.
    pub open spec fn spec_resolve_4k_l3_range_empty(&self, l4i: L4Index, start: (L3Index, L2Index, L1Index), end: (L3Index, L2Index, L1Index)) -> bool {
        forall|l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
            pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l3_index_path_le(start, (l3i, l2i, l1i)) && spec_l3_index_path_le((l3i, l2i, l1i), end)
                ==> self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is None
    }

    /// No 4K leaf resolves between two inclusive (L4, L3, L2, L1) boundaries. The address trigger lets
    /// `mapping_4k_range_empty_from_resolve` carry it to the abstract mapping.
    pub open spec fn spec_resolve_4k_range_empty(&self, start: (L4Index, L3Index, L2Index, L1Index), end: (L4Index, L3Index, L2Index, L1Index)) -> bool {
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
            #![trigger spec_index2va((l4i, l3i, l2i, l1i))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l4_index_path_le(start, (l4i, l3i, l2i, l1i)) && spec_l4_index_path_le((l4i, l3i, l2i, l1i), end)
                ==> self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is None
    }

    /// No abstract 4K mapping exists between two inclusive four-level index boundaries. The tuple order is
    /// (L4, L3, L2, L1).
    pub open spec fn spec_mapping_4k_range_empty(&self, start: (L4Index, L3Index, L2Index, L1Index), end: (L4Index, L3Index, L2Index, L1Index)) -> bool {
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l4_index_path_le(start, (l4i, l3i, l2i, l1i)) && spec_l4_index_path_le((l4i, l3i, l2i, l1i), end)
                ==> !self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
    }

    #[verifier::opaque]
    pub open spec fn spec_mapping_4k_va_range_empty(&self, start_va: VAddr, end_va: VAddr) -> bool {
        forall|va: VAddr| #![trigger self.mapping_4k().dom().contains(va)] spec_va_4k_valid(va) && start_va <= va <= end_va ==> !self.mapping_4k().dom().contains(va)
    }

    /// Every address in the 4K range resolves to a user-present concrete leaf whose abstract mapping carries a
    /// valid physical page pointer.
    pub open spec fn spec_mapping_4k_va_range_present(&self, range: &VaRange4K) -> bool
        recommends
            self.wf(),
            range.wf(),
            self.kernel_l4_end() <= spec_va2index(range.start).0,
    {
        forall|i: int|
            #![trigger self.mapping_4k().dom().contains(range.view().spec_index(i))]
            #![trigger self.spec_resolve_mapping_4k_l1(spec_va2index(range.view().spec_index(i)).0, spec_va2index(range.view().spec_index(i)).1, spec_va2index(range.view().spec_index(i)).2, spec_va2index(range.view().spec_index(i)).3)]
            0 <= i < range.len ==> {
                let va = range.view().spec_index(i);
                let indices = spec_va2index(va);
                &&& self.kernel_l4_end() <= indices.0
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

    pub broadcast proof fn mapping_4k_index_range_empty_implies_va_empty_at(&self, start_l4i: L4Index, start_l3i: L3Index, start_l2i: L2Index, start_l1i: L1Index, end_l4i: L4Index, end_l3i: L3Index,
        end_l2i: L2Index, end_l1i: L1Index, va: VAddr)
        requires
            pei_valid(start_l4i),
            pei_valid(start_l3i),
            pei_valid(start_l2i),
            pei_valid(start_l1i),
            pei_valid(end_l4i),
            pei_valid(end_l3i),
            pei_valid(end_l2i),
            pei_valid(end_l1i),
            self.spec_mapping_4k_range_empty((start_l4i, start_l3i, start_l2i, start_l1i), (end_l4i, end_l3i, end_l2i, end_l1i)),
            spec_va_4k_valid(va),
            spec_index2va((start_l4i, start_l3i, start_l2i, start_l1i)) <= va,
            va <= spec_index2va((end_l4i, end_l3i, end_l2i, end_l1i)),
        ensures
            #![trigger self.mapping_4k().dom().contains(va), spec_index2va((start_l4i, start_l3i, start_l2i, start_l1i)), spec_index2va((end_l4i, end_l3i, end_l2i, end_l1i))]
            !self.mapping_4k().dom().contains(va),
    {
        let va_l4i = spec_v2l4index(va);
        let va_l3i = spec_v2l3index(va);
        let va_l2i = spec_v2l2index(va);
        let va_l1i = spec_v2l1index(va);
        assert(pei_valid(va_l4i) && pei_valid(va_l3i) && pei_valid(va_l2i) && pei_valid(va_l1i)) by { spec_va_4k_valid_imply_indices_valid(); };
        assert(spec_index2va(spec_va2index(va)) == va) by { spec_va_4k_index_roundtrip_at(va, va_l4i, va_l3i, va_l2i, va_l1i); };
        spec_index2va_le_implies_4k_indices_lex_le((start_l4i, start_l3i, start_l2i, start_l1i), (va_l4i, va_l3i, va_l2i, va_l1i));
        spec_index2va_le_implies_4k_indices_lex_le((va_l4i, va_l3i, va_l2i, va_l1i), (end_l4i, end_l3i, end_l2i, end_l1i));
    }

    /// Closure of `mapping_4k_range_empty`: the resolved and the abstract 4K range agree.
    proof fn mapping_4k_range_empty_from_resolve(&self, start: (L4Index, L3Index, L2Index, L1Index), end: (L4Index, L3Index, L2Index, L1Index))
        requires
            self.wf_mapping_4k(),
            self.kernel_l4_end() <= start.0,
        ensures
            self.spec_resolve_4k_range_empty(start, end) == self.spec_mapping_4k_range_empty(start, end),
    { reveal(PageTableC::wf_mapping_4k); }

    /// Closure of `next_mapped_4k_from`: the resolved scan result holds for the abstract 4K mapping.
    proof fn next_mapped_4k_from_resolve(&self, cursor: (L4Index, L3Index, L2Index, L1Index), ret: Option<(L4Index, L3Index, L2Index, L1Index)>)
        requires
            self.wf_mapping_4k(),
            self.kernel_l4_end() <= cursor.0,
            ret is Some ==> {
                let found = ret->Some_0;
                &&& self.kernel_l4_end() <= found.0
                &&& pei_valid(found.0)
                &&& pei_valid(found.1)
                &&& pei_valid(found.2)
                &&& pei_valid(found.3)
                &&& self.spec_resolve_mapping_4k_l1(found.0, found.1, found.2, found.3) is Some
            },
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
                #![trigger self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
                #![trigger spec_index2va((l4i, l3i, l2i, l1i))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i))
                    && (ret is None || !spec_l4_index_path_le(ret->Some_0, (l4i, l3i, l2i, l1i))) ==> self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is None,
        ensures
            ret is Some ==> self.lower.mapping_4k.dom().contains(spec_index2va(ret->Some_0)),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
                #![trigger self.lower.mapping_4k.dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i))
                    && (ret is None || !spec_l4_index_path_le(ret->Some_0, (l4i, l3i, l2i, l1i))) ==> !self.lower.mapping_4k.dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
    { reveal(PageTableC::wf_mapping_4k); }
}

impl PageTableC<PT_TYPE> {
    /// Every 4K slot in the range is available for a new leaf. Missing directory levels are allowed; existing 1G,
    /// 2M, and 4K leaves are not.
    pub open spec fn spec_mapping_4k_va_range_buildable(&self, range: &VaRange4K) -> bool {
        forall|i: int|
            #![trigger self.spec_resolve_mapping_4k_l1(spec_va2index(range.view().spec_index(i)).0, spec_va2index(range.view().spec_index(i)).1, spec_va2index(range.view().spec_index(i)).2, spec_va2index(range.view().spec_index(i)).3)]
            0 <= i < range.len ==> self.spec_4k_entry_usable(spec_va2index(range.view().spec_index(i)).0, spec_va2index(range.view().spec_index(i)).1, spec_va2index(range.view().spec_index(i)).2,
                spec_va2index(range.view().spec_index(i)).3)
    }
}

impl<const TABLE_TYPE: PTType> PageTableHigher<TABLE_TYPE> {
    pub fn mapping_4k_va_range_empty(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, start_va: VAddr, end_va: VAddr) -> (ret: bool)
        requires
            (PageTableC { higher: *self, lower: *lower }).wf(),
            va_4k_valid(start_va),
            va_4k_valid(end_va),
            start_va <= end_va,
            self.kernel_l4_end <= spec_va2index(start_va).0,
        ensures
            ret == (PageTableC { higher: *self, lower: *lower }).spec_mapping_4k_range_empty(spec_va2index(start_va), spec_va2index(end_va)),
            ret ==> (PageTableC { higher: *self, lower: *lower }).spec_mapping_4k_va_range_empty(start_va, end_va),
    {
        let start = va2index(start_va);
        let end = va2index(end_va);
        proof {
            assert(spec_index2va(start) == start_va) by { spec_va_4k_index_roundtrip_at(start_va, start.0, start.1, start.2, start.3); };
            assert(spec_index2va(end) == end_va) by { spec_va_4k_index_roundtrip_at(end_va, end.0, end.1, end.2, end.3); };
            spec_index2va_le_implies_4k_indices_lex_le(start, end);
        }
        let ret = self.mapping_4k_range_empty(Tracked(lower), start, end);
        if ret {
            assert((PageTableC { higher: *self, lower: *lower }).spec_mapping_4k_va_range_empty(start_va, end_va)) by {
                reveal(PageTableC::spec_mapping_4k_va_range_empty);
                broadcast use PageTableC::mapping_4k_index_range_empty_implies_va_empty_at;
            };
        }
        ret
    }

    fn resolve_4k_l1_range_empty(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, l4i: L4Index, l3i: L3Index, l2i: L2Index, l2_entry: &PageEntry, start_l1i: L1Index,
        end_l1i: L1Index) -> (ret: bool)
        requires
            (PageTableC { higher: *self, lower: *lower }).wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            pei_valid(start_l1i),
            pei_valid(end_l1i),
            start_l1i <= end_l1i,
            (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_l2(l4i, l3i, l2i) =~= Some(*l2_entry),
        ensures
            ret == (PageTableC { higher: *self, lower: *lower }).spec_resolve_4k_l1_range_empty(l4i, l3i, l2i, start_l1i, end_l1i),
    {
        let ghost c = PageTableC { higher: *self, lower: *lower };
        let mut l1i = start_l1i;
        while l1i <= end_l1i
            invariant
                c == (PageTableC { higher: *self, lower: *lower }),
                c.wf(),
                self.kernel_l4_end <= l4i && pei_valid(l4i),
                pei_valid(l3i),
                pei_valid(l2i),
                pei_valid(start_l1i),
                pei_valid(end_l1i),
                start_l1i <= l1i <= end_l1i + 1,
                c.spec_resolve_mapping_l2(l4i, l3i, l2i) =~= Some(*l2_entry),
                forall|done_l1i: L1Index|
                    #![trigger c.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, done_l1i)]
                    start_l1i <= done_l1i < l1i ==> c.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, done_l1i) is None,
            decreases end_l1i + 1 - l1i,
        {
            if self.get_entry_l1(Tracked(lower), l4i, l3i, l2i, l1i, l2_entry).is_some() { return false; }
            l1i = l1i + 1;
        }
        true
    }

    fn resolve_4k_l2_range_empty(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, l4i: L4Index, l3i: L3Index, l3_entry: &PageEntry, start: (L2Index, L1Index),
        end: (L2Index, L1Index)) -> (ret: bool)
        requires
            (PageTableC { higher: *self, lower: *lower }).wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(start.0),
            pei_valid(start.1),
            pei_valid(end.0),
            pei_valid(end.1),
            spec_l2_index_path_le(start, end),
            self.spec_resolve_mapping_l3(l4i, l3i) =~= Some(*l3_entry),
        ensures
            ret == (PageTableC { higher: *self, lower: *lower }).spec_resolve_4k_l2_range_empty(l4i, l3i, start, end),
    {
        let ghost c = PageTableC { higher: *self, lower: *lower };
        let mut l2i = start.0;
        while l2i <= end.0
            invariant
                c == (PageTableC { higher: *self, lower: *lower }),
                c.wf(),
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
                    #![trigger c.spec_resolve_mapping_4k_l1(l4i, l3i, done_l2i, done_l1i)]
                    pei_valid(done_l2i) && pei_valid(done_l1i) && spec_l2_index_path_le(start, (done_l2i, done_l1i)) && spec_l2_index_path_le((done_l2i, done_l1i), end) && done_l2i < l2i
                        ==> c.spec_resolve_mapping_4k_l1(l4i, l3i, done_l2i, done_l1i) is None,
            decreases end.0 + 1 - l2i,
        {
            if let Some(l2_entry) = self.get_entry_l2(Tracked(lower), l4i, l3i, l2i, l3_entry) {
                if !self.resolve_4k_l1_range_empty(Tracked(lower), l4i, l3i, l2i, &l2_entry, if l2i == start.0 { start.1 } else { 0 }, if l2i == end.0 { end.1 } else { 511 }) {
                    return false;
                }
            }
            l2i = l2i + 1;
        }
        true
    }

    fn resolve_4k_l3_range_empty(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, l4i: L4Index, l4_entry: &PageEntry, start: (L3Index, L2Index, L1Index),
        end: (L3Index, L2Index, L1Index)) -> (ret: bool)
        requires
            (PageTableC { higher: *self, lower: *lower }).wf(),
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
            ret == (PageTableC { higher: *self, lower: *lower }).spec_resolve_4k_l3_range_empty(l4i, start, end),
    {
        let ghost c = PageTableC { higher: *self, lower: *lower };
        let mut l3i = start.0;
        while l3i <= end.0
            invariant
                c == (PageTableC { higher: *self, lower: *lower }),
                c.wf(),
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
                    #![trigger c.spec_resolve_mapping_4k_l1(l4i, done_l3i, done_l2i, done_l1i)]
                    pei_valid(done_l3i) && pei_valid(done_l2i) && pei_valid(done_l1i) && spec_l3_index_path_le(start, (done_l3i, done_l2i, done_l1i))
                        && spec_l3_index_path_le((done_l3i, done_l2i, done_l1i), end) && done_l3i < l3i ==> c.spec_resolve_mapping_4k_l1(l4i, done_l3i, done_l2i, done_l1i) is None,
            decreases end.0 + 1 - l3i,
        {
            if let Some(l3_entry) = self.get_entry_l3(l4i, l3i, l4_entry) {
                if !self.resolve_4k_l2_range_empty(Tracked(lower), l4i, l3i, &l3_entry, if l3i == start.0 { (start.1, start.2) } else { (0, 0) }, if l3i == end.0 { (end.1, end.2) } else { (511, 511) }) {
                    return false;
                }
            }
            l3i = l3i + 1;
        }
        true
    }

    fn resolve_4k_range_empty(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, start: (L4Index, L3Index, L2Index, L1Index), end: (L4Index, L3Index, L2Index, L1Index)) -> (ret: bool)
        requires
            (PageTableC { higher: *self, lower: *lower }).wf(),
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
            ret == (PageTableC { higher: *self, lower: *lower }).spec_resolve_4k_range_empty(start, end),
    {
        let ghost c = PageTableC { higher: *self, lower: *lower };
        let mut l4i = start.0;
        while l4i <= end.0
            invariant
                c == (PageTableC { higher: *self, lower: *lower }),
                c.wf(),
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
                    #![trigger c.spec_resolve_mapping_4k_l1(done_l4i, done_l3i, done_l2i, done_l1i)]
                    pei_valid(done_l4i) && pei_valid(done_l3i) && pei_valid(done_l2i) && pei_valid(done_l1i) && spec_l4_index_path_le(start, (done_l4i, done_l3i, done_l2i, done_l1i))
                        && spec_l4_index_path_le((done_l4i, done_l3i, done_l2i, done_l1i), end) && done_l4i < l4i ==> c.spec_resolve_mapping_4k_l1(done_l4i, done_l3i, done_l2i, done_l1i) is None,
            decreases end.0 + 1 - l4i,
        {
            if let Some(l4_entry) = self.get_entry_l4(l4i) {
                if !self.resolve_4k_l3_range_empty(Tracked(lower), l4i, &l4_entry, if l4i == start.0 { (start.1, start.2, start.3) } else { (0, 0, 0) },
                    if l4i == end.0 { (end.1, end.2, end.3) } else { (511, 511, 511) }) {
                    return false;
                }
            }
            l4i = l4i + 1;
        }
        true
    }

    /// Check whether the abstract 4K mapping is empty between two inclusive page-table index boundaries. Missing
    /// directory levels and huge-page entries skip their complete 4K subtrees.
    pub fn mapping_4k_range_empty(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, start: (L4Index, L3Index, L2Index, L1Index), end: (L4Index, L3Index, L2Index, L1Index))
        -> (ret: bool)
        requires
            (PageTableC { higher: *self, lower: *lower }).wf(),
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
            ret == (PageTableC { higher: *self, lower: *lower }).spec_mapping_4k_range_empty(start, end),
    {
        let ret = self.resolve_4k_range_empty(Tracked(lower), start, end);
        proof { (PageTableC { higher: *self, lower: *lower }).mapping_4k_range_empty_from_resolve(start, end); }
        ret
    }

    /// The first 4K leaf under one fixed L4/L3/L2 path at or after `start_l1i`; `start_l1i == 512` scans nothing.
    fn next_resolved_4k_l1_from(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, l4i: L4Index, l3i: L3Index, l2i: L2Index, l2_entry: &PageEntry, start_l1i: L1Index)
        -> (ret: Option<L1Index>)
        requires
            (PageTableC { higher: *self, lower: *lower }).wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            start_l1i <= 512,
            (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_l2(l4i, l3i, l2i) =~= Some(*l2_entry),
        ensures
            ret is Some ==> {
                let found = ret->Some_0;
                &&& start_l1i <= found
                &&& pei_valid(found)
                &&& (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, found) is Some
            },
            forall|l1i: L1Index|
                #![trigger (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
                pei_valid(l1i) && start_l1i <= l1i && (ret is None || l1i < ret->Some_0) ==> (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is None,
    {
        let ghost c = PageTableC { higher: *self, lower: *lower };
        let mut l1i = start_l1i;
        while l1i < 512
            invariant
                c == (PageTableC { higher: *self, lower: *lower }),
                c.wf(),
                self.kernel_l4_end <= l4i && pei_valid(l4i),
                pei_valid(l3i),
                pei_valid(l2i),
                start_l1i <= l1i <= 512,
                c.spec_resolve_mapping_l2(l4i, l3i, l2i) =~= Some(*l2_entry),
                forall|done_l1i: L1Index|
                    #![trigger c.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, done_l1i)]
                    start_l1i <= done_l1i < l1i ==> c.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, done_l1i) is None,
            decreases 512 - l1i,
        {
            if self.get_entry_l1(Tracked(lower), l4i, l3i, l2i, l1i, l2_entry).is_some() { return Some(l1i); }
            l1i = l1i + 1;
        }
        None
    }

    /// The first 4K leaf under one fixed L4/L3 path at or after `start` in (L2, L1) order.
    fn next_resolved_4k_l2_from(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, l4i: L4Index, l3i: L3Index, l3_entry: &PageEntry, start: (L2Index, L1Index))
        -> (ret: Option<(L2Index, L1Index)>)
        requires
            (PageTableC { higher: *self, lower: *lower }).wf(),
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
                &&& (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_4k_l1(l4i, l3i, found.0, found.1) is Some
            },
            forall|l2i: L2Index, l1i: L1Index|
                #![trigger (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
                pei_valid(l2i) && pei_valid(l1i) && spec_l2_index_path_le(start, (l2i, l1i)) && (ret is None || !spec_l2_index_path_le(ret->Some_0, (l2i, l1i)))
                    ==> (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is None,
    {
        let ghost c = PageTableC { higher: *self, lower: *lower };
        let mut l2i = start.0;
        while l2i < 512
            invariant
                c == (PageTableC { higher: *self, lower: *lower }),
                c.wf(),
                self.kernel_l4_end <= l4i && pei_valid(l4i),
                pei_valid(l3i),
                pei_valid(start.0),
                start.1 <= 512,
                start.0 <= l2i <= 512,
                self.spec_resolve_mapping_l3(l4i, l3i) =~= Some(*l3_entry),
                forall|done_l2i: L2Index, done_l1i: L1Index|
                    #![trigger c.spec_resolve_mapping_4k_l1(l4i, l3i, done_l2i, done_l1i)]
                    pei_valid(done_l2i) && pei_valid(done_l1i) && spec_l2_index_path_le(start, (done_l2i, done_l1i)) && done_l2i < l2i ==> c.spec_resolve_mapping_4k_l1(l4i, l3i, done_l2i, done_l1i) is None,
            decreases 512 - l2i,
        {
            if let Some(l2_entry) = self.get_entry_l2(Tracked(lower), l4i, l3i, l2i, l3_entry) {
                if let Some(l1i) = self.next_resolved_4k_l1_from(Tracked(lower), l4i, l3i, l2i, &l2_entry, if l2i == start.0 { start.1 } else { 0 }) { return Some((l2i, l1i)); }
            }
            l2i = l2i + 1;
        }
        None
    }

    /// The first 4K leaf under one fixed L4 path at or after `start` in (L3, L2, L1) order.
    fn next_resolved_4k_l3_from(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, l4i: L4Index, l4_entry: &PageEntry, start: (L3Index, L2Index, L1Index))
        -> (ret: Option<(L3Index, L2Index, L1Index)>)
        requires
            (PageTableC { higher: *self, lower: *lower }).wf(),
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
                &&& (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_4k_l1(l4i, found.0, found.1, found.2) is Some
            },
            forall|l3i: L3Index, l2i: L2Index, l1i: L1Index|
                #![trigger (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
                pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l3_index_path_le(start, (l3i, l2i, l1i)) && (ret is None || !spec_l3_index_path_le(ret->Some_0, (l3i, l2i, l1i)))
                    ==> (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is None,
    {
        let ghost c = PageTableC { higher: *self, lower: *lower };
        let mut l3i = start.0;
        while l3i < 512
            invariant
                c == (PageTableC { higher: *self, lower: *lower }),
                c.wf(),
                self.kernel_l4_end <= l4i && pei_valid(l4i),
                pei_valid(start.0),
                pei_valid(start.1),
                start.2 <= 512,
                start.0 <= l3i <= 512,
                self.spec_resolve_mapping_l4(l4i) =~= Some(*l4_entry),
                forall|done_l3i: L3Index, done_l2i: L2Index, done_l1i: L1Index|
                    #![trigger c.spec_resolve_mapping_4k_l1(l4i, done_l3i, done_l2i, done_l1i)]
                    pei_valid(done_l3i) && pei_valid(done_l2i) && pei_valid(done_l1i) && spec_l3_index_path_le(start, (done_l3i, done_l2i, done_l1i)) && done_l3i < l3i
                        ==> c.spec_resolve_mapping_4k_l1(l4i, done_l3i, done_l2i, done_l1i) is None,
            decreases 512 - l3i,
        {
            if let Some(l3_entry) = self.get_entry_l3(l4i, l3i, l4_entry) {
                if let Some(found) = self.next_resolved_4k_l2_from(Tracked(lower), l4i, l3i, &l3_entry, if l3i == start.0 { (start.1, start.2) } else { (0, 0) }) {
                    return Some((l3i, found.0, found.1));
                }
            }
            l3i = l3i + 1;
        }
        None
    }

    /// The first 4K leaf at or after `cursor` in (L4, L3, L2, L1) order.
    fn next_resolved_4k_from(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, cursor: (L4Index, L3Index, L2Index, L1Index)) -> (ret: Option<(L4Index, L3Index, L2Index, L1Index)>)
        requires
            (PageTableC { higher: *self, lower: *lower }).wf(),
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
                &&& (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_4k_l1(found.0, found.1, found.2, found.3) is Some
            },
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
                #![trigger (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
                #![trigger spec_index2va((l4i, l3i, l2i, l1i))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i))
                    && (ret is None || !spec_l4_index_path_le(ret->Some_0, (l4i, l3i, l2i, l1i))) ==> (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is None,
    {
        let ghost c = PageTableC { higher: *self, lower: *lower };
        let mut l4i = cursor.0;
        while l4i < 512
            invariant
                c == (PageTableC { higher: *self, lower: *lower }),
                c.wf(),
                self.kernel_l4_end <= cursor.0 <= l4i <= 512,
                pei_valid(cursor.0),
                pei_valid(cursor.1),
                pei_valid(cursor.2),
                cursor.3 <= 512,
                forall|done_l4i: L4Index, done_l3i: L3Index, done_l2i: L2Index, done_l1i: L1Index|
                    #![trigger c.spec_resolve_mapping_4k_l1(done_l4i, done_l3i, done_l2i, done_l1i)]
                    pei_valid(done_l4i) && pei_valid(done_l3i) && pei_valid(done_l2i) && pei_valid(done_l1i) && spec_l4_index_path_le(cursor, (done_l4i, done_l3i, done_l2i, done_l1i)) && done_l4i < l4i
                        ==> c.spec_resolve_mapping_4k_l1(done_l4i, done_l3i, done_l2i, done_l1i) is None,
            decreases 512 - l4i,
        {
            if let Some(l4_entry) = self.get_entry_l4(l4i) {
                if let Some(found) = self.next_resolved_4k_l3_from(Tracked(lower), l4i, &l4_entry, if l4i == cursor.0 { (cursor.1, cursor.2, cursor.3) } else { (0, 0, 0) }) {
                    return Some((l4i, found.0, found.1, found.2));
                }
            }
            l4i = l4i + 1;
        }
        None
    }

    /// The first 4K mapping at or after `cursor` in (L4, L3, L2, L1) order. `cursor.3 == 512` names the slot just
    /// past `(cursor.0, cursor.1, cursor.2, 511)`, so a caller steps past a found leaf `f` with
    /// `(f.0, f.1, f.2, f.3 + 1)`. Missing directory levels and huge-page entries skip their complete 4K subtrees.
    pub fn next_mapped_4k_from(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, cursor: (L4Index, L3Index, L2Index, L1Index)) -> (ret: Option<(L4Index, L3Index, L2Index, L1Index)>)
        requires
            (PageTableC { higher: *self, lower: *lower }).wf(),
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
                &&& lower.mapping_4k.dom().contains(spec_index2va(found))
            },
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
                #![trigger lower.mapping_4k.dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i))
                    && (ret is None || !spec_l4_index_path_le(ret->Some_0, (l4i, l3i, l2i, l1i))) ==> !lower.mapping_4k.dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
    {
        let ret = self.next_resolved_4k_from(Tracked(lower), cursor);
        proof { (PageTableC { higher: *self, lower: *lower }).next_mapped_4k_from_resolve(cursor, ret); }
        ret
    }
}

impl PageTableHigher<PT_TYPE> {
    /// Every 2M window that covers `range` has its L3 entry linking an L2 page, so each of those windows has a lock.
    pub open spec fn spec_mapping_4k_va_range_windows_exist(&self, range: &VaRange4K) -> bool {
        forall|w: WindowVa| #![trigger va_range_2m_windows(*range).contains(w)] va_range_2m_windows(*range).contains(w) ==> self.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
    }

    /// Check that every 2M window covering `range` has an L2 page. This reads only the L4 and L3 directories of the
    /// big-lock payload, so a big read lock suffices.
    #[verifier(when_used_as_spec(spec_mapping_4k_va_range_windows_exist))]
    pub fn mapping_4k_va_range_windows_exist(&self, range: &VaRange4K) -> (ret: bool)
        requires
            self.inv(),
            range.wf(),
            range.len > 0,
            self.kernel_l4_end <= spec_va2index(range.start).0,
        ensures
            ret == self.spec_mapping_4k_va_range_windows_exist(range),
    {
        let (first_l4i, first_l3i, first_l2i, _) = va2index(range.start);
        let last_va = range.index(range.len - 1);
        let (last_l4i, last_l3i, last_l2i, _) = va2index(last_va);
        proof {
            assert(first_l4i < last_l4i || (first_l4i == last_l4i && (first_l3i < last_l3i || (first_l3i == last_l3i && first_l2i <= last_l2i)))) by {
                range.va_range_lemma(); broadcast use spec_va_4k_valid_index_roundtrip;
                spec_index2va_le_implies_4k_indices_lex_le(spec_va2index(range.start), spec_va2index(last_va));
            };
        }
        let mut l4i = first_l4i;
        let mut l3i = first_l3i;
        while l4i < last_l4i || (l4i == last_l4i && l3i <= last_l3i)
            invariant
                self.inv(),
                range.wf(),
                range.len > 0,
                (first_l4i, first_l3i, first_l2i) == (spec_va2index(range.start).0, spec_va2index(range.start).1, spec_va2index(range.start).2),
                (last_l4i, last_l3i, last_l2i) == (spec_va2index(range.view().spec_index(range.len - 1)).0, spec_va2index(range.view().spec_index(range.len - 1)).1,
                    spec_va2index(range.view().spec_index(range.len - 1)).2),
                KERNEL_MEM_END_L4INDEX <= first_l4i,
                self.kernel_l4_end <= first_l4i,
                pei_valid(last_l4i) && pei_valid(last_l3i) && pei_valid(last_l2i) && pei_valid(first_l3i) && pei_valid(first_l2i),
                first_l4i < last_l4i || (first_l4i == last_l4i && (first_l3i < last_l3i || (first_l3i == last_l3i && first_l2i <= last_l2i))),
                pei_valid(l3i),
                first_l4i < l4i || (first_l4i == l4i && first_l3i <= l3i),
                l4i < last_l4i || (l4i == last_l4i && l3i <= last_l3i) || (l4i == last_l4i + 1 && l3i == 0 && last_l3i == 511) || (l4i == last_l4i && l3i == last_l3i + 1),
                forall|a: L4Index, b: L3Index|
                    #![trigger self.spec_resolve_mapping_l3(a, b)]
                    pei_valid(b) && (first_l4i < a || (first_l4i == a && first_l3i <= b)) && (a < l4i || (a == l4i && b < l3i)) ==> self.spec_resolve_mapping_l3(a, b) is Some,
            decreases (last_l4i * 512 + last_l3i + 1) - (l4i * 512 + l3i),
        {
            let w2 = if l4i == first_l4i && l3i == first_l3i { first_l2i } else { 0 };
            let ghost witness = spec_index2va((l4i, l3i, w2, 0usize));
            proof {
                assert(spec_va_2m_valid(witness)) by (bit_vector) requires witness == spec_index2va((l4i, l3i, w2, 0usize)), KERNEL_MEM_END_L4INDEX <= l4i < 512, l3i < 512, w2 < 512;
                spec_va_4k_index_roundtrip_at(witness, l4i, l3i, w2, 0);
            }
            let l4_entry = self.get_entry_l4(l4i);
            if l4_entry.is_none() {
                proof { assert(va_range_2m_windows(*range).contains(WindowVa { va: witness })); }
                return false;
            }
            let l3_entry = self.get_entry_l3(l4i, l3i, &l4_entry.unwrap());
            if l3_entry.is_none() {
                proof { assert(va_range_2m_windows(*range).contains(WindowVa { va: witness })); }
                return false;
            }
            if l3i < 511 { l3i = l3i + 1; } else { l3i = 0; l4i = l4i + 1; }
        }
        proof { assert(self.spec_mapping_4k_va_range_windows_exist(range)) by { broadcast use spec_va_2m_valid_index_roundtrip; }; }
        true
    }

    /// Check whether every address in a 4K range has a user-present leaf. This scans only the page table and does
    /// not mutate any page-table state.
    pub fn mapping_4k_va_range_present(&self, Tracked(lower): Tracked<&PageTableLower<PT_TYPE>>, range: &VaRange4K) -> (ret: bool)
        requires
            (PageTableC { higher: *self, lower: *lower }).wf(),
            range.wf(),
            self.kernel_l4_end <= spec_va2index(range.start).0,
        ensures
            ret == (PageTableC { higher: *self, lower: *lower }).spec_mapping_4k_va_range_present(range),
            ret == forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < range.len
                ==> lower.mapping_4k.dom().contains(range.view().spec_index(j)) && lower.mapping_4k.spec_index(range.view().spec_index(j)).present,
    {
        let ghost c = PageTableC { higher: *self, lower: *lower };
        let range_start = range.start;
        let range_len = range.len;
        let mut i: usize = 0;
        while i < range_len
            invariant
                c == (PageTableC { higher: *self, lower: *lower }),
                c.wf(),
                range.wf(),
                range_start == range.start,
                range_len == range.len,
                self.kernel_l4_end <= spec_va2index(range.start).0,
                0 <= i <= range_len,
                forall|done: int|
                    #![trigger lower.mapping_4k.dom().contains(range.view().spec_index(done))]
                    #![trigger c.spec_resolve_mapping_4k_l1(spec_va2index(range.view().spec_index(done)).0, spec_va2index(range.view().spec_index(done)).1, spec_va2index(range.view().spec_index(done)).2,
                        spec_va2index(range.view().spec_index(done)).3)]
                    0 <= done < i ==> {
                        let va = range.view().spec_index(done);
                        let indices = spec_va2index(va);
                        &&& c.kernel_l4_end() <= indices.0
                        &&& pei_valid(indices.0)
                        &&& pei_valid(indices.1)
                        &&& pei_valid(indices.2)
                        &&& pei_valid(indices.3)
                        &&& lower.mapping_4k.dom().contains(va)
                        &&& lower.mapping_4k.spec_index(va).present
                        &&& page_ptr_valid(lower.mapping_4k.spec_index(va).addr)
                        &&& {
                            let resolved = c.spec_resolve_mapping_4k_l1(indices.0, indices.1, indices.2, indices.3);
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
            let resolved = self.resolve_mapping_4k_l1(Tracked(lower), l4i, l3i, l2i, l1i);
            if resolved.2.is_none() {
                proof { assert(!lower.mapping_4k.dom().contains(range.view().spec_index(i as int))) by { range.va_range_lemma(); c.wf_mapping_4k_at(l4i, l3i, l2i, l1i); spec_va_4k_index_roundtrip_at(va, l4i, l3i, l2i, l1i); }; }
                return false;
            }
            let entry = resolved.2.unwrap();
            if !entry.present {
                proof {
                    assert(!c.spec_mapping_4k_va_range_present(range)) by { range.va_range_lemma(); assert(spec_index2va((l4i, l3i, l2i, l1i)) == va) by { spec_va_4k_index_roundtrip_at(va, l4i, l3i, l2i, l1i); }; };
                    assert(!lower.mapping_4k.spec_index(range.view().spec_index(i as int)).present) by { range.va_range_lemma(); c.wf_mapping_4k_at(l4i, l3i, l2i, l1i); spec_va_4k_index_roundtrip_at(va, l4i, l3i, l2i, l1i); };
                }
                return false;
            }
            proof {
                assert({
                    let checked_va = range.view().spec_index(i as int);
                    let checked_indices = spec_va2index(checked_va);
                    &&& c.kernel_l4_end() <= checked_indices.0
                    &&& pei_valid(checked_indices.0)
                    &&& pei_valid(checked_indices.1)
                    &&& pei_valid(checked_indices.2)
                    &&& pei_valid(checked_indices.3)
                    &&& lower.mapping_4k.dom().contains(checked_va)
                    &&& lower.mapping_4k.spec_index(checked_va).present
                    &&& page_ptr_valid(lower.mapping_4k.spec_index(checked_va).addr)
                    &&& {
                        let spec_resolved = c.spec_resolve_mapping_4k_l1(checked_indices.0, checked_indices.1, checked_indices.2, checked_indices.3);
                        &&& spec_resolved is Some
                        &&& spec_resolved->0.perm.kernel_present
                        &&& spec_resolved->0.perm.present
                    }
                }) by { range.va_range_lemma(); assert(spec_index2va((l4i, l3i, l2i, l1i)) == va) by { spec_va_4k_index_roundtrip_at(va, l4i, l3i, l2i, l1i); }; c.wf_mapping_4k_at(l4i, l3i, l2i, l1i); };
            }
            i = i + 1;
        }
        true
    }

    pub fn mapping_4k_va_range_buildable(&self, Tracked(lower): Tracked<&PageTableLower<PT_TYPE>>, range: &VaRange4K) -> (ret: bool)
        requires
            (PageTableC { higher: *self, lower: *lower }).wf(),
            range.wf(),
            range.len > 0,
            self.kernel_l4_end <= spec_va2index(range.start).0,
        ensures
            ret == (PageTableC { higher: *self, lower: *lower }).spec_mapping_4k_va_range_buildable(range),
            ret == forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < range.len ==> {
                let indices = spec_va2index(range.view().spec_index(j));
                &&& !self.mapping_1g.view().dom().contains(spec_index2va((indices.0, indices.1, 0, 0)))
                &&& !lower.mapping_2m.dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0)))
                &&& !lower.mapping_4k.dom().contains(range.view().spec_index(j))
            },
    {
        let ghost c = PageTableC { higher: *self, lower: *lower };
        let range_start = range.start;
        let range_len = range.len;
        let mut i: usize = 0;
        while i < range.len
            invariant
                c == (PageTableC { higher: *self, lower: *lower }),
                c.wf(),
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
                        &&& !self.mapping_1g.view().dom().contains(spec_index2va((indices.0, indices.1, 0, 0)))
                        &&& !lower.mapping_2m.dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0)))
                        &&& !lower.mapping_4k.dom().contains(range.view().spec_index(j))
                    },
                forall|j: int|
                    #![trigger c.spec_resolve_mapping_4k_l1(spec_va2index(range.view().spec_index(j)).0, spec_va2index(range.view().spec_index(j)).1, spec_va2index(range.view().spec_index(j)).2,
                        spec_va2index(range.view().spec_index(j)).3)]
                    0 <= j < i ==> {
                        let indices = spec_va2index(range.view().spec_index(j));
                        c.spec_4k_entry_usable(indices.0, indices.1, indices.2, indices.3)
                    },
            decreases range.len - i,
        {
            let va = va_add_range(range_start, i);
            proof { assert(va_4k_valid(va)) by { range.va_range_lemma(); }; }
            let (l4i, l3i, l2i, l1i) = va2index(va);
            proof { assert(self.kernel_l4_end <= l4i) by { assert(spec_va_4k_valid(range_start) && spec_va_4k_valid(va) && range_start <= va) by { range.va_range_lemma(); }; spec_v2l4index_monotonic(range_start, va); }; }
            let resolved = self.resolve_mapping_4k_l1(Tracked(lower), l4i, l3i, l2i, l1i);
            match resolved.1 {
                PageTableErrorCode::NoError | PageTableErrorCode::EntryTakenBy4k | PageTableErrorCode::EntryTakenBy1g | PageTableErrorCode::EntryTakenBy2m => {
                    proof {
                        assert(!c.spec_4k_entry_usable(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2, spec_va2index(va).3)) by { spec_va_4k_valid_imply_indices_valid(); };
                        assert(!c.spec_mapping_4k_va_range_buildable(range)) by { range.va_range_lemma(); };
                        assert({
                            let indices = spec_va2index(range.view().spec_index(i as int));
                            ||| self.mapping_1g.view().dom().contains(spec_index2va((indices.0, indices.1, 0, 0)))
                            ||| lower.mapping_2m.dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0)))
                            ||| lower.mapping_4k.dom().contains(range.view().spec_index(i as int))
                        }) by {
                            range.va_range_lemma(); spec_va_4k_valid_imply_indices_valid(); spec_va_4k_index_roundtrip_at(va, l4i, l3i, l2i, l1i);
                            self.wf_mapping_1g_at(l4i, l3i); c.wf_mapping_2m_at(l4i, l3i, l2i); c.wf_mapping_4k_at(l4i, l3i, l2i, l1i);
                        };
                    }
                    return false;
                },
                PageTableErrorCode::L4EntryNotExist | PageTableErrorCode::L3EntryNotExist | PageTableErrorCode::L2EntryNotExist | PageTableErrorCode::L1EntryNotExist => {},
            }
            proof {
                assert(c.spec_4k_entry_usable(l4i, l3i, l2i, l1i)) by { spec_va_4k_valid_imply_indices_valid(); };
                assert({
                    let checked_indices = spec_va2index(range.view().spec_index(i as int));
                    &&& self.kernel_l4_end <= checked_indices.0
                    &&& pei_valid(checked_indices.0)
                    &&& pei_valid(checked_indices.1)
                    &&& pei_valid(checked_indices.2)
                    &&& pei_valid(checked_indices.3)
                    &&& c.spec_4k_entry_usable(checked_indices.0, checked_indices.1, checked_indices.2, checked_indices.3)
                    &&& !self.mapping_1g.view().dom().contains(spec_index2va((checked_indices.0, checked_indices.1, 0, 0)))
                    &&& !lower.mapping_2m.dom().contains(spec_index2va((checked_indices.0, checked_indices.1, checked_indices.2, 0)))
                    &&& !lower.mapping_4k.dom().contains(range.view().spec_index(i as int))
                }) by {
                    range.va_range_lemma();
                    assert(spec_index2va((l4i, l3i, l2i, l1i)) == va) by { spec_va_4k_index_roundtrip_at(va, l4i, l3i, l2i, l1i); };
                    self.wf_mapping_1g_at(l4i, l3i); c.wf_mapping_2m_at(l4i, l3i, l2i); c.wf_mapping_4k_at(l4i, l3i, l2i, l1i);
                };
            }
            i = i + 1;
        }
        true
    }
}

/// Every 4K index between the first and last page of `range` lies in a covering 2M window, whose base has that index's L4, L3,
/// and L2 indices and a zero L1 index.
pub proof fn va_range_2m_windows_contains_window_of_every_va_in_range(range: VaRange4K)
    requires range.wf(), range.len > 0,
    ensures
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger spec_index2va((l4i, l3i, l2i, l1i))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l4_index_path_le(spec_va2index(range.start), (l4i, l3i, l2i, l1i))
                && spec_l4_index_path_le((l4i, l3i, l2i, l1i), spec_va2index(range.view()[range.len - 1])) ==> {
                let w = WindowVa { va: spec_index2va((l4i, l3i, l2i, 0usize)) };
                &&& spec_va2index(w.va) == (l4i, l3i, l2i, 0usize)
                &&& va_range_2m_windows(range).contains(w)
            },
{ broadcast use spec_va_4k_valid_index_roundtrip, spec_va_4k_index_roundtrip_at, spec_index2va_2m_valid; }

/// Each of the first `n` pages of `range` lies in a 2M window of the range at the page's own L4, L3 and L2 indices.
pub proof fn va_range_2m_windows_contains_window_of_first_n_pages(range: VaRange4K, n: int)
    requires range.wf(), range.len > 0, 0 <= n <= range.len,
    ensures
        forall|j: int| #![trigger range.view()[j]] 0 <= j < n ==> {
            &&& va_range_2m_windows(range).contains(window_of(range.view()[j]))
            &&& spec_va2index(window_of(range.view()[j]).va) == (spec_v2l4index(range.view()[j]), spec_v2l3index(range.view()[j]), spec_v2l2index(range.view()[j]), 0usize)
        },
    decreases n,
{
    if n > 0 {
        va_range_2m_windows_contains_window_of_first_n_pages(range, n - 1);
        let va = range.view()[n - 1];
        let last_va = range.view()[range.len - 1];
        range.va_range_lemma();
        broadcast use spec_va_4k_valid_index_roundtrip;
        spec_index2va_le_implies_4k_indices_lex_le(spec_va2index(range.start), spec_va2index(va));
        spec_index2va_le_implies_4k_indices_lex_le(spec_va2index(va), spec_va2index(last_va));
        va_range_2m_windows_contains_window_of_every_va_in_range(range);
    }
}
} // verus!
