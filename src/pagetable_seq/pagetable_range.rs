use vstd::prelude::*;

verus! {

use super::entry::*;
use super::pagetable_spec::*;
use crate::define::*;
use crate::util::page_ptr_util_u::*;

pub open spec fn spec_l2_index_path_le(
    lhs: (L2Index, L1Index),
    rhs: (L2Index, L1Index),
) -> bool {
    lhs.0 < rhs.0 || (lhs.0 == rhs.0 && lhs.1 <= rhs.1)
}

pub open spec fn spec_l3_index_path_le(
    lhs: (L3Index, L2Index, L1Index),
    rhs: (L3Index, L2Index, L1Index),
) -> bool {
    lhs.0 < rhs.0
        || (lhs.0 == rhs.0 && spec_l2_index_path_le((lhs.1, lhs.2), (rhs.1, rhs.2)))
}

pub open spec fn spec_l4_index_path_le(
    lhs: (L4Index, L3Index, L2Index, L1Index),
    rhs: (L4Index, L3Index, L2Index, L1Index),
) -> bool {
    lhs.0 < rhs.0
        || (lhs.0 == rhs.0
            && spec_l3_index_path_le(
                (lhs.1, lhs.2, lhs.3),
                (rhs.1, rhs.2, rhs.3),
            ))
}

impl<const TABLE_TYPE: PTType> PageTable<TABLE_TYPE> {
    /// No abstract 4K mapping exists in the inclusive L1 interval under one
    /// fixed L4/L3/L2 path.
    pub open spec fn spec_mapping_4k_l1_range_empty(
        &self,
        l4i: L4Index,
        l3i: L3Index,
        l2i: L2Index,
        start_l1i: L1Index,
        end_l1i: L1Index,
    ) -> bool {
        forall|l1i: L1Index|
            #![trigger self.mapping_4k().dom().contains(
                spec_index2va((l4i, l3i, l2i, l1i)),
            )]
            start_l1i <= l1i <= end_l1i
                ==> !self.mapping_4k().dom().contains(
                    spec_index2va((l4i, l3i, l2i, l1i)),
                )
    }

    /// No abstract 4K mapping exists in the inclusive (L2, L1) interval
    /// under one fixed L4/L3 path.
    pub open spec fn spec_mapping_4k_l2_range_empty(
        &self,
        l4i: L4Index,
        l3i: L3Index,
        start: (L2Index, L1Index),
        end: (L2Index, L1Index),
    ) -> bool {
        forall|l2i: L2Index, l1i: L1Index|
            #![trigger self.mapping_4k().dom().contains(
                spec_index2va((l4i, l3i, l2i, l1i)),
            )]
            pei_valid(l2i) && pei_valid(l1i)
                && spec_l2_index_path_le(start, (l2i, l1i))
                && spec_l2_index_path_le((l2i, l1i), end)
                ==> !self.mapping_4k().dom().contains(
                    spec_index2va((l4i, l3i, l2i, l1i)),
                )
    }

    /// No abstract 4K mapping exists in the inclusive (L3, L2, L1)
    /// interval under one fixed L4 path.
    pub open spec fn spec_mapping_4k_l3_range_empty(
        &self,
        l4i: L4Index,
        start: (L3Index, L2Index, L1Index),
        end: (L3Index, L2Index, L1Index),
    ) -> bool {
        forall|l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger self.mapping_4k().dom().contains(
                spec_index2va((l4i, l3i, l2i, l1i)),
            )]
            pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                && spec_l3_index_path_le(start, (l3i, l2i, l1i))
                && spec_l3_index_path_le((l3i, l2i, l1i), end)
                ==> !self.mapping_4k().dom().contains(
                    spec_index2va((l4i, l3i, l2i, l1i)),
                )
    }

    /// No abstract 4K mapping exists between two inclusive four-level index
    /// boundaries. The tuple order is (L4, L3, L2, L1).
    pub open spec fn spec_mapping_4k_range_empty(
        &self,
        start: (L4Index, L3Index, L2Index, L1Index),
        end: (L4Index, L3Index, L2Index, L1Index),
    ) -> bool {
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger self.mapping_4k().dom().contains(
                spec_index2va((l4i, l3i, l2i, l1i)),
            )]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                && spec_l4_index_path_le(start, (l4i, l3i, l2i, l1i))
                && spec_l4_index_path_le((l4i, l3i, l2i, l1i), end)
                ==> !self.mapping_4k().dom().contains(
                    spec_index2va((l4i, l3i, l2i, l1i)),
                )
    }

    #[verifier::opaque]
    pub open spec fn spec_mapping_4k_va_range_empty(
        &self,
        start_va: VAddr,
        end_va: VAddr,
    ) -> bool {
        forall|va: VAddr|
            #![trigger self.mapping_4k().dom().contains(va)]
            spec_va_4k_valid(va) && start_va <= va <= end_va
                ==> !self.mapping_4k().dom().contains(va)
    }

    pub broadcast proof fn mapping_4k_index_range_empty_implies_va_empty_at(
        &self,
        start_l4i: L4Index,
        start_l3i: L3Index,
        start_l2i: L2Index,
        start_l1i: L1Index,
        end_l4i: L4Index,
        end_l3i: L3Index,
        end_l2i: L2Index,
        end_l1i: L1Index,
        va: VAddr,
    )
        requires
            pei_valid(start_l4i),
            pei_valid(start_l3i),
            pei_valid(start_l2i),
            pei_valid(start_l1i),
            pei_valid(end_l4i),
            pei_valid(end_l3i),
            pei_valid(end_l2i),
            pei_valid(end_l1i),
            self.spec_mapping_4k_range_empty(
                (start_l4i, start_l3i, start_l2i, start_l1i),
                (end_l4i, end_l3i, end_l2i, end_l1i),
            ),
            spec_va_4k_valid(va),
            spec_index2va((start_l4i, start_l3i, start_l2i, start_l1i)) <= va,
            va <= spec_index2va((end_l4i, end_l3i, end_l2i, end_l1i)),
        ensures
            #![trigger
                self.mapping_4k().dom().contains(va),
                spec_index2va((start_l4i, start_l3i, start_l2i, start_l1i)),
                spec_index2va((end_l4i, end_l3i, end_l2i, end_l1i)),
            ]
            !self.mapping_4k().dom().contains(va),
    {
        let va_l4i = spec_v2l4index(va);
        let va_l3i = spec_v2l3index(va);
        let va_l2i = spec_v2l2index(va);
        let va_l1i = spec_v2l1index(va);
        assert(
            pei_valid(va_l4i)
                && pei_valid(va_l3i)
                && pei_valid(va_l2i)
                && pei_valid(va_l1i)
        ) by {
            spec_va_4k_valid_imply_indices_valid();
        };
        assert(spec_index2va(spec_va2index(va)) == va) by {
            spec_va_4k_index_roundtrip();
        };
        assert(
            start_l4i < va_l4i
                || (start_l4i == va_l4i
                    && (start_l3i < va_l3i
                        || (start_l3i == va_l3i
                            && (start_l2i < va_l2i
                                || (start_l2i == va_l2i && start_l1i <= va_l1i)))))
        ) by (bit_vector)
            requires
                pei_valid(start_l4i),
                pei_valid(start_l3i),
                pei_valid(start_l2i),
                pei_valid(start_l1i),
                pei_valid(va_l4i),
                pei_valid(va_l3i),
                pei_valid(va_l2i),
                pei_valid(va_l1i),
                spec_index2va((start_l4i, start_l3i, start_l2i, start_l1i))
                    <= spec_index2va((va_l4i, va_l3i, va_l2i, va_l1i)),
        ;
        assert(
            va_l4i < end_l4i
                || (va_l4i == end_l4i
                    && (va_l3i < end_l3i
                        || (va_l3i == end_l3i
                            && (va_l2i < end_l2i
                                || (va_l2i == end_l2i && va_l1i <= end_l1i)))))
        ) by (bit_vector)
            requires
                pei_valid(va_l4i),
                pei_valid(va_l3i),
                pei_valid(va_l2i),
                pei_valid(va_l1i),
                pei_valid(end_l4i),
                pei_valid(end_l3i),
                pei_valid(end_l2i),
                pei_valid(end_l1i),
                spec_index2va((va_l4i, va_l3i, va_l2i, va_l1i))
                    <= spec_index2va((end_l4i, end_l3i, end_l2i, end_l1i)),
        ;
    }

    pub fn mapping_4k_va_range_empty(
        &self,
        start_va: VAddr,
        end_va: VAddr,
    ) -> (ret: bool)
        requires
            self.wf(),
            va_4k_valid(start_va),
            va_4k_valid(end_va),
            start_va <= end_va,
            self.kernel_l4_end <= spec_va2index(start_va).0,
        ensures
            ret == self.spec_mapping_4k_range_empty(
                spec_va2index(start_va),
                spec_va2index(end_va),
            ),
            ret ==> self.spec_mapping_4k_va_range_empty(start_va, end_va),
    {
        let start = va2index(start_va);
        let end = va2index(end_va);
        proof {
            assert(spec_index2va(start) == start_va) by {
                spec_va_4k_index_roundtrip();
            };
            assert(spec_index2va(end) == end_va) by {
                spec_va_4k_index_roundtrip();
            };
        }
        assert(
            spec_v2l4index(start_va) < spec_v2l4index(end_va)
                || (spec_v2l4index(start_va) == spec_v2l4index(end_va)
                    && (spec_v2l3index(start_va) < spec_v2l3index(end_va)
                        || (spec_v2l3index(start_va) == spec_v2l3index(end_va)
                            && (spec_v2l2index(start_va) < spec_v2l2index(end_va)
                                || (spec_v2l2index(start_va) == spec_v2l2index(end_va)
                                    && spec_v2l1index(start_va) <= spec_v2l1index(end_va))))))
        ) by (bit_vector)
            requires
                spec_va_4k_valid(start_va),
                spec_va_4k_valid(end_va),
                start_va <= end_va,
        ;
        let ret = self.mapping_4k_range_empty(start, end);
        if ret {
            assert(self.spec_mapping_4k_va_range_empty(start_va, end_va)) by {
                reveal(PageTable::spec_mapping_4k_va_range_empty);
                broadcast use PageTable::mapping_4k_index_range_empty_implies_va_empty_at;
            };
        }
        ret
    }

    fn mapping_4k_l1_range_empty(
        &self,
        l4i: L4Index,
        l3i: L3Index,
        l2i: L2Index,
        l2_entry: &PageEntry,
        start_l1i: L1Index,
        end_l1i: L1Index,
    ) -> (ret: bool)
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
            ret == self.spec_mapping_4k_l1_range_empty(
                l4i, l3i, l2i, start_l1i, end_l1i,
            ),
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
                forall|done_l1i: L1Index|
                    #![trigger self.mapping_4k().dom().contains(
                        spec_index2va((l4i, l3i, l2i, done_l1i)),
                    )]
                    start_l1i <= done_l1i < l1i
                        ==> !self.mapping_4k().dom().contains(
                            spec_index2va((l4i, l3i, l2i, done_l1i)),
                        ),
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

    fn mapping_4k_l2_range_empty(
        &self,
        l4i: L4Index,
        l3i: L3Index,
        l3_entry: &PageEntry,
        start: (L2Index, L1Index),
        end: (L2Index, L1Index),
    ) -> (ret: bool)
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
                    #![trigger self.mapping_4k().dom().contains(
                        spec_index2va((l4i, l3i, done_l2i, done_l1i)),
                    )]
                    pei_valid(done_l2i)
                        && pei_valid(done_l1i)
                        && spec_l2_index_path_le(start, (done_l2i, done_l1i))
                        && spec_l2_index_path_le((done_l2i, done_l1i), end)
                        && done_l2i < l2i
                        ==> !self.mapping_4k().dom().contains(
                            spec_index2va((l4i, l3i, done_l2i, done_l1i)),
                        ),
            decreases end.0 + 1 - l2i,
        {
            let l2_entry = self.get_entry_l2(l4i, l3i, l2i, l3_entry);
            if let Some(l2_entry) = l2_entry {
                if !self.mapping_4k_l1_range_empty(
                    l4i,
                    l3i,
                    l2i,
                    &l2_entry,
                    if l2i == start.0 { start.1 } else { 0 },
                    if l2i == end.0 { end.1 } else { 511 },
                ) {
                    return false;
                }
            }
            l2i = l2i + 1;
        }
        true
    }

    fn mapping_4k_l3_range_empty(
        &self,
        l4i: L4Index,
        l4_entry: &PageEntry,
        start: (L3Index, L2Index, L1Index),
        end: (L3Index, L2Index, L1Index),
    ) -> (ret: bool)
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
                    #![trigger self.mapping_4k().dom().contains(
                        spec_index2va((l4i, done_l3i, done_l2i, done_l1i)),
                    )]
                    pei_valid(done_l3i)
                        && pei_valid(done_l2i)
                        && pei_valid(done_l1i)
                        && spec_l3_index_path_le(start, (done_l3i, done_l2i, done_l1i))
                        && spec_l3_index_path_le((done_l3i, done_l2i, done_l1i), end)
                        && done_l3i < l3i
                        ==> !self.mapping_4k().dom().contains(
                            spec_index2va((l4i, done_l3i, done_l2i, done_l1i)),
                        ),
            decreases end.0 + 1 - l3i,
        {
            let l3_entry = self.get_entry_l3(l4i, l3i, l4_entry);
            if let Some(l3_entry) = l3_entry {
                if !self.mapping_4k_l2_range_empty(
                    l4i,
                    l3i,
                    &l3_entry,
                    if l3i == start.0 {
                        (start.1, start.2)
                    } else {
                        (0, 0)
                    },
                    if l3i == end.0 {
                        (end.1, end.2)
                    } else {
                        (511, 511)
                    },
                ) {
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
    pub fn mapping_4k_range_empty(
        &self,
        start: (L4Index, L3Index, L2Index, L1Index),
        end: (L4Index, L3Index, L2Index, L1Index),
    ) -> (ret: bool)
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
                    #![trigger self.mapping_4k().dom().contains(
                        spec_index2va((done_l4i, done_l3i, done_l2i, done_l1i)),
                    )]
                    pei_valid(done_l4i)
                        && pei_valid(done_l3i)
                        && pei_valid(done_l2i)
                        && pei_valid(done_l1i)
                        && spec_l4_index_path_le(
                            start,
                            (done_l4i, done_l3i, done_l2i, done_l1i),
                        )
                        && spec_l4_index_path_le(
                            (done_l4i, done_l3i, done_l2i, done_l1i),
                            end,
                        )
                        && done_l4i < l4i
                        ==> !self.mapping_4k().dom().contains(
                            spec_index2va((done_l4i, done_l3i, done_l2i, done_l1i)),
                        ),
            decreases end.0 + 1 - l4i,
        {
            let l4_entry = self.get_entry_l4(l4i);
            if let Some(l4_entry) = l4_entry {
                if !self.mapping_4k_l3_range_empty(
                    l4i,
                    &l4_entry,
                    if l4i == start.0 {
                        (start.1, start.2, start.3)
                    } else {
                        (0, 0, 0)
                    },
                    if l4i == end.0 {
                        (end.1, end.2, end.3)
                    } else {
                        (511, 511, 511)
                    },
                ) {
                    return false;
                }
            }
            l4i = l4i + 1;
        }
        true
    }
}

} // verus!
