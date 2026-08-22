use vstd::prelude::*;

verus! {

use super::entry::*;
use super::pagetable_spec::*;
use crate::define::*;
use crate::util::page_ptr_util_u::*;

pub open spec fn spec_l3_structure_path_le(
    lhs: (L3Index, L2Index),
    rhs: (L3Index, L2Index),
) -> bool {
    lhs.0 < rhs.0 || (lhs.0 == rhs.0 && lhs.1 <= rhs.1)
}

pub open spec fn spec_l4_structure_path_le(
    lhs: (L4Index, L3Index, L2Index),
    rhs: (L4Index, L3Index, L2Index),
) -> bool {
    lhs.0 < rhs.0
        || (lhs.0 == rhs.0
            && spec_l3_structure_path_le((lhs.1, lhs.2), (rhs.1, rhs.2)))
}

impl<const TABLE_TYPE: PTType> PageTable<TABLE_TYPE> {
    pub open spec fn spec_l2_structure_range_present(
        &self,
        l4i: L4Index,
        l3i: L3Index,
        start_l2i: L2Index,
        end_l2i: L2Index,
    ) -> bool {
        forall|l2i: L2Index|
            #![trigger self.spec_resolve_mapping_l2(l4i, l3i, l2i)]
            start_l2i <= l2i <= end_l2i
                ==> self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
    }

    pub open spec fn spec_l3_structure_range_present(
        &self,
        l4i: L4Index,
        start: (L3Index, L2Index),
        end: (L3Index, L2Index),
    ) -> bool {
        forall|l3i: L3Index, l2i: L2Index|
            #![trigger self.spec_resolve_mapping_l2(l4i, l3i, l2i)]
            pei_valid(l3i) && pei_valid(l2i)
                && spec_l3_structure_path_le(start, (l3i, l2i))
                && spec_l3_structure_path_le((l3i, l2i), end)
                ==> self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
    }

    pub open spec fn spec_structure_range_present(
        &self,
        start: (L4Index, L3Index, L2Index),
        end: (L4Index, L3Index, L2Index),
    ) -> bool {
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger self.spec_resolve_mapping_l2(l4i, l3i, l2i)]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                && spec_l4_structure_path_le(start, (l4i, l3i, l2i))
                && spec_l4_structure_path_le((l4i, l3i, l2i), end)
                ==> self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
    }

    #[verifier::opaque]
    pub open spec fn spec_va_range_structure_present(
        &self,
        start_va: VAddr,
        end_va: VAddr,
    ) -> bool {
        forall|va: VAddr|
            #![trigger self.spec_resolve_mapping_l2(
                spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va),
            )]
            spec_va_4k_valid(va) && start_va <= va <= end_va
                ==> {
                    let indices = spec_va2index(va);
                    &&& self.kernel_l4_end <= indices.0
                    &&& pei_valid(indices.0)
                    &&& pei_valid(indices.1)
                    &&& pei_valid(indices.2)
                    &&& pei_valid(indices.3)
                    &&& self.spec_resolve_mapping_l2(
                        indices.0, indices.1, indices.2,
                    ) is Some
                }
    }

    pub broadcast proof fn structure_index_range_present_implies_va_present_at(
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
            self.wf(),
            self.kernel_l4_end <= start_l4i,
            pei_valid(start_l4i),
            pei_valid(start_l3i),
            pei_valid(start_l2i),
            pei_valid(start_l1i),
            pei_valid(end_l4i),
            pei_valid(end_l3i),
            pei_valid(end_l2i),
            pei_valid(end_l1i),
            self.spec_structure_range_present(
                (start_l4i, start_l3i, start_l2i),
                (end_l4i, end_l3i, end_l2i),
            ),
            spec_va_4k_valid(va),
            spec_index2va((start_l4i, start_l3i, start_l2i, start_l1i)) <= va,
            va <= spec_index2va((end_l4i, end_l3i, end_l2i, end_l1i)),
        ensures
            #![trigger
                self.spec_resolve_mapping_l2(
                    spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va),
                ),
                spec_index2va((start_l4i, start_l3i, start_l2i, start_l1i)),
                spec_index2va((end_l4i, end_l3i, end_l2i, end_l1i)),
            ]
            {
                let indices = spec_va2index(va);
                &&& self.kernel_l4_end <= indices.0
                &&& pei_valid(indices.0)
                &&& pei_valid(indices.1)
                &&& pei_valid(indices.2)
                &&& pei_valid(indices.3)
                &&& self.spec_resolve_mapping_l2(
                    indices.0, indices.1, indices.2,
                ) is Some
            },
    {
        let va_l4i = spec_v2l4index(va);
        let va_l3i = spec_v2l3index(va);
        let va_l2i = spec_v2l2index(va);
        let va_l1i = spec_v2l1index(va);
        assert(
            pei_valid(va_l4i) && pei_valid(va_l3i)
                && pei_valid(va_l2i) && pei_valid(va_l1i)
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
                        || (start_l3i == va_l3i && start_l2i <= va_l2i)))
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
                        || (va_l3i == end_l3i && va_l2i <= end_l2i)))
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

    pub fn va_range_structure_present(
        &self,
        start_va: VAddr,
        end_va: VAddr,
    ) -> (ret: bool)
        requires
            self.wf(),
            va_4k_valid(start_va),
            va_4k_valid(end_va),
            start_va <= end_va,
            self.kernel_l4_end <= spec_v2l4index(start_va),
        ensures
            ret == self.spec_structure_range_present(
                (
                    spec_v2l4index(start_va),
                    spec_v2l3index(start_va),
                    spec_v2l2index(start_va),
                ),
                (
                    spec_v2l4index(end_va),
                    spec_v2l3index(end_va),
                    spec_v2l2index(end_va),
                ),
            ),
            ret ==> self.spec_va_range_structure_present(start_va, end_va),
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
                            && spec_v2l2index(start_va) <= spec_v2l2index(end_va))))
        ) by (bit_vector)
            requires
                spec_va_4k_valid(start_va),
                spec_va_4k_valid(end_va),
                start_va <= end_va,
        ;
        let ret = self.structure_range_present(
            (start.0, start.1, start.2),
            (end.0, end.1, end.2),
        );
        if ret {
            assert(self.spec_va_range_structure_present(start_va, end_va)) by {
                reveal(PageTable::spec_va_range_structure_present);
                broadcast use PageTable::structure_index_range_present_implies_va_present_at;
            };
        }
        ret
    }

    fn l2_structure_range_present(
        &self,
        l4i: L4Index,
        l3i: L3Index,
        l3_entry: &PageEntry,
        start_l2i: L2Index,
        end_l2i: L2Index,
    ) -> (ret: bool)
        requires
            self.wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(start_l2i),
            pei_valid(end_l2i),
            start_l2i <= end_l2i,
            self.spec_resolve_mapping_l3(l4i, l3i) =~= Some(*l3_entry),
        ensures
            ret == self.spec_l2_structure_range_present(
                l4i, l3i, start_l2i, end_l2i,
            ),
    {
        let mut l2i = start_l2i;
        while l2i <= end_l2i
            invariant
                self.wf(),
                self.kernel_l4_end <= l4i && pei_valid(l4i),
                pei_valid(l3i),
                pei_valid(start_l2i),
                pei_valid(end_l2i),
                start_l2i <= l2i <= end_l2i + 1,
                self.spec_resolve_mapping_l3(l4i, l3i) =~= Some(*l3_entry),
                forall|done_l2i: L2Index|
                    #![trigger self.spec_resolve_mapping_l2(l4i, l3i, done_l2i)]
                    start_l2i <= done_l2i < l2i
                        ==> self.spec_resolve_mapping_l2(
                            l4i, l3i, done_l2i,
                        ) is Some,
            decreases end_l2i + 1 - l2i,
        {
            if self.get_entry_l2(l4i, l3i, l2i, l3_entry).is_none() {
                return false;
            }
            l2i = l2i + 1;
        }
        true
    }

    fn l3_structure_range_present(
        &self,
        l4i: L4Index,
        l4_entry: &PageEntry,
        start: (L3Index, L2Index),
        end: (L3Index, L2Index),
    ) -> (ret: bool)
        requires
            self.wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(start.0),
            pei_valid(start.1),
            pei_valid(end.0),
            pei_valid(end.1),
            spec_l3_structure_path_le(start, end),
            self.spec_resolve_mapping_l4(l4i) =~= Some(*l4_entry),
        ensures
            ret == self.spec_l3_structure_range_present(l4i, start, end),
    {
        let mut l3i = start.0;
        while l3i <= end.0
            invariant
                self.wf(),
                self.kernel_l4_end <= l4i && pei_valid(l4i),
                pei_valid(start.0),
                pei_valid(start.1),
                pei_valid(end.0),
                pei_valid(end.1),
                spec_l3_structure_path_le(start, end),
                start.0 <= l3i <= end.0 + 1,
                self.spec_resolve_mapping_l4(l4i) =~= Some(*l4_entry),
                forall|done_l3i: L3Index, done_l2i: L2Index|
                    #![trigger self.spec_resolve_mapping_l2(
                        l4i, done_l3i, done_l2i,
                    )]
                    pei_valid(done_l3i) && pei_valid(done_l2i)
                        && spec_l3_structure_path_le(start, (done_l3i, done_l2i))
                        && spec_l3_structure_path_le((done_l3i, done_l2i), end)
                        && done_l3i < l3i
                        ==> self.spec_resolve_mapping_l2(
                            l4i, done_l3i, done_l2i,
                        ) is Some,
            decreases end.0 + 1 - l3i,
        {
            let l3_entry = self.get_entry_l3(l4i, l3i, l4_entry);
            let l3_entry = match l3_entry {
                Some(entry) => entry,
                None => {
                    let probe_l2i = if l3i == start.0 { start.1 } else { 0 };
                    assert(!self.spec_l3_structure_range_present(
                        l4i, start, end,
                    )) by {
                        assert(self.spec_resolve_mapping_l2(
                            l4i, l3i, probe_l2i,
                        ) is None) by {
                            reveal(PageTable::wf_l3);
                        };
                    };
                    return false;
                },
            };
            if !self.l2_structure_range_present(
                l4i,
                l3i,
                &l3_entry,
                if l3i == start.0 { start.1 } else { 0 },
                if l3i == end.0 { end.1 } else { 511 },
            ) {
                return false;
            }
            l3i = l3i + 1;
        }
        true
    }

    pub fn structure_range_present(
        &self,
        start: (L4Index, L3Index, L2Index),
        end: (L4Index, L3Index, L2Index),
    ) -> (ret: bool)
        requires
            self.wf(),
            self.kernel_l4_end <= start.0,
            pei_valid(start.0),
            pei_valid(start.1),
            pei_valid(start.2),
            pei_valid(end.0),
            pei_valid(end.1),
            pei_valid(end.2),
            spec_l4_structure_path_le(start, end),
        ensures
            ret == self.spec_structure_range_present(start, end),
    {
        let mut l4i = start.0;
        while l4i <= end.0
            invariant
                self.wf(),
                self.kernel_l4_end <= start.0 <= l4i,
                pei_valid(start.0),
                pei_valid(start.1),
                pei_valid(start.2),
                pei_valid(end.0),
                pei_valid(end.1),
                pei_valid(end.2),
                spec_l4_structure_path_le(start, end),
                l4i <= end.0 + 1,
                forall|done_l4i: L4Index, done_l3i: L3Index, done_l2i: L2Index|
                    #![trigger self.spec_resolve_mapping_l2(
                        done_l4i, done_l3i, done_l2i,
                    )]
                    pei_valid(done_l4i) && pei_valid(done_l3i) && pei_valid(done_l2i)
                        && spec_l4_structure_path_le(
                            start, (done_l4i, done_l3i, done_l2i),
                        )
                        && spec_l4_structure_path_le(
                            (done_l4i, done_l3i, done_l2i), end,
                        )
                        && done_l4i < l4i
                        ==> self.spec_resolve_mapping_l2(
                            done_l4i, done_l3i, done_l2i,
                        ) is Some,
            decreases end.0 + 1 - l4i,
        {
            let l4_entry = self.get_entry_l4(l4i);
            let l4_entry = match l4_entry {
                Some(entry) => entry,
                None => {
                    let probe = if l4i == start.0 {
                        (start.1, start.2)
                    } else {
                        (0, 0)
                    };
                    assert(!self.spec_structure_range_present(
                        start, end,
                    )) by {
                        assert(self.spec_resolve_mapping_l2(
                            l4i, probe.0, probe.1,
                        ) is None) by {
                            reveal(PageTable::wf_l4);
                        };
                    };
                    return false;
                },
            };
            if !self.l3_structure_range_present(
                l4i,
                &l4_entry,
                if l4i == start.0 { (start.1, start.2) } else { (0, 0) },
                if l4i == end.0 { (end.1, end.2) } else { (511, 511) },
            ) {
                return false;
            }
            l4i = l4i + 1;
        }
        true
    }
}

} // verus!
