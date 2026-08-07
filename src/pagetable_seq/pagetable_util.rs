use vstd::prelude::*;

verus! {

use crate::*;

pub open spec fn paddrs_equal(u: PAddr, v: PAddr) -> bool {
    u == v
}

impl PageTable<PT_TYPE> {
    pub open spec fn spec_4k_entry_useable(
        &self,
        l4i: L4Index,
        l3i: L3Index,
        l2i: L2Index,
        l1i: L2Index,
    ) -> bool
        recommends
            self.wf(),
            self.kernel_l4_end <= l4i < 512,
            0 <= l3i < 512,
            0 <= l2i < 512,
            0 <= l1i < 512,
    {
        &&& self.spec_resolve_mapping_1g_l3(l4i, l3i) is None
        &&& self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is None
        &&& self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is None
    }

    pub fn resolve_mapping_l4(&self, l4i: L4Index) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            self.kernel_l4_end <= l4i < 512,
        ensures
            ret =~= self.spec_resolve_mapping_l4(l4i),
    {
        self.get_entry_l4(l4i)
    }

    pub fn resolve_mapping_4k_l3(&self, l4i: L4Index, l3i: L3Index) -> (ret: (
        Option<PageEntry>,
        PageTableErrorCode,
    ))
        requires
            self.wf(),
            self.kernel_l4_end <= l4i < 512,
            0 <= l3i < 512,
        ensures
            ret.0 =~= self.spec_resolve_mapping_l3(l4i, l3i),
            ret.0 is Some <==> ret.1 == PageTableErrorCode::NoError,
            ret.1 == PageTableErrorCode::L4EntryNotExist <==> self.spec_resolve_mapping_l4(
                l4i,
            ) is None,
            ret.1 == PageTableErrorCode::L3EntryNotExist <==> self.spec_resolve_mapping_1g_l3(
                l4i,
                l3i,
            ) is None && self.spec_resolve_mapping_l3(l4i, l3i) is None
                && self.spec_resolve_mapping_l3(l4i, l3i) is None && self.spec_resolve_mapping_l4(
                l4i,
            ) is Some,
            ret.1 == PageTableErrorCode::EntryTakenBy1g <==> self.spec_resolve_mapping_1g_l3(
                l4i,
                l3i,
            ) is Some,
            ret.1 != PageTableErrorCode::EntryTakenBy2m,
            ret.1 != PageTableErrorCode::L2EntryNotExist,
            ret.1 != PageTableErrorCode::L1EntryNotExist,
    {
        match self.get_entry_l4(l4i) {
            None => { (None, PageTableErrorCode::L4EntryNotExist) },
            Some(l4_entry) => {
                match self.get_entry_1g_l3(l4i, l3i, &l4_entry) {
                    Some(_) => { (None, PageTableErrorCode::EntryTakenBy1g) },
                    None => match self.get_entry_l3(l4i, l3i, &l4_entry) {
                        None => { (None, PageTableErrorCode::L3EntryNotExist) },
                        Some(l3_entry) => { (Some(l3_entry), PageTableErrorCode::NoError) },
                    },
                }
            },
        }
    }

    pub fn resolve_mapping_4k_l2(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> (ret: (
        Option<PageEntry>,
        PageTableErrorCode,
    ))
        requires
            self.wf(),
            self.kernel_l4_end <= l4i < 512,
            0 <= l3i < 512,
            0 <= l2i < 512,
        ensures
            ret.0 =~= self.spec_resolve_mapping_l2(l4i, l3i, l2i),
            ret.0 is Some <==> ret.1 == PageTableErrorCode::NoError,
            ret.1 == PageTableErrorCode::L4EntryNotExist <==> self.spec_resolve_mapping_l4(
                l4i,
            ) is None,
            ret.1 == PageTableErrorCode::L3EntryNotExist <==> self.spec_resolve_mapping_1g_l3(
                l4i,
                l3i,
            ) is None && self.spec_resolve_mapping_l3(l4i, l3i) is None
                && self.spec_resolve_mapping_l3(l4i, l3i) is None && self.spec_resolve_mapping_l4(
                l4i,
            ) is Some,
            ret.1 == PageTableErrorCode::L2EntryNotExist <==> self.spec_resolve_mapping_2m_l2(
                l4i,
                l3i,
                l2i,
            ) is None && self.spec_resolve_mapping_l2(l4i, l3i, l2i) is None
                && self.spec_resolve_mapping_l3(l4i, l3i) is Some,
            ret.1 == PageTableErrorCode::EntryTakenBy1g <==> self.spec_resolve_mapping_1g_l3(
                l4i,
                l3i,
            ) is Some,
            ret.1 == PageTableErrorCode::EntryTakenBy2m <==> self.spec_resolve_mapping_2m_l2(
                l4i,
                l3i,
                l2i,
            ) is Some,
            ret.1 != PageTableErrorCode::L1EntryNotExist,
    {
        match self.resolve_mapping_4k_l3(l4i, l3i) {
            (None, error_code) => { (None, error_code) },
            (Some(l3_entry), _) => {
                match self.get_entry_2m_l2(l4i, l3i, l2i, &l3_entry) {
                    Some(_) => { (None, PageTableErrorCode::EntryTakenBy2m) },
                    None => match self.get_entry_l2(l4i, l3i, l2i, &l3_entry) {
                        None => { (None, PageTableErrorCode::L2EntryNotExist) },
                        Some(l2_entry) => { (Some(l2_entry), PageTableErrorCode::NoError) },
                    },
                }
            },
        }
    }

    pub fn resolve_mapping_4k_l1(
        &self,
        l4i: L4Index,
        l3i: L3Index,
        l2i: L2Index,
        l1i: L2Index,
    ) -> (ret: (Option<PageEntry>, PageTableErrorCode, Option<MapEntry>))
        requires
            self.wf(),
            self.kernel_l4_end <= l4i < 512,
            0 <= l3i < 512,
            0 <= l2i < 512,
            0 <= l1i < 512,
        ensures
            ret.0 =~= self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i),
            ret.0 is Some <==> ret.1 == PageTableErrorCode::NoError,
            ret.0 is Some == ret.2 is Some,
            ret.0 is Some && ret.2 is Some ==> ret.2->0 =~= page_entry_to_map_entry(
                &ret.0->0,
            ),
            ret.1 == PageTableErrorCode::L4EntryNotExist <==> self.spec_resolve_mapping_l4(
                l4i,
            ) is None,
            ret.1 == PageTableErrorCode::L3EntryNotExist ==> self.spec_resolve_mapping_1g_l3(
                l4i,
                l3i,
            ) is None && self.spec_resolve_mapping_l3(l4i, l3i) is None
                && self.spec_resolve_mapping_l3(l4i, l3i) is None && self.spec_resolve_mapping_l4(
                l4i,
            ) is Some,
            ret.1 == PageTableErrorCode::L2EntryNotExist ==> self.spec_resolve_mapping_2m_l2(
                l4i,
                l3i,
                l2i,
            ) is None && self.spec_resolve_mapping_l2(l4i, l3i, l2i) is None
                && self.spec_resolve_mapping_l3(l4i, l3i) is Some,
            ret.1 == PageTableErrorCode::L1EntryNotExist ==> self.spec_resolve_mapping_4k_l1(
                l4i,
                l3i,
                l2i,
                l1i,
            ) is None && self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
            ret.1 == PageTableErrorCode::EntryTakenBy1g <==> self.spec_resolve_mapping_1g_l3(
                l4i,
                l3i,
            ) is Some,
            ret.1 == PageTableErrorCode::EntryTakenBy2m <==> self.spec_resolve_mapping_2m_l2(
                l4i,
                l3i,
                l2i,
            ) is Some,
            ret.1 != PageTableErrorCode::EntryTakenBy4k,
            ret.1 != PageTableErrorCode::EntryTakenBy1g && ret.1
                != PageTableErrorCode::EntryTakenBy2m && ret.1 != PageTableErrorCode::NoError
                ==> self.spec_4k_entry_useable(l4i, l3i, l2i, l1i),
    {
        match self.resolve_mapping_4k_l2(l4i, l3i, l2i) {
            (None, error_code) => { (None, error_code, None) },
            (Some(l2_entry), _) => {
                match self.get_entry_l1(l4i, l3i, l2i, l1i, &l2_entry) {
                    None => { (None, PageTableErrorCode::L1EntryNotExist, None) },
                    Some(l1_entry) => {
                        let map_entry = page_entry_to_map_entry(&l1_entry);
                        (Some(l1_entry), PageTableErrorCode::NoError, Some(map_entry))
                    },
                }
            },
        }
    }
}

} // verus!
