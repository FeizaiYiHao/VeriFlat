use vstd::prelude::*;

verus! {

use crate::define::*;

// use crate::array::*;
use vstd::simple_pptr::*;

// use crate::util::page_ptr_util_u::*;
use crate::pagetable::entry::*;
use crate::pagetable::pagemap::*;
use crate::pagetable::pagetable_spec::*;

pub open spec fn paddrs_equal(u: PAddr, v: PAddr) -> bool {
    u == v
}

impl PageTable {
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
        let tracked l4_perm = self.l4_table.borrow().tracked_borrow(self.cr3);
        let l4_tbl: &PageMap = PPtr::<PageMap>::from_usize(self.cr3).borrow(Tracked(l4_perm));
        let l4_entry = l4_tbl.get(l4i);

        if !l4_entry.perm.present {
            None
        } else {
            Some(l4_entry)
        }
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
        match self.resolve_mapping_l4(l4i) {
            None => { (None, PageTableErrorCode::L4EntryNotExist) },
            Some(l4_entry) => {
                let tracked l3_perm = self.l3_tables.borrow().tracked_borrow(l4_entry.addr);
                let l3_tbl: &PageMap = PPtr::<PageMap>::from_usize(l4_entry.addr).borrow(
                    Tracked(l3_perm),
                );
                let l3_entry = l3_tbl.get(l3i);
                if !l3_entry.perm.present {
                    (None, PageTableErrorCode::L3EntryNotExist)
                } else if l3_entry.perm.ps {
                    (None, PageTableErrorCode::EntryTakenBy1g)
                } else {
                    (Some(l3_entry), PageTableErrorCode::NoError)
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
                let tracked l2_perm = self.l2_tables.borrow().tracked_borrow(l3_entry.addr);
                let l2_tbl: &PageMap = PPtr::<PageMap>::from_usize(l3_entry.addr).borrow(
                    Tracked(l2_perm),
                );
                let l2_entry = l2_tbl.get(l2i);
                if !l2_entry.perm.present {
                    (None, PageTableErrorCode::L2EntryNotExist)
                } else if l2_entry.perm.ps {
                    (None, PageTableErrorCode::EntryTakenBy2m)
                } else {
                    (Some(l2_entry), PageTableErrorCode::NoError)
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
            ret.1 != PageTableErrorCode::EntryTakenBy1g && ret.1
                != PageTableErrorCode::EntryTakenBy2m && ret.1 != PageTableErrorCode::NoError
                ==> self.spec_4k_entry_useable(l4i, l3i, l2i, l1i),
    {
        match self.resolve_mapping_4k_l2(l4i, l3i, l2i) {
            (None, error_code) => { (None, error_code, None) },
            (Some(l2_entry), _) => {
                let tracked l1_perm = self.l1_tables.borrow().tracked_borrow(l2_entry.addr);
                let l1_tbl: &PageMap = PPtr::<PageMap>::from_usize(l2_entry.addr).borrow(
                    Tracked(l1_perm),
                );
                let l1_entry = l1_tbl.get(l1i);
                if !l1_entry.perm.present {
                    (None, PageTableErrorCode::L1EntryNotExist, None)
                } else {
                    assert(l1_entry.perm.ps == false);
                    let map_entry = page_entry_to_map_entry(&l1_entry);
                    (Some(l1_entry), PageTableErrorCode::NoError, Some(map_entry))
                }
            },
        }
    }
}

} // verus!
