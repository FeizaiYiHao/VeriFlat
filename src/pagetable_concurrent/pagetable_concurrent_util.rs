use vstd::prelude::*;
verus! {
use crate::*;
use vstd::simple_pptr::*;

impl<const TABLE_TYPE: PTType> PageTableHigher<TABLE_TYPE> {
    pub fn new(pcid: Option<Pcid>, kernel_entries_ghost: Ghost<Seq<PageEntry>>, page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<PointsTo<PageMap>>, mem_end_l4_index: usize, proc_ptr: RwLockProcessPtr) -> (ret: Self)
        requires
            pei_valid(mem_end_l4_index),
            page_ptr_valid(page_map_ptr),
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            kernel_entries_ghost.view().len() == mem_end_l4_index,
            forall|i: usize| #![trigger page_map_perm.value().spec_index(i).is_empty()] #![trigger page_map_perm.value().spec_index(i)] mem_end_l4_index <= i && pei_valid(i) ==> page_map_perm.value().spec_index(i).is_empty(),
            forall|i: usize|
                #![trigger kernel_entries_ghost.view().spec_index(i as int)]
                #![trigger page_map_perm.value().spec_index(i)]
                0 <= i < mem_end_l4_index ==> kernel_entries_ghost.view().spec_index(i as int) == page_map_perm.value().spec_index(i),
            TABLE_TYPE == PT_TYPE ==> pcid is Some,
            TABLE_TYPE == IOMMU_TYPE ==> pcid is None,
            TABLE_TYPE == IOMMU_TYPE ==> mem_end_l4_index == 0,
        ensures
            ret.inv(),
            ret.cr3 == page_map_ptr,
            ret.pcid == pcid,
            ret.did is None,
            ret.kernel_l4_end == mem_end_l4_index,
            ret.kernel_entries =~= kernel_entries_ghost,
            ret.l4_table.view() == Map::<PageMapPtr, PointsTo<PageMap>>::empty().insert(page_map_ptr, page_map_perm),
            ret.l3_tables.view().dom() == Set::<PageMapPtr>::empty(),
            ret.mapping_1g.view() == Map::<VAddr, MapEntry>::empty(),
            ret.proc_ptr == proc_ptr,
    {
        let mut ret = Self {
            cr3: page_map_ptr, pcid, did: None, kernel_l4_end: mem_end_l4_index, l4_table: Tracked(Map::<PageMapPtr, PointsTo<PageMap>>::tracked_empty()),
            l3_rev_map: Ghost(Map::<PageMapPtr, (L4Index)>::empty()), l3_tables: Tracked(Map::<PageMapPtr, PointsTo<PageMap>>::tracked_empty()),
            l2_rev_map: Ghost(Map::<PageMapPtr, (L4Index, L3Index)>::empty()), mapping_1g: Ghost(Map::<VAddr, MapEntry>::empty()), kernel_entries: kernel_entries_ghost,
            proc_ptr,
        };
        proof {
            ret.l4_table.borrow_mut().tracked_insert(page_map_ptr, page_map_perm);
            ret.new_eof_inv(page_map_perm);
        }
        ret
    }

    pub fn get_entry_l4(&self, target_l4i: L4Index) -> (ret: Option<PageEntry>)
        requires
            self.inv(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
        ensures
            self.spec_resolve_mapping_l4(target_l4i) == ret,
    {
        proof { self.wf_l4_cr3_at(); }
        let tracked l4_perm = self.l4_table.borrow().tracked_borrow(self.cr3);
        let l4_tbl: &PageMap = PPtr::<PageMap>::from_usize(self.cr3).borrow(Tracked(l4_perm));
        let l4_entry = l4_tbl.get(target_l4i);
        if l4_entry.perm.present { Some(l4_entry) } else { None }
    }

    pub fn get_entry_l3(&self, target_l4i: L4Index, target_l3i: L3Index, l4_entry: &PageEntry) -> (ret: Option<PageEntry>)
        requires
            self.inv(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            self.spec_resolve_mapping_l4(target_l4i) =~= Some(*l4_entry),
        ensures
            self.spec_resolve_mapping_l3(target_l4i, target_l3i) =~= ret,
    {
        proof {
            self.wf_l4_at(target_l4i);
            self.wf_l3_at(l4_entry.addr);
        }
        let tracked l3_perm = self.l3_tables.borrow().tracked_borrow(l4_entry.addr);
        let l3_tbl: &PageMap = PPtr::<PageMap>::from_usize(l4_entry.addr).borrow(Tracked(l3_perm));
        let l3_entry = l3_tbl.get(target_l3i);
        if l3_entry.perm.present && !l3_entry.perm.ps { Some(l3_entry) } else { None }
    }

    pub fn get_entry_1g_l3(&self, target_l4i: L4Index, target_l3i: L3Index, l4_entry: &PageEntry) -> (ret: Option<PageEntry>)
        requires
            self.inv(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            self.spec_resolve_mapping_l4(target_l4i) =~= Some(*l4_entry),
        ensures
            self.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) =~= ret,
    {
        proof {
            self.wf_l4_at(target_l4i);
            self.wf_l3_at(l4_entry.addr);
        }
        let tracked l3_perm = self.l3_tables.borrow().tracked_borrow(l4_entry.addr);
        let l3_tbl: &PageMap = PPtr::<PageMap>::from_usize(l4_entry.addr).borrow(Tracked(l3_perm));
        let l3_entry = l3_tbl.get(target_l3i);
        if l3_entry.perm.ps && l3_entry.perm.kernel_present { Some(l3_entry) } else { None }
    }

    pub fn get_entry_l2(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, l3_entry: &PageEntry) -> (ret: Option<PageEntry>)
        requires
            (PageTableC { higher: *self, lower: *lower }).wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            self.spec_resolve_mapping_l3(target_l4i, target_l3i) =~= Some(*l3_entry),
        ensures
            (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) =~= ret,
    {
        proof {
            let c = PageTableC { higher: *self, lower: *lower };
            self.wf_l4_at(target_l4i);
            c.wf_l3_at(self.spec_resolve_mapping_l4(target_l4i)->0.addr, target_l3i);
            c.l2_tokens_paired_at(l3_entry.addr);
        }
        let tracked l2_perm = lower.l2_perms.tracked_borrow(l3_entry.addr);
        let tracked l2_ghost = lower.l2_ghost.tracked_borrow(l3_entry.addr);
        let l2_tbl: &L2PageMap = PPtr::<L2PageMap>::from_usize(l3_entry.addr).borrow(Tracked(l2_perm));
        let l2_entry = l2_tbl.get(Tracked(l2_ghost), target_l2i);
        if l2_entry.perm.present && !l2_entry.perm.ps { Some(l2_entry) } else { None }
    }

    pub fn get_entry_2m_l2(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, l3_entry: &PageEntry) -> (ret: Option<PageEntry>)
        requires
            (PageTableC { higher: *self, lower: *lower }).wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            self.spec_resolve_mapping_l3(target_l4i, target_l3i) =~= Some(*l3_entry),
        ensures
            (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) =~= ret,
    {
        proof {
            let c = PageTableC { higher: *self, lower: *lower };
            self.wf_l4_at(target_l4i);
            c.wf_l3_at(self.spec_resolve_mapping_l4(target_l4i)->0.addr, target_l3i);
            c.l2_tokens_paired_at(l3_entry.addr);
        }
        let tracked l2_perm = lower.l2_perms.tracked_borrow(l3_entry.addr);
        let tracked l2_ghost = lower.l2_ghost.tracked_borrow(l3_entry.addr);
        let l2_tbl: &L2PageMap = PPtr::<L2PageMap>::from_usize(l3_entry.addr).borrow(Tracked(l2_perm));
        let l2_entry = l2_tbl.get(Tracked(l2_ghost), target_l2i);
        if l2_entry.perm.kernel_present && l2_entry.perm.ps { Some(l2_entry) } else { None }
    }

    pub fn get_entry_l1(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index,
        l2_entry: &PageEntry) -> (ret: Option<PageEntry>)
        requires
            (PageTableC { higher: *self, lower: *lower }).wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) =~= Some(*l2_entry),
        ensures
            (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) =~= ret,
            lower.mapping_4k.dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == ret is Some,
            ret is Some ==> lower.mapping_4k.spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)))
                == page_entry_to_map_entry(&ret.unwrap(), Ghost(lower.mapping_4k.spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))).owning_container.view())),
    {
        proof {
            let c = PageTableC { higher: *self, lower: *lower };
            self.wf_l4_at(target_l4i);
            c.wf_l3_at(self.spec_resolve_mapping_l4(target_l4i)->0.addr, target_l3i);
            c.wf_l2_at(self.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, target_l2i);
            c.wf_l1_at(l2_entry.addr);
            c.wf_mapping_4k_at(target_l4i, target_l3i, target_l2i, target_l1i);
        }
        let tracked l1_perm = lower.l1_tables.tracked_borrow(l2_entry.addr);
        let l1_tbl: &PageMap = PPtr::<PageMap>::from_usize(l2_entry.addr).borrow(Tracked(l1_perm));
        let l1_entry = l1_tbl.get(target_l1i);
        if l1_entry.perm.kernel_present { Some(l1_entry) } else { None }
    }
}

impl<const TABLE_TYPE: PTType> PageTableLower<TABLE_TYPE> {
    /// The window half of a table without L2 pages: every map and the locked-window set are empty.
    pub open spec fn spec_empty() -> Self {
        PageTableLower {
            l2_perms: Map::empty(), l2_ghost: Map::empty(), l2_lock: Map::empty(), l1_rev_map: Map::empty(), l1_tables: Map::empty(),
            mapping_4k: Map::empty(), mapping_2m: Map::empty(), locked_windows: Set::empty(), window_stale_cpus: Map::empty(),
        }
    }

    /// The window half of a table that owns only its root page.
    pub proof fn tracked_empty(higher: PageTableHigher<TABLE_TYPE>) -> (tracked ret: Self)
        requires
            higher.inv(),
            higher.l3_tables.view().dom() == Set::<PageMapPtr>::empty(),
        ensures
            ret.l2_perms.dom() == Set::<PageMapPtr>::empty(),
            ret.l1_tables.dom() == Set::<PageMapPtr>::empty(),
            ret.mapping_4k == Map::<VAddr, MapEntry>::empty(),
            ret.mapping_2m == Map::<VAddr, MapEntry>::empty(),
            ret.locked_windows == Set::<WindowVa>::empty(),
            ret == Self::spec_empty(),
            (PageTableC { higher, lower: ret }).wf(),
    {
        let tracked ret = PageTableLower {
            l2_perms: Map::tracked_empty(), l2_ghost: Map::tracked_empty(), l2_lock: Map::tracked_empty(), l1_rev_map: Map::empty(), l1_tables: Map::tracked_empty(),
            mapping_4k: Map::empty(), mapping_2m: Map::empty(), locked_windows: Set::empty(), window_stale_cpus: Map::empty(),
        };
        let c = PageTableC { higher, lower: ret };
        assert(c.wf_l3()) by { reveal(PageTableC::wf_l3); };
        assert(c.l2_tokens_paired()) by { reveal(PageTableC::l2_tokens_paired); };
        assert(c.wf_l2()) by { reveal(PageTableC::wf_l2); };
        assert(c.wf_l1()) by { reveal(PageTableC::wf_l1); };
        assert(c.disjoint_l2()) by { reveal(PageTableC::disjoint_l2); };
        assert(c.wf_mapping_4k()) by { reveal(PageTableC::wf_mapping_4k); reveal(PageTableHigher::wf_l4); };
        assert(c.wf_mapping_2m()) by { reveal(PageTableC::wf_mapping_2m); reveal(PageTableHigher::wf_l4); };
        assert(c.user_only()) by { reveal(PageTableC::user_only); };
        assert(c.rwx_upper_level_entries()) by { reveal(PageTableC::rwx_upper_level_entries); };
        assert(c.table_pages_wf()) by { reveal(PageTableC::table_pages_wf); };
        assert(c.tables_reachable_wf()) by { reveal(PageTableC::tables_reachable_wf); };
        assert(c.wf_window_locks()) by { reveal(PageTableC::wf_window_locks); };
        ret
    }
}

impl PageTableC<PT_TYPE> {
    pub open spec fn spec_4k_entry_usable(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index) -> bool
        recommends
            self.wf(),
            self.kernel_l4_end() <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            pei_valid(l1i),
    {
        &&& self.spec_resolve_mapping_1g_l3(l4i, l3i) is None
        &&& self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is None
        &&& self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is None
    }
}

impl PageTableHigher<PT_TYPE> {
    pub fn resolve_mapping_4k_l3(&self, l4i: L4Index, l3i: L3Index) -> (ret: (Option<PageEntry>, PageTableErrorCode))
        requires
            self.inv(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
        ensures
            ret.0 =~= self.spec_resolve_mapping_l3(l4i, l3i),
            ret.0 is Some <==> ret.1 == PageTableErrorCode::NoError,
            ret.1 == PageTableErrorCode::L4EntryNotExist <==> self.spec_resolve_mapping_l4(l4i) is None,
            ret.1 == PageTableErrorCode::L3EntryNotExist
                <==> self.spec_resolve_mapping_1g_l3(l4i, l3i) is None && self.spec_resolve_mapping_l3(l4i, l3i) is None && self.spec_resolve_mapping_l4(l4i) is Some,
            ret.1 == PageTableErrorCode::EntryTakenBy1g <==> self.spec_resolve_mapping_1g_l3(l4i, l3i) is Some,
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

    pub fn resolve_mapping_4k_l2(&self, Tracked(lower): Tracked<&PageTableLower<PT_TYPE>>, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> (ret: (Option<PageEntry>, PageTableErrorCode))
        requires
            (PageTableC { higher: *self, lower: *lower }).wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
        ensures
            ret.0 =~= (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_l2(l4i, l3i, l2i),
            ret.0 is Some <==> ret.1 == PageTableErrorCode::NoError,
            ret.1 == PageTableErrorCode::L4EntryNotExist <==> self.spec_resolve_mapping_l4(l4i) is None,
            ret.1 == PageTableErrorCode::L3EntryNotExist
                <==> self.spec_resolve_mapping_1g_l3(l4i, l3i) is None && self.spec_resolve_mapping_l3(l4i, l3i) is None && self.spec_resolve_mapping_l4(l4i) is Some,
            ret.1 == PageTableErrorCode::L2EntryNotExist
                <==> (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is None
                && (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_l2(l4i, l3i, l2i) is None && self.spec_resolve_mapping_l3(l4i, l3i) is Some,
            ret.1 == PageTableErrorCode::EntryTakenBy1g <==> self.spec_resolve_mapping_1g_l3(l4i, l3i) is Some,
            ret.1 == PageTableErrorCode::EntryTakenBy2m <==> (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some,
            ret.1 != PageTableErrorCode::L1EntryNotExist,
    {
        match self.resolve_mapping_4k_l3(l4i, l3i) {
            (None, error_code) => { (None, error_code) },
            (Some(l3_entry), _) => {
                match self.get_entry_2m_l2(Tracked(lower), l4i, l3i, l2i, &l3_entry) {
                    Some(_) => { (None, PageTableErrorCode::EntryTakenBy2m) },
                    None => match self.get_entry_l2(Tracked(lower), l4i, l3i, l2i, &l3_entry) {
                        None => { (None, PageTableErrorCode::L2EntryNotExist) },
                        Some(l2_entry) => { (Some(l2_entry), PageTableErrorCode::NoError) },
                    },
                }
            },
        }
    }

    pub fn resolve_mapping_4k_l1(&self, Tracked(lower): Tracked<&PageTableLower<PT_TYPE>>, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index)
        -> (ret: (Option<PageEntry>, PageTableErrorCode, Option<MapEntry>))
        requires
            (PageTableC { higher: *self, lower: *lower }).wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            pei_valid(l1i),
        ensures
            ret.0 =~= (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i),
            ret.0 is Some <==> ret.1 == PageTableErrorCode::NoError,
            ret.0 is Some == ret.2 is Some,
            ret.0 is Some && ret.2 is Some ==> ret.2->0 =~= lower.mapping_4k.spec_index(spec_index2va((l4i, l3i, l2i, l1i))),
            ret.1 == PageTableErrorCode::L4EntryNotExist <==> self.spec_resolve_mapping_l4(l4i) is None,
            ret.1 == PageTableErrorCode::L3EntryNotExist
                ==> self.spec_resolve_mapping_1g_l3(l4i, l3i) is None && self.spec_resolve_mapping_l3(l4i, l3i) is None && self.spec_resolve_mapping_l4(l4i) is Some,
            ret.1 == PageTableErrorCode::L2EntryNotExist
                ==> (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is None
                && (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_l2(l4i, l3i, l2i) is None && self.spec_resolve_mapping_l3(l4i, l3i) is Some,
            ret.1 == PageTableErrorCode::L1EntryNotExist
                ==> (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is None
                && (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
            ret.1 == PageTableErrorCode::EntryTakenBy1g <==> self.spec_resolve_mapping_1g_l3(l4i, l3i) is Some,
            ret.1 == PageTableErrorCode::EntryTakenBy2m <==> (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some,
            ret.1 != PageTableErrorCode::EntryTakenBy4k,
            ret.1 != PageTableErrorCode::EntryTakenBy1g && ret.1 != PageTableErrorCode::EntryTakenBy2m && ret.1 != PageTableErrorCode::NoError
                ==> (PageTableC { higher: *self, lower: *lower }).spec_4k_entry_usable(l4i, l3i, l2i, l1i),
    {
        match self.resolve_mapping_4k_l2(Tracked(lower), l4i, l3i, l2i) {
            (None, error_code) => { (None, error_code, None) },
            (Some(l2_entry), _) => {
                match self.get_entry_l1(Tracked(lower), l4i, l3i, l2i, l1i, &l2_entry) {
                    None => { (None, PageTableErrorCode::L1EntryNotExist, None) },
                    Some(l1_entry) => {
                        let map_entry = page_entry_to_map_entry(&l1_entry, Ghost(lower.mapping_4k.spec_index(spec_index2va((l4i, l3i, l2i, l1i))).owning_container.view()));
                        (Some(l1_entry), PageTableErrorCode::NoError, Some(map_entry))
                    },
                }
            },
        }
    }
}
} // verus!
