use vstd::prelude::*;
verus! {
use crate::*;
use vstd::simple_pptr::*;
impl IommuTable {
    pub fn new(page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<PointsTo<IommuPageMap>>, proc_ptr: RwLockProcessPtr) -> (ret: Self)
        requires
            page_ptr_valid(page_map_ptr),
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().iommu_wf(),
            forall|i: usize| #![trigger page_map_perm.value().spec_index(i).is_empty()] #![trigger page_map_perm.value().spec_index(i)] pei_valid(i) ==> page_map_perm.value().spec_index(i).is_empty(),
        ensures
            ret.wf(),
            ret.cr3 == page_map_ptr,
            ret.did is None,
            ret.is_empty(),
            ret.page_closure() =~= set![page_map_ptr],
            ret.proc_ptr == proc_ptr,
    {
        let mut ret = Self {
            cr3: page_map_ptr,
            did: None,
            l4_table: Tracked(Map::<PageMapPtr, PointsTo<IommuPageMap>>::tracked_empty()),
            l3_rev_map: Ghost(Map::<PageMapPtr, (L4Index)>::empty()),
            l3_tables: Tracked(Map::<PageMapPtr, PointsTo<IommuPageMap>>::tracked_empty()),
            l2_rev_map: Ghost(Map::<PageMapPtr, (L4Index, L3Index)>::empty()),
            l2_tables: Tracked(Map::<PageMapPtr, PointsTo<IommuPageMap>>::tracked_empty()),
            l1_rev_map: Ghost(Map::<PageMapPtr, (L4Index, L3Index, L2Index)>::empty()),
            l1_tables: Tracked(Map::<PageMapPtr, PointsTo<IommuPageMap>>::tracked_empty()),
            mapping_4k: Ghost(Map::<VAddr, MapEntry>::empty()),
            proc_ptr: proc_ptr,
        };
        proof {
            ret.l4_table.borrow_mut().tracked_insert(page_map_ptr, page_map_perm);
            Self::new_eof(ret);
        }
        ret
    }

    proof fn new_eof(ret: Self)
        requires
            page_ptr_valid(ret.cr3),
            ret.l4_table.view().dom() == set![ret.cr3],
            ret.l4_table.view().spec_index(ret.cr3).addr() == ret.cr3,
            ret.l4_table.view().spec_index(ret.cr3).is_init(),
            ret.l4_table.view().spec_index(ret.cr3).value().iommu_wf(),
            forall|i: usize| #![trigger ret.l4_entry(i).is_empty()] #![trigger ret.l4_entry(i)] pei_valid(i) ==> ret.l4_entry(i).is_empty(),
            ret.l3_tables.view() == Map::<PageMapPtr, PointsTo<IommuPageMap>>::empty(),
            ret.l2_tables.view() == Map::<PageMapPtr, PointsTo<IommuPageMap>>::empty(),
            ret.l1_tables.view() == Map::<PageMapPtr, PointsTo<IommuPageMap>>::empty(),
            ret.mapping_4k.view() == Map::<VAddr, MapEntry>::empty(),
        ensures
            ret.wf_l4(),
            ret.wf_l3(),
            ret.wf_l2(),
            ret.wf_l1(),
            ret.disjoint_l4(),
            ret.disjoint_l3(),
            ret.disjoint_l2(),
            ret.wf_mapping_4k(),
            ret.user_only(),
            ret.rwx_upper_level_entries(),
            ret.table_pages_wf(),
            ret.tables_reachable_wf(),
    {
        assert(ret.wf_l4()) by { reveal(IommuTable::wf_l4); };
        assert(ret.wf_l3()) by { reveal(IommuTable::wf_l3); };
        assert(ret.wf_l2()) by { reveal(IommuTable::wf_l2); };
        assert(ret.wf_l1()) by { reveal(IommuTable::wf_l1); };
        assert(ret.disjoint_l4()) by { reveal(IommuTable::disjoint_l4); };
        assert(ret.disjoint_l3()) by { reveal(IommuTable::disjoint_l3); };
        assert(ret.disjoint_l2()) by { reveal(IommuTable::disjoint_l2); };
        assert(ret.wf_mapping_4k()) by { reveal(IommuTable::wf_mapping_4k); };
        assert(ret.user_only()) by { reveal(IommuTable::user_only); };
        assert(ret.rwx_upper_level_entries()) by { reveal(IommuTable::rwx_upper_level_entries); };
        assert(ret.table_pages_wf()) by { reveal(IommuTable::table_pages_wf); };
        assert(ret.tables_reachable_wf()) by { reveal(IommuTable::tables_reachable_wf); };
    }

    pub proof fn wf_l4_at(&self, i: L4Index)
        requires
            self.wf_l4(),
            pei_valid(i),
        ensures
            self.l4_table.view().dom().contains(self.cr3),
            self.l4_table.view()[self.cr3].addr() == self.cr3,
            self.l4_table.view()[self.cr3].is_init(),
            self.l4_table.view()[self.cr3].value().iommu_wf(),
            self.l4_entry(i).perm.present ==> !self.l4_entry(i).perm.ps && self.l3_tables.view().dom().contains(self.l4_entry(i).addr),
    {
        reveal(IommuTable::wf_l4);
    }

    pub proof fn wf_l3_at(&self, p: PageMapPtr, i: usize)
        requires
            self.wf_l3(),
            self.l3_tables.view().dom().contains(p),
            pei_valid(i),
        ensures
            self.l3_tables.view()[p].addr() == p,
            self.l3_tables.view()[p].is_init(),
            self.l3_tables.view()[p].value().iommu_wf(),
            self.l3_entry(p, i).perm.ps && self.l3_entry(p, i).perm.present ==> self.l3_entry(p, i).perm.kernel_present,
            self.l3_entry(p, i).perm.present && !self.l3_entry(p, i).perm.ps ==> self.l2_tables.view().dom().contains(self.l3_entry(p, i).addr),
    {
        reveal(IommuTable::wf_l3);
    }

    pub proof fn wf_l2_at(&self, p: PageMapPtr, i: usize)
        requires
            self.wf_l2(),
            self.l2_tables.view().dom().contains(p),
            pei_valid(i),
        ensures
            self.l2_tables.view()[p].addr() == p,
            self.l2_tables.view()[p].is_init(),
            self.l2_tables.view()[p].value().iommu_wf(),
            self.l2_entry(p, i).perm.ps && self.l2_entry(p, i).perm.present ==> self.l2_entry(p, i).perm.kernel_present,
            self.l2_entry(p, i).perm.present && !self.l2_entry(p, i).perm.ps ==> self.l1_tables.view().dom().contains(self.l2_entry(p, i).addr),
    {
        reveal(IommuTable::wf_l2);
    }

    pub proof fn wf_l1_at(&self, p: PageMapPtr, i: usize)
        requires
            self.wf_l1(),
            self.l1_tables.view().dom().contains(p),
            pei_valid(i),
        ensures
            self.l1_tables.view()[p].addr() == p,
            self.l1_tables.view()[p].is_init(),
            self.l1_tables.view()[p].value().iommu_wf(),
            self.l1_entry(p, i).perm.present ==> !self.l1_entry(p, i).perm.ps && self.l1_entry(p, i).perm.kernel_present,
    {
        reveal(IommuTable::wf_l1);
    }

    pub proof fn table_pages_wf_cr3_at(&self)
        requires self.table_pages_wf()
        ensures page_ptr_valid(self.cr3)
    { reveal(IommuTable::table_pages_wf); }

    pub proof fn table_pages_wf_l3_at(&self, p: PageMapPtr)
        requires
            self.table_pages_wf(),
            self.l3_tables.view().dom().contains(p),
        ensures !self.l4_table.view().dom().contains(p),
    { reveal(IommuTable::table_pages_wf); }

    pub proof fn table_pages_wf_l2_at(&self, p: PageMapPtr)
        requires
            self.table_pages_wf(),
            self.l2_tables.view().dom().contains(p),
        ensures !self.l4_table.view().dom().contains(p),
    { reveal(IommuTable::table_pages_wf); }

    pub proof fn table_pages_wf_l1_at(&self, p: PageMapPtr)
        requires
            self.table_pages_wf(),
            self.l1_tables.view().dom().contains(p),
        ensures !self.l4_table.view().dom().contains(p),
    { reveal(IommuTable::table_pages_wf); }

    pub proof fn wf_mapping_4k_at(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index)
        requires
            self.wf_mapping_4k(),
            pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            pei_valid(l1i),
        ensures
            self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))) == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some,
            self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some ==> {
                let entry = self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0;
                let mapping = self.mapping_4k()[spec_index2va((l4i, l3i, l2i, l1i))];
                &&& mapping.addr == entry.addr
                &&& entry.perm.present ==> mapping.write == entry.perm.write
                &&& mapping.execute_disable == entry.perm.execute_disable
                &&& mapping.is_io == entry.perm.is_io
                &&& mapping.present == entry.perm.present
            },
    {
        reveal(IommuTable::wf_mapping_4k);
    }
}
} // verus!
