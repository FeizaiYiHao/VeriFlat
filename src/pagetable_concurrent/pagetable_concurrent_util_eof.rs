use vstd::prelude::*;
verus! {
use crate::*;
use vstd::simple_pptr::*;

impl<const TABLE_TYPE: PTType> PageTableHigher<TABLE_TYPE> {
    /// EOF closure of `new`: a table that owns only its root page satisfies the big-lock invariant.
    pub(super) proof fn new_eof_inv(&self, page_map_perm: PointsTo<PageMap>)
        requires
            pei_valid(self.kernel_l4_end),
            page_ptr_valid(self.cr3),
            page_map_perm.addr() == self.cr3,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            self.l4_table.view() == Map::<PageMapPtr, PointsTo<PageMap>>::empty().insert(self.cr3, page_map_perm),
            self.l3_tables.view().dom() == Set::<PageMapPtr>::empty(),
            self.mapping_1g.view() == Map::<VAddr, MapEntry>::empty(),
            self.kernel_entries.view().len() == self.kernel_l4_end,
            forall|i: usize| #![trigger page_map_perm.value().spec_index(i).is_empty()] #![trigger page_map_perm.value().spec_index(i)] self.kernel_l4_end <= i && pei_valid(i) ==> page_map_perm.value().spec_index(i).is_empty(),
            forall|i: usize|
                #![trigger self.kernel_entries.view().spec_index(i as int)]
                #![trigger page_map_perm.value().spec_index(i)]
                0 <= i < self.kernel_l4_end ==> self.kernel_entries.view().spec_index(i as int) == page_map_perm.value().spec_index(i),
            self.pcid_wf(),
            self.did_wf(),
            TABLE_TYPE == IOMMU_TYPE ==> self.kernel_l4_end == 0,
        ensures
            self.inv(),
    {
        assert(self.wf_l4()) by { reveal(PageTableHigher::wf_l4); };
        assert(self.wf_l3()) by { reveal(PageTableHigher::wf_l3); };
        assert(self.disjoint_l4()) by { reveal(PageTableHigher::disjoint_l4); };
        assert(self.disjoint_l3()) by { reveal(PageTableHigher::disjoint_l3); };
        assert(self.wf_mapping_1g()) by { reveal(PageTableHigher::wf_mapping_1g); };
        assert(self.user_only()) by { reveal(PageTableHigher::user_only); };
        assert(self.rwx_upper_level_entries()) by { reveal(PageTableHigher::rwx_upper_level_entries); };
        assert(self.table_pages_wf()) by { reveal(PageTableHigher::table_pages_wf); };
        assert(self.tables_reachable_wf()) by { reveal(PageTableHigher::tables_reachable_wf); };
        assert(self.kernel_entries_wf()) by { reveal(PageTableHigher::kernel_entries_wf); };
    }
}
} // verus!
