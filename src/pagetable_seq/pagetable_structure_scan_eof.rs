use vstd::prelude::*;

verus! {
use crate::*;

impl<const TABLE_TYPE: PTType> PageTable<TABLE_TYPE> {
    /// EOF closure of `next_structure_page` when no user L4 entry is present.
    pub(super) proof fn next_structure_page_eof_empty(&self)
        requires
            self.wf(),
            forall|l4i: L4Index| #![trigger self.spec_resolve_mapping_l4(l4i)] self.kernel_l4_end <= l4i && pei_valid(l4i) ==> self.spec_resolve_mapping_l4(l4i) is None,
        ensures self.spec_structure_scan_wf(StructureScan::Empty),
    {
        assert(self.page_closure() =~= set![self.cr3]) by { reveal(PageTable::wf_l4); reveal(PageTable::tables_reachable_wf); };
        assert(TABLE_TYPE == IOMMU_TYPE ==> self.kernel_l4_end == 0) by { self.kernel_entries_wf_l4_end_at(); };
        assert(self.kernel_l4_end <= KERNEL_MEM_END_L4INDEX ==> self.mapping_4k().dom() =~= Set::<VAddr>::empty() && self.mapping_2m().dom() =~= Set::<VAddr>::empty()
            && self.mapping_1g().dom() =~= Set::<VAddr>::empty()) by {
            broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_va_1g_valid_index_roundtrip, iova_4k_valid_index_roundtrip,
                iova_2m_valid_index_roundtrip, iova_1g_valid_index_roundtrip;
            reveal(PageTable::wf_mapping_4k); reveal(PageTable::wf_mapping_2m); reveal(PageTable::wf_mapping_1g);
        };
    }
}
} // verus!
