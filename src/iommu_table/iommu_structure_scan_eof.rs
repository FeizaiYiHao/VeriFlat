use vstd::prelude::*;

verus! {
use crate::*;
use super::entry::*;
use super::page_map::*;

impl IommuTable {
    /// EOF closure of `next_structure_page` when no user L4 entry is present.
    pub(super) proof fn next_structure_page_eof_empty(&self)
        requires
            self.wf(),
            forall|l4i: L4Index| #![trigger self.spec_resolve_mapping_l4(l4i)] pei_valid(l4i) ==> self.spec_resolve_mapping_l4(l4i) is None,
        ensures self.structure_scan_wf(StructureScan::Empty),
    {
        assert(self.page_closure() =~= set![self.cr3]) by { reveal(IommuTable::wf_l4); reveal(IommuTable::tables_reachable_wf); };
        assert(self.mapping_4k().dom() =~= Set::<VAddr>::empty()) by {
            broadcast use spec_va_4k_valid_index_roundtrip, iova_4k_valid_index_roundtrip;
            reveal(IommuTable::wf_mapping_4k);
        };
    }
}
} // verus!
