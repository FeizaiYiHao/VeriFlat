use vstd::prelude::*;
verus! {
use crate::*;
impl IommuTable {
    pub(super) proof fn get_entry_l4_eof_implies_result_contract(&self, target_l4i: L4Index, ret: Option<PageEntry>)
        requires
            self.wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            ret =~= self.spec_resolve_mapping_l4(target_l4i),
        ensures
            self.spec_resolve_mapping_l4(target_l4i) == ret,
            forall|l3i: L3Index, l2i: L2Index, l1i: L1Index|
                #![trigger spec_index2va((target_l4i, l3i, l2i, l1i))]
                #![trigger self.spec_resolve_mapping_4k_l1(target_l4i, l3i, l2i, l1i)]
                pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && ret is None
                    ==> self.spec_resolve_mapping_4k_l1(target_l4i, l3i, l2i, l1i) is None && self.mapping_4k().dom().contains(spec_index2va((target_l4i, l3i, l2i, l1i))) == false,
    {
        reveal(IommuTable::wf_mapping_4k);
    }

    pub(super) proof fn get_entry_l3_eof_implies_result_contract(&self, target_l4i: L4Index, target_l3i: L3Index, l4_entry: &PageEntry, ret: Option<PageEntry>)
        requires
            self.wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            self.spec_resolve_mapping_l4(target_l4i) =~= Some(*l4_entry),
            ret =~= self.spec_resolve_mapping_l3(target_l4i, target_l3i),
        ensures
            self.spec_resolve_mapping_l3(target_l4i, target_l3i) =~= ret,
            forall|l2i: L2Index, l1i: L1Index|
                #![trigger spec_index2va((target_l4i, target_l3i, l2i, l1i))]
                #![trigger self.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, l2i, l1i)]
                pei_valid(l2i) && pei_valid(l1i) && ret is None ==> self.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, l2i, l1i) is None && self.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, l2i, l1i))) == false,
    {
        reveal(IommuTable::wf_mapping_4k);
    }

    pub(super) proof fn get_entry_l2_eof_implies_result_contract(&self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, l3_entry: &PageEntry, ret: Option<PageEntry>)
        requires
            self.wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            self.spec_resolve_mapping_l3(target_l4i, target_l3i) =~= Some(*l3_entry),
            ret =~= self.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i),
        ensures
            self.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) =~= ret,
            forall|l1i: L1Index|
                #![trigger spec_index2va((target_l4i, target_l3i, target_l2i, l1i))]
                #![trigger self.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, l1i)]
                pei_valid(l1i) && ret is None ==> self.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, l1i) is None && self.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, l1i))) == false,
    {
        reveal(IommuTable::wf_mapping_4k);
    }
}
} // verus!
