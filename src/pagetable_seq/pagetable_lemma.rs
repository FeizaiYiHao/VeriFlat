use vstd::prelude::*;
verus! {
use crate::*;

impl<const TABLE_TYPE: PTType> PageTable<TABLE_TYPE> {
    pub broadcast proof fn resolve_l3_addr_unique_at(&self, l4i: L4Index, l3i: L3Index, l4j: L4Index, l3j: L3Index)
        requires
            self.wf_l4(),
            self.disjoint_l4(),
            self.disjoint_l3(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            self.kernel_l4_end <= l4j && pei_valid(l4j),
            pei_valid(l3j),
        ensures
            #![trigger self.spec_resolve_mapping_l3(l4i, l3i), self.spec_resolve_mapping_l3(l4j, l3j)]
            (l4i, l3i) != (l4j, l3j) && self.spec_resolve_mapping_l3(l4i, l3i) is Some && self.spec_resolve_mapping_l3(l4j, l3j) is Some ==> self.spec_resolve_mapping_l3(l4i, l3i)->0.addr != self.spec_resolve_mapping_l3(l4j, l3j)->0.addr,
    {
        reveal(PageTable::wf_l4);
        reveal(PageTable::disjoint_l4);
        reveal(PageTable::disjoint_l3);
    }

    pub broadcast proof fn resolve_l2_addr_unique_at(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index, l4j: L4Index, l3j: L3Index, l2j: L2Index)
        requires
            self.wf_l4(),
            self.wf_l3(),
            self.disjoint_l4(),
            self.disjoint_l3(),
            self.disjoint_l2(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            self.kernel_l4_end <= l4j && pei_valid(l4j),
            pei_valid(l3j),
            pei_valid(l2j),
        ensures
            #![trigger self.spec_resolve_mapping_l2(l4i, l3i, l2i), self.spec_resolve_mapping_l2(l4j, l3j, l2j)]
            (l4i, l3i, l2i) != (l4j, l3j, l2j) && self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some && self.spec_resolve_mapping_l2(l4j, l3j, l2j) is Some
                ==> self.spec_resolve_mapping_l2(l4i, l3i, l2i)->0.addr != self.spec_resolve_mapping_l2(l4j, l3j, l2j)->0.addr,
    {
        reveal(PageTable::wf_l4);
        reveal(PageTable::wf_l3);
        reveal(PageTable::disjoint_l4);
        reveal(PageTable::disjoint_l3);
        reveal(PageTable::disjoint_l2);
    }

    pub broadcast proof fn l2_entry_addr_unique_at(&self, pi: PageMapPtr, l2i: L2Index, pj: PageMapPtr, l2j: L2Index)
        requires
            self.disjoint_l2(),
            self.l2_tables.view().dom().contains(pi),
            self.l2_tables.view().dom().contains(pj),
            pei_valid(l2i),
            pei_valid(l2j),
        ensures
            #![trigger self.disjoint_l2(), self.l2_tables.view().spec_index(pi).value().spec_index(l2i).addr, self.l2_tables.view().spec_index(pj).value().spec_index(l2j).addr]
            (pi, l2i) != (pj, l2j) && self.l2_tables.view().spec_index(pi).value().spec_index(l2i).perm.present
                && self.l2_tables.view().spec_index(pj).value().spec_index(l2j).perm.present && !self.l2_tables.view().spec_index(pi).value().spec_index(l2i).perm.ps && !self.l2_tables.view().spec_index(pj).value().spec_index(l2j).perm.ps
                    ==> self.l2_tables.view().spec_index(pi).value().spec_index(l2i).addr != self.l2_tables.view().spec_index(pj).value().spec_index(l2j).addr,
    {
        reveal(PageTable::disjoint_l2);
    }

    pub broadcast proof fn resolve_l2_target_exists(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index)
        requires
            self.wf_l4(),
            self.wf_l3(),
            self.wf_l2(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
        ensures
            #![trigger self.spec_resolve_mapping_l2(l4i, l3i, l2i)]
            self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some ==> self.l1_tables.view().dom().contains(self.spec_resolve_mapping_l2(l4i, l3i, l2i)->0.addr),
    {
        reveal(PageTable::wf_l4);
        reveal(PageTable::wf_l3);
        reveal(PageTable::wf_l2);
    }

    pub proof fn resolve_l2_unchanged(&self, other: &Self)
        requires
            self.kernel_l4_end == other.kernel_l4_end,
            self.cr3 == other.cr3,
            self.l4_table.view() == other.l4_table.view(),
            self.l3_tables.view() == other.l3_tables.view(),
            self.l2_tables.view() == other.l2_tables.view(),
        ensures
            forall|l4i: L4Index|
                #![trigger pei_valid(l4i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i) ==> forall|l3i: L3Index|
                    #![trigger pei_valid(l3i)]
                    pei_valid(l3i) ==> forall|l2i: L2Index| #![trigger self.spec_resolve_mapping_l2(l4i, l3i, l2i)] pei_valid(l2i) ==> self.spec_resolve_mapping_l2(l4i, l3i, l2i) == other.spec_resolve_mapping_l2(l4i, l3i, l2i),
    {
    }
}
} // verus!
