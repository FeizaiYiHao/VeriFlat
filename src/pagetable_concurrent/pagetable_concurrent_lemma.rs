use vstd::prelude::*;
verus! {
use crate::*;
use vstd::set_lib::*;

/// `f(i)` is in the image of `[lo, hi)` under `f` for every `i` in that range.
pub proof fn lemma_set_range_map_contains_at<B>(lo: usize, hi: usize, f: spec_fn(usize) -> B, i: usize)
    requires
        lo <= i < hi,
    ensures
        Set::range(lo, hi).map(f).contains(f(i)),
{
    assert(Set::range(lo, hi).contains(i)) by { range_set_properties(lo, hi); };
    Set::range(lo, hi).lemma_map_contains(f, f(i));
}

impl<const TABLE_TYPE: PTType> PageTableHigher<TABLE_TYPE> {
    pub proof fn wf_l4_cr3_at(&self)
        requires
            self.wf_l4(),
        ensures
            self.l4_table.view().dom().contains(self.cr3),
            self.l4_table.view().spec_index(self.cr3).addr() == self.cr3,
            self.l4_table.view().spec_index(self.cr3).is_init(),
            self.l4_table.view().spec_index(self.cr3).value().wf(),
    { reveal(PageTableHigher::wf_l4); }

    pub proof fn wf_l4_at(&self, l4i: L4Index)
        requires
            self.wf_l4(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
        ensures
            self.l4_table.view().spec_index(self.cr3).value().spec_index(l4i).perm.present ==> !self.l4_table.view().spec_index(self.cr3).value().spec_index(l4i).perm.ps,
            self.l4_table.view().spec_index(self.cr3).value().spec_index(l4i).perm.present ==> self.l3_tables.view().dom().contains(self.l4_table.view().spec_index(self.cr3).value().spec_index(l4i).addr),
    { reveal(PageTableHigher::wf_l4); }

    pub proof fn wf_l3_at(&self, p: PageMapPtr)
        requires
            self.wf_l3(),
            self.l3_tables.view().dom().contains(p),
        ensures
            self.l3_tables.view().spec_index(p).addr() == p,
            self.l3_tables.view().spec_index(p).is_init(),
            self.l3_tables.view().spec_index(p).value().wf(),
    { reveal(PageTableHigher::wf_l3); }

    pub proof fn table_pages_wf_cr3_at(&self)
        requires self.table_pages_wf()
        ensures page_ptr_valid(self.cr3)
    { reveal(PageTableHigher::table_pages_wf); }

    pub proof fn tables_reachable_wf_at(&self, p: PageMapPtr)
        requires
            self.tables_reachable_wf(),
            self.l3_tables.view().dom().contains(p),
        ensures
            self.kernel_l4_end <= self.l3_rev_map.view().spec_index(p) && pei_valid(self.l3_rev_map.view().spec_index(p)),
            self.spec_resolve_mapping_l4(self.l3_rev_map.view().spec_index(p)) is Some,
            self.spec_resolve_mapping_l4(self.l3_rev_map.view().spec_index(p))->0.addr == p,
    { reveal(PageTableHigher::tables_reachable_wf); }

    pub proof fn wf_mapping_1g_at(&self, l4i: L4Index, l3i: L3Index)
        requires
            self.wf_mapping_1g(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
        ensures
            self.mapping_1g.view().dom().contains(spec_index2va((l4i, l3i, 0, 0))) == self.spec_resolve_mapping_1g_l3(l4i, l3i) is Some,
            self.spec_resolve_mapping_1g_l3(l4i, l3i) is Some
                ==> self.mapping_1g.view().spec_index(spec_index2va((l4i, l3i, 0, 0))).addr == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.addr
                && self.mapping_1g.view().spec_index(spec_index2va((l4i, l3i, 0, 0))).write == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.perm.write
                && self.mapping_1g.view().spec_index(spec_index2va((l4i, l3i, 0, 0))).execute_disable == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.perm.execute_disable
                && self.mapping_1g.view().spec_index(spec_index2va((l4i, l3i, 0, 0))).present == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.perm.present,
    { reveal(PageTableHigher::wf_mapping_1g); }

    pub proof fn kernel_l4_end_valid(&self)
        requires self.kernel_entries_wf()
        ensures pei_valid(self.kernel_l4_end)
    { reveal(PageTableHigher::kernel_entries_wf); }

    pub proof fn kernel_entries_wf_l4_end_at(&self)
        requires self.kernel_entries_wf()
        ensures TABLE_TYPE == IOMMU_TYPE ==> self.kernel_l4_end == 0
    { reveal(PageTableHigher::kernel_entries_wf); }

    pub proof fn kernel_entries_wf_len_at(&self)
        requires self.kernel_entries_wf()
        ensures
            pei_valid(self.kernel_l4_end),
            self.kernel_entries.view().len() == self.kernel_l4_end as nat,
    { reveal(PageTableHigher::kernel_entries_wf); }

    pub proof fn kernel_entries_wf_at(&self, i: usize)
        requires
            self.kernel_entries_wf(),
            0 <= i < self.kernel_l4_end,
        ensures
            self.kernel_entries.view().spec_index(i as int) == self.l4_table.view().spec_index(self.cr3).value().spec_index(i),
    { reveal(PageTableHigher::kernel_entries_wf); }

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
        reveal(PageTableHigher::wf_l4);
        reveal(PageTableHigher::disjoint_l4);
        reveal(PageTableHigher::disjoint_l3);
    }
}

impl<const TABLE_TYPE: PTType> PageTableC<TABLE_TYPE> {
    pub proof fn wf_l3_at(&self, p: PageMapPtr, i: L3Index)
        requires
            self.wf_l3(),
            self.higher.l3_tables.view().dom().contains(p),
            pei_valid(i),
        ensures
            self.higher.l3_tables.view().spec_index(p).value().spec_index(i).perm.present && !self.higher.l3_tables.view().spec_index(p).value().spec_index(i).perm.ps
                ==> self.lower.l2_perms.dom().contains(self.higher.l3_tables.view().spec_index(p).value().spec_index(i).addr),
    { reveal(PageTableC::wf_l3); }

    pub proof fn wf_l2_at(&self, p: PageMapPtr, i: L2Index)
        requires
            self.wf_l2(),
            self.lower.l2_perms.dom().contains(p),
            pei_valid(i),
        ensures
            self.lower.l2_perms.spec_index(p).addr() == p,
            self.lower.l2_perms.spec_index(p).is_init(),
            self.lower.l2_page(p).addr() == p,
            self.lower.l2_page(p).wf(),
            self.lower.l2_page(p).entry_lock(i).inv(),
            self.lower.l2_entry(p, i).perm.ps && self.lower.l2_entry(p, i).perm.present ==> self.lower.l2_entry(p, i).perm.kernel_present,
            (self.lower.l2_entry(p, i).perm.present && !self.lower.l2_entry(p, i).perm.ps) == (self.lower.l2_page(p).entry_lock(i).l1() is Some),
            self.lower.l2_page(p).entry_lock(i).l1() is Some
                ==> self.lower.l1_perm(p, i).addr() == self.lower.l2_entry(p, i).addr && self.lower.l1_rev_map.dom().contains(self.lower.l2_entry(p, i).addr),
    { reveal(PageTableC::wf_l2); }

    pub proof fn wf_l1_at(&self, p: PageMapPtr, i: L2Index)
        requires
            self.wf_l1(),
            self.lower.l2_perms.dom().contains(p),
            pei_valid(i),
            self.lower.l2_page(p).entry_lock(i).l1() is Some,
        ensures
            self.lower.l1_perm(p, i).is_init(),
            self.lower.l1_page(p, i).wf(),
    { reveal(PageTableC::wf_l1); }

    pub proof fn tables_reachable_wf_l2_at(&self, p: PageMapPtr)
        requires
            self.tables_reachable_wf(),
            self.lower.l2_perms.dom().contains(p),
        ensures
            self.kernel_l4_end() <= self.higher.l2_rev_map.view().spec_index(p).0 && pei_valid(self.higher.l2_rev_map.view().spec_index(p).0),
            pei_valid(self.higher.l2_rev_map.view().spec_index(p).1),
            self.spec_resolve_mapping_l3(self.higher.l2_rev_map.view().spec_index(p).0, self.higher.l2_rev_map.view().spec_index(p).1) is Some,
            self.spec_resolve_mapping_l3(self.higher.l2_rev_map.view().spec_index(p).0, self.higher.l2_rev_map.view().spec_index(p).1)->0.addr == p,
    { reveal(PageTableC::tables_reachable_wf); }

    pub proof fn tables_reachable_wf_l1_at(&self, p: PageMapPtr)
        requires
            self.tables_reachable_wf(),
            self.lower.l1_rev_map.dom().contains(p),
        ensures
            self.kernel_l4_end() <= self.lower.l1_rev_map.spec_index(p).0 && pei_valid(self.lower.l1_rev_map.spec_index(p).0),
            pei_valid(self.lower.l1_rev_map.spec_index(p).1) && pei_valid(self.lower.l1_rev_map.spec_index(p).2),
            self.spec_resolve_mapping_l2(self.lower.l1_rev_map.spec_index(p).0, self.lower.l1_rev_map.spec_index(p).1, self.lower.l1_rev_map.spec_index(p).2) is Some,
            self.spec_resolve_mapping_l2(self.lower.l1_rev_map.spec_index(p).0, self.lower.l1_rev_map.spec_index(p).1, self.lower.l1_rev_map.spec_index(p).2)->0.addr == p,
    { reveal(PageTableC::tables_reachable_wf); }

    pub proof fn wf_mapping_4k_at(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index)
        requires
            self.wf_mapping_4k(),
            self.kernel_l4_end() <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            pei_valid(l1i),
        ensures
            self.lower.mapping_4k.dom().contains(spec_index2va((l4i, l3i, l2i, l1i))) == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some,
            self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some
                ==> self.lower.mapping_4k.spec_index(spec_index2va((l4i, l3i, l2i, l1i))).addr == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.addr
                && self.lower.mapping_4k.spec_index(spec_index2va((l4i, l3i, l2i, l1i))).write == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.perm.write
                && self.lower.mapping_4k.spec_index(spec_index2va((l4i, l3i, l2i, l1i))).execute_disable == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.perm.execute_disable
                && self.lower.mapping_4k.spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.perm.present,
    { reveal(PageTableC::wf_mapping_4k); }

    pub proof fn wf_mapping_2m_at(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index)
        requires
            self.wf_mapping_2m(),
            self.kernel_l4_end() <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
        ensures
            self.lower.mapping_2m.dom().contains(spec_index2va((l4i, l3i, l2i, 0))) == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some,
            self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some
                ==> self.lower.mapping_2m.spec_index(spec_index2va((l4i, l3i, l2i, 0))).addr == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.addr
                && self.lower.mapping_2m.spec_index(spec_index2va((l4i, l3i, l2i, 0))).write == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.perm.write
                && self.lower.mapping_2m.spec_index(spec_index2va((l4i, l3i, l2i, 0))).execute_disable == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.perm.execute_disable
                && self.lower.mapping_2m.spec_index(spec_index2va((l4i, l3i, l2i, 0))).present == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.perm.present,
    { reveal(PageTableC::wf_mapping_2m); }

    pub proof fn wf_window_locks_va_at(&self, w: WindowVa)
        requires
            self.wf_window_locks(),
            self.lower.pagetable_window_locks.dom().contains(w),
        ensures
            page_table_key_2m_valid::<TABLE_TYPE>(w.va),
            self.kernel_l4_end() <= spec_v2l4index(w.va),
            self.window_exists(spec_v2l4index(w.va), spec_v2l3index(w.va)),
            self.lower.pagetable_window_locks.spec_index(w) == if self.lower.l2_owner(self.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)) is Some {
                LockStateU::WriteLocked
            } else {
                LockStateU::Unlocked
            },
    { reveal(PageTableC::wf_window_locks); }

    pub proof fn wf_window_locks_slot_at(&self, p: PageMapPtr, i: L2Index)
        requires
            self.wf_window_locks(),
            self.lower.l2_perms.dom().contains(p),
            pei_valid(i),
        ensures
            self.lower.pagetable_window_locks.dom().contains(WindowVa { va: spec_index2va((self.higher.l2_rev_map.view().spec_index(p).0, self.higher.l2_rev_map.view().spec_index(p).1, i, 0)) }),
    { reveal(PageTableC::wf_window_locks); }

    pub broadcast proof fn resolve_l2_addr_unique_at(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index, l4j: L4Index, l3j: L3Index, l2j: L2Index)
        requires
            self.higher.wf_l4(),
            self.wf_l3(),
            self.higher.disjoint_l4(),
            self.higher.disjoint_l3(),
            self.disjoint_l2(),
            self.kernel_l4_end() <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            self.kernel_l4_end() <= l4j && pei_valid(l4j),
            pei_valid(l3j),
            pei_valid(l2j),
        ensures
            #![trigger self.spec_resolve_mapping_l2(l4i, l3i, l2i), self.spec_resolve_mapping_l2(l4j, l3j, l2j)]
            (l4i, l3i, l2i) != (l4j, l3j, l2j) && self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some && self.spec_resolve_mapping_l2(l4j, l3j, l2j) is Some
                ==> self.spec_resolve_mapping_l2(l4i, l3i, l2i)->0.addr != self.spec_resolve_mapping_l2(l4j, l3j, l2j)->0.addr,
    {
        reveal(PageTableHigher::wf_l4);
        reveal(PageTableC::wf_l3);
        reveal(PageTableHigher::disjoint_l4);
        reveal(PageTableHigher::disjoint_l3);
        reveal(PageTableC::disjoint_l2);
    }

    pub broadcast proof fn l2_entry_addr_unique_at(&self, pi: PageMapPtr, l2i: L2Index, pj: PageMapPtr, l2j: L2Index)
        requires
            self.disjoint_l2(),
            self.lower.l2_perms.dom().contains(pi),
            self.lower.l2_perms.dom().contains(pj),
            pei_valid(l2i),
            pei_valid(l2j),
        ensures
            #![trigger self.disjoint_l2(), self.lower.l2_entry(pi, l2i).addr, self.lower.l2_entry(pj, l2j).addr]
            (pi, l2i) != (pj, l2j) && self.lower.l2_entry(pi, l2i).perm.present
                && self.lower.l2_entry(pj, l2j).perm.present && !self.lower.l2_entry(pi, l2i).perm.ps && !self.lower.l2_entry(pj, l2j).perm.ps
                    ==> self.lower.l2_entry(pi, l2i).addr != self.lower.l2_entry(pj, l2j).addr,
    { reveal(PageTableC::disjoint_l2); }

    pub broadcast proof fn resolve_l2_target_exists(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index)
        requires
            self.higher.wf_l4(),
            self.wf_l3(),
            self.wf_l2(),
            self.kernel_l4_end() <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
        ensures
            #![trigger self.spec_resolve_mapping_l2(l4i, l3i, l2i)]
            self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some ==> self.lower.l1_rev_map.dom().contains(self.spec_resolve_mapping_l2(l4i, l3i, l2i)->0.addr),
    {
        reveal(PageTableHigher::wf_l4);
        reveal(PageTableC::wf_l3);
        reveal(PageTableC::wf_l2);
    }

    pub proof fn resolve_l2_unchanged(&self, other: &Self)
        requires
            self.kernel_l4_end() == other.kernel_l4_end(),
            self.cr3() == other.cr3(),
            self.higher.l4_table.view() == other.higher.l4_table.view(),
            self.higher.l3_tables.view() == other.higher.l3_tables.view(),
            forall|p: PageMapPtr, i: L2Index| #![trigger self.lower.l2_entry(p, i)] self.lower.l2_entry(p, i) == other.lower.l2_entry(p, i),
        ensures
            forall|l4i: L4Index|
                #![trigger pei_valid(l4i)]
                self.kernel_l4_end() <= l4i && pei_valid(l4i) ==> forall|l3i: L3Index|
                    #![trigger pei_valid(l3i)]
                    pei_valid(l3i) ==> forall|l2i: L2Index| #![trigger self.spec_resolve_mapping_l2(l4i, l3i, l2i)] pei_valid(l2i) ==> self.spec_resolve_mapping_l2(l4i, l3i, l2i) == other.spec_resolve_mapping_l2(l4i, l3i, l2i),
    {
    }
}
} // verus!
