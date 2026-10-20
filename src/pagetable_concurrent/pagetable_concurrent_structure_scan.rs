use vstd::prelude::*;

verus! {
use crate::*;

// Pending user approval (2026-10-20): field-level eq lemma for a deep-trigger scan_wf.
/// Tables that keep their upper half, L2 ghost entries, and L1 tables resolve every L2, 2M, and 4K entry alike, so
/// `spec_structure_scan_wf` carries across a change of only the window lock state.
pub proof fn spec_structure_scan_wf_preserved_for_lower_tables_eq<const TABLE_TYPE: PTType>(old: PageTableC<TABLE_TYPE>, new: PageTableC<TABLE_TYPE>)
    requires
        new.higher == old.higher,
        new.lower.l2_ghost == old.lower.l2_ghost,
        new.lower.l1_tables == old.lower.l1_tables,
    ensures
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new.spec_resolve_mapping_l2(l4i, l3i, l2i)] new.spec_resolve_mapping_l2(l4i, l3i, l2i) == old.spec_resolve_mapping_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)]
            new.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == old.spec_resolve_mapping_2m_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
            new.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == old.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i),
{}

impl<const TABLE_TYPE: PTType> PageTableHigher<TABLE_TYPE> {
    pub proof fn table_pages_wf_l3_at(&self, p: PageMapPtr)
        requires
            self.table_pages_wf(),
            self.l3_tables.view().dom().contains(p),
        ensures
            !self.l4_table.view().dom().contains(p),
    { reveal(PageTableHigher::table_pages_wf); }
}

impl<const TABLE_TYPE: PTType> PageTableC<TABLE_TYPE> {
    pub proof fn table_pages_wf_l2_at(&self, p: PageMapPtr)
        requires
            self.table_pages_wf(),
            self.lower.l2_perms.dom().contains(p),
        ensures
            !self.higher.l4_table.view().dom().contains(p),
    { reveal(PageTableC::table_pages_wf); }

    pub proof fn table_pages_wf_l1_at(&self, p: PageMapPtr)
        requires
            self.table_pages_wf(),
            self.lower.l1_tables.dom().contains(p),
        ensures
            !self.higher.l4_table.view().dom().contains(p),
    { reveal(PageTableC::table_pages_wf); }

    /// `scan` names a table page that the matching `remove_l*_entry` can unlink, or reports that no user L4 entry is
    /// present.
    pub open spec fn spec_structure_scan_wf(&self, scan: StructureScan) -> bool {
        match scan {
            StructureScan::L1 { l4i, l3i, l2i, l2_p, l1_p } => {
                &&& self.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                &&& self.spec_resolve_mapping_l3(l4i, l3i) is Some && self.spec_resolve_mapping_l3(l4i, l3i)->0.addr == l2_p
                &&& self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some && self.spec_resolve_mapping_l2(l4i, l3i, l2i)->0.addr == l1_p
                &&& forall|i: L1Index| #![trigger self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, i)] pei_valid(i) ==> self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, i) is None
                &&& self.page_closure().contains(l1_p) && l1_p != self.cr3()
            },
            StructureScan::L2 { l4i, l3i, l3_p, l2_p } => {
                &&& self.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i)
                &&& self.spec_resolve_mapping_l4(l4i) is Some && self.spec_resolve_mapping_l4(l4i)->0.addr == l3_p
                &&& self.spec_resolve_mapping_l3(l4i, l3i) is Some && self.spec_resolve_mapping_l3(l4i, l3i)->0.addr == l2_p
                &&& forall|i: L2Index| #![trigger self.spec_resolve_mapping_l2(l4i, l3i, i)] pei_valid(i) ==> self.spec_resolve_mapping_l2(l4i, l3i, i) is None
                &&& forall|i: L2Index| #![trigger self.spec_resolve_mapping_2m_l2(l4i, l3i, i)] pei_valid(i) ==> self.spec_resolve_mapping_2m_l2(l4i, l3i, i) is None
                &&& self.page_closure().contains(l2_p) && l2_p != self.cr3()
            },
            StructureScan::L3 { l4i, l3_p } => {
                &&& self.kernel_l4_end() <= l4i && pei_valid(l4i)
                &&& self.spec_resolve_mapping_l4(l4i) is Some && self.spec_resolve_mapping_l4(l4i)->0.addr == l3_p
                &&& forall|i: L3Index| #![trigger self.spec_resolve_mapping_l3(l4i, i)] pei_valid(i) ==> self.spec_resolve_mapping_l3(l4i, i) is None
                &&& forall|i: L3Index| #![trigger self.spec_resolve_mapping_1g_l3(l4i, i)] pei_valid(i) ==> self.spec_resolve_mapping_1g_l3(l4i, i) is None
                &&& self.page_closure().contains(l3_p) && l3_p != self.cr3()
            },
            StructureScan::Empty => {
                &&& forall|l4i: L4Index| #![trigger self.spec_resolve_mapping_l4(l4i)] self.kernel_l4_end() <= l4i && pei_valid(l4i) ==> self.spec_resolve_mapping_l4(l4i) is None
                &&& self.page_closure() =~= set![self.cr3()]
                &&& self.kernel_l4_end() <= KERNEL_MEM_END_L4INDEX ==> self.mapping_4k().dom() =~= Set::<VAddr>::empty()
                &&& self.kernel_l4_end() <= KERNEL_MEM_END_L4INDEX ==> self.mapping_2m().dom() =~= Set::<VAddr>::empty()
                &&& self.kernel_l4_end() <= KERNEL_MEM_END_L4INDEX ==> self.mapping_1g().dom() =~= Set::<VAddr>::empty()
            },
            StructureScan::Blocked => true,
        }
    }

    /// Closure of `next_structure_page` when no user L4 entry is present.
    proof fn next_structure_page_empty_wf(&self)
        requires
            self.wf(),
            forall|l4i: L4Index| #![trigger self.spec_resolve_mapping_l4(l4i)] self.kernel_l4_end() <= l4i && pei_valid(l4i) ==> self.spec_resolve_mapping_l4(l4i) is None,
        ensures
            self.spec_structure_scan_wf(StructureScan::Empty),
    {
        assert(self.page_closure() =~= set![self.cr3()]) by { reveal(PageTableHigher::wf_l4); reveal(PageTableHigher::tables_reachable_wf); reveal(PageTableC::tables_reachable_wf); };
        assert(TABLE_TYPE == IOMMU_TYPE ==> self.kernel_l4_end() == 0) by { self.higher.kernel_entries_wf_l4_end_at(); };
        assert(self.kernel_l4_end() <= KERNEL_MEM_END_L4INDEX ==> self.mapping_4k().dom() =~= Set::<VAddr>::empty() && self.mapping_2m().dom() =~= Set::<VAddr>::empty()
            && self.mapping_1g().dom() =~= Set::<VAddr>::empty()) by {
            broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_va_1g_valid_index_roundtrip, iova_4k_valid_index_roundtrip, iova_2m_valid_index_roundtrip,
                iova_1g_valid_index_roundtrip;
            reveal(PageTableC::wf_mapping_4k); reveal(PageTableC::wf_mapping_2m); reveal(PageTableHigher::wf_mapping_1g);
        };
    }
}

impl<const TABLE_TYPE: PTType> PageTableHigher<TABLE_TYPE> {
    /// Find the first table page, in index order below the first present user L4 entry, that can be unlinked.
    pub fn next_structure_page(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>) -> (ret: StructureScan)
        requires
            (PageTableC { higher: *self, lower: *lower }).wf(),
        ensures
            (PageTableC { higher: *self, lower: *lower }).spec_structure_scan_wf(ret),
            lower.mapping_4k.dom() =~= Set::<VAddr>::empty() && lower.mapping_2m.dom() =~= Set::<VAddr>::empty() && self.mapping_1g.view().dom() =~= Set::<VAddr>::empty() ==> !(ret is Blocked),
    {
        assert(pei_valid(self.kernel_l4_end)) by { self.kernel_l4_end_valid(); };
        let mut l4i = self.kernel_l4_end;
        while l4i < 512
            invariant
                (PageTableC { higher: *self, lower: *lower }).wf(),
                pei_valid(self.kernel_l4_end),
                self.kernel_l4_end <= l4i <= 512,
                forall|j: L4Index| #![trigger self.spec_resolve_mapping_l4(j)] self.kernel_l4_end <= j < l4i ==> self.spec_resolve_mapping_l4(j) is None,
            decreases 512 - l4i,
        {
            if let Some(l4_entry) = self.get_entry_l4(l4i) { return self.scan_l3_table(Tracked(lower), l4i, &l4_entry); }
            l4i = l4i + 1;
        }
        proof { (PageTableC { higher: *self, lower: *lower }).next_structure_page_empty_wf(); }
        StructureScan::Empty
    }

    /// Unlink the table page that `scan` names and return its memory; every mapping stays. Lock preconditions per branch:
    /// an L1 page is unlinked by clearing its L2 entry, the window spin lock word, so this thread holds that window lock; an L2
    /// page is freed whole, so none of its 512 windows is locked; an L3 page carries no window lock.
    pub fn remove_structure_page(&mut self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, scan: StructureScan, Tracked(lctx): Tracked<&mut LocalContext>)
        -> (ret: Tracked<PagePerm4k>)
        requires
            (PageTableC { higher: *old(self), lower: *old(lower) }).wf(),
            (PageTableC { higher: *old(self), lower: *old(lower) }).spec_structure_scan_wf(scan),
            scan.spec_table_page() is Some,
            scan is L1 ==> (PageTableC { higher: *old(self), lower: *old(lower) }).window_locked_by_thread(scan->L1_l4i, scan->L1_l3i, scan->L1_l2i, old(lctx).thread_id()),
            scan is L2 ==> forall|i: L2Index| #![trigger old(lower).l2_lock_of(scan->L2_l2_p).lock_state(i)] pei_valid(i) ==> old(lower).l2_lock_of(scan->L2_l2_p).lock_state(i) is None,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (PageTableC { higher: *final(self), lower: *final(lower) }).wf(),
            (PageTableC { higher: *final(self), lower: *final(lower) }).page_closure() =~= (PageTableC { higher: *old(self), lower: *old(lower) }).page_closure().remove(scan.spec_table_page()->Some_0),
            final(lower).mapping_4k == old(lower).mapping_4k,
            final(lower).mapping_2m == old(lower).mapping_2m,
            final(self).mapping_1g == old(self).mapping_1g,
            final(self).kernel_entries == old(self).kernel_entries,
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).cr3 == old(self).cr3,
            final(self).pcid == old(self).pcid,
            final(self).proc_ptr == old(self).proc_ptr,
            final(lower).locked_windows == old(lower).locked_windows,
            scan is L1 ==> *final(self) == *old(self),
            scan is L1 ==> final(lower).l2_lock == old(lower).l2_lock,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
                #![trigger (PageTableC { higher: *final(self), lower: *final(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                #![trigger (PageTableC { higher: *old(self), lower: *old(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    ==> (PageTableC { higher: *final(self), lower: *final(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id) == (PageTableC { higher: *old(self), lower: *old(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id),
            ret.view().is_init(),
            ret.view().addr() == scan.spec_table_page()->Some_0,
    {
        match scan {
            StructureScan::L1 { l4i, l3i, l2i, l2_p, l1_p } => {
                let (page_ptr, page_map_perm) = self.remove_l2_entry(Tracked(&mut *lower), l4i, l3i, l2i, l2_p, l1_p, Tracked(&mut *lctx));
                page_map_to_page_perm(page_ptr, page_map_perm)
            },
            StructureScan::L2 { l4i, l3i, l3_p, l2_p } => {
                self.remove_l3_entry(Tracked(&mut *lower), l4i, l3i, l3_p, l2_p, Tracked(&mut *lctx)).1
            },
            StructureScan::L3 { l4i, l3_p } => {
                let (page_ptr, page_map_perm) = self.remove_l4_entry(Tracked(&*lower), l4i, l3_p, Tracked(&mut *lctx));
                page_map_to_page_perm(page_ptr, page_map_perm)
            },
            _ => vstd::pervasive::unreached(),
        }
    }

    fn scan_l3_table(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, l4i: L4Index, l4_entry: &PageEntry) -> (ret: StructureScan)
        requires
            (PageTableC { higher: *self, lower: *lower }).wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            self.spec_resolve_mapping_l4(l4i) =~= Some(*l4_entry),
        ensures
            (PageTableC { higher: *self, lower: *lower }).spec_structure_scan_wf(ret),
            !(ret is Empty),
            lower.mapping_4k.dom() =~= Set::<VAddr>::empty() && lower.mapping_2m.dom() =~= Set::<VAddr>::empty() && self.mapping_1g.view().dom() =~= Set::<VAddr>::empty() ==> !(ret is Blocked),
    {
        let ghost c = PageTableC { higher: *self, lower: *lower };
        let mut l3i: L3Index = 0;
        while l3i < 512
            invariant
                c == (PageTableC { higher: *self, lower: *lower }),
                c.wf(),
                self.kernel_l4_end <= l4i && pei_valid(l4i),
                self.spec_resolve_mapping_l4(l4i) =~= Some(*l4_entry),
                l3i <= 512,
                forall|j: L3Index| #![trigger self.spec_resolve_mapping_l3(l4i, j)] j < l3i ==> self.spec_resolve_mapping_l3(l4i, j) is None,
                forall|j: L3Index| #![trigger self.spec_resolve_mapping_1g_l3(l4i, j)] j < l3i ==> self.spec_resolve_mapping_1g_l3(l4i, j) is None,
            decreases 512 - l3i,
        {
            if self.get_entry_1g_l3(l4i, l3i, l4_entry).is_some() {
                proof { assert(self.mapping_1g.view().dom().contains(spec_index2va((l4i, l3i, 0, 0)))) by { self.wf_mapping_1g_at(l4i, l3i); }; }
                return StructureScan::Blocked;
            }
            if let Some(l3_entry) = self.get_entry_l3(l4i, l3i, l4_entry) { return self.scan_l2_table(Tracked(lower), l4i, l3i, l4_entry, &l3_entry); }
            l3i = l3i + 1;
        }
        proof { assert(c.page_closure().contains(l4_entry.addr) && l4_entry.addr != self.cr3) by { self.wf_l4_at(l4i); self.wf_l4_cr3_at(); self.table_pages_wf_l3_at(l4_entry.addr); }; }
        StructureScan::L3 { l4i, l3_p: l4_entry.addr }
    }

    fn scan_l2_table(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, l4i: L4Index, l3i: L3Index, l4_entry: &PageEntry, l3_entry: &PageEntry) -> (ret: StructureScan)
        requires
            (PageTableC { higher: *self, lower: *lower }).wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            self.spec_resolve_mapping_l4(l4i) =~= Some(*l4_entry),
            self.spec_resolve_mapping_l3(l4i, l3i) =~= Some(*l3_entry),
        ensures
            (PageTableC { higher: *self, lower: *lower }).spec_structure_scan_wf(ret),
            !(ret is Empty),
            lower.mapping_4k.dom() =~= Set::<VAddr>::empty() && lower.mapping_2m.dom() =~= Set::<VAddr>::empty() && self.mapping_1g.view().dom() =~= Set::<VAddr>::empty() ==> !(ret is Blocked),
    {
        let ghost c = PageTableC { higher: *self, lower: *lower };
        let mut l2i: L2Index = 0;
        while l2i < 512
            invariant
                c == (PageTableC { higher: *self, lower: *lower }),
                c.wf(),
                self.kernel_l4_end <= l4i && pei_valid(l4i),
                pei_valid(l3i),
                self.spec_resolve_mapping_l4(l4i) =~= Some(*l4_entry),
                self.spec_resolve_mapping_l3(l4i, l3i) =~= Some(*l3_entry),
                l2i <= 512,
                forall|j: L2Index| #![trigger c.spec_resolve_mapping_l2(l4i, l3i, j)] j < l2i ==> c.spec_resolve_mapping_l2(l4i, l3i, j) is None,
                forall|j: L2Index| #![trigger c.spec_resolve_mapping_2m_l2(l4i, l3i, j)] j < l2i ==> c.spec_resolve_mapping_2m_l2(l4i, l3i, j) is None,
            decreases 512 - l2i,
        {
            if self.get_entry_2m_l2(Tracked(lower), l4i, l3i, l2i, l3_entry).is_some() {
                proof { assert(lower.mapping_2m.dom().contains(spec_index2va((l4i, l3i, l2i, 0)))) by { c.wf_mapping_2m_at(l4i, l3i, l2i); }; }
                return StructureScan::Blocked;
            }
            if let Some(l2_entry) = self.get_entry_l2(Tracked(lower), l4i, l3i, l2i, l3_entry) {
                if self.l1_table_has_no_leaf(Tracked(lower), l4i, l3i, l2i, &l2_entry) {
                    proof { assert(c.page_closure().contains(l2_entry.addr) && l2_entry.addr != self.cr3) by { c.resolve_l2_target_exists(l4i, l3i, l2i); self.wf_l4_cr3_at(); c.table_pages_wf_l1_at(l2_entry.addr); }; }
                    return StructureScan::L1 { l4i, l3i, l2i, l2_p: l3_entry.addr, l1_p: l2_entry.addr };
                }
                return StructureScan::Blocked;
            }
            l2i = l2i + 1;
        }
        proof {
            assert(c.page_closure().contains(l3_entry.addr) && l3_entry.addr != self.cr3) by { self.wf_l4_at(l4i); c.wf_l3_at(l4_entry.addr, l3i); self.wf_l4_cr3_at(); c.table_pages_wf_l2_at(l3_entry.addr); };
        }
        StructureScan::L2 { l4i, l3i, l3_p: l4_entry.addr, l2_p: l3_entry.addr }
    }

    fn l1_table_has_no_leaf(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, l4i: L4Index, l3i: L3Index, l2i: L2Index, l2_entry: &PageEntry) -> (ret: bool)
        requires
            (PageTableC { higher: *self, lower: *lower }).wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_l2(l4i, l3i, l2i) =~= Some(*l2_entry),
        ensures
            ret ==> forall|i: L1Index|
                #![trigger (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, i)]
                pei_valid(i) ==> (PageTableC { higher: *self, lower: *lower }).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, i) is None,
            lower.mapping_4k.dom() =~= Set::<VAddr>::empty() ==> ret,
    {
        let ghost c = PageTableC { higher: *self, lower: *lower };
        let mut l1i: L1Index = 0;
        while l1i < 512
            invariant
                c == (PageTableC { higher: *self, lower: *lower }),
                c.wf(),
                self.kernel_l4_end <= l4i && pei_valid(l4i),
                pei_valid(l3i),
                pei_valid(l2i),
                c.spec_resolve_mapping_l2(l4i, l3i, l2i) =~= Some(*l2_entry),
                l1i <= 512,
                forall|j: L1Index| #![trigger c.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, j)] j < l1i ==> c.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, j) is None,
            decreases 512 - l1i,
        {
            if self.get_entry_l1(Tracked(lower), l4i, l3i, l2i, l1i, l2_entry).is_some() { return false; }
            l1i = l1i + 1;
        }
        true
    }
}
} // verus!
