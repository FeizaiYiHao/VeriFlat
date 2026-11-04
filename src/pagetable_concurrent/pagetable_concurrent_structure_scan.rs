use vstd::prelude::*;

verus! {
use crate::*;

/// Tables with equal upper half and L2 pages, which own the L1 pages, resolve every L2, 2M, and 4K entry alike.
pub proof fn resolve_mappings_eq_for_higher_and_lower_tables_eq<const TABLE_TYPE: PTType>(old: WholePageTable<TABLE_TYPE>, new: WholePageTable<TABLE_TYPE>)
    requires
        new.higher == old.higher,
        new.lower.l2_perms == old.lower.l2_perms,
    ensures
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new.spec_resolve_mapping_l2(l4i, l3i, l2i)] new.spec_resolve_mapping_l2(l4i, l3i, l2i) == old.spec_resolve_mapping_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)]
            new.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == old.spec_resolve_mapping_2m_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
            new.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == old.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i),
{}

impl<const TABLE_TYPE: PTType> WholePageTable<TABLE_TYPE> {
    /// `scan` names a table page of the held chain that the matching unlink can take out, post-order, or reports that no user
    /// root entry holds an L3 page. The scan runs only over a table whose user root entries no longer resolve.
    pub open spec fn structure_scan_wf(&self, scan: StructureScan) -> bool {
        match scan {
            StructureScan::L1 { l4i, l3i, l2i, l2_p, l1_p } => {
                &&& self.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                &&& self.spec_held_l3(l4i, l3i) is Some && self.spec_held_l3(l4i, l3i)->0.addr == l2_p
                &&& self.lower.l2_page(l2_p).entry_lock(l2i).l1() is Some && self.lower.l2_entry(l2_p, l2i).addr == l1_p
                &&& self.spec_resolve_mapping_l2(l4i, l3i, l2i) is None
                &&& self.lower.l2_owner(l2_p, l2i) is None
                &&& self.page_closure().contains(l1_p) && l1_p != self.cr3()
            },
            StructureScan::L2 { l4i, l3i, l3_p, l2_p } => {
                &&& self.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i)
                &&& self.spec_held_l4(l4i) is Some && self.spec_held_l4(l4i)->0.addr == l3_p
                &&& self.spec_held_l3(l4i, l3i) is Some && self.spec_held_l3(l4i, l3i)->0.addr == l2_p
                &&& forall|i: L2Index|
                    #![trigger self.lower.l2_page(l2_p).entry_lock(i).l1()]
                    #![trigger self.lower.l2_entry(l2_p, i)]
                    pei_valid(i) ==> self.lower.l2_page(l2_p).entry_lock(i).l1() is None
                &&& forall|i: L2Index| #![trigger self.spec_resolve_mapping_2m_l2(l4i, l3i, i)] pei_valid(i) ==> self.spec_resolve_mapping_2m_l2(l4i, l3i, i) is None
                &&& forall|i: L2Index| #![trigger self.lower.l2_owner(l2_p, i)] pei_valid(i) ==> self.lower.l2_owner(l2_p, i) is None
                &&& self.page_closure().contains(l2_p) && l2_p != self.cr3()
            },
            StructureScan::L3 { l4i, l3_p } => {
                &&& self.kernel_l4_end() <= l4i && pei_valid(l4i)
                &&& self.spec_held_l4(l4i) is Some && self.spec_held_l4(l4i)->0.addr == l3_p
                &&& forall|i: L3Index| #![trigger self.spec_held_l3(l4i, i)] pei_valid(i) ==> self.spec_held_l3(l4i, i) is None
                &&& forall|i: L3Index| #![trigger self.spec_resolve_mapping_1g_l3(l4i, i)] pei_valid(i) ==> self.spec_resolve_mapping_1g_l3(l4i, i) is None
                &&& self.page_closure().contains(l3_p) && l3_p != self.cr3()
            },
            StructureScan::Empty => {
                &&& forall|i: L4Index| #![trigger self.spec_held_l4(i)] self.kernel_l4_end() <= i && pei_valid(i) ==> self.spec_held_l4(i) is None
                &&& forall|i: L4Index| #![trigger self.spec_resolve_mapping_l4(i)] self.kernel_l4_end() <= i && pei_valid(i) ==> self.spec_resolve_mapping_l4(i) is None
                &&& self.page_closure() =~= set![self.cr3()]
                // When every valid key lies in the user part, no mapping is left.
                &&& self.kernel_l4_end() <= KERNEL_MEM_END_L4INDEX ==> {
                    &&& self.mapping_4k().dom() =~= Set::<VAddr>::empty()
                    &&& self.mapping_2m().dom() =~= Set::<VAddr>::empty()
                    &&& self.mapping_1g().dom() =~= Set::<VAddr>::empty()
                }
            },
            StructureScan::Blocked => false,
        }
    }

    /// Closure of `next_structure_page` when no user root entry holds an L3 page.
    proof fn next_structure_page_eof_empty(&self)
        requires
            self.wf(),
            forall|l4i: L4Index| #![trigger self.spec_held_l4(l4i)] self.kernel_l4_end() <= l4i && pei_valid(l4i) ==> self.spec_held_l4(l4i) is None,
            forall|l4i: L4Index| #![trigger self.spec_resolve_mapping_l4(l4i)] self.kernel_l4_end() <= l4i && pei_valid(l4i) ==> self.spec_resolve_mapping_l4(l4i) is None,
        ensures
            self.structure_scan_wf(StructureScan::Empty),
    {
        assert(self.page_closure() =~= set![self.cr3()]) by { reveal(PageTableHigher::wf_l4); reveal(PageTableHigher::tables_reachable_wf); reveal(WholePageTable::tables_reachable_wf); };
        assert(TABLE_TYPE == IOMMU_TYPE ==> self.kernel_l4_end() == 0) by { self.higher.kernel_entries_wf_iommu_l4_end_at(); };
        assert(self.kernel_l4_end() <= KERNEL_MEM_END_L4INDEX ==> self.mapping_4k().dom() =~= Set::<VAddr>::empty() && self.mapping_2m().dom() =~= Set::<VAddr>::empty()
            && self.mapping_1g().dom() =~= Set::<VAddr>::empty()) by {
            broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_va_1g_valid_index_roundtrip, iova_4k_valid_index_roundtrip, iova_2m_valid_index_roundtrip,
                iova_1g_valid_index_roundtrip;
            reveal(WholePageTable::wf_mapping_4k); reveal(WholePageTable::wf_mapping_2m); reveal(PageTableHigher::wf_mapping_1g);
        };
    }
}

impl<const TABLE_TYPE: PTType> PageTableHigher<TABLE_TYPE> {
    /// Find the first table page of the held chain that can be unlinked, post-order in index order: an L1 page, else an L2 page
    /// that holds no L1 page, else an L3 page that holds no L2 page, else report that only the root is left. Every user root entry
    /// no longer resolves, no window is locked, and no hidden L1 page sits outside a locked window, so each L2 word tells whether
    /// it holds an L1 page.
    pub fn next_structure_page(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>) -> (ret: StructureScan)
        requires
            (WholePageTable { higher: *self, lower: *lower }).wf(),
            forall|l4i: L4Index| #![trigger self.spec_resolve_mapping_l4(l4i)] self.kernel_l4_end <= l4i && pei_valid(l4i) ==> self.spec_resolve_mapping_l4(l4i) is None,
            lower.hidden_l1_tables_in_locked_windows(),
            forall|p: PageMapPtr, i: L2Index| #![trigger lower.l2_owner(p, i)] lower.l2_perms.dom().contains(p) && pei_valid(i) ==> lower.l2_owner(p, i) is None,
        ensures
            (WholePageTable { higher: *self, lower: *lower }).structure_scan_wf(ret),
            !(ret is Blocked),
    {
        assert(pei_valid(self.kernel_l4_end)) by { self.kernel_entries_wf_l4_end_valid_at(); };
        let mut l4i = self.kernel_l4_end;
        while l4i < 512
            invariant
                (WholePageTable { higher: *self, lower: *lower }).wf(),
                forall|j: L4Index| #![trigger self.spec_resolve_mapping_l4(j)] self.kernel_l4_end <= j && pei_valid(j) ==> self.spec_resolve_mapping_l4(j) is None,
                lower.hidden_l1_tables_in_locked_windows(),
                forall|p: PageMapPtr, i: L2Index| #![trigger lower.l2_owner(p, i)] lower.l2_perms.dom().contains(p) && pei_valid(i) ==> lower.l2_owner(p, i) is None,
                pei_valid(self.kernel_l4_end),
                self.kernel_l4_end <= l4i <= 512,
                forall|j: L4Index| #![trigger self.spec_held_l4(j)] self.kernel_l4_end <= j < l4i ==> self.spec_held_l4(j) is None,
            decreases 512 - l4i,
        {
            if let Some(l4_entry) = self.get_held_entry_l4(l4i) { return self.scan_l3_table(Tracked(lower), l4i, &l4_entry); }
            l4i = l4i + 1;
        }
        proof { (WholePageTable { higher: *self, lower: *lower }).next_structure_page_eof_empty(); }
        StructureScan::Empty
    }

    /// Unlink the table page that `scan` names and return its memory; every mapping stays. The scan runs over a table whose user
    /// root entries no longer resolve, so no window exists: an L1 page leaves by clearing its unlocked L2 entry, which no CPU still
    /// lists as caching the window; an L2 page is freed whole; an L3 page carries no window lock. `window_perm` is unused.
    pub fn remove_structure_page(&mut self, Tracked(lower): Tracked<&mut PageTableLower<TABLE_TYPE>>, scan: StructureScan, cpu_tlb: &CpuTLB, cpu_arr: &CpuLockedArray,
        needflush: &PcidNeedFlushArray, Tracked(_window_perm): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<PagePerm4k>)
        requires
            (WholePageTable { higher: *old(self), lower: *old(lower) }).wf(),
            (WholePageTable { higher: *old(self), lower: *old(lower) }).structure_scan_wf(scan),
            scan.spec_table_page() is Some,
            scan is L1 ==> !old(lower).window_stale_cpus.dom().contains((scan->L1_l2_p, scan->L1_l2i)),
            scan is L2 ==> old(lower).hidden_l1_tables_in_locked_windows(),
            table_page_unreferenced_by_structure_caches(*cpu_tlb, *cpu_arr, *needflush, scan.spec_table_page()->Some_0),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            (WholePageTable { higher: *final(self), lower: *final(lower) }).wf(),
            (WholePageTable { higher: *final(self), lower: *final(lower) }).page_closure() =~= (WholePageTable { higher: *old(self), lower: *old(lower) }).page_closure().remove(scan.spec_table_page()->Some_0),
            final(lower).mapping_4k == old(lower).mapping_4k,
            final(lower).mapping_2m == old(lower).mapping_2m,
            final(self).mapping_1g == old(self).mapping_1g,
            final(self).kernel_entries == old(self).kernel_entries,
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).cr3 == old(self).cr3,
            final(self).pcid == old(self).pcid,
            final(self).did == old(self).did,
            final(self).proc_ptr == old(self).proc_ptr,
            final(self).table_stale_cpus == old(self).table_stale_cpus,
            !(scan is L2) ==> final(lower).pagetable_window_locks == old(lower).pagetable_window_locks,
            scan is L2 ==> final(lower).pagetable_window_locks == old(lower).pagetable_window_locks.remove_keys(old(lower).pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == scan->L2_l4i && spec_v2l3index(w.va) == scan->L2_l3i)),
            scan is L2 ==> final(lower).window_stale_cpus == old(lower).window_stale_cpus.filter_keys(|k: (PageMapPtr, L2Index)| k.0 != scan->L2_l2_p),
            !(scan is L2) ==> final(lower).window_stale_cpus == old(lower).window_stale_cpus,
            old(lower).hidden_l1_tables_in_locked_windows() ==> final(lower).hidden_l1_tables_in_locked_windows(),
            scan is L1 ==> *final(self) == *old(self),
            final(lower).l2_perms.dom().subset_of(old(lower).l2_perms.dom()),
            forall|p: PageMapPtr, i: L2Index| #![trigger final(lower).l2_owner(p, i)] final(lower).l2_perms.dom().contains(p) ==> final(lower).l2_owner(p, i) == old(lower).l2_owner(p, i),
            forall|l4i: L4Index| #![trigger final(self).spec_resolve_mapping_l4(l4i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && old(self).spec_resolve_mapping_l4(l4i) is None ==> final(self).spec_resolve_mapping_l4(l4i) is None,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
                #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                #![trigger (WholePageTable { higher: *old(self), lower: *old(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id) == (WholePageTable { higher: *old(self), lower: *old(lower) }).window_locked_by_thread(l4i, l3i, l2i, thread_id),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                old(self).kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i) is Some
                    ==> (WholePageTable { higher: *final(self), lower: *final(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i) == (WholePageTable { higher: *old(self), lower: *old(lower) }).spec_held_4k_l1(l4i, l3i, l2i, l1i),
            ret.view().is_init(),
            ret.view().addr() == scan.spec_table_page()->Some_0,
    {
        match scan {
            StructureScan::L1 { l4i, l3i, l2i, l2_p, l1_p } => {
                let page_map_perm = self.unlink_unresolvable_l1_page(Tracked(&mut *lower), l4i, l3i, l2i, l2_p, l1_p, Tracked(&mut *lctx));
                page_map_to_page_perm(l1_p, page_map_perm, cpu_tlb, cpu_arr, needflush)
            },
            StructureScan::L2 { l4i, l3i, l3_p, l2_p } => {
                self.remove_l3_entry(Tracked(&mut *lower), l4i, l3i, l3_p, l2_p, cpu_tlb, cpu_arr, needflush, Tracked(&mut *lctx)).1
            },
            StructureScan::L3 { l4i, l3_p } => {
                let (pg_ptr, page_map_perm) = self.remove_l4_entry(Tracked(&*lower), l4i, l3_p, Tracked(&mut *lctx));
                page_map_to_page_perm(pg_ptr, page_map_perm, cpu_tlb, cpu_arr, needflush)
            },
            _ => vstd::pervasive::unreached(),
        }
    }

    fn scan_l3_table(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, l4i: L4Index, l4_entry: &PageEntry) -> (ret: StructureScan)
        requires
            (WholePageTable { higher: *self, lower: *lower }).wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            self.spec_held_l4(l4i) =~= Some(*l4_entry),
            self.spec_resolve_mapping_l4(l4i) is None,
            lower.hidden_l1_tables_in_locked_windows(),
            forall|p: PageMapPtr, i: L2Index| #![trigger lower.l2_owner(p, i)] lower.l2_perms.dom().contains(p) && pei_valid(i) ==> lower.l2_owner(p, i) is None,
        ensures
            (WholePageTable { higher: *self, lower: *lower }).structure_scan_wf(ret),
            !(ret is Empty),
    {
        let ghost c = WholePageTable { higher: *self, lower: *lower };
        let mut l3i: L3Index = 0;
        while l3i < 512
            invariant
                c == (WholePageTable { higher: *self, lower: *lower }),
                c.wf(),
                self.kernel_l4_end <= l4i && pei_valid(l4i),
                self.spec_held_l4(l4i) =~= Some(*l4_entry),
                self.spec_resolve_mapping_l4(l4i) is None,
                lower.hidden_l1_tables_in_locked_windows(),
                forall|p: PageMapPtr, i: L2Index| #![trigger lower.l2_owner(p, i)] lower.l2_perms.dom().contains(p) && pei_valid(i) ==> lower.l2_owner(p, i) is None,
                l3i <= 512,
                forall|j: L3Index| #![trigger self.spec_held_l3(l4i, j)] j < l3i ==> self.spec_held_l3(l4i, j) is None,
            decreases 512 - l3i,
        {
            if let Some(l3_entry) = self.get_held_entry_l3(l4i, l3i, l4_entry) { return self.scan_l2_table(Tracked(lower), l4i, l3i, l4_entry, &l3_entry); }
            l3i = l3i + 1;
        }
        proof { assert(c.page_closure().contains(l4_entry.addr) && l4_entry.addr != self.cr3) by { self.wf_l4_at(l4i); self.wf_l4_cr3_at(); self.table_pages_wf_l3_at(l4_entry.addr); }; }
        StructureScan::L3 { l4i, l3_p: l4_entry.addr }
    }

    fn scan_l2_table(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, l4i: L4Index, l3i: L3Index, l4_entry: &PageEntry, l3_entry: &PageEntry) -> (ret: StructureScan)
        requires
            (WholePageTable { higher: *self, lower: *lower }).wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            self.spec_held_l4(l4i) =~= Some(*l4_entry),
            self.spec_held_l3(l4i, l3i) =~= Some(*l3_entry),
            self.spec_resolve_mapping_l4(l4i) is None,
            lower.hidden_l1_tables_in_locked_windows(),
            forall|p: PageMapPtr, i: L2Index| #![trigger lower.l2_owner(p, i)] lower.l2_perms.dom().contains(p) && pei_valid(i) ==> lower.l2_owner(p, i) is None,
        ensures
            (WholePageTable { higher: *self, lower: *lower }).structure_scan_wf(ret),
            !(ret is Empty),
    {
        let ghost c = WholePageTable { higher: *self, lower: *lower };
        proof {
            self.wf_l4_at(l4i);
            c.l3_links_l2_wf_at(l4_entry.addr, l3i);
        }
        let mut l2i: L2Index = 0;
        while l2i < 512
            invariant
                c == (WholePageTable { higher: *self, lower: *lower }),
                c.wf(),
                self.kernel_l4_end <= l4i && pei_valid(l4i),
                pei_valid(l3i),
                self.spec_held_l4(l4i) =~= Some(*l4_entry),
                self.spec_held_l3(l4i, l3i) =~= Some(*l3_entry),
                self.spec_resolve_mapping_l4(l4i) is None,
                lower.hidden_l1_tables_in_locked_windows(),
                forall|p: PageMapPtr, i: L2Index| #![trigger lower.l2_owner(p, i)] lower.l2_perms.dom().contains(p) && pei_valid(i) ==> lower.l2_owner(p, i) is None,
                lower.l2_perms.dom().contains(l3_entry.addr),
                l2i <= 512,
                forall|j: L2Index| #![trigger lower.l2_page(l3_entry.addr).entry_lock(j).l1()] j < l2i ==> lower.l2_page(l3_entry.addr).entry_lock(j).l1() is None,
            decreases 512 - l2i,
        {
            let l2_entry = self.get_l2_entry_word(Tracked(lower), l4i, l3i, l2i, l3_entry);
            if l2_entry.perm.present && !l2_entry.perm.ps {
                proof { assert(c.page_closure().contains(l2_entry.addr) && l2_entry.addr != self.cr3) by { c.wf_l2_at(l3_entry.addr, l2i); self.wf_l4_cr3_at(); c.table_pages_wf_l1_at(l2_entry.addr); }; }
                return StructureScan::L1 { l4i, l3i, l2i, l2_p: l3_entry.addr, l1_p: l2_entry.addr };
            }
            l2i = l2i + 1;
        }
        proof { assert(c.page_closure().contains(l3_entry.addr) && l3_entry.addr != self.cr3) by { self.wf_l4_cr3_at(); c.table_pages_wf_l2_at(l3_entry.addr); }; }
        StructureScan::L2 { l4i, l3i, l3_p: l4_entry.addr, l2_p: l3_entry.addr }
    }
}
} // verus!
