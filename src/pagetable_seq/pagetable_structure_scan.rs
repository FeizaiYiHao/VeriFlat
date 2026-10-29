use vstd::prelude::*;

verus! {
use super::entry::*;
use super::pagetable_spec::*;
use super::pagemap::*;
use crate::*;
use vstd::simple_pptr::*;

/// A table page that a page table can unlink bottom-up, or why it has none.
#[derive(Clone, Copy)]
pub enum StructureScan {
    /// The L1 table `l1_p`, linked from entry `l2i` of the L2 table `l2_p` at `(l4i, l3i)`, records no 4K leaf.
    L1 { l4i: L4Index, l3i: L3Index, l2i: L2Index, l2_p: PageMapPtr, l1_p: PageMapPtr },
    /// The L2 table `l2_p`, linked from entry `l3i` of the L3 table `l3_p` at `l4i`, links nothing.
    L2 { l4i: L4Index, l3i: L3Index, l3_p: PageMapPtr, l2_p: PageMapPtr },
    /// The L3 table `l3_p`, linked from the user L4 entry `l4i`, links nothing.
    L3 { l4i: L4Index, l3_p: PageMapPtr },
    /// No user L4 entry is present, so the root is the only table page.
    Empty,
    /// A leaf is recorded, so no table page can be unlinked.
    Blocked,
}

impl StructureScan {
    /// The table page the scan names, if any.
    pub open spec fn spec_table_page(&self) -> Option<PageMapPtr> {
        match *self {
            StructureScan::L1 { l1_p, .. } => Some(l1_p),
            StructureScan::L2 { l2_p, .. } => Some(l2_p),
            StructureScan::L3 { l3_p, .. } => Some(l3_p),
            _ => None,
        }
    }

    /// The table page the scan names, if any.
    #[verifier::when_used_as_spec(spec_table_page)]
    pub fn table_page(&self) -> (ret: Option<PageMapPtr>)
        ensures ret == self.spec_table_page(),
    {
        match self {
            StructureScan::L1 { l1_p, .. } => Some(*l1_p),
            StructureScan::L2 { l2_p, .. } => Some(*l2_p),
            StructureScan::L3 { l3_p, .. } => Some(*l3_p),
            _ => None,
        }
    }
}

impl<const TABLE_TYPE: PTType> PageTable<TABLE_TYPE> {
    /// `scan` names a table page that the matching `remove_l*_entry` can unlink, or reports that no user L4 entry is present.
    pub open spec fn spec_structure_scan_wf(&self, scan: StructureScan) -> bool {
        match scan {
            StructureScan::L1 { l4i, l3i, l2i, l2_p, l1_p } => {
                &&& self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                &&& self.spec_resolve_mapping_l3(l4i, l3i) is Some && self.spec_resolve_mapping_l3(l4i, l3i)->0.addr == l2_p
                &&& self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some && self.spec_resolve_mapping_l2(l4i, l3i, l2i)->0.addr == l1_p
                &&& forall|i: L1Index| #![trigger self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, i)] pei_valid(i) ==> self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, i) is None
                &&& self.page_closure().contains(l1_p) && l1_p != self.cr3
            },
            StructureScan::L2 { l4i, l3i, l3_p, l2_p } => {
                &&& self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i)
                &&& self.spec_resolve_mapping_l4(l4i) is Some && self.spec_resolve_mapping_l4(l4i)->0.addr == l3_p
                &&& self.spec_resolve_mapping_l3(l4i, l3i) is Some && self.spec_resolve_mapping_l3(l4i, l3i)->0.addr == l2_p
                &&& forall|i: L2Index| #![trigger self.spec_resolve_mapping_l2(l4i, l3i, i)] pei_valid(i) ==> self.spec_resolve_mapping_l2(l4i, l3i, i) is None
                &&& forall|i: L2Index| #![trigger self.spec_resolve_mapping_2m_l2(l4i, l3i, i)] pei_valid(i) ==> self.spec_resolve_mapping_2m_l2(l4i, l3i, i) is None
                &&& self.page_closure().contains(l2_p) && l2_p != self.cr3
            },
            StructureScan::L3 { l4i, l3_p } => {
                &&& self.kernel_l4_end <= l4i && pei_valid(l4i)
                &&& self.spec_resolve_mapping_l4(l4i) is Some && self.spec_resolve_mapping_l4(l4i)->0.addr == l3_p
                &&& forall|i: L3Index| #![trigger self.spec_resolve_mapping_l3(l4i, i)] pei_valid(i) ==> self.spec_resolve_mapping_l3(l4i, i) is None
                &&& forall|i: L3Index| #![trigger self.spec_resolve_mapping_1g_l3(l4i, i)] pei_valid(i) ==> self.spec_resolve_mapping_1g_l3(l4i, i) is None
                &&& self.page_closure().contains(l3_p) && l3_p != self.cr3
            },
            StructureScan::Empty => {
                &&& forall|l4i: L4Index| #![trigger self.spec_resolve_mapping_l4(l4i)] self.kernel_l4_end <= l4i && pei_valid(l4i) ==> self.spec_resolve_mapping_l4(l4i) is None
                &&& self.page_closure() =~= set![self.cr3]
                &&& self.kernel_l4_end <= KERNEL_MEM_END_L4INDEX ==> self.mapping_4k().dom() =~= Set::<VAddr>::empty()
                &&& self.kernel_l4_end <= KERNEL_MEM_END_L4INDEX ==> self.mapping_2m().dom() =~= Set::<VAddr>::empty()
                &&& self.kernel_l4_end <= KERNEL_MEM_END_L4INDEX ==> self.mapping_1g().dom() =~= Set::<VAddr>::empty()
            },
            StructureScan::Blocked => true,
        }
    }

    /// Find the first table page, in index order below the first present user L4 entry, that can be unlinked.
    pub fn next_structure_page(&self) -> (ret: StructureScan)
        requires self.wf(),
        ensures
            self.spec_structure_scan_wf(ret),
            self.mapping_4k().dom() =~= Set::<VAddr>::empty() && self.mapping_2m().dom() =~= Set::<VAddr>::empty() && self.mapping_1g().dom() =~= Set::<VAddr>::empty() ==> !(ret is Blocked),
    {
        proof { self.kernel_l4_end_valid(); }
        let mut l4i = self.kernel_l4_end;
        while l4i < 512
            invariant
                self.wf(),
                pei_valid(self.kernel_l4_end),
                self.kernel_l4_end <= l4i <= 512,
                forall|j: L4Index| #![trigger self.spec_resolve_mapping_l4(j)] self.kernel_l4_end <= j < l4i ==> self.spec_resolve_mapping_l4(j) is None,
            decreases 512 - l4i,
        {
            if let Some(l4_entry) = self.get_entry_l4(l4i) {
                return self.scan_l3_table(l4i, &l4_entry);
            }
            l4i = l4i + 1;
        }
        proof { self.next_structure_page_eof_empty(); }
        StructureScan::Empty
    }

    /// Unlink the table page that `scan` names and return its memory; every mapping stays.
    pub fn remove_structure_page(&mut self, scan: StructureScan, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<PointsTo<PageMap>>)
        requires
            old(self).wf(),
            old(self).spec_structure_scan_wf(scan),
            scan.spec_table_page() is Some,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            final(self).wf(),
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).page_closure() =~= old(self).page_closure().remove(scan.spec_table_page()->Some_0),
            final(self).mapping_4k() =~= old(self).mapping_4k(),
            final(self).mapping_2m() =~= old(self).mapping_2m(),
            final(self).mapping_1g() =~= old(self).mapping_1g(),
            final(self).kernel_entries =~= old(self).kernel_entries,
            final(self).cr3 == old(self).cr3,
            final(self).pcid == old(self).pcid,
            final(self).did == old(self).did,
            final(self).proc_ptr == old(self).proc_ptr,
            ret.view().is_init(),
            ret.view().addr() == scan.spec_table_page()->Some_0,
    {
        match scan {
            StructureScan::L1 { l4i, l3i, l2i, l2_p, l1_p } => self.remove_l2_entry(l4i, l3i, l2i, l2_p, l1_p, Tracked(&mut *lctx)).1,
            StructureScan::L2 { l4i, l3i, l3_p, l2_p } => self.remove_l3_entry(l4i, l3i, l3_p, l2_p, Tracked(&mut *lctx)).1,
            StructureScan::L3 { l4i, l3_p } => self.remove_l4_entry(l4i, l3_p, Tracked(&mut *lctx)).1,
            _ => vstd::pervasive::unreached(),
        }
    }

    fn scan_l3_table(&self, l4i: L4Index, l4_entry: &PageEntry) -> (ret: StructureScan)
        requires
            self.wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            self.spec_resolve_mapping_l4(l4i) =~= Some(*l4_entry),
        ensures
            self.spec_structure_scan_wf(ret),
            !(ret is Empty),
            self.mapping_4k().dom() =~= Set::<VAddr>::empty() && self.mapping_2m().dom() =~= Set::<VAddr>::empty() && self.mapping_1g().dom() =~= Set::<VAddr>::empty() ==> !(ret is Blocked),
    {
        let mut l3i: L3Index = 0;
        while l3i < 512
            invariant
                self.wf(),
                self.kernel_l4_end <= l4i && pei_valid(l4i),
                self.spec_resolve_mapping_l4(l4i) =~= Some(*l4_entry),
                l3i <= 512,
                forall|j: L3Index| #![trigger self.spec_resolve_mapping_l3(l4i, j)] j < l3i ==> self.spec_resolve_mapping_l3(l4i, j) is None,
                forall|j: L3Index| #![trigger self.spec_resolve_mapping_1g_l3(l4i, j)] j < l3i ==> self.spec_resolve_mapping_1g_l3(l4i, j) is None,
            decreases 512 - l3i,
        {
            if self.get_entry_1g_l3(l4i, l3i, l4_entry).is_some() {
                proof { assert(self.mapping_1g().dom().contains(spec_index2va((l4i, l3i, 0, 0)))) by { reveal(PageTable::wf_mapping_1g); }; }
                return StructureScan::Blocked;
            }
            if let Some(l3_entry) = self.get_entry_l3(l4i, l3i, l4_entry) {
                return self.scan_l2_table(l4i, l3i, l4_entry, &l3_entry);
            }
            l3i = l3i + 1;
        }
        proof { assert(self.page_closure().contains(l4_entry.addr) && l4_entry.addr != self.cr3) by { reveal(PageTable::wf_l4); self.table_pages_wf_l3_at(l4_entry.addr); }; }
        StructureScan::L3 { l4i, l3_p: l4_entry.addr }
    }

    fn scan_l2_table(&self, l4i: L4Index, l3i: L3Index, l4_entry: &PageEntry, l3_entry: &PageEntry) -> (ret: StructureScan)
        requires
            self.wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            self.spec_resolve_mapping_l4(l4i) =~= Some(*l4_entry),
            self.spec_resolve_mapping_l3(l4i, l3i) =~= Some(*l3_entry),
        ensures
            self.spec_structure_scan_wf(ret),
            !(ret is Empty),
            self.mapping_4k().dom() =~= Set::<VAddr>::empty() && self.mapping_2m().dom() =~= Set::<VAddr>::empty() && self.mapping_1g().dom() =~= Set::<VAddr>::empty() ==> !(ret is Blocked),
    {
        let mut l2i: L2Index = 0;
        while l2i < 512
            invariant
                self.wf(),
                self.kernel_l4_end <= l4i && pei_valid(l4i),
                pei_valid(l3i),
                self.spec_resolve_mapping_l4(l4i) =~= Some(*l4_entry),
                self.spec_resolve_mapping_l3(l4i, l3i) =~= Some(*l3_entry),
                l2i <= 512,
                forall|j: L2Index| #![trigger self.spec_resolve_mapping_l2(l4i, l3i, j)] j < l2i ==> self.spec_resolve_mapping_l2(l4i, l3i, j) is None,
                forall|j: L2Index| #![trigger self.spec_resolve_mapping_2m_l2(l4i, l3i, j)] j < l2i ==> self.spec_resolve_mapping_2m_l2(l4i, l3i, j) is None,
            decreases 512 - l2i,
        {
            if self.get_entry_2m_l2(l4i, l3i, l2i, l3_entry).is_some() {
                proof { assert(self.mapping_2m().dom().contains(spec_index2va((l4i, l3i, l2i, 0)))) by { reveal(PageTable::wf_mapping_2m); }; }
                return StructureScan::Blocked;
            }
            if let Some(l2_entry) = self.get_entry_l2(l4i, l3i, l2i, l3_entry) {
                if self.l1_table_has_no_leaf(l4i, l3i, l2i, &l2_entry) {
                    proof { assert(self.page_closure().contains(l2_entry.addr) && l2_entry.addr != self.cr3) by { reveal(PageTable::wf_l4); reveal(PageTable::wf_l3); reveal(PageTable::wf_l2); self.table_pages_wf_l1_at(l2_entry.addr); }; }
                    return StructureScan::L1 { l4i, l3i, l2i, l2_p: l3_entry.addr, l1_p: l2_entry.addr };
                }
                return StructureScan::Blocked;
            }
            l2i = l2i + 1;
        }
        proof { assert(self.page_closure().contains(l3_entry.addr) && l3_entry.addr != self.cr3) by { reveal(PageTable::wf_l4); reveal(PageTable::wf_l3); self.table_pages_wf_l2_at(l3_entry.addr); }; }
        StructureScan::L2 { l4i, l3i, l3_p: l4_entry.addr, l2_p: l3_entry.addr }
    }

    fn l1_table_has_no_leaf(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index, l2_entry: &PageEntry) -> (ret: bool)
        requires
            self.wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            self.spec_resolve_mapping_l2(l4i, l3i, l2i) =~= Some(*l2_entry),
        ensures
            ret ==> forall|i: L1Index| #![trigger self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, i)] pei_valid(i) ==> self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, i) is None,
            self.mapping_4k().dom() =~= Set::<VAddr>::empty() ==> ret,
    {
        let mut l1i: L1Index = 0;
        while l1i < 512
            invariant
                self.wf(),
                self.kernel_l4_end <= l4i && pei_valid(l4i),
                pei_valid(l3i),
                pei_valid(l2i),
                self.spec_resolve_mapping_l2(l4i, l3i, l2i) =~= Some(*l2_entry),
                l1i <= 512,
                forall|j: L1Index| #![trigger self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, j)] j < l1i ==> self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, j) is None,
            decreases 512 - l1i,
        {
            if self.get_entry_l1(l4i, l3i, l2i, l1i, l2_entry).is_some() {
                proof { assert(self.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))) by { reveal(PageTable::wf_mapping_4k); }; }
                return false;
            }
            l1i = l1i + 1;
        }
        true
    }
}
} // verus!
