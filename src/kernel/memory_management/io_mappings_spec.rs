use vstd::prelude::*;
use crate::*;
verus! {
/// The BAR table fits its storage, every entry is well formed, BARs whose page envelopes share a page belong to the same
/// PCI function, and any two distinct entries are byte-disjoint.
#[verifier::opaque]
pub open spec fn pci_bar_table_wf(bars: Seq<PciBarEntry>) -> bool {
    &&& bars.len() <= PCI_BAR_TABLE_CAPACITY
    &&& forall|i: int| #![trigger bars[i]] 0 <= i < bars.len() ==> bars[i].wf()
    &&& forall|i: int, j: int, p: PAddr| #![trigger bars[i].envelope_contains(p), bars[j].envelope_contains(p)]
        0 <= i < bars.len() && 0 <= j < bars.len() && bars[i].envelope_contains(p) && bars[j].envelope_contains(p) ==> bars[i].bdf == bars[j].bdf
    &&& forall|i: int, j: int| #![trigger bars[i], bars[j]]
        0 <= i < bars.len() && 0 <= j < bars.len() && i != j
            ==> bars[i].base as int + bars[i].size as int <= bars[j].base as int || bars[j].base as int + bars[j].size as int <= bars[i].base as int
}

/// The index of an entry of `bars` whose page envelope contains the 4K page base `p`, if any.
pub open spec fn pci_bar_entry_of_page(bars: Seq<PciBarEntry>, p: PAddr) -> Option<int> {
    let i = choose|i: int| 0 <= i < bars.len() && #[trigger] bars[i].envelope_contains(p);
    if 0 <= i < bars.len() && bars[i].envelope_contains(p) { Some(i) } else { None }
}

/// The 4K page base `p` lies in the page envelope of some BAR.
pub open spec fn pci_bar_page(bars: Seq<PciBarEntry>, p: PAddr) -> bool { pci_bar_entry_of_page(bars, p) is Some }

/// The PCI function whose BAR envelope contains the 4K page base `p`, if any.
pub open spec fn pci_bar_function_of_page(bars: Seq<PciBarEntry>, p: PAddr) -> Option<PciBdf> {
    match pci_bar_entry_of_page(bars, p) { Some(i) => Some(bars[i].bdf), None => None }
}

/// BAR pages are never kernel-managed: a page-array page in the page envelope of some BAR is `Unavailable` (so,
/// by `Page::inv`, it has no mapping references).
#[verifier::opaque]
pub open spec fn pci_bar_pages_unavailable_wf(bars: Seq<PciBarEntry>, pg_arr: PageLockedArray) -> bool {
    forall|i: PageIndex| #![trigger pg_arr.spec_index(i).view().view().state] #![trigger pci_bar_page(bars, page_index2page_ptr(i))]
        index_valid(NUM_PAGES, i) && pci_bar_page(bars, page_index2page_ptr(i)) ==> pg_arr.spec_index(i).view().view().state is Unavailable
}

/// Every 4K page of the leaf span `[addr, addr + size)` is a BAR page.
pub open spec fn io_span_in_bars(bars: Seq<PciBarEntry>, addr: PAddr, size: usize) -> bool {
    forall|offset: int| #![trigger pci_bar_page(bars, (addr as int + offset * PAGE_SZ_4K as int) as usize)]
        0 <= offset < size as int / PAGE_SZ_4K as int ==> pci_bar_page(bars, (addr as int + offset * PAGE_SZ_4K as int) as usize)
}

/// Every IO leaf of a CPU page table (present or held) maps BAR pages over its whole span.
#[verifier::opaque]
pub open spec fn io_mappings_wf(bars: Seq<PciBarEntry>, pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap) -> bool {
    &&& forall|pt: RwLockPageTableRoot, va: VAddr| #![trigger whole_pagetable(pt_mp, pt_lower, pt).mapping_4k().spec_index(va)]
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).mapping_4k().contains_key(va) && whole_pagetable(pt_mp, pt_lower, pt).mapping_4k().spec_index(va).is_io
            ==> pci_bar_page(bars, whole_pagetable(pt_mp, pt_lower, pt).mapping_4k().spec_index(va).addr)
    &&& forall|pt: RwLockPageTableRoot, va: VAddr| #![trigger whole_pagetable(pt_mp, pt_lower, pt).mapping_2m().spec_index(va)]
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).mapping_2m().contains_key(va) && whole_pagetable(pt_mp, pt_lower, pt).mapping_2m().spec_index(va).is_io
            ==> io_span_in_bars(bars, whole_pagetable(pt_mp, pt_lower, pt).mapping_2m().spec_index(va).addr, PAGE_SZ_2M)
    &&& forall|pt: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
        #![trigger whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
            && whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i) is Some && whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i)->0.perm.is_io
            ==> pci_bar_page(bars, whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i)->0.addr)
    &&& forall|pt: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index|
        #![trigger whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(l4i, l3i, l2i)]
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
            && whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(l4i, l3i, l2i) is Some && whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(l4i, l3i, l2i)->0.perm.is_io
            ==> io_span_in_bars(bars, whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(l4i, l3i, l2i)->0.addr, PAGE_SZ_2M)
}

/// Entries `i` and `j` of the BAR table and the page `p`: the table fits its storage, entry `i` is well formed, `i` and
/// `j` belong to the same PCI function when both envelopes contain `p`, and are byte-disjoint when distinct.
pub proof fn pci_bar_table_wf_at(bars: Seq<PciBarEntry>, i: int, j: int, p: PAddr)
    requires pci_bar_table_wf(bars),
    ensures
        bars.len() <= PCI_BAR_TABLE_CAPACITY,
        0 <= i < bars.len() ==> bars[i].wf(),
        0 <= i < bars.len() && 0 <= j < bars.len() && bars[i].envelope_contains(p) && bars[j].envelope_contains(p) ==> bars[i].bdf == bars[j].bdf,
        0 <= i < bars.len() && 0 <= j < bars.len() && i != j
            ==> bars[i].base as int + bars[i].size as int <= bars[j].base as int || bars[j].base as int + bars[j].size as int <= bars[i].base as int,
{ reveal(pci_bar_table_wf); }

/// Page `i` in the page envelope of some BAR is `Unavailable`.
pub proof fn pci_bar_pages_unavailable_wf_at(bars: Seq<PciBarEntry>, pg_arr: PageLockedArray, i: PageIndex)
    requires pci_bar_pages_unavailable_wf(bars, pg_arr), index_valid(NUM_PAGES, i),
    ensures pci_bar_page(bars, page_index2page_ptr(i)) ==> pg_arr.spec_index(i).view().view().state is Unavailable,
{ reveal(pci_bar_pages_unavailable_wf); }

/// The present IO 4K mapping `va` of page table `pt` maps a BAR page.
pub proof fn io_mappings_wf_4k_at(bars: Seq<PciBarEntry>, pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pt: RwLockPageTableRoot, va: VAddr)
    requires io_mappings_wf(bars, pt_mp, pt_lower),
    ensures
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).mapping_4k().contains_key(va) && whole_pagetable(pt_mp, pt_lower, pt).mapping_4k().spec_index(va).is_io
            ==> pci_bar_page(bars, whole_pagetable(pt_mp, pt_lower, pt).mapping_4k().spec_index(va).addr),
{ reveal(io_mappings_wf); }

/// The present IO 2M mapping `va` of page table `pt` maps BAR pages over its whole span.
pub proof fn io_mappings_wf_2m_at(bars: Seq<PciBarEntry>, pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pt: RwLockPageTableRoot, va: VAddr)
    requires io_mappings_wf(bars, pt_mp, pt_lower),
    ensures
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).mapping_2m().contains_key(va) && whole_pagetable(pt_mp, pt_lower, pt).mapping_2m().spec_index(va).is_io
            ==> io_span_in_bars(bars, whole_pagetable(pt_mp, pt_lower, pt).mapping_2m().spec_index(va).addr, PAGE_SZ_2M),
{ reveal(io_mappings_wf); }

/// The held IO 4K L1 entry `(l4i, l3i, l2i, l1i)` of page table `pt` maps a BAR page.
pub proof fn io_mappings_wf_held_4k_at(
    bars: Seq<PciBarEntry>, pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pt: RwLockPageTableRoot,
    l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index,
)
    requires io_mappings_wf(bars, pt_mp, pt_lower),
    ensures
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
            && whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i) is Some && whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i)->0.perm.is_io
            ==> pci_bar_page(bars, whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i)->0.addr),
{ reveal(io_mappings_wf); }

/// The held IO 2M L2 entry `(l4i, l3i, l2i)` of page table `pt` maps BAR pages over its whole span.
pub proof fn io_mappings_wf_held_2m_at(
    bars: Seq<PciBarEntry>, pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pt: RwLockPageTableRoot,
    l4i: L4Index, l3i: L3Index, l2i: L2Index,
)
    requires io_mappings_wf(bars, pt_mp, pt_lower),
    ensures
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
            && whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(l4i, l3i, l2i) is Some && whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(l4i, l3i, l2i)->0.perm.is_io
            ==> io_span_in_bars(bars, whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(l4i, l3i, l2i)->0.addr, PAGE_SZ_2M),
{ reveal(io_mappings_wf); }
}
