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

/// The 2M chunk at `addr` belongs to function `f`: it is 2M-aligned and lies wholly in the entry chosen for its first page,
/// which is `f`'s (BARs are byte-disjoint, so that entry is the BAR that holds the whole chunk).
pub open spec fn pci_bar_2m_chunk_of(bars: Seq<PciBarEntry>, addr: PAddr, f: PciBdf) -> bool {
    let e = pci_bar_entry_of_page(bars, addr);
    &&& addr % PAGE_SZ_2M == 0
    &&& e is Some
    &&& bars[e->0].bdf == f
    &&& addr as int + PAGE_SZ_2M as int <= bars[e->0].base as int + bars[e->0].size as int
}

/// Each page table's PCI function array records exactly its IO leaves. A recorded BAR mapping `(va, size)` of function `f` is
/// a 4K or 2M user key of the table whose held leaf is an IO leaf mapping a page of a BAR of `f` (4K) or a 2M chunk of one BAR
/// of `f` (2M); every held IO 4K or 2M user leaf is recorded under the function of its target.
#[verifier::opaque]
pub open spec fn pagetable_pci_mappings_wf(bars: Seq<PciBarEntry>, pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap) -> bool {
    &&& forall|pt: RwLockPageTableRoot, f: PciBdf, m: PciBarMapping| #![trigger whole_pagetable(pt_mp, pt_lower, pt).higher.pci.view()[f].contains(m)]
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).higher.pci.view().dom().contains(f) && whole_pagetable(pt_mp, pt_lower, pt).higher.pci.view()[f].contains(m) ==> {
            let c = whole_pagetable(pt_mp, pt_lower, pt);
            &&& !(m.1 is SZ1g)
            &&& m.1 is SZ4k ==> va_4k_valid(m.0) && c.kernel_l4_end() <= spec_v2l4index(m.0)
                && c.spec_held_4k_l1(spec_v2l4index(m.0), spec_v2l3index(m.0), spec_v2l2index(m.0), spec_v2l1index(m.0)) is Some
                && c.spec_held_4k_l1(spec_v2l4index(m.0), spec_v2l3index(m.0), spec_v2l2index(m.0), spec_v2l1index(m.0))->0.perm.is_io
                && pci_bar_function_of_page(bars, c.spec_held_4k_l1(spec_v2l4index(m.0), spec_v2l3index(m.0), spec_v2l2index(m.0), spec_v2l1index(m.0))->0.addr) == Some(f)
            &&& m.1 is SZ2m ==> va_2m_valid(m.0) && c.kernel_l4_end() <= spec_v2l4index(m.0)
                && c.spec_held_2m_l2(spec_v2l4index(m.0), spec_v2l3index(m.0), spec_v2l2index(m.0)) is Some
                && c.spec_held_2m_l2(spec_v2l4index(m.0), spec_v2l3index(m.0), spec_v2l2index(m.0))->0.perm.is_io
                && pci_bar_2m_chunk_of(bars, c.spec_held_2m_l2(spec_v2l4index(m.0), spec_v2l3index(m.0), spec_v2l2index(m.0))->0.addr, f)
        }
    &&& forall|pt: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
        #![trigger whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
            && whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i) is Some && whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i)->0.perm.is_io ==> {
            let f = pci_bar_function_of_page(bars, whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i)->0.addr);
            &&& f is Some
            &&& whole_pagetable(pt_mp, pt_lower, pt).higher.pci.view().dom().contains(f->0)
            &&& whole_pagetable(pt_mp, pt_lower, pt).higher.pci.view()[f->0].contains((spec_index2va((l4i, l3i, l2i, l1i)), PageSize::SZ4k))
        }
    &&& forall|pt: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(l4i, l3i, l2i)]
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
            && whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(l4i, l3i, l2i) is Some && whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(l4i, l3i, l2i)->0.perm.is_io ==> {
            let f = pci_bar_function_of_page(bars, whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(l4i, l3i, l2i)->0.addr);
            &&& f is Some
            &&& pci_bar_2m_chunk_of(bars, whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(l4i, l3i, l2i)->0.addr, f->0)
            &&& whole_pagetable(pt_mp, pt_lower, pt).higher.pci.view().dom().contains(f->0)
            &&& whole_pagetable(pt_mp, pt_lower, pt).higher.pci.view()[f->0].contains((spec_index2va((l4i, l3i, l2i, 0)), PageSize::SZ2m))
        }
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

/// The recorded BAR mapping `m` of function `f` in page table `pt` is a held IO leaf of `pt` at `m`'s key mapping a page (4K) or
/// a 2M chunk (2M) of a BAR of `f`.
pub proof fn pagetable_pci_mappings_wf_mapping_at(bars: Seq<PciBarEntry>, pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pt: RwLockPageTableRoot, f: PciBdf, m: PciBarMapping)
    requires pagetable_pci_mappings_wf(bars, pt_mp, pt_lower),
    ensures
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).higher.pci.view().dom().contains(f) && whole_pagetable(pt_mp, pt_lower, pt).higher.pci.view()[f].contains(m) ==> {
            let c = whole_pagetable(pt_mp, pt_lower, pt);
            &&& !(m.1 is SZ1g)
            &&& m.1 is SZ4k ==> va_4k_valid(m.0) && c.kernel_l4_end() <= spec_v2l4index(m.0)
                && c.spec_held_4k_l1(spec_v2l4index(m.0), spec_v2l3index(m.0), spec_v2l2index(m.0), spec_v2l1index(m.0)) is Some
                && c.spec_held_4k_l1(spec_v2l4index(m.0), spec_v2l3index(m.0), spec_v2l2index(m.0), spec_v2l1index(m.0))->0.perm.is_io
                && pci_bar_function_of_page(bars, c.spec_held_4k_l1(spec_v2l4index(m.0), spec_v2l3index(m.0), spec_v2l2index(m.0), spec_v2l1index(m.0))->0.addr) == Some(f)
            &&& m.1 is SZ2m ==> va_2m_valid(m.0) && c.kernel_l4_end() <= spec_v2l4index(m.0)
                && c.spec_held_2m_l2(spec_v2l4index(m.0), spec_v2l3index(m.0), spec_v2l2index(m.0)) is Some
                && c.spec_held_2m_l2(spec_v2l4index(m.0), spec_v2l3index(m.0), spec_v2l2index(m.0))->0.perm.is_io
                && pci_bar_2m_chunk_of(bars, c.spec_held_2m_l2(spec_v2l4index(m.0), spec_v2l3index(m.0), spec_v2l2index(m.0))->0.addr, f)
        },
{ reveal(pagetable_pci_mappings_wf); }

/// The held IO 4K leaf `(l4i, l3i, l2i, l1i)` of page table `pt` maps a BAR page and is recorded under that page's function.
pub proof fn pagetable_pci_mappings_wf_held_4k_at(
    bars: Seq<PciBarEntry>, pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pt: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index,
)
    requires pagetable_pci_mappings_wf(bars, pt_mp, pt_lower),
    ensures
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
            && whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i) is Some && whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i)->0.perm.is_io ==> {
            let f = pci_bar_function_of_page(bars, whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i)->0.addr);
            &&& f is Some
            &&& whole_pagetable(pt_mp, pt_lower, pt).higher.pci.view().dom().contains(f->0)
            &&& whole_pagetable(pt_mp, pt_lower, pt).higher.pci.view()[f->0].contains((spec_index2va((l4i, l3i, l2i, l1i)), PageSize::SZ4k))
        },
{ reveal(pagetable_pci_mappings_wf); }

/// The held IO 2M leaf `(l4i, l3i, l2i)` of page table `pt` maps a 2M chunk of one BAR and is recorded under that BAR's function.
pub proof fn pagetable_pci_mappings_wf_held_2m_at(
    bars: Seq<PciBarEntry>, pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pt: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index,
)
    requires pagetable_pci_mappings_wf(bars, pt_mp, pt_lower),
    ensures
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
            && whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(l4i, l3i, l2i) is Some && whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(l4i, l3i, l2i)->0.perm.is_io ==> {
            let f = pci_bar_function_of_page(bars, whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(l4i, l3i, l2i)->0.addr);
            &&& f is Some
            &&& pci_bar_2m_chunk_of(bars, whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(l4i, l3i, l2i)->0.addr, f->0)
            &&& whole_pagetable(pt_mp, pt_lower, pt).higher.pci.view().dom().contains(f->0)
            &&& whole_pagetable(pt_mp, pt_lower, pt).higher.pci.view()[f->0].contains((spec_index2va((l4i, l3i, l2i, 0)), PageSize::SZ2m))
        },
{ reveal(pagetable_pci_mappings_wf); }
}
