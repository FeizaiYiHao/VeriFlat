use vstd::prelude::*;
use crate::*;
verus! {
/// Every present BAR slot names a valid PCI function, a BAR index below 6, and a well-formed byte range.
#[verifier::opaque]
pub open spec fn pci_bar_slots_wf(bars: Map<BarKey, BarRegion>) -> bool {
    forall|bar: BarKey| #![trigger bars.contains_key(bar)]
        bars.contains_key(bar) ==> pci_bdf_valid(bar.0.0, bar.0.1, bar.0.2) && bar.1 < 6 && bars[bar].wf()
}

/// BAR pages are never kernel-managed: a page-array page in the page envelope of a BAR slot is `Unavailable` (so,
/// by `Page::inv`, it has no mapping references).
#[verifier::opaque]
pub open spec fn pci_bar_pages_unavailable_wf(bars: Map<BarKey, BarRegion>, pg_arr: PageLockedArray) -> bool {
    forall|i: PageIndex, bar: BarKey| #![trigger pg_arr.spec_index(i).view().view().state, bars.contains_key(bar)]
        index_valid(NUM_PAGES, i) && bars.contains_key(bar) && bars[bar].envelope_contains(page_index2page_ptr(i))
            ==> pg_arr.spec_index(i).view().view().state is Unavailable
}

/// The 4K page base `p` lies in the page envelope of some BAR slot of some PCI function.
pub open spec fn pci_bar_page(bars: Map<BarKey, BarRegion>, p: PAddr) -> bool {
    exists|bus: usize, device: usize, function: usize, bar: usize| #![trigger bars.contains_key(((bus, device, function), bar))]
        bars.contains_key(((bus, device, function), bar)) && bars[((bus, device, function), bar)].envelope_contains(p)
}

/// Every 4K page of the leaf span `[addr, addr + size)` is a BAR page.
pub open spec fn io_span_in_bars(bars: Map<BarKey, BarRegion>, addr: PAddr, size: usize) -> bool {
    forall|offset: int| #![trigger pci_bar_page(bars, (addr as int + offset * PAGE_SZ_4K as int) as usize)]
        0 <= offset < size as int / PAGE_SZ_4K as int ==> pci_bar_page(bars, (addr as int + offset * PAGE_SZ_4K as int) as usize)
}

/// Every IO leaf of a CPU page table (present or held) and of an IOMMU table maps BAR pages over its whole span.
#[verifier::opaque]
pub open spec fn io_mappings_wf(bars: Map<BarKey, BarRegion>, pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, it_mp: IommuTableLockedMap) -> bool {
    &&& forall|pt: RwLockPageTableRoot, va: VAddr| #![trigger whole_pagetable(pt_mp, pt_lower, pt).mapping_4k().spec_index(va)]
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).mapping_4k().contains_key(va) && whole_pagetable(pt_mp, pt_lower, pt).mapping_4k().spec_index(va).is_io
            ==> io_span_in_bars(bars, whole_pagetable(pt_mp, pt_lower, pt).mapping_4k().spec_index(va).addr, PAGE_SZ_4K)
    &&& forall|pt: RwLockPageTableRoot, va: VAddr| #![trigger whole_pagetable(pt_mp, pt_lower, pt).mapping_2m().spec_index(va)]
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).mapping_2m().contains_key(va) && whole_pagetable(pt_mp, pt_lower, pt).mapping_2m().spec_index(va).is_io
            ==> io_span_in_bars(bars, whole_pagetable(pt_mp, pt_lower, pt).mapping_2m().spec_index(va).addr, PAGE_SZ_2M)
    &&& forall|pt: RwLockPageTableRoot, va: VAddr| #![trigger whole_pagetable(pt_mp, pt_lower, pt).mapping_1g().spec_index(va)]
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).mapping_1g().contains_key(va) && whole_pagetable(pt_mp, pt_lower, pt).mapping_1g().spec_index(va).is_io
            ==> io_span_in_bars(bars, whole_pagetable(pt_mp, pt_lower, pt).mapping_1g().spec_index(va).addr, PAGE_SZ_1G)
    &&& forall|pt: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
        #![trigger whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
            && whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i) is Some && whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i)->0.perm.is_io
            ==> io_span_in_bars(bars, whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i)->0.addr, PAGE_SZ_4K)
    &&& forall|pt: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index|
        #![trigger whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(l4i, l3i, l2i)]
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
            && whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(l4i, l3i, l2i) is Some && whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(l4i, l3i, l2i)->0.perm.is_io
            ==> io_span_in_bars(bars, whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(l4i, l3i, l2i)->0.addr, PAGE_SZ_2M)
    &&& forall|pt: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index|
        #![trigger whole_pagetable(pt_mp, pt_lower, pt).spec_held_1g_l3(l4i, l3i)]
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i)
            && whole_pagetable(pt_mp, pt_lower, pt).spec_held_1g_l3(l4i, l3i) is Some && whole_pagetable(pt_mp, pt_lower, pt).spec_held_1g_l3(l4i, l3i)->0.perm.is_io
            ==> io_span_in_bars(bars, whole_pagetable(pt_mp, pt_lower, pt).spec_held_1g_l3(l4i, l3i)->0.addr, PAGE_SZ_1G)
    &&& forall|it: RwLockPageTableRoot, iova: VAddr| #![trigger it_mp.spec_index(it).view().mapping_4k().spec_index(iova)]
        it_mp.dom().contains(it) && it_mp.spec_index(it).view().mapping_4k().contains_key(iova) && it_mp.spec_index(it).view().mapping_4k().spec_index(iova).is_io
            ==> io_span_in_bars(bars, it_mp.spec_index(it).view().mapping_4k().spec_index(iova).addr, PAGE_SZ_4K)
}

/// The present BAR slot `bar` names a valid PCI function, a BAR index below 6, and a well-formed byte range.
pub proof fn pci_bar_slots_wf_at(bars: Map<BarKey, BarRegion>, bar: BarKey)
    requires pci_bar_slots_wf(bars),
    ensures bars.contains_key(bar) ==> pci_bdf_valid(bar.0.0, bar.0.1, bar.0.2) && bar.1 < 6 && bars[bar].wf(),
{ reveal(pci_bar_slots_wf); }

/// Page `i` in the page envelope of BAR slot `bar` is `Unavailable`.
pub proof fn pci_bar_pages_unavailable_wf_at(bars: Map<BarKey, BarRegion>, pg_arr: PageLockedArray, i: PageIndex, bar: BarKey)
    requires pci_bar_pages_unavailable_wf(bars, pg_arr),
    ensures
        index_valid(NUM_PAGES, i) && bars.contains_key(bar) && bars[bar].envelope_contains(page_index2page_ptr(i))
            ==> pg_arr.spec_index(i).view().view().state is Unavailable,
{ reveal(pci_bar_pages_unavailable_wf); }

/// The present IO 4K mapping `va` of page table `pt` maps a BAR page.
pub proof fn io_mappings_wf_4k_at(bars: Map<BarKey, BarRegion>, pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, it_mp: IommuTableLockedMap, pt: RwLockPageTableRoot, va: VAddr)
    requires io_mappings_wf(bars, pt_mp, pt_lower, it_mp),
    ensures
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).mapping_4k().contains_key(va) && whole_pagetable(pt_mp, pt_lower, pt).mapping_4k().spec_index(va).is_io
            ==> io_span_in_bars(bars, whole_pagetable(pt_mp, pt_lower, pt).mapping_4k().spec_index(va).addr, PAGE_SZ_4K),
{ reveal(io_mappings_wf); }

/// The present IO 2M mapping `va` of page table `pt` maps BAR pages over its whole span.
pub proof fn io_mappings_wf_2m_at(bars: Map<BarKey, BarRegion>, pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, it_mp: IommuTableLockedMap, pt: RwLockPageTableRoot, va: VAddr)
    requires io_mappings_wf(bars, pt_mp, pt_lower, it_mp),
    ensures
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).mapping_2m().contains_key(va) && whole_pagetable(pt_mp, pt_lower, pt).mapping_2m().spec_index(va).is_io
            ==> io_span_in_bars(bars, whole_pagetable(pt_mp, pt_lower, pt).mapping_2m().spec_index(va).addr, PAGE_SZ_2M),
{ reveal(io_mappings_wf); }

/// The present IO 1G mapping `va` of page table `pt` maps BAR pages over its whole span.
pub proof fn io_mappings_wf_1g_at(bars: Map<BarKey, BarRegion>, pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, it_mp: IommuTableLockedMap, pt: RwLockPageTableRoot, va: VAddr)
    requires io_mappings_wf(bars, pt_mp, pt_lower, it_mp),
    ensures
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).mapping_1g().contains_key(va) && whole_pagetable(pt_mp, pt_lower, pt).mapping_1g().spec_index(va).is_io
            ==> io_span_in_bars(bars, whole_pagetable(pt_mp, pt_lower, pt).mapping_1g().spec_index(va).addr, PAGE_SZ_1G),
{ reveal(io_mappings_wf); }

/// The held IO 4K L1 entry `(l4i, l3i, l2i, l1i)` of page table `pt` maps a BAR page.
pub proof fn io_mappings_wf_held_4k_at(
    bars: Map<BarKey, BarRegion>, pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, it_mp: IommuTableLockedMap, pt: RwLockPageTableRoot,
    l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index,
)
    requires io_mappings_wf(bars, pt_mp, pt_lower, it_mp),
    ensures
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
            && whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i) is Some && whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i)->0.perm.is_io
            ==> io_span_in_bars(bars, whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i)->0.addr, PAGE_SZ_4K),
{ reveal(io_mappings_wf); }

/// The held IO 2M L2 entry `(l4i, l3i, l2i)` of page table `pt` maps BAR pages over its whole span.
pub proof fn io_mappings_wf_held_2m_at(
    bars: Map<BarKey, BarRegion>, pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, it_mp: IommuTableLockedMap, pt: RwLockPageTableRoot,
    l4i: L4Index, l3i: L3Index, l2i: L2Index,
)
    requires io_mappings_wf(bars, pt_mp, pt_lower, it_mp),
    ensures
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
            && whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(l4i, l3i, l2i) is Some && whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(l4i, l3i, l2i)->0.perm.is_io
            ==> io_span_in_bars(bars, whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(l4i, l3i, l2i)->0.addr, PAGE_SZ_2M),
{ reveal(io_mappings_wf); }

/// The held IO 1G L3 entry `(l4i, l3i)` of page table `pt` maps BAR pages over its whole span.
pub proof fn io_mappings_wf_held_1g_at(
    bars: Map<BarKey, BarRegion>, pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, it_mp: IommuTableLockedMap, pt: RwLockPageTableRoot,
    l4i: L4Index, l3i: L3Index,
)
    requires io_mappings_wf(bars, pt_mp, pt_lower, it_mp),
    ensures
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i)
            && whole_pagetable(pt_mp, pt_lower, pt).spec_held_1g_l3(l4i, l3i) is Some && whole_pagetable(pt_mp, pt_lower, pt).spec_held_1g_l3(l4i, l3i)->0.perm.is_io
            ==> io_span_in_bars(bars, whole_pagetable(pt_mp, pt_lower, pt).spec_held_1g_l3(l4i, l3i)->0.addr, PAGE_SZ_1G),
{ reveal(io_mappings_wf); }

/// The IO 4K leaf `iova` of IOMMU table `it` maps a BAR page.
pub proof fn io_mappings_wf_iommu_4k_at(bars: Map<BarKey, BarRegion>, pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, it_mp: IommuTableLockedMap, it: RwLockPageTableRoot, iova: VAddr)
    requires io_mappings_wf(bars, pt_mp, pt_lower, it_mp),
    ensures
        it_mp.dom().contains(it) && it_mp.spec_index(it).view().mapping_4k().contains_key(iova) && it_mp.spec_index(it).view().mapping_4k().spec_index(iova).is_io
            ==> io_span_in_bars(bars, it_mp.spec_index(it).view().mapping_4k().spec_index(iova).addr, PAGE_SZ_4K),
{ reveal(io_mappings_wf); }
}
