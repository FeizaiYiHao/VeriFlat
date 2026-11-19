use vstd::prelude::*;
use core::marker::ConstParamTy;
verus! {
use crate::*;
use vstd::simple_pptr::*;
use super::pagemap_util_t::*;
use super::entry::*;
use super::pagemap::*;

/// Mapping keys are CPU virtual addresses for ordinary page tables and IOVAs
/// for VT-d second-level tables.  In particular, an IOMMU mapping may use L4
/// index zero; only its page-size alignment is constrained by the IOVA model.
pub open spec fn page_table_key_4k_valid<const TABLE_TYPE: PTType>(addr: usize) -> bool {
    if TABLE_TYPE == PT_TYPE { va_4k_valid(addr) } else { iova_4k_valid(addr) }
}

pub open spec fn page_table_key_2m_valid<const TABLE_TYPE: PTType>(addr: usize) -> bool {
    if TABLE_TYPE == PT_TYPE { va_2m_valid(addr) } else { iova_2m_valid(addr) }
}

pub open spec fn page_table_key_1g_valid<const TABLE_TYPE: PTType>(addr: usize) -> bool {
    if TABLE_TYPE == PT_TYPE { va_1g_valid(addr) } else { iova_1g_valid(addr) }
}

/// mapping_xx is the abstract mappings of each page size.
/// if an entry exists in mapping_xx.dom(), the entry is visible to the kernel at least.
/// if the entry has present flag set, it's visible to the page table walk.
/// our TLB spec will be that the TLB is `always` a subset of kernel view. Regardless the locking state of the page table.
/// `l3_rev_map`, `l2_rev_map` and `l1_rev_map` give, for each L3, L2 and L1 page, the path of the entry that links it.
/// `kernel_entries` are the root's kernel L4 entries `[0, kernel_l4_end)`; the user L4 entries start at `kernel_l4_end`.
///
/// The concrete PointsTo maps are public only because Verus public open specs
/// need representation visibility. They are not an executable mutation API;
/// published writes must use the phase-checked PageTable operations. A future
/// opaque-view/typestate split is needed before Rust privacy can enforce this.
pub struct PageTable<const TABLE_TYPE: PTType> {
    pub cr3: PageTableRoot,
    pub pcid: Option<Pcid>,
    pub did: Option<VtdDomainId>,
    pub kernel_l4_end: usize,
    pub l4_table: Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    pub l3_rev_map: Ghost<Map<PageMapPtr, (L4Index)>>,
    pub l3_tables: Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    pub l2_rev_map: Ghost<Map<PageMapPtr, (L4Index, L3Index)>>,
    pub l2_tables: Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    pub l1_rev_map: Ghost<Map<PageMapPtr, (L4Index, L3Index, L2Index)>>,
    pub l1_tables: Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    pub mapping_4k: Ghost<Map<VAddr, MapEntry>>,
    pub mapping_2m: Ghost<Map<VAddr, MapEntry>>,
    pub mapping_1g: Ghost<Map<VAddr, MapEntry>>,
    pub kernel_entries: Ghost<Seq<PageEntry>>,
    pub proc_ptr: RwLockProcessPtr
}

/// The page-table mappings, VT-d domain id, and outer lock mode visible through a process.
///
/// Directory topology, backing page-map pages, CR3/PCID bookkeeping, and the
/// owning process pointer are kernel implementation state. A CPU table never has a domain id.  Publishing or
/// removing an abstract mapping changes this view; preparing an empty walk
/// does not. `pagetable_window_locks` holds the lock mode of every 2M window of an existing L2 page of a split CPU
/// table; it is empty for an IOMMU table.
pub ghost struct PageTableU {
    pub lock_state: LockStateU,
    pub did: Option<VtdDomainId>,
    pub mapping_4k: Map<VAddr, MapEntry>,
    pub mapping_2m: Map<VAddr, MapEntry>,
    pub mapping_1g: Map<VAddr, MapEntry>,
    pub pagetable_window_locks: Map<WindowVa, LockStateU>,
    /// Each PCI function the process owns, with its number of BAR mappings; empty for an IOMMU table.
    pub pci_functions: Map<PciBdf, nat>,
}

/// `m` with every window of `range` that it holds write-locked.
pub open spec fn pagetable_window_locks_after_locking_range(m: Map<WindowVa, LockStateU>, range: VaRange4K, cpu_id: CpuId) -> Map<WindowVa, LockStateU> {
    Map::new(m.dom(), |w: WindowVa| if va_range_2m_windows(range).contains(w) { LockStateU::WriteLocked { writer: cpu_id } } else { m[w] })
}

/// Every window of `range` that `m` holds is unlocked.
pub open spec fn pagetable_range_windows_unlocked(m: Map<WindowVa, LockStateU>, range: VaRange4K) -> bool {
    forall|w: WindowVa| #![trigger va_range_2m_windows(range).contains(w)] va_range_2m_windows(range).contains(w) && m.dom().contains(w) ==> m[w] is Unlocked
}

/// `m` holds every window of `range`.
pub open spec fn pagetable_range_windows_exist(m: Map<WindowVa, LockStateU>, range: VaRange4K) -> bool {
    forall|w: WindowVa| #![trigger va_range_2m_windows(range).contains(w)] va_range_2m_windows(range).contains(w) ==> m.dom().contains(w)
}

/// `m` with every window of `range` that it holds unlocked.
pub open spec fn pagetable_window_locks_after_unlocking_range(m: Map<WindowVa, LockStateU>, range: VaRange4K) -> Map<WindowVa, LockStateU> {
    Map::new(m.dom(), |w: WindowVa| if va_range_2m_windows(range).contains(w) { LockStateU::Unlocked } else { m[w] })
}

/// `m` plus the 512 windows of a new L2 page under L3 entry `(l4i, l3i)`: those in `locked_range` start
/// write-locked, the others unlocked.
pub open spec fn pagetable_window_locks_after_new_l2_page(m: Map<WindowVa, LockStateU>, l4i: L4Index, l3i: L3Index, locked_range: VaRange4K, cpu_id: CpuId) -> Map<WindowVa, LockStateU> {
    Map::new(m.dom() + Set::<usize>::range(0, 512).map_by(|i: usize| WindowVa { va: spec_index2va((l4i, l3i, i, 0usize)) }, |w: WindowVa| spec_v2l2index(w.va)),
        |w: WindowVa| if m.dom().contains(w) { m[w] } else if va_range_2m_windows(locked_range).contains(w) { LockStateU::WriteLocked { writer: cpu_id } } else { LockStateU::Unlocked })
}

impl PageTable<PT_TYPE> {
    pub fn new(pcid: Option<Pcid>, kernel_entries_ghost: Ghost<Seq<PageEntry>>, page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<PointsTo<PageMap>>, mem_end_l4_index: usize, proc_ptr: RwLockProcessPtr) -> (ret: Self)
        requires
            pei_valid(mem_end_l4_index),
            page_ptr_valid(page_map_ptr),
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            kernel_entries_ghost.view().len() == mem_end_l4_index,
            forall|i: usize| #![trigger page_map_perm.value().spec_index(i).is_empty()] #![trigger page_map_perm.value().spec_index(i)] mem_end_l4_index <= i && pei_valid(i) ==> page_map_perm.value().spec_index(i).is_empty(),
            forall|i: usize|
                #![trigger kernel_entries_ghost.view().spec_index(i as int)]
                #![trigger page_map_perm.value().spec_index(i)]
                0 <= i < mem_end_l4_index ==> kernel_entries_ghost.view().spec_index(i as int) == page_map_perm.value().spec_index(i),
            pcid is Some,
        ensures
            ret.wf(),
            ret.cr3 == page_map_ptr,
            ret.pcid == pcid,
            ret.did is None,
            ret.kernel_l4_end == mem_end_l4_index,
            ret.kernel_entries =~= kernel_entries_ghost,
            ret.is_empty(),
            ret.page_closure() =~= set![page_map_ptr],
            ret.proc_ptr == proc_ptr,
    {
        let mut ret = Self {
            cr3: page_map_ptr,
            pcid,
            did: None,
            kernel_l4_end: mem_end_l4_index,
            l4_table: Tracked(Map::<PageMapPtr, PointsTo<PageMap>>::tracked_empty()),
            l3_rev_map: Ghost(Map::<PageMapPtr, (L4Index)>::empty()),
            l3_tables: Tracked(Map::<PageMapPtr, PointsTo<PageMap>>::tracked_empty()),
            l2_rev_map: Ghost(Map::<PageMapPtr, (L4Index, L3Index)>::empty()),
            l2_tables: Tracked(Map::<PageMapPtr, PointsTo<PageMap>>::tracked_empty()),
            l1_rev_map: Ghost(Map::<PageMapPtr, (L4Index, L3Index, L2Index)>::empty()),
            l1_tables: Tracked(Map::<PageMapPtr, PointsTo<PageMap>>::tracked_empty()),
            mapping_4k: Ghost(Map::<VAddr, MapEntry>::empty()),
            mapping_2m: Ghost(Map::<VAddr, MapEntry>::empty()),
            mapping_1g: Ghost(Map::<VAddr, MapEntry>::empty()),
            kernel_entries: kernel_entries_ghost,
            proc_ptr: proc_ptr,
        };
        proof {
            ret.l4_table.borrow_mut().tracked_insert(page_map_ptr, page_map_perm);
            Self::new_eof(ret);
        }
        ret
    }

    /// EOF closure of `new`: a table whose only page is the root closes every structural leaf of `wf`.
    proof fn new_eof(ret: Self)
        requires
            pei_valid(ret.kernel_l4_end),
            page_ptr_valid(ret.cr3),
            ret.l4_table.view().dom() == set![ret.cr3],
            ret.l4_table.view().spec_index(ret.cr3).addr() == ret.cr3,
            ret.l4_table.view().spec_index(ret.cr3).is_init(),
            ret.l4_table.view().spec_index(ret.cr3).value().wf(),
            ret.kernel_entries.view().len() == ret.kernel_l4_end,
            forall|i: usize|
                #![trigger ret.l4_entry(i).is_empty()]
                #![trigger ret.l4_entry(i)]
                ret.kernel_l4_end <= i && pei_valid(i) ==> ret.l4_entry(i).is_empty(),
            forall|i: usize|
                #![trigger ret.kernel_entries.view().spec_index(i as int)]
                #![trigger ret.l4_entry(i)]
                0 <= i < ret.kernel_l4_end ==> ret.kernel_entries.view().spec_index(i as int) == ret.l4_entry(i),
            ret.l3_tables.view() == Map::<PageMapPtr, PointsTo<PageMap>>::empty(),
            ret.l2_tables.view() == Map::<PageMapPtr, PointsTo<PageMap>>::empty(),
            ret.l1_tables.view() == Map::<PageMapPtr, PointsTo<PageMap>>::empty(),
            ret.mapping_4k.view() == Map::<VAddr, MapEntry>::empty(),
            ret.mapping_2m.view() == Map::<VAddr, MapEntry>::empty(),
            ret.mapping_1g.view() == Map::<VAddr, MapEntry>::empty(),
        ensures
            ret.wf_l4(),
            ret.wf_l3(),
            ret.wf_l2(),
            ret.wf_l1(),
            ret.disjoint_l4(),
            ret.disjoint_l3(),
            ret.disjoint_l2(),
            ret.wf_mapping_4k(),
            ret.wf_mapping_2m(),
            ret.wf_mapping_1g(),
            ret.user_only(),
            ret.rwx_upper_level_entries(),
            ret.table_pages_wf(),
            ret.tables_reachable_wf(),
            ret.kernel_entries_wf(),
    {
        assert(ret.wf_l4()) by { reveal(PageTable::wf_l4); };
        assert(ret.wf_l3()) by { reveal(PageTable::wf_l3); };
        assert(ret.wf_l2()) by { reveal(PageTable::wf_l2); };
        assert(ret.wf_l1()) by { reveal(PageTable::wf_l1); };
        assert(ret.disjoint_l4()) by { reveal(PageTable::disjoint_l4); };
        assert(ret.disjoint_l3()) by { reveal(PageTable::disjoint_l3); };
        assert(ret.disjoint_l2()) by { reveal(PageTable::disjoint_l2); };
        assert(ret.wf_mapping_4k()) by { reveal(PageTable::wf_mapping_4k); };
        assert(ret.wf_mapping_2m()) by { reveal(PageTable::wf_mapping_2m); };
        assert(ret.wf_mapping_1g()) by { reveal(PageTable::wf_mapping_1g); };
        assert(ret.user_only()) by { reveal(PageTable::user_only); };
        assert(ret.rwx_upper_level_entries()) by { reveal(PageTable::rwx_upper_level_entries); };
        assert(ret.table_pages_wf()) by { reveal(PageTable::table_pages_wf); };
        assert(ret.tables_reachable_wf()) by { reveal(PageTable::tables_reachable_wf); };
        assert(ret.kernel_entries_wf()) by { reveal(PageTable::kernel_entries_wf); };
    }

    pub open spec fn is_empty(&self) -> bool {
        &&& forall|i: L4Index| #![trigger self.l4_entry(i).perm.present] self.kernel_l4_end <= i && pei_valid(i) ==> self.l4_entry(i).is_empty()
        &&& self.l3_tables.view().dom() == Set::<PageMapPtr>::empty()
        &&& self.l2_tables.view().dom() == Set::<PageMapPtr>::empty()
        &&& self.l1_tables.view().dom() == Set::<PageMapPtr>::empty()
        &&& self.mapping_4k() == Map::<VAddr, MapEntry>::empty()
        &&& self.mapping_2m() == Map::<VAddr, MapEntry>::empty()
        &&& self.mapping_1g() == Map::<VAddr, MapEntry>::empty()
    }

    pub open spec fn page_closure(&self) -> Set<PagePtr> {
        self.l3_tables.view().dom() + self.l2_tables.view().dom() + self.l1_tables.view().dom() + self.l4_table.view().dom()
    }

    pub open spec fn mapping_4k(&self) -> Map<VAddr, MapEntry> { self.mapping_4k.view() }
    pub open spec fn mapping_2m(&self) -> Map<VAddr, MapEntry> { self.mapping_2m.view() }
    pub open spec fn mapping_1g(&self) -> Map<VAddr, MapEntry> { self.mapping_1g.view() }

    #[verifier::inline]
    pub open spec fn l4_entry(&self, i: L4Index) -> PageEntry { self.l4_table.view().spec_index(self.cr3).value().spec_index(i) }

    #[verifier::inline]
    pub open spec fn l3_entry(&self, p: PageMapPtr, i: L3Index) -> PageEntry { self.l3_tables.view().spec_index(p).value().spec_index(i) }

    #[verifier::inline]
    pub open spec fn l2_entry(&self, p: PageMapPtr, i: L2Index) -> PageEntry { self.l2_tables.view().spec_index(p).value().spec_index(i) }

    #[verifier::inline]
    pub open spec fn l1_entry(&self, p: PageMapPtr, i: L1Index) -> PageEntry { self.l1_tables.view().spec_index(p).value().spec_index(i) }

    /// A CPU table has a PCID.
    pub open spec fn pcid_wf(&self) -> bool { self.pcid is Some }

    /// A CPU table has no VT-d domain id.
    pub open spec fn did_wf(&self) -> bool { self.did is None }

    pub open spec fn pcid_value(&self) -> Pcid
        recommends self.pcid is Some,
    {
        self.pcid.unwrap()
    }

    #[verifier::opaque]
    pub open spec fn wf_l4(&self) -> bool {
        &&& self.l4_table.view().dom() =~= Set::<PageMapPtr>::empty().insert(self.cr3)
        &&& self.cr3 == self.l4_table.view().spec_index(self.cr3).addr()
        &&& self.l4_table.view().spec_index(self.cr3).is_init()
        &&& self.l4_table.view().spec_index(self.cr3).value().wf()
        // A present user L4 entry links an L3 page. L4 maps no leaf, so its kernel_present bit has no meaning, and the
        // hardware forbids the page-size bit at L4.
        &&& forall|i: L4Index|
            #![trigger self.l4_entry(i).perm.present]
            self.kernel_l4_end <= i && pei_valid(i) ==> {
                &&& self.l4_entry(i).perm.present ==> !self.l4_entry(i).perm.ps
                &&& self.l4_entry(i).perm.present ==> self.l3_tables.view().dom().contains(self.l4_entry(i).addr)
            }
    }

    /// Present user L4 entries link distinct L3 pages.
    #[verifier::opaque]
    pub open spec fn disjoint_l4(&self) -> bool {
        &&& forall|i: L4Index, j: L4Index|
            #![trigger self.l4_entry(i), self.l4_entry(j)]
            i != j && self.kernel_l4_end <= i && pei_valid(i) && self.kernel_l4_end <= j && pei_valid(j)
                && self.l4_entry(i).perm.present && self.l4_entry(j).perm.present
                ==> self.l4_entry(i).addr != self.l4_entry(j).addr
    }

    #[verifier::opaque]
    pub open spec fn wf_l3(&self) -> bool {
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(p)]
            self.l3_tables.view().dom().contains(p) ==> {
                &&& self.l3_tables.view().spec_index(p).addr() == p
                &&& self.l3_tables.view().spec_index(p).is_init()
                &&& self.l3_tables.view().spec_index(p).value().wf()
            }
        // Last level page entry must have kernel present set if it's present
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(p)]
            self.l3_tables.view().dom().contains(p) ==> forall|i: L3Index|
                #![trigger self.l3_entry(p, i)]
                pei_valid(i) && self.l3_entry(p, i).perm.ps && self.l3_entry(p, i).perm.present ==> self.l3_entry(p, i).perm.kernel_present
        // A present non-huge L3 entry links an L2 page.
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(p)]
            self.l3_tables.view().dom().contains(p) ==> forall|i: L3Index|
                #![trigger self.l3_entry(p, i)]
                pei_valid(i) && self.l3_entry(p, i).perm.present && !self.l3_entry(p, i).perm.ps
                    ==> self.l2_tables.view().dom().contains(self.l3_entry(p, i).addr)
    }

    /// Present non-huge L3 entries link distinct L2 pages, in one L3 page and across L3 pages.
    #[verifier::opaque]
    pub open spec fn disjoint_l3(&self) -> bool {
        &&& forall|pi: PageMapPtr, pj: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(pi), self.l3_tables.view().dom().contains(pj)]
            self.l3_tables.view().dom().contains(pi) && self.l3_tables.view().dom().contains(pj) ==> forall|l3i: L3Index, l3j: L3Index|
                #![trigger self.l3_entry(pi, l3i), self.l3_entry(pj, l3j)]
                (pi, l3i) != (pj, l3j) && pei_valid(l3i) && pei_valid(l3j)
                    && self.l3_entry(pi, l3i).perm.present && !self.l3_entry(pi, l3i).perm.ps
                    && self.l3_entry(pj, l3j).perm.present && !self.l3_entry(pj, l3j).perm.ps
                    ==> self.l3_entry(pi, l3i).addr != self.l3_entry(pj, l3j).addr
    }

    #[verifier::opaque]
    pub open spec fn wf_l2(&self) -> bool {
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables.view().dom().contains(p)]
            self.l2_tables.view().dom().contains(p) ==> {
                &&& self.l2_tables.view().spec_index(p).addr() == p
                &&& self.l2_tables.view().spec_index(p).is_init()
                &&& self.l2_tables.view().spec_index(p).value().wf()
            }
        // Last level page entry must have kernel present set if it's present
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables.view().dom().contains(p)]
            self.l2_tables.view().dom().contains(p) ==> forall|i: L2Index|
                #![trigger self.l2_entry(p, i)]
                pei_valid(i) && self.l2_entry(p, i).perm.ps && self.l2_entry(p, i).perm.present ==> self.l2_entry(p, i).perm.kernel_present
        // A present non-huge L2 entry links an L1 page.
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables.view().dom().contains(p)]
            self.l2_tables.view().dom().contains(p) ==> forall|i: L2Index|
                #![trigger self.l2_entry(p, i)]
                pei_valid(i) && self.l2_entry(p, i).perm.present && !self.l2_entry(p, i).perm.ps
                    ==> self.l1_tables.view().dom().contains(self.l2_entry(p, i).addr)
    }

    /// Present non-huge L2 entries link distinct L1 pages, in one L2 page and across L2 pages.
    #[verifier::opaque]
    pub open spec fn disjoint_l2(&self) -> bool {
        &&& forall|pi: PageMapPtr, pj: PageMapPtr|
            #![trigger self.l2_tables.view().dom().contains(pi), self.l2_tables.view().dom().contains(pj)]
            self.l2_tables.view().dom().contains(pi) && self.l2_tables.view().dom().contains(pj) ==> forall|l2i: L2Index, l2j: L2Index|
                #![trigger pei_valid(l2i), pei_valid(l2j), self.l2_entry(pi, l2i), self.l2_entry(pj, l2j)]
                (pi, l2i) != (pj, l2j) && pei_valid(l2i) && pei_valid(l2j)
                    && self.l2_entry(pi, l2i).perm.present && !self.l2_entry(pi, l2i).perm.ps
                    && self.l2_entry(pj, l2j).perm.present && !self.l2_entry(pj, l2j).perm.ps
                    ==> self.l2_entry(pi, l2i).addr != self.l2_entry(pj, l2j).addr
    }

    #[verifier::opaque]
    pub open spec fn wf_l1(&self) -> bool {
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables.view().dom().contains(p)]
            self.l1_tables.view().dom().contains(p) ==> {
                &&& self.l1_tables.view().spec_index(p).addr() == p
                &&& self.l1_tables.view().spec_index(p).is_init()
                &&& self.l1_tables.view().spec_index(p).value().wf()
            }
        // A present L1 entry is a 4K leaf: no page-size bit, kernel_present bit set.
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables.view().dom().contains(p)]
            self.l1_tables.view().dom().contains(p) ==> forall|i: L1Index|
                #![trigger self.l1_entry(p, i)]
                pei_valid(i) && self.l1_entry(p, i).perm.present ==> !self.l1_entry(p, i).perm.ps && self.l1_entry(p, i).perm.kernel_present
    }

    /// Every present user entry, at every level, has the user bit.
    #[verifier::opaque]
    pub open spec fn user_only(&self) -> bool {
        &&& forall|i: L4Index|
            #![trigger self.l4_entry(i)]
            self.kernel_l4_end <= i && pei_valid(i) && self.l4_entry(i).perm.present ==> self.l4_entry(i).perm.user
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(p)]
            self.l3_tables.view().dom().contains(p) ==> forall|i: L3Index|
                #![trigger self.l3_entry(p, i)]
                pei_valid(i) && self.l3_entry(p, i).perm.present ==> self.l3_entry(p, i).perm.user
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables.view().dom().contains(p)]
            self.l2_tables.view().dom().contains(p) ==> forall|i: L2Index|
                #![trigger self.l2_entry(p, i)]
                pei_valid(i) && self.l2_entry(p, i).perm.present ==> self.l2_entry(p, i).perm.user
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables.view().dom().contains(p)]
            self.l1_tables.view().dom().contains(p) ==> forall|i: L1Index|
                #![trigger self.l1_entry(p, i)]
                pei_valid(i) && self.l1_entry(p, i).perm.present ==> self.l1_entry(p, i).perm.user
    }

    /// Present non-leaf entries never restrict rights: write bit set, execute_disable bit clear.
    #[verifier::opaque]
    pub open spec fn rwx_upper_level_entries(&self) -> bool {
        &&& forall|i: L4Index|
            #![trigger self.l4_entry(i)]
            self.kernel_l4_end <= i && pei_valid(i) && self.l4_entry(i).perm.present ==> self.l4_entry(i).perm.write && !self.l4_entry(i).perm.execute_disable
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(p)]
            self.l3_tables.view().dom().contains(p) ==> forall|i: L3Index|
                #![trigger self.l3_entry(p, i)]
                pei_valid(i) && self.l3_entry(p, i).perm.present && !self.l3_entry(p, i).perm.ps
                    ==> self.l3_entry(p, i).perm.write && !self.l3_entry(p, i).perm.execute_disable
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables.view().dom().contains(p)]
            self.l2_tables.view().dom().contains(p) ==> forall|i: L2Index|
                #![trigger self.l2_entry(p, i)]
                pei_valid(i) && self.l2_entry(p, i).perm.present && !self.l2_entry(p, i).perm.ps
                    ==> self.l2_entry(p, i).perm.write && !self.l2_entry(p, i).perm.execute_disable
    }

    /// Table pages are valid page pointers and each lies in exactly one level map.
    #[verifier::opaque]
    pub open spec fn table_pages_wf(&self) -> bool {
        &&& page_ptr_valid(self.cr3)
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(p), page_ptr_valid(p)]
            self.l3_tables.view().dom().contains(p) ==> page_ptr_valid(p)
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables.view().dom().contains(p), page_ptr_valid(p)]
            self.l2_tables.view().dom().contains(p) ==> page_ptr_valid(p)
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables.view().dom().contains(p), page_ptr_valid(p)]
            self.l1_tables.view().dom().contains(p) ==> page_ptr_valid(p)
        &&& self.l4_table.view().dom().disjoint(self.l3_tables.view().dom())
        &&& self.l4_table.view().dom().disjoint(self.l2_tables.view().dom())
        &&& self.l4_table.view().dom().disjoint(self.l1_tables.view().dom())
        &&& self.l3_tables.view().dom().disjoint(self.l2_tables.view().dom())
        &&& self.l3_tables.view().dom().disjoint(self.l1_tables.view().dom())
        &&& self.l2_tables.view().dom().disjoint(self.l1_tables.view().dom())
    }

    pub proof fn table_pages_wf_cr3_at(&self)
        requires self.table_pages_wf()
        ensures page_ptr_valid(self.cr3)
    { reveal(PageTable::table_pages_wf); }

    pub open spec fn spec_resolve_mapping_l4(&self, l4i: L4Index) -> Option<PageEntry>
        recommends
            self.kernel_l4_end <= l4i && pei_valid(l4i),
    {
        if self.l4_entry(l4i).perm.present || l4i < self.kernel_l4_end { Some(self.l4_entry(l4i)) }
        else { None }
    }

    pub open spec fn spec_resolve_mapping_1g_l3(&self, l4i: L4Index, l3i: L3Index) -> Option<PageEntry>
        recommends
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
    {
        if self.spec_resolve_mapping_l4(l4i) is Some
            && self.l3_entry(self.spec_resolve_mapping_l4(l4i)->0.addr, l3i).perm.ps
            && self.l3_entry(self.spec_resolve_mapping_l4(l4i)->0.addr, l3i).perm.kernel_present {
            Some(self.l3_entry(self.spec_resolve_mapping_l4(l4i)->0.addr, l3i))
        } else {
            None
        }
    }

    pub open spec fn spec_resolve_mapping_l3(&self, l4i: L4Index, l3i: L3Index) -> Option<PageEntry>
        recommends
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
    {
        if self.spec_resolve_mapping_l4(l4i) is Some
            && self.l3_entry(self.spec_resolve_mapping_l4(l4i)->0.addr, l3i).perm.present
            && self.l3_entry(self.spec_resolve_mapping_l4(l4i)->0.addr, l3i).perm.ps == false {
            Some(self.l3_entry(self.spec_resolve_mapping_l4(l4i)->0.addr, l3i))
        } else {
            None
        }
    }

    pub open spec fn spec_resolve_mapping_2m_l2(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> Option<PageEntry>
        recommends
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
    {
        if self.spec_resolve_mapping_l3(l4i, l3i) is Some
            && self.l2_entry(self.spec_resolve_mapping_l3(l4i, l3i)->0.addr, l2i).perm.kernel_present
            && self.l2_entry(self.spec_resolve_mapping_l3(l4i, l3i)->0.addr, l2i).perm.ps {
            Some(self.l2_entry(self.spec_resolve_mapping_l3(l4i, l3i)->0.addr, l2i))
        } else {
            None
        }
    }

    pub open spec fn spec_resolve_mapping_l2(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> Option<PageEntry>
        recommends
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
    {
        if self.spec_resolve_mapping_l3(l4i, l3i) is Some
            && self.l2_entry(self.spec_resolve_mapping_l3(l4i, l3i)->0.addr, l2i).perm.present
            && self.l2_entry(self.spec_resolve_mapping_l3(l4i, l3i)->0.addr, l2i).perm.ps == false {
            Some(self.l2_entry(self.spec_resolve_mapping_l3(l4i, l3i)->0.addr, l2i))
        } else {
            None
        }
    }

    pub open spec fn spec_resolve_mapping_4k_l1(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index) -> Option<PageEntry>
        recommends
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            pei_valid(l1i),
    {
        if self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some && self.l1_entry(self.spec_resolve_mapping_l2(l4i, l3i, l2i)->0.addr, l1i).perm.kernel_present {
            Some(self.l1_entry(self.spec_resolve_mapping_l2(l4i, l3i, l2i)->0.addr, l1i))
        } else {
            None
        }
    }

    /// Every mapping key is a valid VA (CPU table) or IOVA (IOMMU table) of its page size, and every frame a valid page of
    /// that size.
    pub open spec fn va_addr_valid(&self) -> bool {
        &&& forall|va: VAddr|
            #![trigger va_4k_valid(va), self.mapping_4k.view().dom().contains(va)]
            #![trigger self.mapping_4k.view().dom().contains(va), page_ptr_valid(self.mapping_4k.view().spec_index(va).addr)]
            #![trigger self.mapping_4k.view().dom().contains(va)]
            #![trigger page_ptr_valid(self.mapping_4k.view().spec_index(va).addr)]
            self.mapping_4k.view().dom().contains(va) ==> page_table_key_4k_valid::<PT_TYPE>(va) && mapping_4k_target_valid(self.mapping_4k.view().spec_index(va).addr, self.mapping_4k.view().spec_index(va).is_io)
        &&& forall|va: VAddr|
            #![trigger va_2m_valid(va), self.mapping_2m.view().dom().contains(va)]
            #![trigger self.mapping_2m.view().dom().contains(va), page_ptr_2m_valid(self.mapping_2m.view().spec_index(va).addr)]
            #![trigger self.mapping_2m.view().dom().contains(va)]
            self.mapping_2m.view().dom().contains(va) ==> page_table_key_2m_valid::<PT_TYPE>(va) && mapping_2m_target_valid(self.mapping_2m.view().spec_index(va).addr, self.mapping_2m.view().spec_index(va).is_io)
        &&& forall|va: VAddr|
            #![trigger va_1g_valid(va), self.mapping_1g.view().dom().contains(va)]
            #![trigger self.mapping_1g.view().dom().contains(va), page_ptr_1g_valid(self.mapping_1g.view().spec_index(va).addr)]
            #![trigger self.mapping_1g.view().dom().contains(va)]
            self.mapping_1g.view().dom().contains(va) ==> page_table_key_1g_valid::<PT_TYPE>(va) && page_ptr_1g_valid(self.mapping_1g.view().spec_index(va).addr)
    }

    /// mapping_4k holds exactly the resolved 4K leaves, with their frame, write, execute_disable and present bits.
    #[verifier::opaque]
    pub open spec fn wf_mapping_4k(&self) -> bool {
        &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger self.mapping_4k.view().spec_index(spec_index2va((l4i,l3i,l2i,l1i)))]
            #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
            self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> {
                &&& self.mapping_4k.view().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))) == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some
                &&& self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some
                    ==> self.mapping_4k.view().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).addr == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.addr
                    && self.mapping_4k.view().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).write == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.perm.write
                    && self.mapping_4k.view().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).execute_disable == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.perm.execute_disable
                    && self.mapping_4k.view().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).is_io == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.perm.is_io
                    && self.mapping_4k.view().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.perm.present
            }
    }

    /// mapping_2m holds exactly the resolved 2M leaves, with their frame, write, execute_disable and present bits.
    #[verifier::opaque]
    pub open spec fn wf_mapping_2m(&self) -> bool {
        &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger self.mapping_2m.view().spec_index(spec_index2va((l4i,l3i,l2i,0)))]
            #![trigger self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)]
            self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> {
                &&& self.mapping_2m.view().dom().contains(spec_index2va((l4i, l3i, l2i, 0))) == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some
                &&& self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some
                    ==> self.mapping_2m.view().spec_index(spec_index2va((l4i, l3i, l2i, 0))).addr == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.addr
                    && self.mapping_2m.view().spec_index(spec_index2va((l4i, l3i, l2i, 0))).write == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.perm.write
                    && self.mapping_2m.view().spec_index(spec_index2va((l4i, l3i, l2i, 0))).execute_disable == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.perm.execute_disable
                    && self.mapping_2m.view().spec_index(spec_index2va((l4i, l3i, l2i, 0))).is_io == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.perm.is_io
                    && self.mapping_2m.view().spec_index(spec_index2va((l4i, l3i, l2i, 0))).present == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.perm.present
            }
    }

    /// mapping_1g holds exactly the resolved 1G leaves, with their frame, write, execute_disable and present bits.
    #[verifier::opaque]
    pub open spec fn wf_mapping_1g(&self) -> bool {
        &&& forall|l4i: L4Index, l3i: L3Index|
            #![trigger self.mapping_1g.view().spec_index(spec_index2va((l4i,l3i,0,0)))]
            #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
            self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> {
                &&& self.mapping_1g.view().dom().contains(spec_index2va((l4i, l3i, 0, 0))) == self.spec_resolve_mapping_1g_l3(l4i, l3i) is Some
                &&& self.spec_resolve_mapping_1g_l3(l4i, l3i) is Some
                    ==> self.mapping_1g.view().spec_index(spec_index2va((l4i, l3i, 0, 0))).addr == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.addr
                    && self.mapping_1g.view().spec_index(spec_index2va((l4i, l3i, 0, 0))).write == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.perm.write
                    && self.mapping_1g.view().spec_index(spec_index2va((l4i, l3i, 0, 0))).execute_disable == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.perm.execute_disable
                    && self.mapping_1g.view().spec_index(spec_index2va((l4i, l3i, 0, 0))).is_io == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.perm.is_io
                    && self.mapping_1g.view().spec_index(spec_index2va((l4i, l3i, 0, 0))).present == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.perm.present
            }
    }

    /// Every L3, L2 and L1 page is linked from the user part of the root along the path its reverse map stores.
    #[verifier::opaque]
    pub open spec fn tables_reachable_wf(&self) -> bool {
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(p)]
            self.l3_tables.view().dom().contains(p) ==> {
                let l4i = self.l3_rev_map.view().spec_index(p);
                &&& self.kernel_l4_end <= l4i && pei_valid(l4i)
                &&& self.spec_resolve_mapping_l4(l4i) is Some && self.spec_resolve_mapping_l4(l4i)->0.addr == p
            }
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables.view().dom().contains(p)]
            self.l2_tables.view().dom().contains(p) ==> {
                let (l4i, l3i) = self.l2_rev_map.view().spec_index(p);
                &&& self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i)
                &&& self.spec_resolve_mapping_l3(l4i, l3i) is Some && self.spec_resolve_mapping_l3(l4i, l3i)->0.addr == p
            }
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables.view().dom().contains(p)]
            self.l1_tables.view().dom().contains(p) ==> {
                let (l4i, l3i, l2i) = self.l1_rev_map.view().spec_index(p);
                &&& self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                &&& self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some && self.spec_resolve_mapping_l2(l4i, l3i, l2i)->0.addr == p
            }
    }

    /// kernel_entries equals the root's kernel L4 entries `[0, kernel_l4_end)`.
    #[verifier::opaque]
    pub open spec fn kernel_entries_wf(&self) -> bool {
        &&& pei_valid(self.kernel_l4_end)
        &&& self.kernel_entries.view().len() =~= self.kernel_l4_end as nat
        &&& forall|i: L4Index|
            #![trigger self.kernel_entries.view().spec_index(i as int)]
            0 <= i < self.kernel_l4_end && pei_valid(i) ==> self.kernel_entries.view().spec_index(i as int) == self.l4_entry(i)
    }

    pub proof fn kernel_entries_wf_l4_end_valid_at(&self)
        requires self.kernel_entries_wf()
        ensures pei_valid(self.kernel_l4_end)
    { reveal(PageTable::kernel_entries_wf); }

    pub proof fn kernel_entries_wf_len_at(&self)
        requires self.kernel_entries_wf()
        ensures
            pei_valid(self.kernel_l4_end),
            self.kernel_entries.view().len() == self.kernel_l4_end as nat,
    { reveal(PageTable::kernel_entries_wf); }

    /// The page-table invariant: structure and disjointness of every level, the three mapping maps, user and rights
    /// bits, table pages and their reachability, kernel entries, PCID and domain id.
    pub open spec fn wf(&self) -> bool {
        &&& self.va_addr_valid()
        &&& self.wf_l4()
        &&& self.wf_l3()
        &&& self.wf_l2()
        &&& self.wf_l1()
        &&& self.disjoint_l4()
        &&& self.disjoint_l3()
        &&& self.disjoint_l2()
        &&& self.wf_mapping_4k()
        &&& self.wf_mapping_2m()
        &&& self.wf_mapping_1g()
        &&& self.user_only()
        &&& self.rwx_upper_level_entries()
        &&& self.table_pages_wf()
        &&& self.tables_reachable_wf()
        &&& self.kernel_entries_wf()
        &&& self.pcid_wf()
        &&& self.did_wf()
    }
}

impl LockInvTrait for PageTable<PT_TYPE> {
    /// The page-table invariant `wf`.
    open spec fn inv(&self) -> bool {
        &&& self.wf()
    }
}
impl LockMajorTrait for PageTable<PT_TYPE> {
    open spec fn lock_major_1(&self) -> LockMajorId { 0x233 }
    open spec fn lock_major_2(&self) -> LockMajorId { 0x233 }
    open spec fn lock_major_3(&self) -> LockMajorId { 0x233 }

    open spec fn lock_major_default(&self) -> LockMajorId {
        PAGE_TABLE_LOCK_MAJOR
    }

    open spec fn lock_major_1_predicate(&self) -> bool { false }
    open spec fn lock_major_2_predicate(&self) -> bool { false }
    open spec fn lock_major_3_predicate(&self) -> bool { false }
    open spec fn lock_major_default_predicate(&self) -> bool { true }
}

impl LockOwnerIdTrait for PageTable<PT_TYPE> {
    open spec fn container_depth(&self) -> LockOwnerId { LockOwnerId::none() }
    open spec fn process_depth(&self) -> LockOwnerId { LockOwnerId::none() }
}
} // verus!
