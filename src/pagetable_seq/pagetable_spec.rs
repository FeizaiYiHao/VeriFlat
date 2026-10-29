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
/// if an entry exists in mapping_xx.dom(), is entry is visible to the kernel at least.
/// if the entry has present flag set, it's visible to the page table walk.
/// our TLB spec will be that the TLB is `always` a subset of kernel view. Regardless the locking state of the page table.
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
/// does not.
pub ghost struct PageTableU {
    pub lock_state: LockStateU,
    pub did: Option<VtdDomainId>,
    pub mapping_4k: Map<VAddr, MapEntry>,
    pub mapping_2m: Map<VAddr, MapEntry>,
    pub mapping_1g: Map<VAddr, MapEntry>,
}

impl<const TABLE_TYPE: PTType> PageTable<TABLE_TYPE> {
    /// The owner of the outer RwLock supplies its mode; the payload has no lock state.
    pub open spec fn user_view(&self, lock_state: LockStateU) -> PageTableU {
        PageTableU {
            lock_state,
            did: if TABLE_TYPE == PT_TYPE { None } else { self.did },
            mapping_4k: self.mapping_4k().filter_keys(|va: VAddr| self.mapping_4k().spec_index(va).present),
            mapping_2m: self.mapping_2m().filter_keys(|va: VAddr| self.mapping_2m().spec_index(va).present),
            mapping_1g: self.mapping_1g().filter_keys(|va: VAddr| self.mapping_1g().spec_index(va).present),
        }
    }

    /// Every 4K, 2M, and 1G leaf is user-present, so the user view shows the whole mapping.
    pub open spec fn leaves_present(&self) -> bool {
        &&& forall|va: VAddr| #![trigger self.mapping_4k().dom().contains(va)] self.mapping_4k().dom().contains(va) ==> self.mapping_4k().spec_index(va).present
        &&& forall|va: VAddr| #![trigger self.mapping_2m().dom().contains(va)] self.mapping_2m().dom().contains(va) ==> self.mapping_2m().spec_index(va).present
        &&& forall|va: VAddr| #![trigger self.mapping_1g().dom().contains(va)] self.mapping_1g().dom().contains(va) ==> self.mapping_1g().spec_index(va).present
    }

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
            TABLE_TYPE == PT_TYPE ==> pcid is Some,
            TABLE_TYPE == IOMMU_TYPE ==> pcid is None,
            TABLE_TYPE == IOMMU_TYPE ==> mem_end_l4_index == 0,
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
            TABLE_TYPE == IOMMU_TYPE ==> ret.kernel_l4_end == 0,
            ret.l4_table.view().dom() == set![ret.cr3],
            ret.l4_table.view().spec_index(ret.cr3).addr() == ret.cr3,
            ret.l4_table.view().spec_index(ret.cr3).is_init(),
            ret.l4_table.view().spec_index(ret.cr3).value().wf(),
            ret.kernel_entries.view().len() == ret.kernel_l4_end,
            forall|i: usize|
                #![trigger ret.l4_table.view().spec_index(ret.cr3).value().spec_index(i).is_empty()]
                #![trigger ret.l4_table.view().spec_index(ret.cr3).value().spec_index(i)]
                ret.kernel_l4_end <= i && pei_valid(i) ==> ret.l4_table.view().spec_index(ret.cr3).value().spec_index(i).is_empty(),
            forall|i: usize|
                #![trigger ret.kernel_entries.view().spec_index(i as int)]
                #![trigger ret.l4_table.view().spec_index(ret.cr3).value().spec_index(i)]
                0 <= i < ret.kernel_l4_end ==> ret.kernel_entries.view().spec_index(i as int) == ret.l4_table.view().spec_index(ret.cr3).value().spec_index(i),
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
        &&& forall|i: L4Index| #![trigger self.l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.present] self.kernel_l4_end <= i && pei_valid(i) ==> self.l4_table.view().spec_index(self.cr3).value().spec_index(i).is_empty()
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

    pub open spec fn pcid_wf(&self) -> bool {
        &&& TABLE_TYPE == PT_TYPE ==> self.pcid is Some
        &&& TABLE_TYPE == IOMMU_TYPE ==> self.pcid is None
    }

    /// A CPU table has no VT-d domain id; an IOMMU table may carry one valid id.
    pub open spec fn did_wf(&self) -> bool {
        &&& TABLE_TYPE == PT_TYPE ==> self.did is None
        &&& self.did is Some ==> vtd_domain_id_valid(self.did->Some_0)
    }

    pub open spec fn pcid_value(&self) -> Pcid
        recommends
            TABLE_TYPE == PT_TYPE,
            self.pcid is Some,
    {
        self.pcid.unwrap()
    }

    #[verifier::opaque]
    pub open spec fn wf_l4(&self) -> bool {
        &&& self.l4_table.view().dom() =~= Set::<PageMapPtr>::empty().insert(self.cr3)
        &&& self.cr3 == self.l4_table.view().spec_index(self.cr3).addr()
        &&& self.l4_table.view().spec_index(self.cr3).is_init()
        &&& self.l4_table.view().spec_index(self.cr3).value().wf()
        // L4 does not map to any last level page entry. There's no meaning for kernel_present bit.
        // L4 cannot enable page size bit (hardware limit)
        &&& forall|i: L4Index|
            #![trigger self.l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.present]
            self.kernel_l4_end <= i && pei_valid(i) ==> {
                &&& self.l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.present ==> !self.l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.ps
                &&& self.l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.present ==> self.l3_tables.view().dom().contains(self.l4_table.view().spec_index(self.cr3).value().spec_index(i).addr)
            }
    }
    #[verifier::opaque]
    pub open spec fn disjoint_l4(&self) -> bool {
        &&& forall|i: L4Index, j: L4Index|
            #![trigger self.l4_table.view().spec_index(self.cr3).value().spec_index(i), self.l4_table.view().spec_index(self.cr3).value().spec_index(j)]
            i != j && self.kernel_l4_end <= i && pei_valid(i) && self.kernel_l4_end <= j && pei_valid(j) && self.l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.present && self.l4_table.view().spec_index(self.cr3).value().spec_index(j).perm.present
                ==> self.l4_table.view().spec_index(self.cr3).value().spec_index(i).addr != self.l4_table.view().spec_index(self.cr3).value().spec_index(j).addr
    }

    #[verifier::opaque]
    pub open spec fn wf_l3(&self) -> bool {
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(p)]
            self.l3_tables.view().dom().contains(p) ==> self.l3_tables.view().spec_index(p).addr() == p && self.l3_tables.view().spec_index(p).is_init() && self.l3_tables.view().spec_index(p).value().wf()
        // Last level page entry must have kernel present set if it's present
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(p)]
            self.l3_tables.view().dom().contains(p) ==> forall|i: L3Index|
                #![trigger self.l3_tables.view().spec_index(p).value().spec_index(i)]
                pei_valid(i) && self.l3_tables.view().spec_index(p).value().spec_index(i).perm.ps && self.l3_tables.view().spec_index(p).value().spec_index(i).perm.present
                    ==> self.l3_tables.view().spec_index(p).value().spec_index(i).perm.kernel_present
        // all l3 points to valid l2 tables
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(p)]
            self.l3_tables.view().dom().contains(p) ==> forall|i: L3Index|
                #![trigger self.l3_tables.view().spec_index(p).value().spec_index(i)]
                pei_valid(i) && self.l3_tables.view().spec_index(p).value().spec_index(i).perm.present && !self.l3_tables.view().spec_index(p).value().spec_index(i).perm.ps
                    ==> self.l2_tables.view().dom().contains(self.l3_tables.view().spec_index(p).value().spec_index(i).addr)
    }

    #[verifier::opaque]
    pub open spec fn disjoint_l3(&self) -> bool {
        //L3 tables are disjoint
        &&& forall|pi: PageMapPtr, pj: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(pi), self.l3_tables.view().dom().contains(pj)]
            self.l3_tables.view().dom().contains(pi) && self.l3_tables.view().dom().contains(pj) ==> forall|l3i: L3Index, l3j: L3Index|
                #![trigger self.l3_tables.view().spec_index(pi).value().spec_index(l3i), self.l3_tables.view().spec_index(pj).value().spec_index(l3j)]
                pei_valid(l3i) && pei_valid(l3j) && self.l3_tables.view().spec_index(pi).value().spec_index(l3i).perm.present && !self.l3_tables.view().spec_index(pi).value().spec_index(l3i).perm.ps
                && self.l3_tables.view().spec_index(pj).value().spec_index(l3j).perm.present && !self.l3_tables.view().spec_index(pj).value().spec_index(l3j).perm.ps ==> {
                    &&& pi != pj ==> self.l3_tables.view().spec_index(pi).value().spec_index(l3i).addr != self.l3_tables.view().spec_index(pj).value().spec_index(l3j).addr
                    &&& pi == pj && l3i != l3j ==> self.l3_tables.view().spec_index(pi).value().spec_index(l3i).addr != self.l3_tables.view().spec_index(pj).value().spec_index(l3j).addr
                }
    }

    #[verifier::opaque]
    pub open spec fn wf_l2(&self) -> bool {
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables.view().dom().contains(p)]
            self.l2_tables.view().dom().contains(p) ==> self.l2_tables.view().spec_index(p).addr() == p && self.l2_tables.view().spec_index(p).is_init() && self.l2_tables.view().spec_index(p).value().wf()
        // Last level page entry must have kernel present set if it's present
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables.view().dom().contains(p)]
            self.l2_tables.view().dom().contains(p) ==> forall|i: L2Index|
                #![trigger self.l2_tables.view().spec_index(p).value().spec_index(i)]
                pei_valid(i) && self.l2_tables.view().spec_index(p).value().spec_index(i).perm.ps && self.l2_tables.view().spec_index(p).value().spec_index(i).perm.present
                    ==> self.l2_tables.view().spec_index(p).value().spec_index(i).perm.kernel_present
        // All L2 maps to valid L1 tables
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables.view().dom().contains(p)]
            self.l2_tables.view().dom().contains(p) ==> forall|i: L2Index|
                #![trigger self.l2_tables.view().spec_index(p).value().spec_index(i)]
                pei_valid(i) && self.l2_tables.view().spec_index(p).value().spec_index(i).perm.present && self.l2_tables.view().spec_index(p).value().spec_index(i).perm.ps == false
                    ==> self.l1_tables.view().dom().contains(self.l2_tables.view().spec_index(p).value().spec_index(i).addr)
    }

    #[verifier::opaque]
    pub open spec fn disjoint_l2(&self) -> bool {
        // L2 mappings are unique
        &&& forall|pi: PageMapPtr, pj: PageMapPtr|
            #![trigger self.l2_tables.view().dom().contains(pi), self.l2_tables.view().dom().contains(pj)]
            self.l2_tables.view().dom().contains(pi) && self.l2_tables.view().dom().contains(pj) ==> forall|l2i: L2Index, l2j: L2Index|
                #![trigger pei_valid(l2i), pei_valid(l2j), self.l2_tables.view().spec_index(pi).value().spec_index(l2i), self.l2_tables.view().spec_index(pj).value().spec_index(l2j)]
                pei_valid(l2i) && pei_valid(l2j) && self.l2_tables.view().spec_index(pi).value().spec_index(l2i).perm.present && !self.l2_tables.view().spec_index(pi).value().spec_index(l2i).perm.ps
                && self.l2_tables.view().spec_index(pj).value().spec_index(l2j).perm.present && !self.l2_tables.view().spec_index(pj).value().spec_index(l2j).perm.ps ==> {
                    &&& pi != pj ==> self.l2_tables.view().spec_index(pi).value().spec_index(l2i).addr != self.l2_tables.view().spec_index(pj).value().spec_index(l2j).addr
                    &&& pi == pj && l2i != l2j ==> self.l2_tables.view().spec_index(pi).value().spec_index(l2i).addr != self.l2_tables.view().spec_index(pj).value().spec_index(l2j).addr
                }
    }

    #[verifier::opaque]
    pub open spec fn wf_l1(&self) -> bool {
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables.view().dom().contains(p)]
            self.l1_tables.view().dom().contains(p) ==> self.l1_tables.view().spec_index(p).addr() == p && self.l1_tables.view().spec_index(p).is_init() && self.l1_tables.view().spec_index(p).value().wf()
        // no hugepage in l1
        // Last level page entry must have kernel present set if it's present
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables.view().dom().contains(p)]
            self.l1_tables.view().dom().contains(p) ==> forall|i: L1Index|
                #![trigger self.l1_tables.view().spec_index(p).value().spec_index(i)]
                pei_valid(i) && self.l1_tables.view().spec_index(p).value().spec_index(i).perm.present
                    ==> self.l1_tables.view().spec_index(p).value().spec_index(i).perm.ps == false && self.l1_tables.view().spec_index(p).value().spec_index(i).perm.kernel_present
    }

    #[verifier::opaque]
    pub open spec fn user_only(&self) -> bool {
        &&& forall|i: L4Index|
            #![trigger self.l4_table.view().spec_index(self.cr3).value().spec_index(i)]
            self.kernel_l4_end <= i && pei_valid(i) && self.l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.present
                ==> self.l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.user
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(p)]
            self.l3_tables.view().dom().contains(p) ==> forall|i: L3Index|
                #![trigger self.l3_tables.view().spec_index(p).value().spec_index(i)]
                pei_valid(i) && self.l3_tables.view().spec_index(p).value().spec_index(i).perm.present ==> self.l3_tables.view().spec_index(p).value().spec_index(i).perm.user
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables.view().dom().contains(p)]
            self.l2_tables.view().dom().contains(p) ==> forall|i: L2Index|
                #![trigger self.l2_tables.view().spec_index(p).value().spec_index(i)]
                pei_valid(i) && self.l2_tables.view().spec_index(p).value().spec_index(i).perm.present ==> self.l2_tables.view().spec_index(p).value().spec_index(i).perm.user
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables.view().dom().contains(p)]
            self.l1_tables.view().dom().contains(p) ==> forall|i: L1Index|
                #![trigger self.l1_tables.view().spec_index(p).value().spec_index(i)]
                pei_valid(i) && self.l1_tables.view().spec_index(p).value().spec_index(i).perm.present ==> self.l1_tables.view().spec_index(p).value().spec_index(i).perm.user
    }

    #[verifier::opaque]
    pub open spec fn rwx_upper_level_entries(&self) -> bool {
        &&& forall|i: L4Index|
            #![trigger self.l4_table.view().spec_index(self.cr3).value().spec_index(i)]
            self.kernel_l4_end <= i && pei_valid(i) && self.l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.present
                ==> self.l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.write && !self.l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.execute_disable
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(p)]
            self.l3_tables.view().dom().contains(p) ==> forall|i: L3Index|
                #![trigger self.l3_tables.view().spec_index(p).value().spec_index(i)]
                pei_valid(i) && self.l3_tables.view().spec_index(p).value().spec_index(i).perm.present && !self.l3_tables.view().spec_index(p).value().spec_index(i).perm.ps
                    ==> self.l3_tables.view().spec_index(p).value().spec_index(i).perm.write && !self.l3_tables.view().spec_index(p).value().spec_index(i).perm.execute_disable
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables.view().dom().contains(p)]
            self.l2_tables.view().dom().contains(p) ==> forall|i: L2Index|
                #![trigger self.l2_tables.view().spec_index(p).value().spec_index(i)]
                pei_valid(i) && self.l2_tables.view().spec_index(p).value().spec_index(i).perm.present && !self.l2_tables.view().spec_index(p).value().spec_index(i).perm.ps
                    ==> self.l2_tables.view().spec_index(p).value().spec_index(i).perm.write && !self.l2_tables.view().spec_index(p).value().spec_index(i).perm.execute_disable
    }

    #[verifier::opaque]
    pub open spec fn table_pages_wf(&self) -> bool {
        &&& page_ptr_valid(self.cr3)
        &&& forall|p: PageMapPtr| #![trigger self.l3_tables.view().dom().contains(p), page_ptr_valid(p)] self.l3_tables.view().dom().contains(p) ==> page_ptr_valid(p)
        &&& forall|p: PageMapPtr| #![trigger self.l2_tables.view().dom().contains(p), page_ptr_valid(p)] self.l2_tables.view().dom().contains(p) ==> page_ptr_valid(p)
        &&& forall|p: PageMapPtr| #![trigger self.l1_tables.view().dom().contains(p), page_ptr_valid(p)] self.l1_tables.view().dom().contains(p) ==> page_ptr_valid(p)
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

    pub proof fn table_pages_wf_l3_at(&self, p: PageMapPtr)
        requires
            self.table_pages_wf(),
            self.l3_tables.view().dom().contains(p),
        ensures !self.l4_table.view().dom().contains(p),
    { reveal(PageTable::table_pages_wf); }

    pub proof fn table_pages_wf_l2_at(&self, p: PageMapPtr)
        requires
            self.table_pages_wf(),
            self.l2_tables.view().dom().contains(p),
        ensures !self.l4_table.view().dom().contains(p),
    { reveal(PageTable::table_pages_wf); }

    pub proof fn table_pages_wf_l1_at(&self, p: PageMapPtr)
        requires
            self.table_pages_wf(),
            self.l1_tables.view().dom().contains(p),
        ensures !self.l4_table.view().dom().contains(p),
    { reveal(PageTable::table_pages_wf); }

    pub open spec fn spec_resolve_mapping_l4(&self, l4i: L4Index) -> Option<PageEntry>
        recommends
            self.kernel_l4_end <= l4i && pei_valid(l4i),
    {
        if self.l4_table.view().spec_index(self.cr3).value().spec_index(l4i).perm.present || l4i < self.kernel_l4_end { Some(self.l4_table.view().spec_index(self.cr3).value().spec_index(l4i)) }
        else { None }
    }

    pub open spec fn spec_resolve_mapping_1g_l3(&self, l4i: L4Index, l3i: L3Index) -> Option<PageEntry>
        recommends
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
    {
        if self.spec_resolve_mapping_l4(l4i) is Some
            && self.l3_tables.view().spec_index(self.spec_resolve_mapping_l4(l4i)->0.addr).value().spec_index(l3i).perm.ps
            && self.l3_tables.view().spec_index(self.spec_resolve_mapping_l4(l4i)->0.addr).value().spec_index(l3i).perm.kernel_present {
            Some(self.l3_tables.view().spec_index(self.spec_resolve_mapping_l4(l4i)->0.addr).value().spec_index(l3i))
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
            && self.l3_tables.view().spec_index(self.spec_resolve_mapping_l4(l4i)->0.addr).value().spec_index(l3i).perm.present
            && self.l3_tables.view().spec_index(self.spec_resolve_mapping_l4(l4i)->0.addr).value().spec_index(l3i).perm.ps == false {
            Some(self.l3_tables.view().spec_index(self.spec_resolve_mapping_l4(l4i)->0.addr).value().spec_index(l3i))
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
            && self.l2_tables.view().spec_index(self.spec_resolve_mapping_l3(l4i,l3i)->0.addr).value().spec_index(l2i).perm.kernel_present
            && self.l2_tables.view().spec_index(self.spec_resolve_mapping_l3(l4i,l3i)->0.addr).value().spec_index(l2i).perm.ps {
            Some(self.l2_tables.view().spec_index(self.spec_resolve_mapping_l3(l4i,l3i)->0.addr).value().spec_index(l2i))
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
            && self.l2_tables.view().spec_index(self.spec_resolve_mapping_l3(l4i,l3i)->0.addr).value().spec_index(l2i).perm.present
            && self.l2_tables.view().spec_index(self.spec_resolve_mapping_l3(l4i,l3i)->0.addr).value().spec_index(l2i).perm.ps == false {
            Some(self.l2_tables.view().spec_index(self.spec_resolve_mapping_l3(l4i,l3i)->0.addr).value().spec_index(l2i))
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
        if self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some && self.l1_tables.view().spec_index(self.spec_resolve_mapping_l2(l4i,l3i,l2i)->0.addr).value().spec_index(l1i).perm.kernel_present {
            Some(self.l1_tables.view().spec_index(self.spec_resolve_mapping_l2(l4i,l3i,l2i)->0.addr).value().spec_index(l1i))
        } else {
            None
        }
    }

    pub open spec fn va_addr_valid(&self) -> bool { self.va_addr_valid_inner() }

    pub open spec fn va_addr_valid_inner(&self) -> bool {
        &&& forall|va: VAddr|
            #![trigger va_4k_valid(va), self.mapping_4k.view().dom().contains(va)]
            #![trigger self.mapping_4k.view().dom().contains(va), page_ptr_valid(self.mapping_4k.view().spec_index(va).addr)]
            #![trigger self.mapping_4k.view().dom().contains(va)]
            #![trigger page_ptr_valid(self.mapping_4k.view().spec_index(va).addr)]
            self.mapping_4k.view().dom().contains(va) ==> page_table_key_4k_valid::<TABLE_TYPE>(va) && page_ptr_valid(self.mapping_4k.view().spec_index(va).addr)
        &&& forall|va: VAddr|
            #![trigger va_2m_valid(va), self.mapping_2m.view().dom().contains(va)]
            #![trigger self.mapping_2m.view().dom().contains(va), page_ptr_2m_valid(self.mapping_2m.view().spec_index(va).addr)]
            #![trigger self.mapping_2m.view().dom().contains(va)]
            self.mapping_2m.view().dom().contains(va) ==> page_table_key_2m_valid::<TABLE_TYPE>(va) && page_ptr_2m_valid(self.mapping_2m.view().spec_index(va).addr)
        &&& forall|va: VAddr|
            #![trigger va_1g_valid(va), self.mapping_1g.view().dom().contains(va)]
            #![trigger self.mapping_1g.view().dom().contains(va), page_ptr_1g_valid(self.mapping_1g.view().spec_index(va).addr)]
            #![trigger self.mapping_1g.view().dom().contains(va)]
            self.mapping_1g.view().dom().contains(va) ==> page_table_key_1g_valid::<TABLE_TYPE>(va) && page_ptr_1g_valid(self.mapping_1g.view().spec_index(va).addr)
    }

    #[verifier::opaque]
    pub open spec fn wf_mapping_4k(&self) -> bool {
        &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
            #![trigger self.mapping_4k.view().spec_index(spec_index2va((l4i,l3i,l2i,l1i)))]
            #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
            self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> {
                    &&& self.mapping_4k.view().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))) == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some
                    &&& self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some
                        ==> self.mapping_4k.view().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).addr == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.addr
                        && self.mapping_4k.view().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).write == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.perm.write
                        && self.mapping_4k.view().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).execute_disable == self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)->0.perm.execute_disable
                        && self.mapping_4k.view().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present == self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)->0.perm.present
                }
    }

    #[verifier::opaque]
    pub open spec fn wf_mapping_2m(&self) -> bool {
        &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger self.mapping_2m.view().spec_index(spec_index2va((l4i,l3i,l2i,0)))]
            #![trigger self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)]
            self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> (self.mapping_2m.view().dom().contains(spec_index2va((l4i, l3i, l2i, 0))) == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some) && (self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some
                    ==> self.mapping_2m.view().spec_index(spec_index2va((l4i, l3i, l2i, 0))).addr == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.addr
                    && self.mapping_2m.view().spec_index(spec_index2va((l4i, l3i, l2i, 0))).write == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.perm.write
                    && self.mapping_2m.view().spec_index(spec_index2va((l4i, l3i, l2i, 0))).execute_disable == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.perm.execute_disable
                    && self.mapping_2m.view().spec_index(spec_index2va((l4i, l3i, l2i, 0))).present == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.perm.present)
    }

    #[verifier::opaque]
    pub open spec fn wf_mapping_1g(&self) -> bool {
        &&& forall|l4i: L4Index, l3i: L3Index|
            #![trigger self.mapping_1g.view().spec_index(spec_index2va((l4i,l3i,0,0)))]
            #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
            self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> {
                    &&& self.mapping_1g.view().dom().contains(spec_index2va((l4i, l3i, 0, 0))) == self.spec_resolve_mapping_1g_l3(l4i, l3i) is Some
                    &&& self.spec_resolve_mapping_1g_l3(l4i,l3i) is Some
                        ==> self.mapping_1g.view().spec_index(spec_index2va((l4i, l3i, 0, 0))).addr == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.addr
                        && self.mapping_1g.view().spec_index(spec_index2va((l4i, l3i, 0, 0))).write == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.perm.write
                        && self.mapping_1g.view().spec_index(spec_index2va((l4i, l3i, 0, 0))).execute_disable == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.perm.execute_disable
                        && self.mapping_1g.view().spec_index(spec_index2va((l4i, l3i, 0, 0))).present == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.perm.present
                }
    }

    /// Every walk-table page hangs under the user part of the root at the path its reverse map records.
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

    #[verifier::opaque]
    pub open spec fn kernel_entries_wf(&self) -> bool {
        &&& TABLE_TYPE == IOMMU_TYPE ==> self.kernel_l4_end == 0
        &&& pei_valid(self.kernel_l4_end)
        &&& self.kernel_entries.view().len() =~= self.kernel_l4_end as nat
        &&& forall|i: usize|
            #![trigger self.kernel_entries.view().spec_index(i as int)]
            0 <= i < self.kernel_l4_end && pei_valid(i) ==> self.kernel_entries.view().spec_index(i as int) == self.l4_table.view().spec_index(self.cr3).value().spec_index(i)
    }

    pub proof fn kernel_l4_end_valid(&self)
        requires
            self.kernel_entries_wf()
        ensures
            pei_valid(self.kernel_l4_end)
    {
        reveal(PageTable::kernel_entries_wf);
    }

    pub proof fn kernel_entries_wf_l4_end_at(&self)
        requires self.kernel_entries_wf()
        ensures TABLE_TYPE == IOMMU_TYPE ==> self.kernel_l4_end == 0
    { reveal(PageTable::kernel_entries_wf); }

    pub proof fn kernel_entries_wf_len_at(&self)
        requires self.kernel_entries_wf()
        ensures
            pei_valid(self.kernel_l4_end),
            self.kernel_entries.view().len() == self.kernel_l4_end as nat,
    { reveal(PageTable::kernel_entries_wf); }

    pub proof fn wf_mapping_2m_at(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index)
        requires
            self.wf_mapping_2m(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
        ensures
            self.mapping_2m.view().dom().contains(spec_index2va((l4i, l3i, l2i, 0))) == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some,
            self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some
                ==> self.mapping_2m.view().spec_index(spec_index2va((l4i, l3i, l2i, 0))).addr == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.addr
                && self.mapping_2m.view().spec_index(spec_index2va((l4i, l3i, l2i, 0))).write == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.perm.write
                && self.mapping_2m.view().spec_index(spec_index2va((l4i, l3i, l2i, 0))).execute_disable == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.perm.execute_disable
                && self.mapping_2m.view().spec_index(spec_index2va((l4i, l3i, l2i, 0))).present == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.perm.present,
    { reveal(PageTable::wf_mapping_2m); }

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
    { reveal(PageTable::wf_mapping_1g); }

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

impl<const TABLE_TYPE: PTType> LockInvTrait for PageTable<TABLE_TYPE> {
    open spec fn inv(&self) -> bool {
        &&& self.wf()
    }
}
impl<const TABLE_TYPE: PTType> LockMajorTrait for PageTable<TABLE_TYPE> {
    open spec fn lock_major_1(&self) -> LockMajorId { 0x233 }
    open spec fn lock_major_2(&self) -> LockMajorId { 0x233 }
    open spec fn lock_major_3(&self) -> LockMajorId { 0x233 }

    open spec fn lock_major_default(&self) -> LockMajorId {
        if TABLE_TYPE == PT_TYPE { PAGE_TABLE_LOCK_MAJOR }
        else { IOMMU_TABLE_LOCK_MAJOR }
    }

    open spec fn lock_major_1_predicate(&self) -> bool { false }
    open spec fn lock_major_2_predicate(&self) -> bool { false }
    open spec fn lock_major_3_predicate(&self) -> bool { false }
    open spec fn lock_major_default_predicate(&self) -> bool { true }
}

impl<const TABLE_TYPE: PTType> LockOwnerIdTrait for PageTable<TABLE_TYPE> {
    open spec fn container_depth(&self) -> LockOwnerId { LockOwnerId::none() }
    open spec fn process_depth(&self) -> LockOwnerId { LockOwnerId::none() }
}
} // verus!
