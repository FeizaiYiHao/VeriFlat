use vstd::prelude::*;
verus! {
use crate::*;
use vstd::simple_pptr::*;
use super::l2_page_map::*;

/// Big-lock payload of a split page table: L4/L3 directories, 1G leaves and bookkeeping.
///
/// `LockInvTrait::inv` is the L4/L3/1G half of the table invariant, so the holder of the big lock in either mode
/// gets it from the lock. The cross-half and lower-half clauses live in `PageTableC::wf`.
pub struct PageTableHigher<const TABLE_TYPE: PTType> {
    pub cr3: PageTableRoot,
    pub pcid: Option<Pcid>,
    pub did: Option<VtdDomainId>,
    pub kernel_l4_end: usize,
    pub l4_table: Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    pub l3_rev_map: Ghost<Map<PageMapPtr, (L4Index)>>,
    pub l3_tables: Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    pub l2_rev_map: Ghost<Map<PageMapPtr, (L4Index, L3Index)>>,
    pub mapping_1g: Ghost<Map<VAddr, MapEntry>>,
    pub kernel_entries: Ghost<Seq<PageEntry>>,
    pub proc_ptr: RwLockProcessPtr,
}

/// Window half: L2 pages (each entry a 2M-window spin lock that also owns the L1 page it links), the L1 reverse
/// map, 4K and 2M leaves, the lock mode of every window of an existing L2 page, and for each 2M window
/// `(L2 page, L2 index)` that still hides cleared leaves from some TLB, the CPUs that have neither flushed nor
/// skipped it yet.
pub tracked struct PageTableLower<const TABLE_TYPE: PTType> {
    pub tracked l2_perms: Map<PageMapPtr, PointsTo<L2PageMap>>,
    pub ghost l1_rev_map: Map<PageMapPtr, (L4Index, L3Index, L2Index)>,
    pub ghost mapping_4k: Map<VAddr, MapEntry>,
    pub ghost mapping_2m: Map<VAddr, MapEntry>,
    pub ghost pagetable_window_locks: Map<WindowVa, LockStateU>,
    pub ghost window_stale_cpus: Map<(PageMapPtr, L2Index), Set<CpuId>>,
}

/// One whole page table: the big-lock payload and its window half.
pub ghost struct PageTableC<const TABLE_TYPE: PTType> {
    pub higher: PageTableHigher<TABLE_TYPE>,
    pub lower: PageTableLower<TABLE_TYPE>,
}

/// One 2M window as its holder sees it: its L2 page and entry, the entry's lock owner, the L1 page that entry links,
/// and the CPUs that still owe the window a TLB flush.
pub ghost struct PageTableWindowView {
    pub l2_page: PageMapPtr,
    pub l2_entry: PageEntry,
    pub lock_state: SpinLockState,
    pub l1_table: Option<PointsTo<PageMap>>,
    pub stale_cpus: Option<Set<CpuId>>,
}

/// Base address of one 2M window. Alignment is `wf`, not a type invariant: the window lock map and
/// `pagetable_window_locks` carry it in their invariants.
pub ghost struct WindowVa { pub va: VAddr }

impl WindowVa {
    /// A 2M-aligned user address.
    pub open spec fn wf(&self) -> bool { page_table_key_2m_valid::<PT_TYPE>(self.va) }
    pub open spec fn l4i(&self) -> L4Index { spec_v2l4index(self.va) }
    pub open spec fn l3i(&self) -> L3Index { spec_v2l3index(self.va) }
    pub open spec fn l2i(&self) -> L2Index { spec_v2l2index(self.va) }
}

/// The 2M window that contains `va`.
pub open spec fn window_of(va: VAddr) -> WindowVa { WindowVa { va: spec_index2va((spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), 0)) } }

/// Window `(l4i, l3i, l2i)` of the table rooted at `root`; window locks follow every page-table and IOMMU table lock.
pub open spec fn window_lock_id(root: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> LockId {
    LockId { container: LockOwnerId::None, process: LockOwnerId::None, major: PAGE_TABLE_WINDOW_LOCK_MAJOR, minor: seq![root, l4i, l3i, l2i] }
}

pub open spec fn window_obj_id(root: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> KernelObjId {
    KernelObjId::PageTableWindow(root, WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) })
}

/// `window_lock_id` of window `w`.
pub open spec fn window_lock_id_of(root: RwLockPageTableRoot, w: WindowVa) -> LockId { window_lock_id(root, spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va)) }

/// `window_obj_id` of window `w`.
pub open spec fn window_obj_id_of(root: RwLockPageTableRoot, w: WindowVa) -> KernelObjId { window_obj_id(root, spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va)) }

/// Bases of the 2M windows that cover `range`: the 2M-aligned user addresses in path order between the windows of its
/// first and last page.
pub open spec fn va_range_2m_windows(range: VaRange4K) -> ISet<WindowVa> {
    let first = spec_va2index(range.start);
    let last = spec_va2index(range.view().spec_index(range.len - 1));
    ISet::new(|w: WindowVa| page_table_key_2m_valid::<PT_TYPE>(w.va) && spec_l4_index_path_le((first.0, first.1, first.2, 0), spec_va2index(w.va)) && spec_l4_index_path_le(spec_va2index(w.va), (last.0, last.1, last.2, 0)))
}

impl<const TABLE_TYPE: PTType> PageTableHigher<TABLE_TYPE> {
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

    #[verifier::opaque]
    pub open spec fn wf_l4(&self) -> bool {
        &&& self.l4_table.view().dom() =~= Set::<PageMapPtr>::empty().insert(self.cr3)
        &&& self.cr3 == self.l4_table.view().spec_index(self.cr3).addr()
        &&& self.l4_table.view().spec_index(self.cr3).is_init()
        &&& self.l4_table.view().spec_index(self.cr3).value().wf()
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
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(p)]
            self.l3_tables.view().dom().contains(p) ==> forall|i: L3Index|
                #![trigger self.l3_tables.view().spec_index(p).value().spec_index(i)]
                pei_valid(i) && self.l3_tables.view().spec_index(p).value().spec_index(i).perm.ps && self.l3_tables.view().spec_index(p).value().spec_index(i).perm.present
                    ==> self.l3_tables.view().spec_index(p).value().spec_index(i).perm.kernel_present
    }

    #[verifier::opaque]
    pub open spec fn disjoint_l3(&self) -> bool {
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
    }

    #[verifier::opaque]
    pub open spec fn table_pages_wf(&self) -> bool {
        &&& page_ptr_valid(self.cr3)
        &&& forall|p: PageMapPtr| #![trigger self.l3_tables.view().dom().contains(p), page_ptr_valid(p)] self.l3_tables.view().dom().contains(p) ==> page_ptr_valid(p)
        &&& self.l4_table.view().dom().disjoint(self.l3_tables.view().dom())
    }

    /// Every L3 page hangs under the user part of the root at the index its reverse map records.
    #[verifier::opaque]
    pub open spec fn tables_reachable_wf(&self) -> bool {
        forall|p: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(p)]
            self.l3_tables.view().dom().contains(p) ==> {
                let l4i = self.l3_rev_map.view().spec_index(p);
                &&& self.kernel_l4_end <= l4i && pei_valid(l4i)
                &&& self.spec_resolve_mapping_l4(l4i) is Some && self.spec_resolve_mapping_l4(l4i)->0.addr == p
            }
    }

    pub open spec fn va_addr_valid(&self) -> bool {
        forall|va: VAddr|
            #![trigger va_1g_valid(va), self.mapping_1g.view().dom().contains(va)]
            #![trigger self.mapping_1g.view().dom().contains(va), page_ptr_1g_valid(self.mapping_1g.view().spec_index(va).addr)]
            #![trigger self.mapping_1g.view().dom().contains(va)]
            self.mapping_1g.view().dom().contains(va) ==> page_table_key_1g_valid::<TABLE_TYPE>(va) && page_ptr_1g_valid(self.mapping_1g.view().spec_index(va).addr)
    }

    #[verifier::opaque]
    pub open spec fn wf_mapping_1g(&self) -> bool {
        &&& forall|l4i: L4Index, l3i: L3Index|
            #![trigger self.mapping_1g.view().spec_index(spec_index2va((l4i, l3i, 0, 0)))]
            #![trigger self.spec_resolve_mapping_1g_l3(l4i, l3i)]
            self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> {
                    &&& self.mapping_1g.view().dom().contains(spec_index2va((l4i, l3i, 0, 0))) == self.spec_resolve_mapping_1g_l3(l4i, l3i) is Some
                    &&& self.spec_resolve_mapping_1g_l3(l4i, l3i) is Some
                        ==> self.mapping_1g.view().spec_index(spec_index2va((l4i, l3i, 0, 0))).addr == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.addr
                        && self.mapping_1g.view().spec_index(spec_index2va((l4i, l3i, 0, 0))).write == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.perm.write
                        && self.mapping_1g.view().spec_index(spec_index2va((l4i, l3i, 0, 0))).execute_disable == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.perm.execute_disable
                        && self.mapping_1g.view().spec_index(spec_index2va((l4i, l3i, 0, 0))).present == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.perm.present
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
}

impl<const TABLE_TYPE: PTType> LockInvTrait for PageTableHigher<TABLE_TYPE> {
    open spec fn inv(&self) -> bool {
        &&& self.va_addr_valid()
        &&& self.wf_l4()
        &&& self.wf_l3()
        &&& self.disjoint_l4()
        &&& self.disjoint_l3()
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

impl<const TABLE_TYPE: PTType> LockMajorTrait for PageTableHigher<TABLE_TYPE> {
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

impl<const TABLE_TYPE: PTType> LockOwnerIdTrait for PageTableHigher<TABLE_TYPE> {
    open spec fn container_depth(&self) -> LockOwnerId { LockOwnerId::none() }
    open spec fn process_depth(&self) -> LockOwnerId { LockOwnerId::none() }
}

impl<const TABLE_TYPE: PTType> PageTableLower<TABLE_TYPE> {
    #[verifier::inline]
    pub open spec fn l2_page(&self, p: PageMapPtr) -> L2PageMap { self.l2_perms.spec_index(p).value() }

    #[verifier::inline]
    pub open spec fn l2_entry(&self, p: PageMapPtr, i: L2Index) -> PageEntry { self.l2_page(p).entry_lock(i).view() }

    #[verifier::inline]
    pub open spec fn l2_owner(&self, p: PageMapPtr, i: L2Index) -> SpinLockState { self.l2_page(p).entry_lock(i).owner() }

    #[verifier::inline]
    pub open spec fn l1_perm(&self, p: PageMapPtr, i: L2Index) -> PointsTo<PageMap> { self.l2_page(p).entry_lock(i).l1()->Some_0 }

    #[verifier::inline]
    pub open spec fn l1_page(&self, p: PageMapPtr, i: L2Index) -> PageMap { self.l1_perm(p, i).value() }
}

impl<const TABLE_TYPE: PTType> PageTableC<TABLE_TYPE> {
    pub open spec fn cr3(&self) -> PageTableRoot { self.higher.cr3 }
    pub open spec fn did(&self) -> Option<VtdDomainId> { self.higher.did }
    pub open spec fn kernel_l4_end(&self) -> usize { self.higher.kernel_l4_end }
    pub open spec fn mapping_4k(&self) -> Map<VAddr, MapEntry> { self.lower.mapping_4k }
    pub open spec fn mapping_2m(&self) -> Map<VAddr, MapEntry> { self.lower.mapping_2m }
    pub open spec fn mapping_1g(&self) -> Map<VAddr, MapEntry> { self.higher.mapping_1g.view() }

    /// The owner of the outer RwLock supplies its mode; the payload has no lock state.
    pub open spec fn user_view(&self, lock_state: LockStateU) -> PageTableU {
        PageTableU {
            lock_state,
            did: if TABLE_TYPE == PT_TYPE { None } else { self.did() },
            mapping_4k: self.mapping_4k().filter_keys(|va: VAddr| self.mapping_4k().spec_index(va).present),
            mapping_2m: self.mapping_2m().filter_keys(|va: VAddr| self.mapping_2m().spec_index(va).present),
            mapping_1g: self.mapping_1g().filter_keys(|va: VAddr| self.mapping_1g().spec_index(va).present),
            pagetable_window_locks: self.lower.pagetable_window_locks,
        }
    }

    /// Every 4K, 2M, and 1G leaf is user-present, so the user view shows the whole mapping.
    pub open spec fn leaves_present(&self) -> bool {
        &&& forall|va: VAddr| #![trigger self.mapping_4k().dom().contains(va)] self.mapping_4k().dom().contains(va) ==> self.mapping_4k().spec_index(va).present
        &&& forall|va: VAddr| #![trigger self.mapping_2m().dom().contains(va)] self.mapping_2m().dom().contains(va) ==> self.mapping_2m().spec_index(va).present
        &&& forall|va: VAddr| #![trigger self.mapping_1g().dom().contains(va)] self.mapping_1g().dom().contains(va) ==> self.mapping_1g().spec_index(va).present
    }

    pub open spec fn is_empty(&self) -> bool {
        &&& forall|i: L4Index|
            #![trigger self.higher.l4_table.view().spec_index(self.cr3()).value().spec_index(i).perm.present]
            self.kernel_l4_end() <= i && pei_valid(i) ==> self.higher.l4_table.view().spec_index(self.cr3()).value().spec_index(i).is_empty()
        &&& self.higher.l3_tables.view().dom() == Set::<PageMapPtr>::empty()
        &&& self.lower.l2_perms.dom() == Set::<PageMapPtr>::empty()
        &&& self.lower.l1_rev_map.dom() == Set::<PageMapPtr>::empty()
        &&& self.mapping_4k() == Map::<VAddr, MapEntry>::empty()
        &&& self.mapping_2m() == Map::<VAddr, MapEntry>::empty()
        &&& self.mapping_1g() == Map::<VAddr, MapEntry>::empty()
        &&& self.lower.pagetable_window_locks == Map::<WindowVa, LockStateU>::empty()
        &&& self.lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()
    }

    pub open spec fn page_closure(&self) -> Set<PagePtr> {
        self.higher.l3_tables.view().dom() + self.lower.l2_perms.dom() + self.lower.l1_rev_map.dom() + self.higher.l4_table.view().dom()
    }

    // The L4/L3 walk belongs to the big-lock payload; inline so both levels share one trigger term.
    #[verifier::inline]
    pub open spec fn spec_resolve_mapping_l4(&self, l4i: L4Index) -> Option<PageEntry> { self.higher.spec_resolve_mapping_l4(l4i) }
    #[verifier::inline]
    pub open spec fn spec_resolve_mapping_1g_l3(&self, l4i: L4Index, l3i: L3Index) -> Option<PageEntry> { self.higher.spec_resolve_mapping_1g_l3(l4i, l3i) }
    #[verifier::inline]
    pub open spec fn spec_resolve_mapping_l3(&self, l4i: L4Index, l3i: L3Index) -> Option<PageEntry> { self.higher.spec_resolve_mapping_l3(l4i, l3i) }

    pub open spec fn spec_resolve_mapping_2m_l2(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> Option<PageEntry>
        recommends
            self.kernel_l4_end() <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
    {
        if self.spec_resolve_mapping_l3(l4i, l3i) is Some
            && self.lower.l2_entry(self.spec_resolve_mapping_l3(l4i, l3i)->0.addr, l2i).perm.kernel_present
            && self.lower.l2_entry(self.spec_resolve_mapping_l3(l4i, l3i)->0.addr, l2i).perm.ps {
            Some(self.lower.l2_entry(self.spec_resolve_mapping_l3(l4i, l3i)->0.addr, l2i))
        } else {
            None
        }
    }

    pub open spec fn spec_resolve_mapping_l2(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> Option<PageEntry>
        recommends
            self.kernel_l4_end() <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
    {
        if self.spec_resolve_mapping_l3(l4i, l3i) is Some
            && self.lower.l2_entry(self.spec_resolve_mapping_l3(l4i, l3i)->0.addr, l2i).perm.present
            && self.lower.l2_entry(self.spec_resolve_mapping_l3(l4i, l3i)->0.addr, l2i).perm.ps == false {
            Some(self.lower.l2_entry(self.spec_resolve_mapping_l3(l4i, l3i)->0.addr, l2i))
        } else {
            None
        }
    }

    pub open spec fn spec_resolve_mapping_4k_l1(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index) -> Option<PageEntry>
        recommends
            self.kernel_l4_end() <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            pei_valid(l1i),
    {
        if self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some && self.lower.l1_page(self.spec_resolve_mapping_l3(l4i, l3i)->0.addr, l2i).spec_index(l1i).perm.kernel_present {
            Some(self.lower.l1_page(self.spec_resolve_mapping_l3(l4i, l3i)->0.addr, l2i).spec_index(l1i))
        } else {
            None
        }
    }

    /// The 512 windows under L3 entry `(l4i, l3i)` exist exactly when that entry links an L2 page.
    pub open spec fn window_exists(&self, l4i: L4Index, l3i: L3Index) -> bool
        recommends
            self.kernel_l4_end() <= l4i && pei_valid(l4i),
            pei_valid(l3i),
    {
        self.spec_resolve_mapping_l3(l4i, l3i) is Some
    }

    pub open spec fn window_l2_page(&self, l4i: L4Index, l3i: L3Index) -> PageMapPtr
        recommends
            self.window_exists(l4i, l3i),
    {
        self.spec_resolve_mapping_l3(l4i, l3i)->0.addr
    }

    pub open spec fn window_locked_by_thread(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId) -> bool {
        &&& self.window_exists(l4i, l3i)
        &&& self.lower.l2_owner(self.window_l2_page(l4i, l3i), l2i) is Some
        &&& self.lower.l2_owner(self.window_l2_page(l4i, l3i), l2i)->Some_thread_id == thread_id
    }

    /// Window `(l4i, l3i, l2i)` exists and some thread holds its lock; that holder is named so the window-holder
    /// invariant can fire on it.
    pub open spec fn window_locked(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> bool {
        self.window_locked_by_thread(l4i, l3i, l2i, self.lower.l2_owner(self.window_l2_page(l4i, l3i), l2i)->Some_thread_id)
    }

    /// Every 4K leaf the user cannot see lies in a locked 2M window; every 2M and 1G leaf is present.
    pub open spec fn hidden_leaves_in_locked_windows(&self) -> bool {
        &&& forall|va: VAddr| #![trigger self.mapping_4k().spec_index(va)] self.mapping_4k().dom().contains(va) && !self.mapping_4k().spec_index(va).present ==> self.window_locked(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))
        &&& forall|va: VAddr| #![trigger self.mapping_2m().dom().contains(va)] self.mapping_2m().dom().contains(va) ==> self.mapping_2m().spec_index(va).present
        &&& forall|va: VAddr| #![trigger self.mapping_1g().dom().contains(va)] self.mapping_1g().dom().contains(va) ==> self.mapping_1g().spec_index(va).present
    }

    /// The 4K leaves of window `w` and its 2M leaf are present.
    pub open spec fn window_leaves_present(&self, w: WindowVa) -> bool {
        &&& forall|va: VAddr|
            #![trigger self.mapping_4k().spec_index(va)]
            self.mapping_4k().dom().contains(va) && spec_v2l4index(va) == spec_v2l4index(w.va) && spec_v2l3index(va) == spec_v2l3index(w.va)
                && spec_v2l2index(va) == spec_v2l2index(w.va) ==> self.mapping_4k().spec_index(va).present
        &&& self.mapping_2m().dom().contains(w.va) ==> self.mapping_2m().spec_index(w.va).present
    }

    /// Window `w`: its L2 page and entry, that entry's lock owner, the L1 page the entry links, and its stale-CPU set.
    pub open spec fn window_view(&self, w: WindowVa) -> PageTableWindowView {
        let l2_page = self.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va));
        let l2i = spec_v2l2index(w.va);
        let l2_entry = self.lower.l2_entry(l2_page, l2i);
        PageTableWindowView {
            l2_page,
            l2_entry,
            lock_state: self.lower.l2_owner(l2_page, l2i),
            l1_table: self.lower.l2_page(l2_page).entry_lock(l2i).l1(),
            stale_cpus: if self.lower.window_stale_cpus.dom().contains((l2_page, l2i)) { Some(self.lower.window_stale_cpus.spec_index((l2_page, l2i))) } else { None },
        }
    }

    /// No thread other than `thread_id` holds window `(l4i, l3i, l2i)`.
    pub open spec fn window_free_for(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId) -> bool {
        self.window_exists(l4i, l3i) && self.lower.l2_owner(self.window_l2_page(l4i, l3i), l2i) is Some
            ==> self.lower.l2_owner(self.window_l2_page(l4i, l3i), l2i)->Some_thread_id == thread_id
    }

    /// Every present non-huge L3 entry links an L2 page of the window half.
    #[verifier::opaque]
    pub open spec fn wf_l3(&self) -> bool {
        forall|p: PageMapPtr|
            #![trigger self.higher.l3_tables.view().dom().contains(p)]
            self.higher.l3_tables.view().dom().contains(p) ==> forall|i: L3Index|
                #![trigger self.higher.l3_tables.view().spec_index(p).value().spec_index(i)]
                pei_valid(i) && self.higher.l3_tables.view().spec_index(p).value().spec_index(i).perm.present && !self.higher.l3_tables.view().spec_index(p).value().spec_index(i).perm.ps
                    ==> self.lower.l2_perms.dom().contains(self.higher.l3_tables.view().spec_index(p).value().spec_index(i).addr)
    }

    /// Each L2 page sits at its address with every entry `inv`; a huge present entry is kernel-present; a present
    /// non-huge entry, and only such an entry, owns the L1 page at its address, which the L1 reverse map records.
    #[verifier::opaque]
    pub open spec fn wf_l2(&self) -> bool {
        &&& forall|p: PageMapPtr|
            #![trigger self.lower.l2_perms.dom().contains(p)]
            self.lower.l2_perms.dom().contains(p) ==> {
                &&& self.lower.l2_perms.spec_index(p).addr() == p
                &&& self.lower.l2_perms.spec_index(p).is_init()
                &&& self.lower.l2_page(p).addr() == p
                &&& self.lower.l2_page(p).wf()
            }
        &&& forall|p: PageMapPtr|
            #![trigger self.lower.l2_perms.dom().contains(p)]
            self.lower.l2_perms.dom().contains(p) ==> forall|i: L2Index|
                #![trigger self.lower.l2_entry(p, i)]
                pei_valid(i) && self.lower.l2_entry(p, i).perm.ps && self.lower.l2_entry(p, i).perm.present ==> self.lower.l2_entry(p, i).perm.kernel_present
        &&& forall|p: PageMapPtr|
            #![trigger self.lower.l2_perms.dom().contains(p)]
            self.lower.l2_perms.dom().contains(p) ==> forall|i: L2Index|
                #![trigger self.lower.l2_page(p).entry_lock(i).l1()]
                pei_valid(i) ==> {
                    &&& (self.lower.l2_entry(p, i).perm.present && !self.lower.l2_entry(p, i).perm.ps) == (self.lower.l2_page(p).entry_lock(i).l1() is Some)
                    &&& self.lower.l2_page(p).entry_lock(i).l1() is Some
                        ==> self.lower.l1_perm(p, i).addr() == self.lower.l2_entry(p, i).addr && self.lower.l1_rev_map.dom().contains(self.lower.l2_entry(p, i).addr)
                }
    }

    #[verifier::opaque]
    pub open spec fn disjoint_l2(&self) -> bool {
        forall|pi: PageMapPtr, pj: PageMapPtr|
            #![trigger self.lower.l2_perms.dom().contains(pi), self.lower.l2_perms.dom().contains(pj)]
            self.lower.l2_perms.dom().contains(pi) && self.lower.l2_perms.dom().contains(pj) ==> forall|l2i: L2Index, l2j: L2Index|
                #![trigger pei_valid(l2i), pei_valid(l2j), self.lower.l2_entry(pi, l2i), self.lower.l2_entry(pj, l2j)]
                pei_valid(l2i) && pei_valid(l2j) && self.lower.l2_entry(pi, l2i).perm.present && !self.lower.l2_entry(pi, l2i).perm.ps
                && self.lower.l2_entry(pj, l2j).perm.present && !self.lower.l2_entry(pj, l2j).perm.ps ==> {
                    &&& pi != pj ==> self.lower.l2_entry(pi, l2i).addr != self.lower.l2_entry(pj, l2j).addr
                    &&& pi == pj && l2i != l2j ==> self.lower.l2_entry(pi, l2i).addr != self.lower.l2_entry(pj, l2j).addr
                }
    }

    /// Every L1 page that an L2 entry owns is initialized and well formed, and its present entries are 4K leaves.
    #[verifier::opaque]
    pub open spec fn wf_l1(&self) -> bool {
        &&& forall|p: PageMapPtr|
            #![trigger self.lower.l2_perms.dom().contains(p)]
            self.lower.l2_perms.dom().contains(p) ==> forall|i: L2Index|
                #![trigger self.lower.l1_perm(p, i)]
                pei_valid(i) && self.lower.l2_page(p).entry_lock(i).l1() is Some ==> self.lower.l1_perm(p, i).is_init() && self.lower.l1_page(p, i).wf()
        &&& forall|p: PageMapPtr|
            #![trigger self.lower.l2_perms.dom().contains(p)]
            self.lower.l2_perms.dom().contains(p) ==> forall|i: L2Index, j: L1Index|
                #![trigger self.lower.l1_page(p, i).spec_index(j)]
                pei_valid(i) && self.lower.l2_page(p).entry_lock(i).l1() is Some && pei_valid(j) && self.lower.l1_page(p, i).spec_index(j).perm.present
                    ==> self.lower.l1_page(p, i).spec_index(j).perm.ps == false && self.lower.l1_page(p, i).spec_index(j).perm.kernel_present
    }

    #[verifier::opaque]
    pub open spec fn user_only(&self) -> bool {
        &&& forall|p: PageMapPtr|
            #![trigger self.lower.l2_perms.dom().contains(p)]
            self.lower.l2_perms.dom().contains(p) ==> forall|i: L2Index| #![trigger self.lower.l2_entry(p, i)] pei_valid(i) && self.lower.l2_entry(p, i).perm.present ==> self.lower.l2_entry(p, i).perm.user
        &&& forall|p: PageMapPtr|
            #![trigger self.lower.l2_perms.dom().contains(p)]
            self.lower.l2_perms.dom().contains(p) ==> forall|i: L2Index, j: L1Index|
                #![trigger self.lower.l1_page(p, i).spec_index(j)]
                pei_valid(i) && self.lower.l2_page(p).entry_lock(i).l1() is Some && pei_valid(j) && self.lower.l1_page(p, i).spec_index(j).perm.present
                    ==> self.lower.l1_page(p, i).spec_index(j).perm.user
    }

    #[verifier::opaque]
    pub open spec fn rwx_upper_level_entries(&self) -> bool {
        forall|p: PageMapPtr|
            #![trigger self.lower.l2_perms.dom().contains(p)]
            self.lower.l2_perms.dom().contains(p) ==> forall|i: L2Index|
                #![trigger self.lower.l2_entry(p, i)]
                pei_valid(i) && self.lower.l2_entry(p, i).perm.present && !self.lower.l2_entry(p, i).perm.ps
                    ==> self.lower.l2_entry(p, i).perm.write && !self.lower.l2_entry(p, i).perm.execute_disable
    }

    #[verifier::opaque]
    pub open spec fn table_pages_wf(&self) -> bool {
        &&& forall|p: PageMapPtr| #![trigger self.lower.l2_perms.dom().contains(p), page_ptr_valid(p)] self.lower.l2_perms.dom().contains(p) ==> page_ptr_valid(p)
        &&& forall|p: PageMapPtr| #![trigger self.lower.l1_rev_map.dom().contains(p), page_ptr_valid(p)] self.lower.l1_rev_map.dom().contains(p) ==> page_ptr_valid(p)
        &&& self.higher.l4_table.view().dom().disjoint(self.lower.l2_perms.dom())
        &&& self.higher.l4_table.view().dom().disjoint(self.lower.l1_rev_map.dom())
        &&& self.higher.l3_tables.view().dom().disjoint(self.lower.l2_perms.dom())
        &&& self.higher.l3_tables.view().dom().disjoint(self.lower.l1_rev_map.dom())
        &&& self.lower.l2_perms.dom().disjoint(self.lower.l1_rev_map.dom())
    }

    /// Every L2 and L1 page hangs under the user part of the root at the path its reverse map records.
    #[verifier::opaque]
    pub open spec fn tables_reachable_wf(&self) -> bool {
        &&& forall|p: PageMapPtr|
            #![trigger self.lower.l2_perms.dom().contains(p)]
            self.lower.l2_perms.dom().contains(p) ==> {
                let (l4i, l3i) = self.higher.l2_rev_map.view().spec_index(p);
                &&& self.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i)
                &&& self.spec_resolve_mapping_l3(l4i, l3i) is Some && self.spec_resolve_mapping_l3(l4i, l3i)->0.addr == p
            }
        &&& forall|p: PageMapPtr|
            #![trigger self.lower.l1_rev_map.dom().contains(p)]
            self.lower.l1_rev_map.dom().contains(p) ==> {
                let (l4i, l3i, l2i) = self.lower.l1_rev_map.spec_index(p);
                &&& self.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                &&& self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some && self.spec_resolve_mapping_l2(l4i, l3i, l2i)->0.addr == p
            }
    }

    /// 4K and 2M keys and frames are valid; the 1G half is in `PageTableHigher::va_addr_valid`.
    pub open spec fn va_addr_valid(&self) -> bool {
        &&& forall|va: VAddr|
            #![trigger va_4k_valid(va), self.lower.mapping_4k.dom().contains(va)]
            #![trigger self.lower.mapping_4k.dom().contains(va), page_ptr_valid(self.lower.mapping_4k.spec_index(va).addr)]
            #![trigger self.lower.mapping_4k.dom().contains(va)]
            #![trigger page_ptr_valid(self.lower.mapping_4k.spec_index(va).addr)]
            self.lower.mapping_4k.dom().contains(va) ==> page_table_key_4k_valid::<TABLE_TYPE>(va) && page_ptr_valid(self.lower.mapping_4k.spec_index(va).addr)
        &&& forall|va: VAddr|
            #![trigger va_2m_valid(va), self.lower.mapping_2m.dom().contains(va)]
            #![trigger self.lower.mapping_2m.dom().contains(va), page_ptr_2m_valid(self.lower.mapping_2m.spec_index(va).addr)]
            #![trigger self.lower.mapping_2m.dom().contains(va)]
            self.lower.mapping_2m.dom().contains(va) ==> page_table_key_2m_valid::<TABLE_TYPE>(va) && page_ptr_2m_valid(self.lower.mapping_2m.spec_index(va).addr)
    }

    #[verifier::opaque]
    pub open spec fn wf_mapping_4k(&self) -> bool {
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
            #![trigger self.lower.mapping_4k.spec_index(spec_index2va((l4i, l3i, l2i, l1i)))]
            #![trigger self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
            self.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> {
                    &&& self.lower.mapping_4k.dom().contains(spec_index2va((l4i, l3i, l2i, l1i))) == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some
                    &&& self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some
                        ==> self.lower.mapping_4k.spec_index(spec_index2va((l4i, l3i, l2i, l1i))).addr == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.addr
                        && self.lower.mapping_4k.spec_index(spec_index2va((l4i, l3i, l2i, l1i))).write == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.perm.write
                        && self.lower.mapping_4k.spec_index(spec_index2va((l4i, l3i, l2i, l1i))).execute_disable == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.perm.execute_disable
                        && self.lower.mapping_4k.spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.perm.present
                }
    }

    #[verifier::opaque]
    pub open spec fn wf_mapping_2m(&self) -> bool {
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger self.lower.mapping_2m.spec_index(spec_index2va((l4i, l3i, l2i, 0)))]
            #![trigger self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)]
            self.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> (self.lower.mapping_2m.dom().contains(spec_index2va((l4i, l3i, l2i, 0))) == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some) && (self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some
                    ==> self.lower.mapping_2m.spec_index(spec_index2va((l4i, l3i, l2i, 0))).addr == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.addr
                    && self.lower.mapping_2m.spec_index(spec_index2va((l4i, l3i, l2i, 0))).write == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.perm.write
                    && self.lower.mapping_2m.spec_index(spec_index2va((l4i, l3i, l2i, 0))).execute_disable == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.perm.execute_disable
                    && self.lower.mapping_2m.spec_index(spec_index2va((l4i, l3i, l2i, 0))).present == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.perm.present)
    }

    /// `pagetable_window_locks` records, for every window it holds, an existing user window and the mode of that
    /// window's lock bit; it holds every window of every L2 page.
    #[verifier::opaque]
    pub open spec fn wf_window_locks(&self) -> bool {
        &&& forall|w: WindowVa|
            #![trigger self.lower.pagetable_window_locks.dom().contains(w)]
            self.lower.pagetable_window_locks.dom().contains(w) ==> {
                &&& page_table_key_2m_valid::<TABLE_TYPE>(w.va)
                &&& self.kernel_l4_end() <= spec_v2l4index(w.va)
                &&& self.window_exists(spec_v2l4index(w.va), spec_v2l3index(w.va))
                &&& self.lower.pagetable_window_locks.spec_index(w) == if self.lower.l2_owner(self.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)) is Some {
                    LockStateU::WriteLocked
                } else {
                    LockStateU::Unlocked
                }
            }
        &&& forall|p: PageMapPtr, i: L2Index|
            #![trigger self.lower.l2_owner(p, i)]
            #![trigger self.lower.pagetable_window_locks.dom().contains(WindowVa { va: spec_index2va((self.higher.l2_rev_map.view().spec_index(p).0, self.higher.l2_rev_map.view().spec_index(p).1, i, 0)) })]
            self.lower.l2_perms.dom().contains(p) && pei_valid(i) ==> {
                let (l4i, l3i) = self.higher.l2_rev_map.view().spec_index(p);
                self.lower.pagetable_window_locks.dom().contains(WindowVa { va: spec_index2va((l4i, l3i, i, 0)) })
            }
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.higher.inv()
        &&& self.va_addr_valid()
        &&& self.wf_l3()
        &&& self.wf_l2()
        &&& self.wf_l1()
        &&& self.disjoint_l2()
        &&& self.wf_mapping_4k()
        &&& self.wf_mapping_2m()
        &&& self.user_only()
        &&& self.rwx_upper_level_entries()
        &&& self.table_pages_wf()
        &&& self.tables_reachable_wf()
        &&& self.wf_window_locks()
    }
}
} // verus!
