use vstd::prelude::*;
verus! {
use crate::*;
use super::entry::*;
use super::page_map::*;
use vstd::simple_pptr::*;

/// Legacy 4-level VT-d second-level table, 4K leaves only. The IommuPageMap view is a bit lens; IOMMU publication has its own
/// codec. Hidden leaves keep address/kernel_present/software-XD in memory and old write permission in mapping_4k until domain
/// invalidation. Fields are public for specs only.
pub struct IommuTable {
    pub cr3: PageTableRoot,
    pub did: Option<VtdDomainId>,
    pub l4_table: Tracked<Map<PageMapPtr, PointsTo<IommuPageMap>>>,
    pub l3_rev_map: Ghost<Map<PageMapPtr, (L4Index)>>,
    pub l3_tables: Tracked<Map<PageMapPtr, PointsTo<IommuPageMap>>>,
    pub l2_rev_map: Ghost<Map<PageMapPtr, (L4Index, L3Index)>>,
    pub l2_tables: Tracked<Map<PageMapPtr, PointsTo<IommuPageMap>>>,
    pub l1_rev_map: Ghost<Map<PageMapPtr, (L4Index, L3Index, L2Index)>>,
    pub l1_tables: Tracked<Map<PageMapPtr, PointsTo<IommuPageMap>>>,
    pub mapping_4k: Ghost<Map<VAddr, MapEntry>>,
    pub proc_ptr: RwLockProcessPtr
}

impl IommuTable {
    /// The owner of the outer LockCell supplies `lock_state`, holders included; the payload has no lock state. The table maps 4K
    /// leaves only, so the 2M and 1G maps of the shared `PageTableU` are empty.
    pub open spec fn user_view(&self, lock_state: LockStateU) -> PageTableU {
        PageTableU {
            lock_state,
            did: self.did,
            mapping_4k: self.mapping_4k().filter_keys(|va: VAddr| self.mapping_4k().spec_index(va).present),
            mapping_2m: Map::empty(),
            mapping_1g: Map::empty(),
            pagetable_window_locks: Map::empty(),
            pci_functions: Map::empty(),
        }
    }

    /// Every retained 4K leaf is present, so the user view shows the whole mapping.
    pub open spec fn leaves_present(&self) -> bool {
        forall|va: VAddr| #![trigger self.mapping_4k().dom().contains(va)] self.mapping_4k().dom().contains(va) ==> self.mapping_4k().spec_index(va).present
    }

    pub open spec fn is_empty(&self) -> bool {
        &&& forall|i: L4Index| #![trigger self.l4_entry(i).perm.present] pei_valid(i) ==> self.l4_entry(i).is_empty()
        &&& self.l3_tables.view().dom() == Set::<PageMapPtr>::empty()
        &&& self.l2_tables.view().dom() == Set::<PageMapPtr>::empty()
        &&& self.l1_tables.view().dom() == Set::<PageMapPtr>::empty()
        &&& self.mapping_4k() == Map::<VAddr, MapEntry>::empty()
    }

    pub open spec fn page_closure(&self) -> Set<PagePtr> {
        self.l3_tables.view().dom() + self.l2_tables.view().dom() + self.l1_tables.view().dom() + self.l4_table.view().dom()
    }

    pub open spec fn mapping_4k(&self) -> Map<VAddr, MapEntry> { self.mapping_4k.view() }

    #[verifier::inline]
    pub open spec fn l4_entry(&self, i: L4Index) -> PageEntry { self.l4_table.view().spec_index(self.cr3).value().spec_index(i) }

    #[verifier::inline]
    pub open spec fn l3_entry(&self, p: PageMapPtr, i: L3Index) -> PageEntry { self.l3_tables.view().spec_index(p).value().spec_index(i) }

    #[verifier::inline]
    pub open spec fn l2_entry(&self, p: PageMapPtr, i: L2Index) -> PageEntry { self.l2_tables.view().spec_index(p).value().spec_index(i) }

    #[verifier::inline]
    pub open spec fn l1_entry(&self, p: PageMapPtr, i: L1Index) -> PageEntry { self.l1_tables.view().spec_index(p).value().spec_index(i) }

    /// A referenced table carries one valid VT-d domain id.
    pub open spec fn did_wf(&self) -> bool {
        &&& self.did is Some ==> vtd_domain_id_valid(self.did->Some_0)
    }

    #[verifier::opaque]
    pub open spec fn wf_l4(&self) -> bool {
        &&& self.l4_table.view().dom() =~= Set::<PageMapPtr>::empty().insert(self.cr3)
        &&& self.cr3 == self.l4_table.view().spec_index(self.cr3).addr()
        &&& self.l4_table.view().spec_index(self.cr3).is_init()
        &&& self.l4_table.view().spec_index(self.cr3).value().iommu_wf()
        // A present user L4 entry links an L3 page. L4 maps no leaf, so its kernel_present bit has no meaning, and the
        // hardware forbids the page-size bit at L4.
        &&& forall|i: L4Index|
            #![trigger self.l4_entry(i).perm.present]
            pei_valid(i) ==> {
                &&& self.l4_entry(i).perm.present ==> !self.l4_entry(i).perm.ps
                &&& self.l4_entry(i).perm.present ==> self.l3_tables.view().dom().contains(self.l4_entry(i).addr)
            }
    }

    /// Present user L4 entries link distinct L3 pages.
    #[verifier::opaque]
    pub open spec fn disjoint_l4(&self) -> bool {
        &&& forall|i: L4Index, j: L4Index|
            #![trigger self.l4_entry(i), self.l4_entry(j)]
            i != j && pei_valid(i) && pei_valid(j)
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
                &&& self.l3_tables.view().spec_index(p).value().iommu_wf()
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
                &&& self.l2_tables.view().spec_index(p).value().iommu_wf()
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
                &&& self.l1_tables.view().spec_index(p).value().iommu_wf()
            }
        // A present L1 entry is a 4K leaf: no page-size bit, kernel_present bit set.
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables.view().dom().contains(p)]
            self.l1_tables.view().dom().contains(p) ==> forall|i: L1Index|
                #![trigger self.l1_entry(p, i)]
                pei_valid(i) && self.l1_entry(p, i).perm.present ==> !self.l1_entry(p, i).perm.ps && self.l1_entry(p, i).perm.kernel_present
    }

    /// No present entry carries the CPU user bit.
    #[verifier::opaque]
    pub open spec fn user_only(&self) -> bool {
        &&& forall|i: L4Index|
            #![trigger self.l4_entry(i)]
            pei_valid(i) && self.l4_entry(i).perm.present ==> !self.l4_entry(i).perm.user
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(p)]
            self.l3_tables.view().dom().contains(p) ==> forall|i: L3Index|
                #![trigger self.l3_entry(p, i)]
                pei_valid(i) && self.l3_entry(p, i).perm.present ==> !self.l3_entry(p, i).perm.user
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables.view().dom().contains(p)]
            self.l2_tables.view().dom().contains(p) ==> forall|i: L2Index|
                #![trigger self.l2_entry(p, i)]
                pei_valid(i) && self.l2_entry(p, i).perm.present ==> !self.l2_entry(p, i).perm.user
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables.view().dom().contains(p)]
            self.l1_tables.view().dom().contains(p) ==> forall|i: L1Index|
                #![trigger self.l1_entry(p, i)]
                pei_valid(i) && self.l1_entry(p, i).perm.present ==> !self.l1_entry(p, i).perm.user
    }

    /// Present non-leaf entries never restrict rights: write bit set, execute_disable bit clear.
    #[verifier::opaque]
    pub open spec fn rwx_upper_level_entries(&self) -> bool {
        &&& forall|i: L4Index|
            #![trigger self.l4_entry(i)]
            pei_valid(i) && self.l4_entry(i).perm.present ==> self.l4_entry(i).perm.write && !self.l4_entry(i).perm.execute_disable
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

    pub open spec fn spec_resolve_mapping_l4(&self, l4i: L4Index) -> Option<PageEntry>
        recommends
            pei_valid(l4i),
    {
        if self.l4_entry(l4i).perm.present { Some(self.l4_entry(l4i)) } else { None }
    }

    pub open spec fn spec_resolve_mapping_l3(&self, l4i: L4Index, l3i: L3Index) -> Option<PageEntry>
        recommends
            pei_valid(l4i),
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

    pub open spec fn spec_resolve_mapping_l2(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> Option<PageEntry>
        recommends
            pei_valid(l4i),
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
            pei_valid(l4i),
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

    /// Every 4K mapping key is a valid IOVA, and every frame is a valid page.
    pub open spec fn va_addr_valid(&self) -> bool {
        &&& forall|va: VAddr|
            #![trigger va_4k_valid(va), self.mapping_4k.view().dom().contains(va)]
            #![trigger self.mapping_4k.view().dom().contains(va), page_ptr_valid(self.mapping_4k.view().spec_index(va).addr)]
            #![trigger self.mapping_4k.view().dom().contains(va)]
            #![trigger page_ptr_valid(self.mapping_4k.view().spec_index(va).addr)]
            self.mapping_4k.view().dom().contains(va) ==> iova_4k_valid(va) && page_ptr_valid(self.mapping_4k.view().spec_index(va).addr)
    }

    /// Non-empty leaves retain their frame, software XD, and historical write permission; present leaves also agree on hardware W.
    #[verifier::opaque]
    pub open spec fn wf_mapping_4k(&self) -> bool {
        &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger self.mapping_4k.view().spec_index(spec_index2va((l4i,l3i,l2i,l1i)))]
            #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> {
                &&& self.mapping_4k.view().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))) == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some
                &&& self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some
                    ==> self.mapping_4k.view().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).addr == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.addr
                    && (self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.perm.present ==> self.mapping_4k.view().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).write == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.perm.write)
                    && self.mapping_4k.view().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).execute_disable == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.perm.execute_disable
                    && self.mapping_4k.view().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).is_io == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.perm.is_io
                    && self.mapping_4k.view().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.perm.present
            }
    }

    /// Every L3, L2 and L1 page is linked from the user part of the root along the path its reverse map stores.
    #[verifier::opaque]
    pub open spec fn tables_reachable_wf(&self) -> bool {
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(p)]
            self.l3_tables.view().dom().contains(p) ==> {
                let l4i = self.l3_rev_map.view().spec_index(p);
                &&& pei_valid(l4i)
                &&& self.spec_resolve_mapping_l4(l4i) is Some && self.spec_resolve_mapping_l4(l4i)->0.addr == p
            }
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables.view().dom().contains(p)]
            self.l2_tables.view().dom().contains(p) ==> {
                let (l4i, l3i) = self.l2_rev_map.view().spec_index(p);
                &&& pei_valid(l4i) && pei_valid(l3i)
                &&& self.spec_resolve_mapping_l3(l4i, l3i) is Some && self.spec_resolve_mapping_l3(l4i, l3i)->0.addr == p
            }
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables.view().dom().contains(p)]
            self.l1_tables.view().dom().contains(p) ==> {
                let (l4i, l3i, l2i) = self.l1_rev_map.view().spec_index(p);
                &&& pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                &&& self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some && self.spec_resolve_mapping_l2(l4i, l3i, l2i)->0.addr == p
            }
    }

    /// The page-table invariant: structure and disjointness of every level, the 4K mapping, user and rights bits, table pages and their reachability, and the domain id.
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
        &&& self.user_only()
        &&& self.rwx_upper_level_entries()
        &&& self.table_pages_wf()
        &&& self.tables_reachable_wf()
        &&& self.did_wf()
    }
}

impl LockInvTrait for IommuTable {
    /// The page-table invariant `wf`.
    open spec fn inv(&self) -> bool {
        &&& self.wf()
    }
}
impl LockMajorTrait for IommuTable {
    open spec fn lock_major_1(&self) -> LockMajorId { 0x233 }
    open spec fn lock_major_2(&self) -> LockMajorId { 0x233 }
    open spec fn lock_major_3(&self) -> LockMajorId { 0x233 }

    open spec fn lock_major_default(&self) -> LockMajorId {
        IOMMU_TABLE_LOCK_MAJOR
    }

    open spec fn lock_major_1_predicate(&self) -> bool { false }
    open spec fn lock_major_2_predicate(&self) -> bool { false }
    open spec fn lock_major_3_predicate(&self) -> bool { false }
    open spec fn lock_major_default_predicate(&self) -> bool { true }
}

impl LockOwnerIdTrait for IommuTable {
    open spec fn container_depth(&self) -> LockOwnerId { LockOwnerId::none() }
    open spec fn process_depth(&self) -> LockOwnerId { LockOwnerId::none() }
}
} // verus!
