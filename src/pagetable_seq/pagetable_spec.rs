use vstd::prelude::*;
use core::marker::ConstParamTy;
use std::usize;
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
pub struct PageTable<const TABLE_TYPE:PTType> {
    pub cr3: PageTableRoot,
    pub pcid: Option<Pcid>,
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

/// The part of a page table observable through a process address space.
///
/// Directory topology, backing page-map pages, CR3/PCID bookkeeping, and the
/// owning process pointer are kernel implementation state.  Publishing or
/// removing an abstract mapping changes this view; preparing an empty walk
/// does not.
pub ghost struct PageTableU {
    pub mapping_4k: Map<VAddr, MapEntry>,
    pub mapping_2m: Map<VAddr, MapEntry>,
    pub mapping_1g: Map<VAddr, MapEntry>,
}

impl<const TABLE_TYPE:PTType> PageTable<TABLE_TYPE> {
    pub open spec fn user_view(&self) -> PageTableU {
        PageTableU {
            mapping_4k: self.mapping_4k(),
            mapping_2m: self.mapping_2m(),
            mapping_1g: self.mapping_1g(),
        }
    }

    pub fn new(
        pcid: Option<Pcid>,
        kernel_entries_ghost: Ghost<Seq<PageEntry>>,
        page_map_ptr: PageMapPtr,
        Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
        mem_end_l4_index: usize,
        proc_ptr: RwLockProcessPtr,
    ) -> (ret: Self)
        requires
             pei_valid(mem_end_l4_index),
            page_ptr_valid(page_map_ptr),
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            kernel_entries_ghost.view().len() == mem_end_l4_index,
            forall|i: usize|
                #![trigger page_map_perm.value().spec_index(i).is_empty()]
                mem_end_l4_index <= i && pei_valid(i) ==> page_map_perm.value().spec_index(i).is_empty(),
            forall|i: usize|
                #![trigger kernel_entries_ghost.view().spec_index(i as int)]
                #![trigger page_map_perm.value().spec_index(i)]
                0 <= i < mem_end_l4_index ==> kernel_entries_ghost.view().spec_index(i as int)
                    == page_map_perm.value().spec_index(i),
            pei_valid(mem_end_l4_index),
            TABLE_TYPE == PT_TYPE ==> pcid is Some,
            TABLE_TYPE == IOMMU_TYPE ==> pcid is None,
            TABLE_TYPE == IOMMU_TYPE ==> mem_end_l4_index == 0,
        ensures
            ret.wf(),
            ret.pcid == pcid,
            ret.kernel_l4_end == mem_end_l4_index,
            ret.page_closure() == Set::empty().insert(page_map_ptr),
            ret.mapping_4k() == Map::<VAddr, MapEntry>::empty(),
            ret.mapping_2m() == Map::<VAddr, MapEntry>::empty(),
            ret.mapping_1g() == Map::<VAddr, MapEntry>::empty(),
            ret.kernel_entries =~= kernel_entries_ghost,
            ret.is_empty(),
            ret.proc_ptr == proc_ptr,
    {
        assert(forall|i: usize|
            #![trigger page_map_perm.value().spec_index(i).is_empty()]
            #![trigger page_map_perm.value().spec_index(i)]
            mem_end_l4_index <= i && pei_valid(i) ==> page_map_perm.value().spec_index(i).is_empty()
            );
        let mut ret = Self {
            cr3: page_map_ptr,
            pcid,
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
        }

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
        assert(ret.kernel_entries_wf()) by { reveal(PageTable::kernel_entries_wf); };

        ret
    }

    pub open spec fn is_empty(&self) -> bool {
        &&& forall|i: L4Index|
            #![trigger self.l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.present]
            self.kernel_l4_end <= i && pei_valid(i) ==> self.l4_table.view().spec_index(self.cr3).value().spec_index(i).is_empty()
        &&& self.l3_tables.view().dom() == Set::<PageMapPtr>::empty()
        &&& self.l2_tables.view().dom() == Set::<PageMapPtr>::empty()
        &&& self.l1_tables.view().dom() == Set::<PageMapPtr>::empty()
        &&& self.mapping_4k() == Map::<VAddr, MapEntry>::empty()
        &&& self.mapping_2m() == Map::<VAddr, MapEntry>::empty()
        &&& self.mapping_1g() == Map::<VAddr, MapEntry>::empty()
    }

    pub open   spec fn page_closure(&self) -> Set<PagePtr> {
        self.l3_tables.view().dom() + self.l2_tables.view().dom() + self.l1_tables.view().dom() + self.l4_table.view().dom()
    }

    pub open   spec fn mapping_4k(&self) -> Map<VAddr, MapEntry> {
        self.mapping_4k.view()

    }
    pub open   spec fn mapping_2m(&self) -> Map<VAddr, MapEntry> {
        self.mapping_2m.view()
    }

    pub open   spec fn mapping_1g(&self) -> Map<VAddr, MapEntry> {
        self.mapping_1g.view()
    }

    pub open spec fn pcid_wf(&self) -> bool {
        &&&
        TABLE_TYPE == PT_TYPE ==> self.pcid is Some
        &&&
        TABLE_TYPE == IOMMU_TYPE ==> self.pcid is None
    }

    pub open spec fn pcid_value(&self) -> Pcid
        recommends
            TABLE_TYPE == PT_TYPE,
            self.pcid is Some,
    {
        self.pcid.unwrap()
    }

    #[verifier::opaque]
    pub open   spec fn wf_l4(&self) -> bool {
        &&& self.l4_table.view().dom() =~= Set::<PageMapPtr>::empty().insert(self.cr3)
        &&& self.cr3 == self.l4_table.view().spec_index(self.cr3).addr()
        &&& self.l4_table.view().spec_index(self.cr3).is_init()
        &&& self.l4_table.view().spec_index(self.cr3).value().wf()
        // L4 does not map to any last level page entry. There's no meaning for kernel_present bit.
        // L4 cannot enable page size bit (hardware limit)
        &&&
        forall|i: L4Index|
        #![trigger self.l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.present]
        self.kernel_l4_end <= i && pei_valid(i)
            ==>
            {
                &&&
                self.l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.present
                ==>
                !self.l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.ps
                &&&
                self.l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.present
                ==>
                self.l3_tables.view().dom().contains(self.l4_table.view().spec_index(self.cr3).value().spec_index(i).addr)
            }
    }
    #[verifier::opaque]
    pub open   spec fn disjoint_l4(&self) -> bool {
        &&&
        forall|i: L4Index, j: L4Index|
            #![trigger pei_valid(i), pei_valid(j)]
            i != j && self.kernel_l4_end <= i && pei_valid(i) && self.kernel_l4_end <= j && pei_valid(j)
            && self.l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.present
            && self.l4_table.view().spec_index(self.cr3).value().spec_index(j).perm.present
            ==>
            self.l4_table.view().spec_index(self.cr3).value().spec_index(i).addr
                != self.l4_table.view().spec_index(self.cr3).value().spec_index(j).addr
    }

    #[verifier::opaque]
    pub open   spec fn wf_l3(&self) -> bool {
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(p)]
            self.l3_tables.view().dom().contains(p)
                ==>
                self.l3_tables.view().spec_index(p).addr() == p
                && self.l3_tables.view().spec_index(p).is_init()
                && self.l3_tables.view().spec_index(p).value().wf()
        // Last level page entry must have kernel present set if it's present
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(p)]
            self.l3_tables.view().dom().contains(p)
            ==> forall|i: L3Index|
                #![trigger pei_valid(i)]
                pei_valid(i)
                && self.l3_tables.view().spec_index(p).value().spec_index(i).perm.ps
                && self.l3_tables.view().spec_index(p).value().spec_index(i).perm.present
                ==>
                self.l3_tables.view().spec_index(p).value().spec_index(i).perm.kernel_present
        // all l3 points to valid l2 tables
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(p)]
            self.l3_tables.view().dom().contains(p)
            ==> forall|i: L3Index|
                #![trigger pei_valid(i)]
                pei_valid(i)
                && self.l3_tables.view().spec_index(p).value().spec_index(i).perm.present
                && !self.l3_tables.view().spec_index(p).value().spec_index(i).perm.ps
                ==> self.l2_tables.view().dom().contains(self.l3_tables.view().spec_index(p).value().spec_index(i).addr)
    }

    #[verifier::opaque]
    pub open   spec fn disjoint_l3(&self) -> bool {
        //L3 tables are disjoint
        &&& forall|pi: PageMapPtr, pj: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(pi), self.l3_tables.view().dom().contains(pj)]
            self.l3_tables.view().dom().contains(pi)
            && self.l3_tables.view().dom().contains(pj)
            ==> forall|l3i: L3Index, l3j: L3Index|
                #![trigger pei_valid(l3i), pei_valid(l3j)]
                pei_valid(l3i) && pei_valid(l3j)
                && self.l3_tables.view().spec_index(pi).value().spec_index(l3i).perm.present
                && !self.l3_tables.view().spec_index(pi).value().spec_index(l3i).perm.ps
                && self.l3_tables.view().spec_index(pj).value().spec_index(l3j).perm.present
                && !self.l3_tables.view().spec_index(pj).value().spec_index(l3j).perm.ps
                ==>
                {
                    &&&
                    pi != pj ==> self.l3_tables.view().spec_index(pi).value().spec_index(l3i).addr != self.l3_tables.view().spec_index(pj).value().spec_index(l3j).addr
                    &&&
                    pi == pj && l3i != l3j ==> self.l3_tables.view().spec_index(pi).value().spec_index(l3i).addr != self.l3_tables.view().spec_index(pj).value().spec_index(l3j).addr
                }
    }

    #[verifier::opaque]
    pub open   spec fn wf_l2(&self) -> bool {
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables.view().dom().contains(p)]
            self.l2_tables.view().dom().contains(p)
            ==>
            self.l2_tables.view().spec_index(p).addr() == p
            && self.l2_tables.view().spec_index(p).is_init()
            && self.l2_tables.view().spec_index(p).value().wf()
        // Last level page entry must have kernel present set if it's present
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables.view().dom().contains(p)]
            self.l2_tables.view().dom().contains(p)
            ==> forall|i: L2Index|
                #![trigger pei_valid(i)]
                pei_valid(i)
            && self.l2_tables.view().spec_index(p).value().spec_index(i).perm.ps
            && self.l2_tables.view().spec_index(p).value().spec_index(i).perm.present
                ==>
                self.l2_tables.view().spec_index(p).value().spec_index(i).perm.kernel_present
        // All L2 maps to valid L1 tables
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables.view().dom().contains(p)]
            self.l2_tables.view().dom().contains(p)
            ==> forall|i: L2Index|
                #![trigger pei_valid(i)]
                pei_valid(i)
                && self.l2_tables.view().spec_index(p).value().spec_index(i).perm.present
                && self.l2_tables.view().spec_index(p).value().spec_index(i).perm.ps == false
                ==>
                self.l1_tables.view().dom().contains(self.l2_tables.view().spec_index(p).value().spec_index(i).addr)
    }

    #[verifier::opaque]
    pub open   spec fn disjoint_l2(&self) -> bool {
    // L2 mappings are unique
        &&&
        forall|pi: PageMapPtr, pj: PageMapPtr|
            #![trigger self.l2_tables.view().dom().contains(pi),
                self.l2_tables.view().dom().contains(pj)]
            self.l2_tables.view().dom().contains(pi)
            &&
            self.l2_tables.view().dom().contains(pj)
            ==>
            forall|l2i: L2Index, l2j: L2Index|
                #![trigger
                    pei_valid(l2i),
                    pei_valid(l2j),
                    self.l2_tables.view().spec_index(pi).value().spec_index(l2i),
                    self.l2_tables.view().spec_index(pj).value().spec_index(l2j)
                ]
                pei_valid(l2i) && pei_valid(l2j)
                && self.l2_tables.view().spec_index(pi).value().spec_index(l2i).perm.present
                && !self.l2_tables.view().spec_index(pi).value().spec_index(l2i).perm.ps
                && self.l2_tables.view().spec_index(pj).value().spec_index(l2j).perm.present
                && !self.l2_tables.view().spec_index(pj).value().spec_index(l2j).perm.ps
                ==>
                {
                    &&&
                    pi != pj  ==> self.l2_tables.view().spec_index(pi).value().spec_index(l2i).addr != self.l2_tables.view().spec_index(pj).value().spec_index(l2j).addr
                    &&&
                    pi == pj && l2i != l2j ==> self.l2_tables.view().spec_index(pi).value().spec_index(l2i).addr != self.l2_tables.view().spec_index(pj).value().spec_index(l2j).addr
                }
    }

    #[verifier::opaque]
    pub open   spec fn wf_l1(&self) -> bool {
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables.view().dom().contains(p)]
            self.l1_tables.view().dom().contains(p)
                ==>
                self.l1_tables.view().spec_index(p).addr() == p
                && self.l1_tables.view().spec_index(p).is_init()
                && self.l1_tables.view().spec_index(p).value().wf()
        // no hugepage in l1
        // Last level page entry must have kernel present set if it's present
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables.view().dom().contains(p)]
            self.l1_tables.view().dom().contains(p)
            ==> forall|i: L1Index|
                #![trigger pei_valid(i)]
                pei_valid(i)
                && self.l1_tables.view().spec_index(p).value().spec_index(i).perm.present
                ==>
                self.l1_tables.view().spec_index(p).value().spec_index(i).perm.ps == false
                &&
                self.l1_tables.view().spec_index(p).value().spec_index(i).perm.kernel_present
    }

    #[verifier::opaque]
    pub open   spec fn user_only(&self) -> bool {
        &&& forall|i: L4Index|
            #![trigger
                // self.l4_table.view().spec_index(self.cr3).value().spec_index(i),
                pei_valid(i)
            ]
            self.kernel_l4_end <= i && pei_valid(i) && self.l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.present
                ==> self.l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.user
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(p)]
            self.l3_tables.view().dom().contains(p)
            ==> forall|i: L3Index|
                #![trigger pei_valid(i)]
                pei_valid(i)
                && self.l3_tables.view().spec_index(p).value().spec_index(i).perm.present
                ==> self.l3_tables.view().spec_index(p).value().spec_index(i).perm.user
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables.view().dom().contains(p)]
            self.l2_tables.view().dom().contains(p)
            ==> forall|i: L2Index|
                #![trigger pei_valid(i)]
                pei_valid(i)
                && self.l2_tables.view().spec_index(p).value().spec_index(i).perm.present
                ==> self.l2_tables.view().spec_index(p).value().spec_index(i).perm.user
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables.view().dom().contains(p)]
            self.l1_tables.view().dom().contains(p)
            ==> forall|i: L1Index|
                #![trigger pei_valid(i)]
                pei_valid(i)
                && self.l1_tables.view().spec_index(p).value().spec_index(i).perm.present
                ==> self.l1_tables.view().spec_index(p).value().spec_index(i).perm.user
    }

    #[verifier::opaque]
    pub open   spec fn rwx_upper_level_entries(&self) -> bool {
        &&& forall|i: L4Index|
            #![trigger
                // self.l4_table.view().spec_index(self.cr3).value().spec_index(i)
                 pei_valid(i)
                ]
            self.kernel_l4_end <= i && pei_valid(i) && self.l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.present
                ==> self.l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.write
                && !self.l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.execute_disable
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables.view().dom().contains(p)]
            self.l3_tables.view().dom().contains(p)
            ==> forall|i: L3Index|
                #![trigger pei_valid(i)]
                pei_valid(i)
                && self.l3_tables.view().spec_index(p).value().spec_index(i).perm.present
                && !self.l3_tables.view().spec_index(p).value().spec_index(i).perm.ps
                ==> self.l3_tables.view().spec_index(p).value().spec_index(i).perm.write
                && !self.l3_tables.view().spec_index(p).value().spec_index(i).perm.execute_disable
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables.view().dom().contains(p)]
            self.l2_tables.view().dom().contains(p)
            ==> forall|i: L2Index|
                #![trigger pei_valid(i)]
                pei_valid(i)
                && self.l2_tables.view().spec_index(p).value().spec_index(i).perm.present
                && !self.l2_tables.view().spec_index(p).value().spec_index(i).perm.ps
                ==> self.l2_tables.view().spec_index(p).value().spec_index(i).perm.write
                && !self.l2_tables.view().spec_index(p).value().spec_index(i).perm.execute_disable
    }

    #[verifier::opaque]
    pub open   spec fn table_pages_wf(&self) -> bool {
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
        &&&
        self.l4_table.view().dom().disjoint(self.l3_tables.view().dom())
        &&&
        self.l4_table.view().dom().disjoint(self.l2_tables.view().dom())
        &&&
        self.l4_table.view().dom().disjoint(self.l1_tables.view().dom())
        &&&
        self.l3_tables.view().dom().disjoint(self.l2_tables.view().dom())
        &&&
        self.l3_tables.view().dom().disjoint(self.l1_tables.view().dom())
        &&&
        self.l2_tables.view().dom().disjoint(self.l1_tables.view().dom())
    }

    pub open   spec fn spec_resolve_mapping_l4(&self, l4i: L4Index) -> Option<PageEntry>
        recommends
            self.kernel_l4_end <= l4i && pei_valid(l4i),
    {
        if self.l4_table.view().spec_index(self.cr3).value().spec_index(l4i).perm.present || l4i < self.kernel_l4_end {
            Some(self.l4_table.view().spec_index(self.cr3).value().spec_index(l4i))
        } else {
            None
        }
    }

    pub open   spec fn spec_resolve_mapping_1g_l3(&self, l4i: L4Index, l3i: L3Index) -> Option<PageEntry>
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

    pub open   spec fn spec_resolve_mapping_l3(&self, l4i: L4Index, l3i: L3Index) -> Option<PageEntry>
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

    pub open   spec fn spec_resolve_mapping_2m_l2(
        &self,
        l4i: L4Index,
        l3i: L3Index,
        l2i: L2Index,
    ) -> Option<PageEntry>
        recommends
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
    {
        if self.spec_resolve_mapping_l3(l4i, l3i) is Some
            && self.l2_tables.view().spec_index(self.spec_resolve_mapping_l3(l4i,l3i)->0.addr).value().spec_index(l2i).perm.kernel_present
            && self.l2_tables.view().spec_index(self.spec_resolve_mapping_l3(l4i,l3i)->0.addr).value().spec_index(l2i).perm.ps
            {
            Some(self.l2_tables.view().spec_index(self.spec_resolve_mapping_l3(l4i,l3i)->0.addr).value().spec_index(l2i))
        } else {
            None
        }
    }

    pub open   spec fn spec_resolve_mapping_l2(
        &self,
        l4i: L4Index,
        l3i: L3Index,
        l2i: L2Index,
    ) -> Option<PageEntry>
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

    pub open   spec fn spec_resolve_mapping_4k_l1(
        &self,
        l4i: L4Index,
        l3i: L3Index,
        l2i: L2Index,
        l1i: L1Index,
    ) -> Option<PageEntry>
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

    pub open spec fn va_addr_valid(&self) -> bool {
        self.va_addr_valid_inner()
    }

    pub open spec fn va_addr_valid_inner(&self) -> bool {
        &&& forall|va: VAddr|
            #![trigger va_4k_valid(va), self.mapping_4k.view().dom().contains(va)]
            #![trigger self.mapping_4k.view().dom().contains(va), page_ptr_valid(self.mapping_4k.view().spec_index(va).addr)]
            #![trigger self.mapping_4k.view().dom().contains(va)]
            #![trigger page_ptr_valid(self.mapping_4k.view().spec_index(va).addr)]
            self.mapping_4k.view().dom().contains(va)
                ==>
                page_table_key_4k_valid::<TABLE_TYPE>(va)
                &&
                page_ptr_valid(self.mapping_4k.view().spec_index(va).addr)
        &&& forall|va: VAddr|
            #![trigger va_2m_valid(va), self.mapping_2m.view().dom().contains(va)]
            #![trigger self.mapping_2m.view().dom().contains(va), page_ptr_2m_valid(self.mapping_2m.view().spec_index(va).addr)]
            #![trigger self.mapping_2m.view().dom().contains(va)]
            self.mapping_2m.view().dom().contains(va)
                ==>
                page_table_key_2m_valid::<TABLE_TYPE>(va)
                &&
                page_ptr_2m_valid(self.mapping_2m.view().spec_index(va).addr)
        &&& forall|va: VAddr|
            #![trigger va_1g_valid(va), self.mapping_1g.view().dom().contains(va)]
            #![trigger self.mapping_1g.view().dom().contains(va), page_ptr_1g_valid(self.mapping_1g.view().spec_index(va).addr)]
            #![trigger self.mapping_1g.view().dom().contains(va)]
            self.mapping_1g.view().dom().contains(va)
                ==>
                page_table_key_1g_valid::<TABLE_TYPE>(va)
                &&
                page_ptr_1g_valid(self.mapping_1g.view().spec_index(va).addr)
    }

    #[verifier::opaque]
    pub open   spec fn wf_mapping_4k(&self) -> bool {
        &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
            #![trigger self.mapping_4k.view().spec_index(spec_index2va((l4i,l3i,l2i,l1i)))]
            #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
            self.kernel_l4_end <= l4i && pei_valid(l4i)
                && pei_valid(l3i)
                && pei_valid(l2i)
                && pei_valid(l1i)
                ==>
                {
                    &&&
                    self.mapping_4k.view().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))) 
                        == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some
                    &&&
                    self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some
                        ==>
                        self.mapping_4k.view().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).addr == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.addr
                        && self.mapping_4k.view().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).write == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.perm.write
                        && self.mapping_4k.view().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).execute_disable == self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i,)->0.perm.execute_disable
                        && self.mapping_4k.view().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present == self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i,)->0.perm.present
                }   
    }

    #[verifier::opaque]
    pub open   spec fn wf_mapping_2m(&self) -> bool {
        &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger
                self.mapping_2m.view().spec_index(spec_index2va((l4i,l3i,l2i,0)))
                ]
            #![trigger
                self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)
                ]
            self.kernel_l4_end <= l4i && pei_valid(l4i)
                && pei_valid(l3i)
                && pei_valid(l2i)
                ==>
                (self.mapping_2m.view().dom().contains(spec_index2va((l4i, l3i, l2i, 0))) == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some)
                &&
                (
                    self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some
                    ==>
                    self.mapping_2m.view().spec_index(spec_index2va((l4i, l3i, l2i, 0))).addr == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.addr
                    && self.mapping_2m.view().spec_index(spec_index2va((l4i, l3i, l2i, 0))).write == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.perm.write
                    && self.mapping_2m.view().spec_index(spec_index2va((l4i, l3i, l2i, 0))).execute_disable == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.perm.execute_disable
                    && self.mapping_2m.view().spec_index(spec_index2va((l4i, l3i, l2i, 0))).present == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.perm.present
                )
    }

    #[verifier::opaque]
    pub open   spec fn wf_mapping_1g(&self) -> bool {
        &&& forall|l4i: L4Index, l3i: L3Index|
            #![trigger self.mapping_1g.view().spec_index(spec_index2va((l4i,l3i,0,0)))]
            #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
            self.kernel_l4_end <= l4i && pei_valid(l4i)
                && pei_valid(l3i)
                ==>
                {
                    &&& 
                    self.mapping_1g.view().dom().contains(spec_index2va((l4i, l3i, 0, 0))) 
                    == 
                    self.spec_resolve_mapping_1g_l3(l4i, l3i) is Some
                    &&& 
                    self.spec_resolve_mapping_1g_l3(l4i,l3i) is Some
                    ==>
                    self.mapping_1g.view().spec_index(spec_index2va((l4i, l3i, 0, 0))).addr == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.addr
                    && self.mapping_1g.view().spec_index(spec_index2va((l4i, l3i, 0, 0))).write == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.perm.write
                    && self.mapping_1g.view().spec_index(spec_index2va((l4i, l3i, 0, 0))).execute_disable == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.perm.execute_disable
                    && self.mapping_1g.view().spec_index(spec_index2va((l4i, l3i, 0, 0))).present == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.perm.present
                }
    }

    #[verifier::opaque]
    pub open   spec fn kernel_entries_wf(&self) -> bool {
        &&&
        TABLE_TYPE == IOMMU_TYPE ==> self.kernel_l4_end == 0
        &&& pei_valid(self.kernel_l4_end)
        &&& self.kernel_entries.view().len() =~= self.kernel_l4_end as nat
        &&& forall|i: usize|
            #![trigger self.kernel_entries.view().spec_index(i as int)]
            0 <= i < self.kernel_l4_end && pei_valid(i)
                ==> self.kernel_entries.view().spec_index(i as int)
                    == self.l4_table.view().spec_index(self.cr3).value().spec_index(i)
    }

    pub open   spec fn wf(&self) -> bool {
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
        &&& self.kernel_entries_wf()
        &&& self.pcid_wf()
    }

    pub open   spec fn l4_entry_exists(&self, l4i: L4Index) -> bool
        recommends
            self.wf(),
    {
        self.spec_resolve_mapping_l4(l4i) is Some
    }

    pub open   spec fn l3_2m_entry_exists(&self, l4i: L4Index, l3i: L3Index) -> bool
        recommends
            self.wf(),
            self.l4_entry_exists(l4i),
    {
        self.spec_resolve_mapping_l3(l4i, l3i) is Some
    }

    pub open   spec fn l3_4k_entry_exists(&self, l4i: L4Index, l3i: L3Index) -> bool
        recommends
            self.wf(),
            self.l4_entry_exists(l4i),
    {
        self.spec_resolve_mapping_l3(l4i, l3i) is Some
    }

    pub open   spec fn l2_4k_entry_exists(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> bool
        recommends
            self.wf(),
            self.l3_4k_entry_exists(l4i, l3i),
    {
        self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
    }
}

impl<const TABLE_TYPE:PTType> PageTable<TABLE_TYPE> {
    pub broadcast proof fn resolve_4k_l1_unchanged_at(
        &self,
        other: &Self,
        l4i: L4Index,
        l3i: L3Index,
        l2i: L2Index,
        l1i: L1Index,
    )
        requires
            self.kernel_l4_end == other.kernel_l4_end,
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            pei_valid(l1i),
            self.spec_resolve_mapping_l2(l4i, l3i, l2i)
                == other.spec_resolve_mapping_l2(l4i, l3i, l2i),
            self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some ==>
                self.l1_tables.view().spec_index(
                    self.spec_resolve_mapping_l2(l4i, l3i, l2i)->0.addr,
                ).value().spec_index(l1i)
                    == other.l1_tables.view().spec_index(
                        other.spec_resolve_mapping_l2(l4i, l3i, l2i)->0.addr,
                    ).value().spec_index(l1i),
        ensures
            #![trigger self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i), other.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
            self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)
                == other.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i),
    {
    }

    pub broadcast proof fn resolve_l3_addr_unique_at(
        &self,
        l4i: L4Index,
        l3i: L3Index,
        l4j: L4Index,
        l3j: L3Index,
    )
        requires
            self.wf_l4(),
            self.disjoint_l4(),
            self.disjoint_l3(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            self.kernel_l4_end <= l4j && pei_valid(l4j),
            pei_valid(l3j),
        ensures
            #![trigger self.spec_resolve_mapping_l3(l4i, l3i), self.spec_resolve_mapping_l3(l4j, l3j)]
            (l4i, l3i) != (l4j, l3j)
                && self.spec_resolve_mapping_l3(l4i, l3i) is Some
                && self.spec_resolve_mapping_l3(l4j, l3j) is Some
                ==> self.spec_resolve_mapping_l3(l4i, l3i)->0.addr
                    != self.spec_resolve_mapping_l3(l4j, l3j)->0.addr,
    {
        assert((l4i, l3i) != (l4j, l3j)
            && self.spec_resolve_mapping_l3(l4i, l3i) is Some
            && self.spec_resolve_mapping_l3(l4j, l3j) is Some
            ==> self.spec_resolve_mapping_l3(l4i, l3i)->0.addr
                != self.spec_resolve_mapping_l3(l4j, l3j)->0.addr) by {
            reveal(PageTable::wf_l4);
            reveal(PageTable::disjoint_l4);
            reveal(PageTable::disjoint_l3);
        };
    }

    pub broadcast proof fn resolve_l2_addr_unique_at(
        &self,
        l4i: L4Index,
        l3i: L3Index,
        l2i: L2Index,
        l4j: L4Index,
        l3j: L3Index,
        l2j: L2Index,
    )
        requires
            self.wf_l4(),
            self.wf_l3(),
            self.disjoint_l4(),
            self.disjoint_l3(),
            self.disjoint_l2(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            self.kernel_l4_end <= l4j && pei_valid(l4j),
            pei_valid(l3j),
            pei_valid(l2j),
        ensures
            #![trigger self.spec_resolve_mapping_l2(l4i, l3i, l2i), self.spec_resolve_mapping_l2(l4j, l3j, l2j)]
            (l4i, l3i, l2i) != (l4j, l3j, l2j)
                && self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                && self.spec_resolve_mapping_l2(l4j, l3j, l2j) is Some
                ==> self.spec_resolve_mapping_l2(l4i, l3i, l2i)->0.addr
                    != self.spec_resolve_mapping_l2(l4j, l3j, l2j)->0.addr,
    {
        assert((l4i, l3i, l2i) != (l4j, l3j, l2j)
            && self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
            && self.spec_resolve_mapping_l2(l4j, l3j, l2j) is Some
            ==> self.spec_resolve_mapping_l2(l4i, l3i, l2i)->0.addr
                != self.spec_resolve_mapping_l2(l4j, l3j, l2j)->0.addr) by {
            reveal(PageTable::wf_l4);
            reveal(PageTable::wf_l3);
            reveal(PageTable::disjoint_l4);
            reveal(PageTable::disjoint_l3);
            reveal(PageTable::disjoint_l2);
        };
    }

    pub broadcast proof fn l2_entry_addr_unique_at(
        &self,
        pi: PageMapPtr,
        l2i: L2Index,
        pj: PageMapPtr,
        l2j: L2Index,
    )
        requires
            self.disjoint_l2(),
            self.l2_tables.view().dom().contains(pi),
            self.l2_tables.view().dom().contains(pj),
            pei_valid(l2i),
            pei_valid(l2j),
        ensures
            #![trigger self.disjoint_l2(), self.l2_tables.view().spec_index(pi).value().spec_index(l2i).addr, self.l2_tables.view().spec_index(pj).value().spec_index(l2j).addr]
            (pi, l2i) != (pj, l2j)
                && self.l2_tables.view().spec_index(pi).value().spec_index(l2i).perm.present
                && self.l2_tables.view().spec_index(pj).value().spec_index(l2j).perm.present
                && !self.l2_tables.view().spec_index(pi).value().spec_index(l2i).perm.ps
                && !self.l2_tables.view().spec_index(pj).value().spec_index(l2j).perm.ps
                ==> self.l2_tables.view().spec_index(pi).value().spec_index(l2i).addr
                    != self.l2_tables.view().spec_index(pj).value().spec_index(l2j).addr,
    {
        assert((pi, l2i) != (pj, l2j)
            && self.l2_tables.view().spec_index(pi).value().spec_index(l2i).perm.present
            && self.l2_tables.view().spec_index(pj).value().spec_index(l2j).perm.present
            && !self.l2_tables.view().spec_index(pi).value().spec_index(l2i).perm.ps
            && !self.l2_tables.view().spec_index(pj).value().spec_index(l2j).perm.ps
            ==> self.l2_tables.view().spec_index(pi).value().spec_index(l2i).addr
                != self.l2_tables.view().spec_index(pj).value().spec_index(l2j).addr) by {
            reveal(PageTable::disjoint_l2);
        };
    }

    pub broadcast proof fn resolve_l2_target_exists(
        &self,
        l4i: L4Index,
        l3i: L3Index,
        l2i: L2Index,
    )
        requires
            self.wf_l4(),
            self.wf_l3(),
            self.wf_l2(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
        ensures
            #![trigger self.spec_resolve_mapping_l2(l4i, l3i, l2i)]
            self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                ==> self.l1_tables.view().dom().contains(
                    self.spec_resolve_mapping_l2(l4i, l3i, l2i)->0.addr,
                ),
    {
        assert(self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
            ==> self.l1_tables.view().dom().contains(
                self.spec_resolve_mapping_l2(l4i, l3i, l2i)->0.addr,
            )) by {
            reveal(PageTable::wf_l4);
            reveal(PageTable::wf_l3);
            reveal(PageTable::wf_l2);
        };
    }

    pub proof fn resolve_l2_unchanged(&self, other: &Self)
        requires
            self.kernel_l4_end == other.kernel_l4_end,
            self.cr3 == other.cr3,
            self.l4_table.view() == other.l4_table.view(),
            self.l3_tables.view() == other.l3_tables.view(),
            self.l2_tables.view() == other.l2_tables.view(),
        ensures
            forall|l4i: L4Index|
                #![trigger pei_valid(l4i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i)
                ==> forall|l3i: L3Index|
                    #![trigger pei_valid(l3i)]
                    pei_valid(l3i)
                ==> forall|l2i: L2Index|
                #![trigger self.spec_resolve_mapping_l2(l4i, l3i, l2i)]
                    pei_valid(l2i) ==>
                        self.spec_resolve_mapping_l2(l4i, l3i, l2i)
                            == other.spec_resolve_mapping_l2(l4i, l3i, l2i),
    {
    }

}

    impl<const TABLE_TYPE:PTType> LockInvTrait for  PageTable<TABLE_TYPE> {
        open spec fn inv(&self) -> bool{
            &&&
            self.wf()
        }
    }
    impl<const TABLE_TYPE:PTType> LockMajorTrait for  PageTable<TABLE_TYPE> {

        open spec fn lock_major_1(&self) -> LockMajorId {
            0x233
        }

        open spec fn lock_major_2(&self) -> LockMajorId {
            0x233
        }

        open spec fn lock_major_3(&self) -> LockMajorId {
            0x233
        }

        open spec fn lock_major_default(&self) -> LockMajorId {
            if TABLE_TYPE == PT_TYPE {
                PAGE_TABLE_LOCK_MAJOR
            } else {
                IOMMU_TABLE_LOCK_MAJOR
            }
        }

        open spec fn lock_major_1_predicate(&self) -> bool {
            false
        }

        open spec fn lock_major_2_predicate(&self) -> bool {
            false
        }

        open spec fn lock_major_3_predicate(&self) -> bool {
            false
        }

        open spec fn lock_major_default_predicate(&self) -> bool {
            true
        }

    }

    impl<const TABLE_TYPE:PTType> LockOwnerIdTrait for  PageTable<TABLE_TYPE> {
        open spec fn container_depth(&self) -> LockOwnerId {
            LockOwnerId::none()
        }

        open spec fn process_depth(&self) -> LockOwnerId {
            LockOwnerId::none()
        }
    }

    impl<const TABLE_TYPE:PTType> LockUserVisibilityTrait for PageTable<TABLE_TYPE> {
        open spec fn is_user_visible() -> bool {
            true
        }
    }

} // verus!
