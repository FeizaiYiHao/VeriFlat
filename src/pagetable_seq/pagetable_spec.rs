use vstd::prelude::*;
use core::marker::ConstParamTy;
use std::usize;
verus! {

use crate::define::*;
use crate::locks::*;
use vstd::simple_pptr::*;
use crate::util::page_ptr_util_u::*;
use super::pagemap_util_t::*;
use super::entry::*;
use super::pagemap::*;
use crate::lemma::lemma_u::*;

/// mapping_xx is the abstract mappings of each page size.
/// if an entry exists in mapping_xx.dom(), is entry is visible to the kernel at least. 
/// if the entry has present flag set, it's visible to the page table walk. 
/// our TLB spec will be that the TLB is `alway` a subset of kernel view. Regardless the locking state of the page table.
pub struct PageTable<const TABLE_TYPE:PTType> {
    pub cr3: PageTableRoot,
    pub pcid: Option<Pcid>,
    pub ioid: Option<IOid>,
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

impl<const TABLE_TYPE:PTType> PageTable<TABLE_TYPE> {
    pub fn new(
        pcid_or_ioid: usize,
        kernel_entries_ghost: Ghost<Seq<PageEntry>>,
        page_map_ptr: PageMapPtr,
        Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
        mem_end_l4_index: usize,
        proc_ptr: RwLockProcessPtr,
    ) -> (ret: Self)
        requires
             0 <= mem_end_l4_index < 512,
            page_ptr_valid(page_map_ptr),
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            kernel_entries_ghost@.len() == mem_end_l4_index,
            forall|i: usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                mem_end_l4_index <= i < 512 ==> page_map_perm.value()[i].is_empty(),
            forall|i: usize|
                #![trigger kernel_entries_ghost@[i as int]]
                #![trigger page_map_perm.value()[i]]
                0 <= i < mem_end_l4_index ==> kernel_entries_ghost@[i as int]
                    == page_map_perm.value()[i],
            0 <= mem_end_l4_index < 512,

            TABLE_TYPE == IOMMU_TYPE ==> mem_end_l4_index == 0,
        ensures
            ret.wf(),
            ret.pcid_or_ioid() == pcid_or_ioid,
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
            #![trigger page_map_perm.value()[i].is_empty()]
            #![trigger page_map_perm.value()[i]]
            mem_end_l4_index <= i < 512 ==> page_map_perm.value()[i].is_empty()
            );
        let mut ret = Self {
            cr3: page_map_ptr,
            pcid: if TABLE_TYPE == PT_TYPE {Some(pcid_or_ioid)}else{None},
            ioid: if TABLE_TYPE == IOMMU_TYPE {Some(pcid_or_ioid)}else{None},
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
        assert(ret.l3_tables@.dom() == Set::<PageMapPtr>::empty());
        assert(ret.l2_tables@.dom() == Set::<PageMapPtr>::empty());
        assert(ret.l1_tables@.dom() == Set::<PageMapPtr>::empty());
        assert(ret.l4_table@.dom() == Set::<PageMapPtr>::empty());
        proof {
            ret.l4_table.borrow_mut().tracked_insert(page_map_ptr, page_map_perm);
        }
        assert(ret.l3_tables@.dom() == Set::<PageMapPtr>::empty());
        assert(ret.l2_tables@.dom() == Set::<PageMapPtr>::empty());
        assert(ret.l1_tables@.dom() == Set::<PageMapPtr>::empty());
        assert(ret.l4_table@.dom() == Set::<PageMapPtr>::empty().insert(page_map_ptr));
        assert(ret.page_closure() == Set::empty().insert(page_map_ptr));

        assert(ret.wf_l4());
        assert(ret.wf_l3());
        assert(ret.wf_l2());
        assert(ret.wf_l1());
        assert(ret.wf_mapping_4k());
        assert(ret.wf_mapping_2m());
        assert(ret.wf_mapping_1g());
        assert(ret.user_only());
        assert(ret.rwx_upper_level_entries());
        assert(ret.table_pages_wf());
        assert(ret.kernel_entries_wf());
        assert(ret.pcid_ioid_wf());

        ret
    }

    pub open spec fn is_empty(&self) -> bool {
        &&& forall|i: L4Index|
            #![trigger self.l4_table@[self.cr3].value()[i].perm.present]
            self.kernel_l4_end <= i < 512 ==> self.l4_table@[self.cr3].value()[i].is_empty()
        &&& self.l3_tables@.dom() == Set::<PageMapPtr>::empty()
        &&& self.l2_tables@.dom() == Set::<PageMapPtr>::empty()
        &&& self.l1_tables@.dom() == Set::<PageMapPtr>::empty()
        &&& self.mapping_4k() == Map::<VAddr, MapEntry>::empty()
        &&& self.mapping_2m() == Map::<VAddr, MapEntry>::empty()
        &&& self.mapping_1g() == Map::<VAddr, MapEntry>::empty()
    }

    pub open   spec fn page_closure(&self) -> Set<PagePtr> {
        self.l3_tables@.dom() + self.l2_tables@.dom() + self.l1_tables@.dom() + self.l4_table@.dom()
    }

    pub open   spec fn mapping_4k(&self) -> Map<VAddr, MapEntry> {
        self.mapping_4k@

    }
    pub open   spec fn mapping_2m(&self) -> Map<VAddr, MapEntry> {
        self.mapping_2m@
    }

    pub open   spec fn mapping_1g(&self) -> Map<VAddr, MapEntry> {
        self.mapping_1g@
    }

    pub open   spec fn pcid_ioid_wf(&self) -> bool {
        &&&
        TABLE_TYPE == PT_TYPE ==> self.pcid is Some && self.ioid is None
        &&&
        TABLE_TYPE == IOMMU_TYPE ==> self.pcid is None && self.ioid is Some
    }

    pub open spec fn pcid_or_ioid(&self) -> usize{
        if TABLE_TYPE == PT_TYPE{
            self.pcid.unwrap()
        }else{
            self.ioid.unwrap()
        }
    }

    pub open   spec fn wf_l4(&self) -> bool {
        &&& self.l4_table@.dom() =~= Set::<PageMapPtr>::empty().insert(self.cr3)
        &&& self.cr3 == self.l4_table@[self.cr3].addr()
        &&& self.l4_table@[self.cr3].is_init()
        &&& self.l4_table@[self.cr3].value().wf()
        // L4 does not map to any last level page entry. There's no meaning for kernel_present bit.
        // L4 cannot enable page size bit (hardware limit)
        &&& 
        forall|i: L4Index|
        #![trigger self.l4_table@[self.cr3].value()[i].perm.present, self.l4_table@[self.cr3].value()[i].perm.ps]
        self.kernel_l4_end <= i < 512 
            ==> 
            self.l4_table@[self.cr3].value()[i].perm.present ==> !self.l4_table@[self.cr3].value()[i].perm.ps
        //all l4 points to valid l3 tables
        &&& forall|i: L4Index|
            #![trigger self.l4_table@[self.cr3].value()[i].perm.present]
            // #![trigger self.l3_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr)]
            self.kernel_l4_end <= i < 512 
                && self.l4_table@[self.cr3].value()[i].perm.present
                ==> 
                self.l3_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr)
    }
    pub open   spec fn disjoint_l4(&self) -> bool {
        &&& forall|i: L4Index, j: L4Index|
        //  #![trigger self.l4_table@[self.cr3].value()[i].perm.present, self.l4_table@[self.cr3].value()[j].perm.present]
            #![trigger self.l4_table@[self.cr3].value()[i].addr, self.l4_table@[self.cr3].value()[j].addr]
            i != j && self.kernel_l4_end <= i < 512
                && self.l4_table@[self.cr3].value()[i].perm.present && self.kernel_l4_end <= j < 512
                && self.l4_table@[self.cr3].value()[j].perm.present
                ==> self.l4_table@[self.cr3].value()[i].addr
                != self.l4_table@[self.cr3].value()[j].addr
    }

    pub open   spec fn wf_l3(&self) -> bool {
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables@[p].addr()]
            #![trigger self.l3_tables@[p].is_init()]
            #![trigger self.l3_tables@[p].value().wf()]
            self.l3_tables@.dom().contains(p) 
                ==> 
                self.l3_tables@[p].addr() == p
                && self.l3_tables@[p].is_init()
                && self.l3_tables@[p].value().wf()
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_rev_map@.dom().contains(p)]
            #![trigger self.l3_rev_map@[p]]
            self.l3_tables@.dom().contains(p) 
                ==> 
                self.kernel_l4_end <= self.l3_rev_map@[p] < 512
                && self.l3_rev_map@.dom().contains(p) 
                && self.spec_resolve_mapping_l4(self.l3_rev_map@[p]) is Some 
                && self.spec_resolve_mapping_l4(self.l3_rev_map@[p])->0.addr == p
        // Last level page entry must have kernel present set if it's present
        &&& forall|p: PageMapPtr, i: L3Index|
            #![trigger self.l3_tables@[p].value()[i].perm.ps, self.l3_tables@[p].value()[i].perm.present]
            self.l3_tables@.dom().contains(p) && 0 <= i < 512 && self.l3_tables@[p].value()[i].perm.ps && self.l3_tables@[p].value()[i].perm.present
                ==> 
                self.l3_tables@[p].value()[i].perm.kernel_present
        // all l3 points to valid l2 tables
        &&& forall|p: PageMapPtr, i: L3Index|
            // #![trigger self.l3_tables@[p].value()[i].perm.present, self.l3_tables@[p].value()[i].perm.ps, self.l2_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)]
            #![trigger self.l2_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)]
            self.l3_tables@.dom().contains(p) 
                && 0 <= i < 512
                && self.l3_tables@[p].value()[i].perm.present
                && !self.l3_tables@[p].value()[i].perm.ps 
                ==> self.l2_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)
    }

    pub open   spec fn disjoint_l3(&self) -> bool {
        //L3 tables are disjoint
        &&& forall|pi: PageMapPtr, pj: PageMapPtr, l3i: L3Index, l3j: L3Index|
            // #![trigger self.l3_tables@.dom().contains(pi), self.l3_tables@.dom().contains(pj), self.l3_tables@[pi].value()[l3i].addr, self.l3_tables@[pj].value()[l3j].addr, self.l3_tables@[pi].value()[l3i].perm.ps, self.l3_tables@[pj].value()[l3j].perm.ps, self.l3_tables@[pi].value()[l3i].perm.present, self.l3_tables@[pj].value()[l3j].perm.present]
            // #![trigger self.l3_tables@[pi].value()[l3i].perm.present, self.l3_tables@[pj].value()[l3j].perm.present]
            #![trigger self.l3_tables@[pi].value()[l3i].addr, self.l3_tables@[pj].value()[l3j].addr]
                self.l3_tables@.dom().contains(pi) 
                && self.l3_tables@.dom().contains(pj)
                && 0 <= l3i < 512 && 0 <= l3j < 512 
                && self.l3_tables@[pi].value()[l3i].perm.present
                && self.l3_tables@[pj].value()[l3j].perm.present
                && !self.l3_tables@[pi].value()[l3i].perm.ps
                && !self.l3_tables@[pj].value()[l3j].perm.ps
                ==> 
                {
                    &&&
                    pi != pj ==> self.l3_tables@[pi].value()[l3i].addr != self.l3_tables@[pj].value()[l3j].addr
                    &&&
                    pi == pj && l3i != l3j ==> self.l3_tables@[pi].value()[l3i].addr != self.l3_tables@[pj].value()[l3j].addr
                }
    }

    pub open   spec fn wf_l2(&self) -> bool {
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables@[p].addr()]
            #![trigger self.l2_tables@[p].is_init()]
            #![trigger self.l2_tables@[p].value().wf()]
            self.l2_tables@.dom().contains(p) 
            ==> 
            self.l2_tables@[p].addr() == p 
            && self.l2_tables@[p].is_init()
            && self.l2_tables@[p].value().wf()
        // all l2 tables exist in l3 mapping
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_rev_map@[p]]
            #![trigger self.l2_rev_map@.dom().contains(p)]
            self.l2_tables@.dom().contains(p) 
                ==> self.l2_rev_map@.dom().contains(p) 
                && self.kernel_l4_end <= self.l2_rev_map@[p].0 < 512 
                && 0 <= self.l2_rev_map@[p].1 < 512 
                && self.spec_resolve_mapping_l3(self.l2_rev_map@[p].0, self.l2_rev_map@[p].1) is Some 
                && self.spec_resolve_mapping_l3(self.l2_rev_map@[p].0,self.l2_rev_map@[p].1,)->0.addr == p
        // Last level page entry must have kernel present set if it's present
        &&& forall|p: PageMapPtr, i: L2Index|
            #![trigger self.l2_tables@[p].value()[i].perm.ps, self.l2_tables@[p].value()[i].perm.present]
            self.l2_tables@.dom().contains(p) && 0 <= i < 512 && self.l2_tables@[p].value()[i].perm.ps && self.l2_tables@[p].value()[i].perm.present
                ==> 
                self.l2_tables@[p].value()[i].perm.kernel_present
        // All L2 maps to vaild L1 tables
        &&& forall|p: PageMapPtr, i: L2Index|
            #![trigger self.l1_tables@.dom().contains(self.l2_tables@[p].value()[i].addr) ]
            self.l2_tables@.dom().contains(p) 
                && 0 <= i < 512
                && self.l2_tables@[p].value()[i].perm.present
                && self.l2_tables@[p].value()[i].perm.ps == false
                ==> 
                self.l1_tables@.dom().contains(self.l2_tables@[p].value()[i].addr)
    }

    pub open   spec fn disjoint_l2(&self) -> bool {
    // L2 mappings are unique
        &&& forall|pi: PageMapPtr, pj: PageMapPtr, l2i: L2Index, l2j: L2Index|
            // #![trigger self.l2_tables@[pi].value()[l2i].perm, self.l2_tables@[pj].value()[l2j].perm, self.l2_tables@[pi].value()[l2i].addr, self.l2_tables@[pj].value()[l2j].addr]
            #![trigger self.l2_tables@[pi].value()[l2i].addr, self.l2_tables@[pj].value()[l2j].addr]
            self.l2_tables@.dom().contains(pi) 
                && self.l2_tables@.dom().contains(pj)
                && 0 <= l2i < 512 
                && 0 <= l2j < 512 
                && self.l2_tables@[pi].value()[l2i].perm.present
                && self.l2_tables@[pj].value()[l2j].perm.present
                && !self.l2_tables@[pi].value()[l2i].perm.ps
                && !self.l2_tables@[pj].value()[l2j].perm.ps
                ==> 
                {
                    &&&
                    pi != pj  ==> self.l2_tables@[pi].value()[l2i].addr != self.l2_tables@[pj].value()[l2j].addr
                    &&&
                    pi == pj && l2i != l2j ==> self.l2_tables@[pi].value()[l2i].addr != self.l2_tables@[pj].value()[l2j].addr
                }
    }

    pub open   spec fn wf_l1(&self) -> bool {
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables@[p].addr()]
            #![trigger self.l1_tables@[p].is_init()]
            #![trigger self.l1_tables@[p].value().wf()]
            self.l1_tables@.dom().contains(p) 
                ==> 
                self.l1_tables@[p].addr() == p
                && self.l1_tables@[p].is_init()
                && self.l1_tables@[p].value().wf()
        // all l1 tables exist in l2 mapping
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_rev_map@.dom().contains(p)]
            #![trigger self.l1_rev_map@[p]]
            self.l1_tables@.dom().contains(p) 
                ==> 
                self.l1_rev_map@.dom().contains(p) 
                && self.kernel_l4_end <= self.l1_rev_map@[p].0 < 512 
                && 0 <= self.l1_rev_map@[p].1 < 512 
                && 0 <= self.l1_rev_map@[p].2 < 512 
                && self.spec_resolve_mapping_l2(self.l1_rev_map@[p].0,self.l1_rev_map@[p].1,self.l1_rev_map@[p].2) is Some 
                && self.spec_resolve_mapping_l2(self.l1_rev_map@[p].0,self.l1_rev_map@[p].1,self.l1_rev_map@[p].2)->0.addr == p
        // no hugepage in l1
        // Last level page entry must have kernel present set if it's present
        &&& forall|p: PageMapPtr, i: L1Index|
            #![trigger self.l1_tables@[p].value()[i].perm.ps]
            self.l1_tables@.dom().contains(p) && 0 <= i < 512
                && self.l1_tables@[p].value()[i].perm.present
                ==> 
                self.l1_tables@[p].value()[i].perm.ps == false
                &&
                self.l1_tables@[p].value()[i].perm.kernel_present
    }

    pub open   spec fn user_only(&self) -> bool {
        &&& forall|i: L4Index|
            #![trigger self.l4_table@[self.cr3].value()[i].perm, self.l4_table@[self.cr3].value()[i].perm.user]
            self.kernel_l4_end <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present
                ==> self.l4_table@[self.cr3].value()[i].perm.user
        &&& forall|p: PageMapPtr, i: L3Index|
            #![trigger self.l3_tables@[p].value()[i].perm, self.l3_tables@[p].value()[i].perm.user]
            self.l3_tables@.dom().contains(p) && 0 <= i < 512
                && self.l3_tables@[p].value()[i].perm.present
                ==> self.l3_tables@[p].value()[i].perm.user
        &&& forall|p: PageMapPtr, i: L2Index|
            #![trigger self.l2_tables@[p].value()[i].perm, self.l2_tables@[p].value()[i].perm.user]
            self.l2_tables@.dom().contains(p) && 0 <= i < 512
                && self.l2_tables@[p].value()[i].perm.present
                ==> self.l2_tables@[p].value()[i].perm.user
        &&& forall|p: PageMapPtr, i: L1Index|
            #![trigger self.l1_tables@[p].value()[i].perm, self.l1_tables@[p].value()[i].perm.user]
            self.l1_tables@.dom().contains(p) && 0 <= i < 512
                && self.l1_tables@[p].value()[i].perm.present
                ==> self.l1_tables@[p].value()[i].perm.user
    }

    pub open   spec fn rwx_upper_level_entries(&self) -> bool {
        &&& forall|i: L4Index|
            #![trigger self.l4_table@[self.cr3].value()[i].perm]
            self.kernel_l4_end <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present
                ==> self.l4_table@[self.cr3].value()[i].perm.write
                && !self.l4_table@[self.cr3].value()[i].perm.execute_disable
        &&& forall|p: PageMapPtr, i: L3Index|
            #![trigger self.l3_tables@[p].value()[i].perm]
            self.l3_tables@.dom().contains(p) && 0 <= i < 512
                && self.l3_tables@[p].value()[i].perm.present
                && !self.l3_tables@[p].value()[i].perm.ps
                ==> self.l3_tables@[p].value()[i].perm.write
                && !self.l3_tables@[p].value()[i].perm.execute_disable
        &&& forall|p: PageMapPtr, i: L2Index|
            #![trigger  self.l2_tables@[p].value()[i].perm]
            self.l2_tables@.dom().contains(p) && 0 <= i < 512
                && self.l2_tables@[p].value()[i].perm.present
                && !self.l2_tables@[p].value()[i].perm.ps
                ==> self.l2_tables@[p].value()[i].perm.write
                && !self.l2_tables@[p].value()[i].perm.execute_disable
    }

    pub open   spec fn table_pages_wf(&self) -> bool {
        &&& page_ptr_valid(self.cr3)
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables@.dom().contains(p), page_ptr_valid(p)]
            self.l3_tables@.dom().contains(p) ==> page_ptr_valid(p)
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables@.dom().contains(p), page_ptr_valid(p)]
            self.l2_tables@.dom().contains(p) ==> page_ptr_valid(p)
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables@.dom().contains(p), page_ptr_valid(p)]
            self.l1_tables@.dom().contains(p) ==> page_ptr_valid(p)
        &&&
        self.l4_table@.dom().disjoint(self.l3_tables@.dom())
        &&&
        self.l4_table@.dom().disjoint(self.l2_tables@.dom())
        &&&
        self.l4_table@.dom().disjoint(self.l1_tables@.dom())
        &&&
        self.l3_tables@.dom().disjoint(self.l2_tables@.dom())
        &&&
        self.l3_tables@.dom().disjoint(self.l1_tables@.dom())
        &&&
        self.l2_tables@.dom().disjoint(self.l1_tables@.dom())
    }

    pub open   spec fn spec_resolve_mapping_l4(&self, l4i: L4Index) -> Option<PageEntry>
        recommends
            self.kernel_l4_end <= l4i < 512,
    {
        if self.l4_table@[self.cr3].value()[l4i].perm.present || l4i < self.kernel_l4_end {
            Some(self.l4_table@[self.cr3].value()[l4i])
        } else {
            None
        }
    }

    pub open   spec fn spec_resolve_mapping_1g_l3(&self, l4i: L4Index, l3i: L3Index) -> Option<PageEntry>
        recommends
            self.kernel_l4_end <= l4i < 512,
            0 <= l3i < 512,
    {
        if self.spec_resolve_mapping_l4(l4i) is Some 
            && self.l3_tables@[self.spec_resolve_mapping_l4(l4i)->0.addr].value()[l3i].perm.ps
            && self.l3_tables@[self.spec_resolve_mapping_l4(l4i)->0.addr].value()[l3i].perm.kernel_present {    
            Some(self.l3_tables@[self.spec_resolve_mapping_l4(l4i)->0.addr].value()[l3i])
        } else {
            None
        }
    }

    pub open   spec fn spec_resolve_mapping_l3(&self, l4i: L4Index, l3i: L3Index) -> Option<PageEntry>
        recommends
            self.kernel_l4_end <= l4i < 512,
            0 <= l3i < 512,
    {
        if self.spec_resolve_mapping_l4(l4i) is Some 
            && self.l3_tables@[self.spec_resolve_mapping_l4(l4i)->0.addr].value()[l3i].perm.present 
            && self.l3_tables@[self.spec_resolve_mapping_l4(l4i)->0.addr].value()[l3i].perm.ps == false {
            Some(self.l3_tables@[self.spec_resolve_mapping_l4(l4i)->0.addr].value()[l3i])
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
            self.kernel_l4_end <= l4i < 512,
            0 <= l3i < 512,
            0 <= l2i < 512,
    {
        if self.spec_resolve_mapping_l3(l4i, l3i) is Some 
            && self.l2_tables@[self.spec_resolve_mapping_l3(l4i,l3i)->0.addr].value()[l2i].perm.kernel_present 
            && self.l2_tables@[self.spec_resolve_mapping_l3(l4i,l3i)->0.addr].value()[l2i].perm.ps 
            {
            Some(self.l2_tables@[self.spec_resolve_mapping_l3(l4i,l3i)->0.addr].value()[l2i])
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
            self.kernel_l4_end <= l4i < 512,
            0 <= l3i < 512,
            0 <= l2i < 512,
    {
        if self.spec_resolve_mapping_l3(l4i, l3i) is Some 
            && self.l2_tables@[self.spec_resolve_mapping_l3(l4i,l3i)->0.addr].value()[l2i].perm.present 
            && self.l2_tables@[self.spec_resolve_mapping_l3(l4i,l3i)->0.addr].value()[l2i].perm.ps == false {
            Some(self.l2_tables@[self.spec_resolve_mapping_l3(l4i,l3i)->0.addr].value()[l2i])
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
            self.kernel_l4_end <= l4i < 512,
            0 <= l3i < 512,
            0 <= l2i < 512,
            0 <= l1i < 512,
    {
        if self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some && self.l1_tables@[self.spec_resolve_mapping_l2(l4i,l3i,l2i)->0.addr].value()[l1i].perm.kernel_present {
            Some(self.l1_tables@[self.spec_resolve_mapping_l2(l4i,l3i,l2i)->0.addr].value()[l1i])
        } else {
            None
        }

    }

    pub open spec fn va_addr_valid(&self) -> bool {
        self.va_addr_valid_inner()
    }

    pub open spec fn va_addr_valid_inner(&self) -> bool {
        &&& forall|va: VAddr|
            #![trigger va_4k_valid(va), self.mapping_4k@.dom().contains(va)]
            #![trigger self.mapping_4k@.dom().contains(va), page_ptr_valid(self.mapping_4k@[va].addr)]
            #![trigger self.mapping_4k@.dom().contains(va)]
            #![trigger page_ptr_valid(self.mapping_4k@[va].addr)]
            self.mapping_4k@.dom().contains(va) 
                ==> 
                va_4k_valid(va)
                &&
                page_ptr_valid(self.mapping_4k@[va].addr)
        &&& forall|va: VAddr|
            #![trigger va_2m_valid(va), self.mapping_2m@.dom().contains(va)]
            #![trigger self.mapping_2m@.dom().contains(va), page_ptr_2m_valid(self.mapping_2m@[va].addr)]
            #![trigger self.mapping_2m@.dom().contains(va)]
            self.mapping_2m@.dom().contains(va) 
                ==> 
                va_2m_valid(va)
                && 
                page_ptr_2m_valid(self.mapping_2m@[va].addr)
        &&& forall|va: VAddr|
            #![trigger va_1g_valid(va), self.mapping_1g@.dom().contains(va)]
            #![trigger self.mapping_1g@.dom().contains(va), page_ptr_1g_valid(self.mapping_1g@[va].addr)]
            #![trigger self.mapping_1g@.dom().contains(va)]
            self.mapping_1g@.dom().contains(va) 
                ==> 
                va_1g_valid(va)
                &&
                page_ptr_1g_valid(self.mapping_1g@[va].addr)
    }

    pub open   spec fn wf_mapping_4k(&self) -> bool {
        &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
            #![trigger self.mapping_4k@[spec_index2va((l4i,l3i,l2i,l1i))]]
            #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
            self.kernel_l4_end <= l4i < 512 
                && 0 <= l3i < 512 
                && 0 <= l2i < 512 
                && 0 <= l1i < 512
                ==> 
                self.mapping_4k@.dom().contains(spec_index2va((l4i, l3i, l2i, l1i))) == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some
        &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
            #![trigger self.mapping_4k@[spec_index2va((l4i,l3i,l2i,l1i))]]
            self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512
                && self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some
                ==> 
                self.mapping_4k@[spec_index2va((l4i, l3i, l2i, l1i))].addr == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.addr
                && self.mapping_4k@[spec_index2va((l4i, l3i, l2i, l1i))].write == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.perm.write
                && self.mapping_4k@[spec_index2va((l4i, l3i, l2i, l1i))].execute_disable == self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i,)->0.perm.execute_disable
                && self.mapping_4k@[spec_index2va((l4i, l3i, l2i, l1i))].present == self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i,)->0.perm.present
    }

    pub open   spec fn wf_mapping_2m(&self) -> bool {
        &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger self.mapping_2m@[spec_index2va((l4i,l3i,l2i,0))]]
            #![trigger self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
            self.kernel_l4_end <= l4i < 512 
                && 0 <= l3i < 512 
                && 0 <= l2i < 512
                ==> 
                self.mapping_2m@.dom().contains(spec_index2va((l4i, l3i, l2i, 0))) == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some
        &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger self.mapping_2m@[spec_index2va((l4i,l3i,l2i,0))]]
            self.kernel_l4_end <= l4i < 512 
                && 0 <= l3i < 512 
                && 0 <= l2i < 512
                && self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some
                ==> 
                self.mapping_2m@[spec_index2va((l4i, l3i, l2i, 0))].addr == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.addr
                && self.mapping_2m@[spec_index2va((l4i, l3i, l2i, 0))].write == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.perm.write
                && self.mapping_2m@[spec_index2va((l4i, l3i, l2i, 0))].execute_disable == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.perm.execute_disable
                && self.mapping_2m@[spec_index2va((l4i, l3i, l2i, 0))].present == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)->0.perm.present
    }

    pub open   spec fn wf_mapping_1g(&self) -> bool {
        &&& forall|l4i: L4Index, l3i: L3Index|
            #![trigger self.mapping_1g@[spec_index2va((l4i,l3i,0,0))]]
            #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
            self.kernel_l4_end <= l4i < 512
                && 0 <= l3i < 512 
                ==> 
                self.mapping_1g@.dom().contains(spec_index2va((l4i, l3i, 0, 0))) == self.spec_resolve_mapping_1g_l3(l4i, l3i) is Some
        &&& forall|l4i: L4Index, l3i: L3Index|
            #![trigger self.mapping_1g@[spec_index2va((l4i,l3i,0,0))]]
            #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
            self.kernel_l4_end <= l4i < 512 
                && 0 <= l3i < 512 
                && self.spec_resolve_mapping_1g_l3(l4i,l3i) is Some 
                ==> 
                self.mapping_1g@[spec_index2va((l4i, l3i, 0, 0))].addr == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.addr
                && self.mapping_1g@[spec_index2va((l4i, l3i, 0, 0))].write == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.perm.write
                && self.mapping_1g@[spec_index2va((l4i, l3i, 0, 0))].execute_disable == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.perm.execute_disable
                && self.mapping_1g@[spec_index2va((l4i, l3i, 0, 0))].present == self.spec_resolve_mapping_1g_l3(l4i, l3i)->0.perm.present
    }

    pub open   spec fn kernel_entries_wf(&self) -> bool {
        &&&
        TABLE_TYPE == IOMMU_TYPE ==> self.kernel_l4_end == 0
        &&& self.kernel_l4_end < 512
        &&& self.kernel_entries@.len() =~= self.kernel_l4_end as nat
        &&& forall|i: usize|
            #![trigger self.kernel_entries@[i as int]]
            0 <= i < self.kernel_l4_end ==> self.kernel_entries@[i as int]
                == self.l4_table@[self.cr3].value()[i]
    }

    pub open   spec fn wf(&self) -> bool {
        &&& self.va_addr_valid()
        &&& self.levels_wf()
        &&& self.disjoint_wf()
        &&& self.mappings_wf()
        &&& self.additonal_wf()
    }

    pub closed   spec fn levels_wf(&self) -> bool {
        &&& self.wf_l4()
        &&& self.wf_l3()
        &&& self.wf_l2()
        &&& self.wf_l1()
    }
    pub closed   spec fn disjoint_wf(&self) -> bool {
        &&& self.disjoint_l4()
        &&& self.disjoint_l3()
        &&& self.disjoint_l2()
    }

    pub closed   spec fn mappings_wf(&self) -> bool {
        &&& self.wf_mapping_4k()
        &&& self.wf_mapping_2m()
        &&& self.wf_mapping_1g()
    }

    pub closed   spec fn additonal_wf(&self) -> bool {
        &&& self.user_only()
        &&& self.rwx_upper_level_entries()
        &&& self.table_pages_wf()
        &&& self.kernel_entries_wf()
        &&& self.pcid_ioid_wf()
    }
    pub broadcast proof fn reveal_page_table_wf(&self)
        ensures
            #[trigger] self.wf() <==> {
                &&& self.va_addr_valid()
                &&& self.levels_wf()
                &&& self.disjoint_wf()
                &&& self.mappings_wf()
                &&& self.additonal_wf()
            },
    {
    }
    pub broadcast proof fn reveal_page_table_levels_wf(&self)
        ensures
            #[trigger] self.levels_wf() <==> {
                &&& self.wf_l4()
                &&& self.wf_l3()
                &&& self.wf_l2()
                &&& self.wf_l1()
            },
    {
}    pub broadcast proof fn reveal_page_table_disjoint_wf(&self)
        ensures
            #[trigger] self.disjoint_wf() <==> {
                &&& self.disjoint_l4()
                &&& self.disjoint_l3()
                &&& self.disjoint_l2()
            },
    {
    }
    pub broadcast proof fn reveal_page_table_mappings_wf(&self)
        ensures
            #[trigger] self.mappings_wf() <==> {
                &&& self.wf_mapping_4k()
                &&& self.wf_mapping_2m()
                &&& self.wf_mapping_1g()
            },
    {
    }
    pub broadcast proof fn reveal_page_table_addtional_wf(&self)
        ensures
            #[trigger] self.additonal_wf() <==> {
                &&& self.user_only()
                &&& self.rwx_upper_level_entries()
                &&& self.table_pages_wf()
                &&& self.kernel_entries_wf()
                &&& self.pcid_ioid_wf()
            },
    {
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

// proof
pub proof fn va_addr_valid_proof<const TABLE_TYPE:PTType>()
    ensures 
        forall|pt: PageTable<TABLE_TYPE>|
            pt.va_addr_valid() == pt.va_addr_valid_inner()
{}

impl<const TABLE_TYPE:PTType> PageTable<TABLE_TYPE> {
    pub proof fn internal_resolve_disjoint(&self)
        requires
            self.wf(),
        ensures
            forall|l4i: L4Index, l4j: L4Index|
                #![trigger self.spec_resolve_mapping_l4(l4i), self.spec_resolve_mapping_l4(l4j)]
                self.kernel_l4_end <= l4i < 512 
                    && self.kernel_l4_end <= l4j < 512 
                    && l4i != l4j 
                    && self.spec_resolve_mapping_l4(l4i) is Some 
                    && self.spec_resolve_mapping_l4(l4j) is Some 
                    ==> 
                    self.spec_resolve_mapping_l4(l4i)->0.addr != self.spec_resolve_mapping_l4(l4j)->0.addr,
            forall|l4i: L4Index, l3i: L3Index, l4j: L4Index, l3j: L3Index|
                #![trigger self.spec_resolve_mapping_l3(l4i,l3i), self.spec_resolve_mapping_l3(l4j,l3j)]
                #![trigger self.l3_tables@[self.l4_table@[self.cr3].value()[l4i].addr].value()[l3i], self.l3_tables@[self.l4_table@[self.cr3].value()[l4j].addr].value()[l3j]]
                self.kernel_l4_end <= l4i < 512 
                    && 0 <= l3i < 512 
                    && self.kernel_l4_end <= l4j < 512
                    && 0 <= l3j < 512 
                    && (l4i, l3i) != (l4j, l3j) 
                    && self.spec_resolve_mapping_l3(l4i,l3i) is Some 
                    && self.spec_resolve_mapping_l3(l4j, l3j) is Some
                    ==> 
                    self.spec_resolve_mapping_l3(l4i, l3i)->0.addr != self.spec_resolve_mapping_l3(l4j, l3j)->0.addr
                    ,
            forall|l4i: L4Index,l3i: L3Index, l2i: L3Index, l4j: L4Index, l3j: L3Index, l2j: L2Index|
                #![trigger self.spec_resolve_mapping_l2(l4i,l3i,l2i), self.spec_resolve_mapping_l2(l4j,l3j,l2j)]
                #![trigger self.l2_tables@[self.l3_tables@[self.l4_table@[self.cr3].value()[l4i].addr].value()[l3i].addr].value()[l2i], self.l2_tables@[self.l3_tables@[self.l4_table@[self.cr3].value()[l4j].addr].value()[l3j].addr].value()[l2j]]
                self.kernel_l4_end <= l4i < 512 
                    && 0 <= l3i < 512 
                    && 0 <= l2i < 512
                    && self.kernel_l4_end <= l4j < 512 
                    && 0 <= l3j < 512 
                    && 0 <= l2j < 512 
                    && (l4i,l3i,l2i) != (l4j, l3j, l2j) 
                    && self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                    && self.spec_resolve_mapping_l2(l4j, l3j, l2j) is Some
                    ==> 
                    self.spec_resolve_mapping_l2(l4i, l3i, l2i)->0.addr != self.spec_resolve_mapping_l2(l4j, l3j, l2j)->0.addr,
    {
    }

    pub proof fn four_level_empty_imply_4k_map_empty(&self)
        requires
            self.wf(),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
                #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512 ==>
                    self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i) is None,
        ensures
            self.mapping_4k@.dom() == Set::<VAddr>::empty(),
    {
        va_lemma();
        admit();
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
            PAGE_TABLE_LOCK_MAJOR
        }
        
        open spec fn lock_major_1_predicate(&self) -> bool {
            arbitrary()
        }
        
        open spec fn lock_major_2_predicate(&self) -> bool {
            arbitrary()
        }
        
        open spec fn lock_major_3_predicate(&self) -> bool {
            arbitrary()
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

} // verus!
