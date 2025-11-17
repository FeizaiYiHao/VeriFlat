use vstd::prelude::*;

verus! {

use crate::define::*;
use crate::primitive::LockInv;
use vstd::simple_pptr::*;
use crate::util::page_ptr_util_u::*;
use super::pagemap_util_t::*;
use super::entry::*;
use super::pagemap::*;
use crate::lemma::lemma_u::*;

pub struct PageTable {
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
}

impl PageTable {
    pub fn new(
        pcid: Option<Pcid>,
        ioid: Option<IOid>,
        kernel_entries_ghost: Ghost<Seq<PageEntry>>,
        page_map_ptr: PageMapPtr,
        Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
        mem_end_l4_index: usize,
    ) -> (ret: Self)
        requires
            pcid is Some != ioid is Some,
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
        ensures
            ret.wf(),
            ret.pcid == pcid,
            ret.ioid == ioid,
            ret.kernel_l4_end == mem_end_l4_index,
            ret.page_closure() == Set::empty().insert(page_map_ptr),
            ret.mapping_4k() == Map::<VAddr, MapEntry>::empty(),
            ret.mapping_2m() == Map::<VAddr, MapEntry>::empty(),
            ret.mapping_1g() == Map::<VAddr, MapEntry>::empty(),
            ret.kernel_entries =~= kernel_entries_ghost,
            ret.is_empty(),
    {
        assert(forall|i: usize|
            #![trigger page_map_perm.value()[i].is_empty()]
            #![trigger page_map_perm.value()[i]]
            mem_end_l4_index <= i < 512 ==> page_map_perm.value()[i].is_empty()
            );
        let mut ret = Self {
            cr3: page_map_ptr,
            pcid: pcid,
            ioid: ioid,
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
        assert(ret.present_or_zero());
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

    pub open   spec fn page_not_mapped(&self, pa: PAddr) -> bool {
        &&& forall 
            |va: VAddr|
            #![trigger self.mapping_4k().dom().contains(va), self.mapping_4k()[va].addr]
                self.mapping_4k().dom().contains(va) ==> self.mapping_4k()[va].addr != pa
        &&& forall 
            |va: VAddr|
            #![trigger self.mapping_2m().dom().contains(va), self.mapping_2m()[va].addr]
                self.mapping_2m().dom().contains(va) ==> self.mapping_2m()[va].addr != pa
        &&& forall 
            |va: VAddr|
            #![trigger self.mapping_1g().dom().contains(va), self.mapping_1g()[va].addr]
                self.mapping_1g().dom().contains(va) ==> self.mapping_1g()[va].addr != pa
    }

    pub open   spec fn mapped_4k_pages(&self) -> Set<PAddr> {
        Set::<PAddr>::new(|pa: PAddr| self.is_4k_pa_mapped(pa))
    }

    pub open   spec fn is_4k_pa_mapped(&self, pa: PAddr) -> bool {
        exists|va: VAddr|
            #![auto]
            self.mapping_4k().dom().contains(va) && self.mapping_4k()[va].addr == pa
    }

    pub open   spec fn mapped_2m_pages(&self) -> Set<PAddr> {
        Set::<PAddr>::new(|pa: PAddr| self.is_2m_pa_mapped(pa))
    }

    pub open   spec fn is_2m_pa_mapped(&self, pa: PAddr) -> bool {
        exists|va: VAddr|
            #![auto]
            self.mapping_2m().dom().contains(va) && self.mapping_2m()[va].addr == pa
    }

    pub open   spec fn mapped_1g_pages(&self) -> Set<PAddr> {
        Set::<PAddr>::new(|pa: PAddr| self.is_1g_pa_mapped(pa))
    }

    pub open   spec fn is_1g_pa_mapped(&self, pa: PAddr) -> bool {
        exists|va: VAddr|
            #![auto]
            self.mapping_1g().dom().contains(va) && self.mapping_1g()[va].addr == pa
    }

    pub open   spec fn pcid_ioid_wf(&self) -> bool {
        self.pcid is Some != self.ioid is Some
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
        //L4 table only maps to L3
        &&& forall|i: L4Index|
         // #![trigger self.l4_table@[self.cr3].value()[i].perm.present]
            #![trigger self.l2_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr)]
            #![trigger self.l1_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr)]
            self.kernel_l4_end <= i < 512 
                && self.l4_table@[self.cr3].value()[i].perm.present
                ==> 
                self.l2_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr) == false 
                && self.l1_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr) == false 
                && self.cr3 != self.l4_table@[self.cr3].value()[i].addr
        // no self mapping
        &&& forall|i: L4Index|
         // #![trigger self.l4_table@[self.cr3].value()[i].perm.present]
            #![trigger self.l4_table@[self.cr3].value()[i].addr, self.l4_table@[self.cr3].value()[i].perm.present]
            self.kernel_l4_end <= i < 512 
                && self.l4_table@[self.cr3].value()[i].perm.present
                ==> 
                self.cr3 != self.l4_table@[self.cr3].value()[i].addr
        //all l4 points to valid l3 tables
        &&& forall|i: L4Index|
            #![trigger self.l3_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr)]
            self.kernel_l4_end <= i < 512 
                && self.l4_table@[self.cr3].value()[i].perm.present
                ==> 
                self.l3_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr)
    }
    pub open   spec fn disjoint_l4(&self) -> bool {
        &&& forall|i: L4Index, j: L4Index|
         // #![trigger self.l4_table@[self.cr3].value()[i].perm.present, self.l4_table@[self.cr3].value()[j].perm.present]
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
        //L3 tables does not map to L4 or L1
        // all l3 points to valid l2 tables
        &&& forall|p: PageMapPtr, i: L3Index|
            // #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l3_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)]
            // #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l1_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)]
            // #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l3_tables@[p].value()[i].addr]
            // #![trigger self.l2_tables@.dom().contains(self.l3_tables@[p].value()[i].addr), self.l3_tables@[p].value()[i].perm.present, self.l3_tables@[p].value()[i].addr]
            #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l3_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)]
            #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l1_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)]
            #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l3_tables@[p].value()[i].addr]
            self.l3_tables@.dom().contains(p) 
                && 0 <= i < 512
                && self.l3_tables@[p].value()[i].perm.present
                && self.l3_tables@[p].value()[i].perm.ps == false
                ==> 
                self.l3_tables@.dom().contains(self.l3_tables@[p].value()[i].addr) == false 
                && self.l1_tables@.dom().contains(self.l3_tables@[p].value()[i].addr) == false 
                && self.cr3 != self.l3_tables@[p].value()[i].addr
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
            //L3 tables unique within
        &&& forall|p: PageMapPtr, l3i: L3Index, l3j: L3Index|
            // #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[l3i].addr, self.l3_tables@[p].value()[l3j].addr, self.l3_tables@[p].value()[l3i].perm.ps, self.l3_tables@[p].value()[l3j].perm.ps, self.l3_tables@[p].value()[l3i].addr, self.l3_tables@[p].value()[l3j].addr]
            // #![trigger self.l3_tables@[p].value()[l3i].perm.present, self.l3_tables@[p].value()[l3j].perm.present]
            #![trigger self.l3_tables@[p].value()[l3i].addr, self.l3_tables@[p].value()[l3j].addr]
            self.l3_tables@.dom().contains(p) 
                && l3i != l3j 
                && 0 <= l3i < 512 
                && 0 <= l3j < 512
                && self.l3_tables@[p].value()[l3i].perm.present
                && self.l3_tables@[p].value()[l3j].perm.present
                && !self.l3_tables@[p].value()[l3i].perm.ps
                && !self.l3_tables@[p].value()[l3j].perm.ps 
                ==> 
                self.l3_tables@[p].value()[l3i].addr!= self.l3_tables@[p].value()[l3j].addr
            //L3 tables are disjoint
        &&& forall|pi: PageMapPtr, pj: PageMapPtr, l3i: L3Index, l3j: L3Index|
            // #![trigger self.l3_tables@.dom().contains(pi), self.l3_tables@.dom().contains(pj), self.l3_tables@[pi].value()[l3i].addr, self.l3_tables@[pj].value()[l3j].addr, self.l3_tables@[pi].value()[l3i].perm.ps, self.l3_tables@[pj].value()[l3j].perm.ps, self.l3_tables@[pi].value()[l3i].perm.present, self.l3_tables@[pj].value()[l3j].perm.present]
            // #![trigger self.l3_tables@[pi].value()[l3i].perm.present, self.l3_tables@[pj].value()[l3j].perm.present]
            #![trigger self.l3_tables@[pi].value()[l3i].addr,self.l3_tables@[pj].value()[l3j].addr]
            pi != pj 
                && self.l3_tables@.dom().contains(pi) 
                && self.l3_tables@.dom().contains(pj)
                && 0 <= l3i < 512 && 0 <= l3j < 512 
                && self.l3_tables@[pi].value()[l3i].perm.present
                && self.l3_tables@[pj].value()[l3j].perm.present
                && !self.l3_tables@[pi].value()[l3i].perm.ps
                && !self.l3_tables@[pj].value()[l3j].perm.ps
                ==> 
                self.l3_tables@[pi].value()[l3i].addr != self.l3_tables@[pj].value()[l3j].addr
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
        // L2 does not map to L4, L3, or self
        &&& forall|p: PageMapPtr, i: L2Index|
            #![trigger self.l2_tables@.dom().contains(p), self.l2_tables@[p].value()[i].perm.present, self.l2_tables@.dom().contains(self.l2_tables@[p].value()[i].addr)]
            #![trigger self.l2_tables@.dom().contains(p), self.l2_tables@[p].value()[i].perm.present, self.l3_tables@.dom().contains(self.l2_tables@[p].value()[i].addr)]
            #![trigger self.l2_tables@.dom().contains(p), self.l2_tables@[p].value()[i].perm.present, self.l2_tables@[p].value()[i].addr]
            self.l2_tables@.dom().contains(p) 
                && 0 <= i < 512
                && self.l2_tables@[p].value()[i].perm.present
                && self.l2_tables@[p].value()[i].perm.ps == false
                ==> 
                self.l2_tables@.dom().contains(self.l2_tables@[p].value()[i].addr) == false 
                && self.l3_tables@.dom().contains(self.l2_tables@[p].value()[i].addr) == false 
                && self.cr3 != self.l2_tables@[p].value()[i].addr
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
            // L2 mappings are unique within
        &&& forall|p: PageMapPtr, l2i: L2Index, l2j: L2Index|
            #![trigger self.l2_tables@[p].value()[l2i].addr, self.l2_tables@[p].value()[l2j].addr]
            self.l2_tables@.dom().contains(p) 
                && l2i != l2j 
                && 0 <= l2i < 512 
                && 0 <= l2j < 512
                && self.l2_tables@[p].value()[l2i].perm.present
                && self.l2_tables@[p].value()[l2j].perm.present
                && !self.l2_tables@[p].value()[l2i].perm.ps
                && !self.l2_tables@[p].value()[l2j].perm.ps 
                ==> 
                self.l2_tables@[p].value()[l2i].addr != self.l2_tables@[p].value()[l2j].addr
            // L2 mappings are unique
        &&& forall|pi: PageMapPtr, pj: PageMapPtr, l2i: L2Index, l2j: L2Index|
            #![trigger self.l2_tables@[pi].value()[l2i].addr, self.l2_tables@[pj].value()[l2j].addr]
            self.l2_tables@.dom().contains(pi) 
                && self.l2_tables@.dom().contains(pj)
                && 0 <= l2i < 512 
                && 0 <= l2j < 512 
                && self.l2_tables@[pi].value()[l2i].perm.present
                && self.l2_tables@[pj].value()[l2j].perm.present
                && !self.l2_tables@[pi].value()[l2i].perm.ps
                && !self.l2_tables@[pj].value()[l2j].perm.ps
                && pi != pj 
                ==> 
                self.l2_tables@[pi].value()[l2i].addr != self.l2_tables@[pj].value()[l2j].addr
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

    pub open   spec fn present_or_zero(&self) -> bool {
        true
        // &&& forall|i: L4Index|
        //     #![trigger self.l4_table@[self.cr3].value()[i].is_empty()]
        //     self.kernel_l4_end <= i < 512 && !self.l4_table@[self.cr3].value()[i].perm.present
        //         ==> self.l4_table@[self.cr3].value()[i].is_empty()
        // &&& forall|p: PageMapPtr, i: L3Index|
        //     #![trigger self.l3_tables@[p].value()[i].is_empty()]
        //     self.l3_tables@.dom().contains(p) && 0 <= i < 512
        //         && !self.l3_tables@[p].value()[i].perm.present
        //         ==> self.l3_tables@[p].value()[i].is_empty()
        // &&& forall|p: PageMapPtr, i: L2Index|
        //     #![trigger self.l2_tables@[p].value()[i].is_empty()]
        //     self.l2_tables@.dom().contains(p) && 0 <= i < 512
        //         && !self.l2_tables@[p].value()[i].perm.present
        //         ==> self.l2_tables@[p].value()[i].is_empty()
        // &&& forall|p: PageMapPtr, i: L1Index|
        //     #![trigger self.l1_tables@[p].value()[i].is_empty()]
        //     self.l1_tables@.dom().contains(p) && 0 <= i < 512
        //         && !self.l1_tables@[p].value()[i].perm.present
        //         ==> self.l1_tables@[p].value()[i].is_empty()
    }

    pub open   spec fn rwx_upper_level_entries(&self) -> bool {
        &&& forall|i: L4Index|
            #![trigger self.l4_table@[self.cr3].value()[i].perm]
            // #![trigger self.l4_table@[self.cr3].value()[i].perm.execute_disable]
            self.kernel_l4_end <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present
                ==> self.l4_table@[self.cr3].value()[i].perm.write
                && !self.l4_table@[self.cr3].value()[i].perm.execute_disable
        &&& forall|p: PageMapPtr, i: L3Index|
            #![trigger self.l3_tables@[p].value()[i].perm]
            // #![trigger self.l3_tables@[p].value()[i].perm.execute_disable]
            self.l3_tables@.dom().contains(p) && 0 <= i < 512
                && self.l3_tables@[p].value()[i].perm.present
                && !self.l3_tables@[p].value()[i].perm.ps
                ==> self.l3_tables@[p].value()[i].perm.write
                && !self.l3_tables@[p].value()[i].perm.execute_disable
        &&& forall|p: PageMapPtr, i: L2Index|
            #![trigger  self.l2_tables@[p].value()[i].perm]
            // #![trigger self.l2_tables@[p].value()[i].perm.execute_disable]
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

    // #[verifier(inline)]
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

    pub open   spec fn wf_mapping_4k(&self) -> bool {
        &&& forall|va: VAddr|
            #![trigger va_4k_valid(va), self.mapping_4k@.dom().contains(va)]
            #![trigger self.mapping_4k@.dom().contains(va), page_ptr_valid(self.mapping_4k@[va].addr)]
            self.mapping_4k@.dom().contains(va) 
                ==> 
                va_4k_valid(va)
                &&
                page_ptr_valid(self.mapping_4k@[va].addr)
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
        &&& forall|va: VAddr|
            #![trigger va_2m_valid(va), self.mapping_2m@.dom().contains(va)]
            #![trigger self.mapping_2m@.dom().contains(va), page_ptr_2m_valid(self.mapping_2m@[va].addr)]
            self.mapping_2m@.dom().contains(va) 
                ==> 
                va_2m_valid(va)
                && page_ptr_2m_valid(self.mapping_2m@[va].addr)
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
        &&& forall|va: VAddr|
            #![trigger va_1g_valid(va), self.mapping_1g@.dom().contains(va)]
            #![trigger self.mapping_1g@.dom().contains(va), page_ptr_1g_valid(self.mapping_1g@[va].addr)]
            self.mapping_1g@.dom().contains(va) 
                ==> 
                va_1g_valid(va)
                &&
                page_ptr_1g_valid(self.mapping_1g@[va].addr)
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
        &&& self.kernel_l4_end < 512
        &&& self.kernel_entries@.len() =~= self.kernel_l4_end as nat
        &&& forall|i: usize|
            #![trigger self.kernel_entries@[i as int]]
            0 <= i < self.kernel_l4_end ==> self.kernel_entries@[i as int]
                == self.l4_table@[self.cr3].value()[i]
    }

    pub closed   spec fn wf(&self) -> bool {
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
        &&& self.present_or_zero()
        &&& self.table_pages_wf()
        &&& self.kernel_entries_wf()
        &&& self.pcid_ioid_wf()
    }
    pub broadcast proof fn reveal_page_table_wf(&self)
        ensures
            #[trigger] self.wf() <==> {
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
                &&& self.present_or_zero()
                &&& self.table_pages_wf()
                &&& self.kernel_entries_wf()
                &&& self.pcid_ioid_wf()
            },
    {
    }

    // pub open   spec fn l4_kernel_entries_reserved(&self) -> bool
    //     recommends self.wf_l4(),
    // {
    //     forall|l4i: L4Index| #![auto] 0<=l4i<KERNEL_MEM_END_L4INDEX ==> self.l4_table@[self.cr3]@.value->0[l4i] is None
    // }
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
impl PageTable {
    pub proof fn no_mapping_infer_not_mapped(&self, page_map_ptr: PageMapPtr)
        requires
            self.wf(),
            forall|va: VAddr|
                #![trigger self.mapping_4k().dom().contains(va)]
                #![trigger self.mapping_4k()[va]]
                self.mapping_4k().dom().contains(va) ==> self.mapping_4k()[va].addr != page_map_ptr,
            forall|va: VAddr|
                #![auto]
                self.mapping_2m().dom().contains(va) ==> self.mapping_2m()[va].addr != page_map_ptr,
            forall|va: VAddr|
                #![auto]
                self.mapping_1g().dom().contains(va) ==> self.mapping_1g()[va].addr != page_map_ptr,
        ensures
            self.page_not_mapped(page_map_ptr),
    {
    }

    pub proof fn no_mapping_infer_no_reslove(&self)
        requires
            self.wf(),
        ensures
            self.mapping_2m().dom() =~= Set::empty() ==> forall|
                l4i: L4Index,
                l3i: L3Index,
                l2i: L2Index,
            |
                #![trigger self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512
                    ==> self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some == false,
            self.mapping_1g().dom() =~= Set::empty() ==> forall|l4i: L4Index, l3i: L3Index|
                #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
                self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512
                    ==> self.spec_resolve_mapping_1g_l3(l4i, l3i) is Some == false,
    {
    }

    pub proof fn ps_entries_exist_in_mapped_pages(&self)
        requires
            self.wf(),
        ensures
            forall|p: PageMapPtr, i: L3Index|
                #![trigger self.l3_tables@[p].value()[i].addr]
                self.l3_tables@.dom().contains(p) && 0 <= i < 512
                    && self.l3_tables@[p].value()[i].perm.present
                    && self.l3_tables@[p].value()[i].perm.ps ==> self.page_not_mapped(
                    self.l3_tables@[p].value()[i].addr) == false,
            forall|p: PageMapPtr, i: L3Index|
                #![trigger self.l3_tables@[p].value()[i].addr]
                self.l3_tables@.dom().contains(p) && 0 <= i < 512
                    && self.l3_tables@[p].value()[i].perm.present
                    && !self.l3_tables@[p].value()[i].perm.ps ==> self.l2_tables@.dom().contains(
                    self.l3_tables@[p].value()[i].addr,
                ),
            forall|p: PageMapPtr, i: L2Index|
                #![trigger self.l2_tables@[p].value()[i].addr]
                self.l2_tables@.dom().contains(p) && 0 <= i < 512
                    && self.l2_tables@[p].value()[i].perm.present
                    && self.l2_tables@[p].value()[i].perm.ps ==> self.page_not_mapped(self.l2_tables@[p].value()[i].addr,) == false,
            forall|p: PageMapPtr, i: L2Index|
                #![trigger self.l2_tables@[p].value()[i].addr]
                self.l2_tables@.dom().contains(p) && 0 <= i < 512
                    && self.l2_tables@[p].value()[i].perm.present
                    && !self.l2_tables@[p].value()[i].perm.ps ==> self.l1_tables@.dom().contains(
                    self.l2_tables@[p].value()[i].addr,
                ),
            forall|p: PageMapPtr, i: L1Index|
                #![trigger self.l1_tables@[p].value()[i].addr]
                self.l1_tables@.dom().contains(p) && 0 <= i < 512
                    && self.l1_tables@[p].value()[i].perm.present
                    ==>self.page_not_mapped(self.l1_tables@[p].value()[i].addr) == false,
    {
        admit();
    }

        pub proof fn ps_entries_exist_in_mapped_pages_l3(&self)
        requires
            self.wf_l4(),
            self.wf_l3(),
            self.wf_mapping_1g(),
        ensures
            forall|p: PageMapPtr, i: L3Index|
                #![trigger self.l3_tables@[p].value()[i].addr]
                self.l3_tables@.dom().contains(p) && 0 <= i < 512
                    && self.l3_tables@[p].value()[i].perm.present
                    && self.l3_tables@[p].value()[i].perm.ps ==> self.page_not_mapped(
                    self.l3_tables@[p].value()[i].addr) == false,
            forall|p: PageMapPtr, i: L3Index|
                #![trigger self.l3_tables@[p].value()[i].addr]
                self.l3_tables@.dom().contains(p) && 0 <= i < 512
                    && self.l3_tables@[p].value()[i].perm.present
                    && !self.l3_tables@[p].value()[i].perm.ps ==> self.l2_tables@.dom().contains(
                    self.l3_tables@[p].value()[i].addr,
                ),
    {
        assert(forall|p: PageMapPtr, i: L3Index|
                #![trigger self.l3_tables@[p].value()[i].addr]
                self.l3_tables@.dom().contains(p) && 0 <= i < 512
                    && self.l3_tables@[p].value()[i].perm.present
                    && self.l3_tables@[p].value()[i].perm.ps ==> 
                    self.spec_resolve_mapping_1g_l3(self.l3_rev_map@[p], i) is Some
                    &&
                    self.spec_resolve_mapping_1g_l3(self.l3_rev_map@[p], i).unwrap().addr == self.l3_tables@[p].value()[i].addr
                    &&
                    self.mapping_1g@.dom().contains(spec_index2va((self.l3_rev_map@[p], i, 0, 0)))
                    &&
                    self.mapping_1g()[spec_index2va((self.l3_rev_map@[p], i, 0, 0))].addr == self.l3_tables@[p].value()[i].addr
        );
    }

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
                self.kernel_l4_end <= l4i < 512 
                    && 0 <= l3i < 512 
                    && self.kernel_l4_end <= l4j < 512
                    && 0 <= l3j < 512 
                    && (l4i, l3i) != (l4j, l3j) 
                    && self.spec_resolve_mapping_l3(l4i,l3i) is Some 
                    && self.spec_resolve_mapping_l3(l4j, l3j) is Some
                    ==> 
                    self.spec_resolve_mapping_l3(l4i, l3i)->0.addr != self.spec_resolve_mapping_l3(l4j, l3j)->0.addr,
            forall|l4i: L4Index,l3i: L3Index, l2i: L3Index, l4j: L4Index, l3j: L3Index, l2j: L2Index|
                #![trigger self.spec_resolve_mapping_l2(l4i,l3i,l2i), self.spec_resolve_mapping_l2(l4j,l3j,l2j)]
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

    impl LockInv for PageTable{
        open spec fn inv(&self) -> bool{
            &&&
            self.wf()
        }
        open spec fn lock_minor(&self) -> LockMinorId{
            self.cr3
        }
    }

} // verus!
