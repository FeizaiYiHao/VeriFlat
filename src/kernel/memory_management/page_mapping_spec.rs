use vstd::prelude::*;
use crate::*;
verus! {

    // impl Kernel{
    //     pub open spec fn kernel_page_array_pagetable_map_inv(&self) -> bool{
    //         &&&
    //         self.page_array_pagetable_map_inv1()
    //         &&&
    //         self.page_array_pagetable_map_inv2()
    //         &&&
    //         self.pagetable_map_page_array_inv1()
    //         &&&
    //         self.pagetable_map_page_array_inv2()
    //     }

    //     // #[verifier(external_body)]
    //     // pub proof fn page_array_pagetable_map_inv1_open(&self)
    //     //     ensures 
    //     //         forall|p_i:PageIndex, mapping: (RwLockPageTableRoot, VAddr)|
    //     //             #![auto]
    //     //             page_index_valid(p_i) && self.page_array@[p_i as int]@.mappings_4k@.contains(mapping)
    //     //             ==>{
    //     //                 |||
    //     //                 self.page_array@[p_i as int].wlocked()
    //     //                 |||
    //     //                 self.pagetable_map.dom().contains(mapping.0)
    //     //             },
    //     // {
    //     // }

    //     pub open spec fn page_array_pagetable_map_inv1(&self) -> bool{
    //         &&&
    //         forall|p_i:PageIndex, pt_r: RwLockPageTableRoot, va: VAddr|
    //             #![trigger self.page_array[p_i]@@.mappings_4k@.contains((pt_r, va))]
    //             page_index_valid(p_i) && self.page_array[p_i]@@.mappings_4k@.contains((pt_r, va))
    //             ==>{
    //                 |||
    //                 self.page_array[p_i]@.locking_thread() is Write
    //                 |||
    //                 self.pagetable_map.dom().contains(pt_r)
    //             }
    //     }

    //     pub open spec fn page_array_pagetable_map_inv2(&self) -> bool{
    //         &&&
    //         forall|p_i:PageIndex, pt_r: RwLockPageTableRoot, va: VAddr|
    //             #![auto]
    //             page_index_valid(p_i) && self.page_array[p_i]@@.mappings_4k@.contains((pt_r, va))
    //             ==>
    //             {
    //                 |||
    //                 write_locked_by_same_thread(self.page_array[p_i]@, self.pagetable_map[pt_r])
    //                 |||
    //                 (self.pagetable_map[pt_r]@.mapping_4k().contains_key(va) && self.pagetable_map[pt_r]@.mapping_4k()[va].addr == page_index2page_ptr(p_i))
    //             }
    //     }

    //     pub open spec fn pagetable_map_page_array_inv1(&self) -> bool{
    //         &&&
    //         forall|pt_r:RwLockPageTableRoot, va:VAddr|
    //             #![trigger self.pagetable_map[pt_r]@.mapping_4k().contains_key(va)]
    //             #![trigger self.pagetable_map[pt_r]@.mapping_4k()[va]]
    //             self.pagetable_map.dom().contains(pt_r) && self.pagetable_map[pt_r]@.mapping_4k().contains_key(va)
    //             ==>{
    //                 // |||
    //                 // self.pagetable_map[pt_r].locking_thread() is Write
    //                 |||
    //                 page_ptr_valid(self.pagetable_map[pt_r]@.mapping_4k()[va].addr)
    //             }
    //     }

    //     pub open spec fn pagetable_map_page_array_inv2(&self) -> bool{
    //         &&&
    //         forall|pt_r:RwLockPageTableRoot, va:VAddr|
    //             #![trigger self.pagetable_map[pt_r]@.mapping_4k().contains_key(va)]
    //             #![trigger self.pagetable_map[pt_r]@.mapping_4k()[va]]
    //             self.pagetable_map.dom().contains(pt_r) && self.pagetable_map[pt_r]@.mapping_4k().contains_key(va)
    //             ==>{
    //                 |||
    //                 write_locked_by_same_thread(self.page_array[page_ptr2page_index(self.pagetable_map[pt_r]@.mapping_4k()[va].addr)]@, self.pagetable_map[pt_r])
    //                 |||
    //                 self.page_array[page_ptr2page_index(self.pagetable_map[pt_r]@.mapping_4k()[va].addr)]@@.mappings_4k@.contains((pt_r, va))
    //             }
    //     }
    // }

    pub open spec fn page_mapping_wf(pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE>, page_array: LockedArray<Page, NUM_PAGES, NO_KILL_STATE>) -> bool {
        &&&
        mapped_4k_page_pagetable_mapping_match(pagetable_map, page_array)
    }

    pub proof fn mapped_4k_page_pagetable_mapping_match_proof()
        ensures 
            forall|pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE>, page_array: LockedArray<Page, NUM_PAGES, NO_KILL_STATE>|
                mapped_4k_page_pagetable_mapping_match_inner(pagetable_map, page_array) <==> mapped_4k_page_pagetable_mapping_match(pagetable_map, page_array) 
    {}

    pub closed spec fn mapped_4k_page_pagetable_mapping_match(pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE>, page_array: LockedArray<Page, NUM_PAGES, NO_KILL_STATE>) -> bool {
        mapped_4k_page_pagetable_mapping_match_inner(pagetable_map, page_array) 
    }

    pub open spec fn mapped_4k_page_pagetable_mapping_match_inner(pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE>, page_array: LockedArray<Page, NUM_PAGES, NO_KILL_STATE>) -> bool {
        &&&
        forall|p_i:PageIndex, pt_ptr:RwLockPageTableRoot, va: VAddr|
            #![trigger page_array.spec_index(p_i).view().view().mappings_4k().contains((pt_ptr, va))]
            page_index_valid(p_i)
            &&
            page_array.spec_index(p_i).view().wlocked() == false
            &&
            page_array.spec_index(p_i).view().view().mappings_4k().contains((pt_ptr, va))
            ==>
            pagetable_map.dom().contains(pt_ptr)
            &&
            {
                |||
                write_locked_by_same_thread(page_array.spec_index(p_i).view(), pagetable_map.spec_index(pt_ptr))
                |||
                pagetable_map.spec_index(pt_ptr).view().mapping_4k().contains_key(va)
                &&
                pagetable_map.spec_index(pt_ptr).view().mapping_4k()[va].addr == page_index2page_ptr(p_i)
            }
        &&&
        forall|pt_ptr:RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr|
            pagetable_map.dom().contains(pt_ptr)
            &&
            pagetable_map.spec_index(pt_ptr).wlocked() == false
            &&
            pagetable_map.spec_index(pt_ptr).view().mapping_4k().contains_key(va)
            &&
            pagetable_map.spec_index(pt_ptr).view().mapping_4k()[va].addr == page_ptr
            ==>
            {
                |||
                write_locked_by_same_thread(page_array.spec_index(page_ptr2page_index(page_ptr)).view(), pagetable_map.spec_index(pt_ptr))
                |||
                page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().mappings_4k().contains((pt_ptr, va))
            }
    }
    

}