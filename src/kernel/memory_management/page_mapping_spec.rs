use vstd::prelude::*;
use crate::*;
verus! {
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
            page_array.spec_index(p_i).view().view().mappings_4k().contains((pt_ptr, va))
            ==> 
            pagetable_map.dom().contains(pt_ptr)
            &&
            pagetable_map.spec_index(pt_ptr).view().mapping_4k().contains_key(va)
            &&
            pagetable_map.spec_index(pt_ptr).view().mapping_4k()[va].addr == page_index2page_ptr(p_i)
            
        &&&
        forall|pt_ptr:RwLockPageTableRoot, va: VAddr|
            #![trigger pagetable_map.spec_index(pt_ptr).view().mapping_4k().contains_key(va)]
            pagetable_map.dom().contains(pt_ptr)
            &&
            pagetable_map.spec_index(pt_ptr).view().mapping_4k().contains_key(va)
            ==>
            page_array.spec_index(page_ptr2page_index(pagetable_map.spec_index(pt_ptr).view().mapping_4k()[va].addr)).view().view().mappings_4k().contains((pt_ptr, va))
    }
    

}