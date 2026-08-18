use vstd::prelude::*;
use crate::*;
verus! {
    pub open spec fn page_pagetable_wf(pagetable_map: PageTableLockedMap, page_array: PageLockedArray) -> bool {
        &&&
        mapped_4k_page_pagetable_wf(pagetable_map, page_array)        
        &&&
        mapped_2m_page_pagetable_wf(pagetable_map, page_array)        
        &&&
        mapped_1g_page_pagetable_wf(pagetable_map, page_array)
    }

    #[verifier::opaque]
    pub open spec fn mapped_4k_page_pagetable_wf(pagetable_map: PageTableLockedMap, page_array: PageLockedArray
        ) -> bool {
        &&&
        forall|p_i:PageIndex|
            #![trigger page_array.spec_index(p_i)]
            index_valid(NUM_PAGES, p_i)
            &&
            page_array.spec_index(p_i).view().view().state == PageState::Mapped4k
            ==>
            forall|pt_ptr:RwLockPageTableRoot, va: VAddr|
                #![trigger page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va))]
                #![trigger pagetable_map.spec_index(pt_ptr).view().mapping_4k().spec_index(va)]
                page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va))
                ==>
                pagetable_map.dom().contains(pt_ptr)
                &&
                pagetable_map.spec_index(pt_ptr).view().mapping_4k().contains_key(va)
                &&
                pagetable_map.spec_index(pt_ptr).view().mapping_4k().spec_index(va).addr == page_index2page_ptr(p_i)
            
        &&&
        forall|pt_ptr:RwLockPageTableRoot|
            #![trigger pagetable_map.dom().contains(pt_ptr)]
            pagetable_map.dom().contains(pt_ptr)
            ==>
            forall|va: VAddr|
                #![trigger pagetable_map.spec_index(pt_ptr).view().mapping_4k().contains_key(va)]
                #![trigger pagetable_map.spec_index(pt_ptr).view().mapping_4k().spec_index(va)]
                pagetable_map.spec_index(pt_ptr).view().mapping_4k().contains_key(va)
                ==>
                page_array.spec_index(page_ptr2page_index(pagetable_map.spec_index(pt_ptr).view().mapping_4k().spec_index(va).addr)).view().view().state == PageState::Mapped4k
                &&
                page_array.spec_index(page_ptr2page_index(pagetable_map.spec_index(pt_ptr).view().mapping_4k().spec_index(va).addr)).view().view().mappings().contains((pt_ptr, va))
    }

    #[verifier::opaque]
    pub open spec fn mapped_2m_page_pagetable_wf(pagetable_map: PageTableLockedMap, page_array: PageLockedArray
        ) -> bool {
        &&&
        forall|p_i:PageIndex, pt_ptr:RwLockPageTableRoot, va: VAddr|
            #![trigger page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va))]
            index_valid(NUM_PAGES, p_i)
            &&
            page_array.spec_index(p_i).view().view().state == PageState::Mapped2m
            &&
            page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va))
            ==> 
            pagetable_map.dom().contains(pt_ptr)
            &&
            pagetable_map.spec_index(pt_ptr).view().mapping_2m().contains_key(va)
            &&
            pagetable_map.spec_index(pt_ptr).view().mapping_2m().spec_index(va).addr == page_index2page_ptr(p_i)
            
        &&&
        forall|pt_ptr:RwLockPageTableRoot, va: VAddr|
            #![trigger pagetable_map.spec_index(pt_ptr).view().mapping_2m().contains_key(va)]
            pagetable_map.dom().contains(pt_ptr)
            &&
            pagetable_map.spec_index(pt_ptr).view().mapping_2m().contains_key(va)
            ==>
            page_array.spec_index(page_ptr2page_index(pagetable_map.spec_index(pt_ptr).view().mapping_2m().spec_index(va).addr)).view().view().state == PageState::Mapped2m
            &&
            page_array.spec_index(page_ptr2page_index(pagetable_map.spec_index(pt_ptr).view().mapping_2m().spec_index(va).addr)).view().view().mappings().contains((pt_ptr, va))
    }

    #[verifier::opaque]
    pub open spec fn mapped_1g_page_pagetable_wf(pagetable_map: PageTableLockedMap, page_array: PageLockedArray
        ) -> bool {
        &&&
        forall|p_i:PageIndex, pt_ptr:RwLockPageTableRoot, va: VAddr|
            #![trigger page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va))]
            index_valid(NUM_PAGES, p_i)
            &&
            page_array.spec_index(p_i).view().view().state == PageState::Mapped1g
            &&
            page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va))
            ==> 
            pagetable_map.dom().contains(pt_ptr)
            &&
            pagetable_map.spec_index(pt_ptr).view().mapping_1g().contains_key(va)
            &&
            pagetable_map.spec_index(pt_ptr).view().mapping_1g().spec_index(va).addr == page_index2page_ptr(p_i)
            
        &&&
        forall|pt_ptr:RwLockPageTableRoot, va: VAddr|
            #![trigger pagetable_map.spec_index(pt_ptr).view().mapping_1g().contains_key(va)]
            pagetable_map.dom().contains(pt_ptr)
            &&
            pagetable_map.spec_index(pt_ptr).view().mapping_1g().contains_key(va)
            ==>
            page_array.spec_index(page_ptr2page_index(pagetable_map.spec_index(pt_ptr).view().mapping_1g().spec_index(va).addr)).view().view().state == PageState::Mapped1g
            &&
            page_array.spec_index(page_ptr2page_index(pagetable_map.spec_index(pt_ptr).view().mapping_1g().spec_index(va).addr)).view().view().mappings().contains((pt_ptr, va))
    }

    #[verifier::opaque]
    pub open spec fn container_process_page_pagetable_wf(container_map: ContainerLockedMap, 
            process_map: ProcessLockedMap, 
            pagetable_map: PageTableLockedMap, 
            page_array: PageLockedArray) -> bool {
        &&&
        forall|p_i:PageIndex, pt_ptr:RwLockPageTableRoot, va: VAddr|
            #![trigger page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va))]
            index_valid(NUM_PAGES, p_i)
            &&
            page_array.spec_index(p_i).view().view().is_mapped()
            &&
            page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va))
            ==> 
            {
                |||
                process_map.spec_index(pagetable_map.spec_index(pt_ptr).view().proc_ptr).view_rodata().view().owning_container
                    ==
                    page_array.spec_index(p_i).view().view().owning_container
                |||
                container_map.spec_index(page_array.spec_index(p_i).view().view().owning_container).view()
                    .subtree_set.view().contains(process_map.spec_index(pagetable_map.spec_index(pt_ptr).view().proc_ptr).view_rodata().view().owning_container)
            }
    }

}
