use vstd::prelude::*;
use crate::*;
verus! {
    pub open spec fn page_pagetable_wf(pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>, page_array: LockedArray<Page, (), (), NUM_PAGES, NO_KILL_STATE>) -> bool {
        &&&
        mapped_4k_page_pagetable_wf(pagetable_map, page_array)        
        &&&
        mapped_2m_page_pagetable_wf(pagetable_map, page_array)        
        &&&
        mapped_1g_page_pagetable_wf(pagetable_map, page_array)
    }

    pub proof fn mapped_4k_page_pagetable_wf_proof()
        ensures 
            forall|pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>, page_array: LockedArray<Page, (), (), NUM_PAGES, NO_KILL_STATE>|
                mapped_4k_page_pagetable_wf_inner(pagetable_map, page_array) <==> mapped_4k_page_pagetable_wf(pagetable_map, page_array),
            forall|pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>, page_array: LockedArray<Page, (), (), NUM_PAGES, NO_KILL_STATE>|
                mapped_2m_page_pagetable_wf_inner(pagetable_map, page_array) <==> mapped_2m_page_pagetable_wf(pagetable_map, page_array),
            forall|pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>, page_array: LockedArray<Page, (), (), NUM_PAGES, NO_KILL_STATE>|
                mapped_1g_page_pagetable_wf_inner(pagetable_map, page_array) <==> mapped_1g_page_pagetable_wf(pagetable_map, page_array),
    {}

    pub closed spec fn mapped_4k_page_pagetable_wf(pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>, page_array: LockedArray<Page, (), (), NUM_PAGES, NO_KILL_STATE>) -> bool {
        mapped_4k_page_pagetable_wf_inner(pagetable_map, page_array) 
    }

    pub open spec fn mapped_4k_page_pagetable_wf_inner(pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>, page_array: LockedArray<Page, (), (), NUM_PAGES, NO_KILL_STATE>
        ) -> bool {
        &&&
        forall|p_i:PageIndex, pt_ptr:RwLockPageTableRoot, va: VAddr|
            #![trigger page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va))]
            page_index_valid(p_i)
            &&
            page_array.spec_index(p_i).view().view().state == PageState::Mapped4k
            &&
            page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va))
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
            page_array.spec_index(page_ptr2page_index(pagetable_map.spec_index(pt_ptr).view().mapping_4k()[va].addr)).view().view().state == PageState::Mapped4k
            &&
            page_array.spec_index(page_ptr2page_index(pagetable_map.spec_index(pt_ptr).view().mapping_4k()[va].addr)).view().view().mappings().contains((pt_ptr, va))
    }

    pub proof fn mapped_2m_page_pagetable_wf_proof()
        ensures 
            forall|pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>, page_array: LockedArray<Page, (), (), NUM_PAGES, NO_KILL_STATE>|
                mapped_2m_page_pagetable_wf_inner(pagetable_map, page_array) <==> mapped_2m_page_pagetable_wf(pagetable_map, page_array) 
    {}

    pub closed spec fn mapped_2m_page_pagetable_wf(pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>, page_array: LockedArray<Page, (), (), NUM_PAGES, NO_KILL_STATE>) -> bool {
        mapped_2m_page_pagetable_wf_inner(pagetable_map, page_array) 
    }

    pub open spec fn mapped_2m_page_pagetable_wf_inner(pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>, page_array: LockedArray<Page, (), (), NUM_PAGES, NO_KILL_STATE>
        ) -> bool {
        &&&
        forall|p_i:PageIndex, pt_ptr:RwLockPageTableRoot, va: VAddr|
            #![trigger page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va))]
            page_index_valid(p_i)
            &&
            page_array.spec_index(p_i).view().view().state == PageState::Mapped2m
            &&
            page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va))
            ==> 
            pagetable_map.dom().contains(pt_ptr)
            &&
            pagetable_map.spec_index(pt_ptr).view().mapping_2m().contains_key(va)
            &&
            pagetable_map.spec_index(pt_ptr).view().mapping_2m()[va].addr == page_index2page_ptr(p_i)
            
        &&&
        forall|pt_ptr:RwLockPageTableRoot, va: VAddr|
            #![trigger pagetable_map.spec_index(pt_ptr).view().mapping_2m().contains_key(va)]
            pagetable_map.dom().contains(pt_ptr)
            &&
            pagetable_map.spec_index(pt_ptr).view().mapping_2m().contains_key(va)
            ==>
            page_array.spec_index(page_ptr2page_index(pagetable_map.spec_index(pt_ptr).view().mapping_2m()[va].addr)).view().view().state == PageState::Mapped2m
            &&
            page_array.spec_index(page_ptr2page_index(pagetable_map.spec_index(pt_ptr).view().mapping_2m()[va].addr)).view().view().mappings().contains((pt_ptr, va))
    }

    pub proof fn mapped_1g_page_pagetable_wf_proof()
        ensures 
            forall|pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>, page_array: LockedArray<Page, (), (), NUM_PAGES, NO_KILL_STATE>|
                mapped_1g_page_pagetable_wf_inner(pagetable_map, page_array) <==> mapped_1g_page_pagetable_wf(pagetable_map, page_array) 
    {}

    pub closed spec fn mapped_1g_page_pagetable_wf(pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>, page_array: LockedArray<Page, (), (), NUM_PAGES, NO_KILL_STATE>) -> bool {
        mapped_1g_page_pagetable_wf_inner(pagetable_map, page_array) 
    }

    pub open spec fn mapped_1g_page_pagetable_wf_inner(pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>, page_array: LockedArray<Page, (), (), NUM_PAGES, NO_KILL_STATE>
        ) -> bool {
        &&&
        forall|p_i:PageIndex, pt_ptr:RwLockPageTableRoot, va: VAddr|
            #![trigger page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va))]
            page_index_valid(p_i)
            &&
            page_array.spec_index(p_i).view().view().state == PageState::Mapped1g
            &&
            page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va))
            ==> 
            pagetable_map.dom().contains(pt_ptr)
            &&
            pagetable_map.spec_index(pt_ptr).view().mapping_1g().contains_key(va)
            &&
            pagetable_map.spec_index(pt_ptr).view().mapping_1g()[va].addr == page_index2page_ptr(p_i)
            
        &&&
        forall|pt_ptr:RwLockPageTableRoot, va: VAddr|
            #![trigger pagetable_map.spec_index(pt_ptr).view().mapping_1g().contains_key(va)]
            pagetable_map.dom().contains(pt_ptr)
            &&
            pagetable_map.spec_index(pt_ptr).view().mapping_1g().contains_key(va)
            ==>
            page_array.spec_index(page_ptr2page_index(pagetable_map.spec_index(pt_ptr).view().mapping_1g()[va].addr)).view().view().state == PageState::Mapped1g
            &&
            page_array.spec_index(page_ptr2page_index(pagetable_map.spec_index(pt_ptr).view().mapping_1g()[va].addr)).view().view().mappings().contains((pt_ptr, va))
    }

    pub proof fn container_process_page_pagetable_wf_proof()
        ensures 
            forall| container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, (), CONTAINER_HAS_KILL_STATE>, 
                process_map: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>, 
                pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>, 
                page_array: LockedArray<Page, (), (), NUM_PAGES, NO_KILL_STATE>|
            container_process_page_pagetable_wf_inner(container_map, process_map, pagetable_map, page_array) <==> container_process_page_pagetable_wf(container_map, process_map, pagetable_map, page_array) 
    {}

    pub closed spec fn container_process_page_pagetable_wf(
        container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, (), CONTAINER_HAS_KILL_STATE>, 
            process_map: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>, 
            pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>, 
            page_array: LockedArray<Page, (), (), NUM_PAGES, NO_KILL_STATE>
    ) -> bool {
        container_process_page_pagetable_wf_inner(container_map, process_map, pagetable_map, page_array) 
    }

    pub open spec fn container_process_page_pagetable_wf_inner(container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, (), CONTAINER_HAS_KILL_STATE>, 
            process_map: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>, 
            pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>, 
            page_array: LockedArray<Page, (), (), NUM_PAGES, NO_KILL_STATE>) -> bool {
        &&&
        forall|p_i:PageIndex, pt_ptr:RwLockPageTableRoot, va: VAddr|
            #![trigger page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va))]
            page_index_valid(p_i)
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