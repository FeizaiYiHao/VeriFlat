use core::slice;

use vstd::prelude::*;
use crate::*;

verus! {
        pub proof fn pagetable_pages_wf_proof()
            ensures 
                forall|pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>, page_array: LockedArray<Page, (), (), NUM_PAGES, NO_KILL_STATE>|
                    pagetable_pages_wf_inner(pagetable_map, page_array) <==> pagetable_pages_wf(pagetable_map, page_array)
        {}

        pub closed spec fn pagetable_pages_wf(pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>, page_array: LockedArray<Page, (), (), NUM_PAGES, NO_KILL_STATE>) -> bool {
            &&&
            pagetable_pages_wf_inner(pagetable_map, page_array)
        }

        pub open spec fn pagetable_pages_wf_inner(pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>, page_array: LockedArray<Page, (), (), NUM_PAGES, NO_KILL_STATE>) -> bool{
            &&&
            forall|page_index:PageIndex|
            #![trigger page_array.spec_index(page_index)]
            #![trigger pagetable_map.dom().contains(page_index2page_ptr(page_index))]
            page_index_wf(page_index)
            ==>
            {
                page_array.spec_index(page_index).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::AsPageTableRoot}
                ==>
                pagetable_map.dom().contains(page_index2page_ptr(page_index))
            }
            &&
            {
                page_array.spec_index(page_index).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::PageTable { pagetable_root }}
                ==>
                pagetable_map.dom().contains(pagetable_root)
                &&
                pagetable_map.spec_index(pagetable_root).view().page_closure().contains(page_index2page_ptr(page_index))
            }
            &&&
            forall|pt_ptr:RwLockPageTableRoot|
            #![trigger page_array.spec_index(page_ptr2page_index(pt_ptr))]
            #![trigger pagetable_map.dom().contains(pt_ptr)]
            pagetable_map.dom().contains(pt_ptr)
            ==>
            page_ptr_valid(pt_ptr)
            &&
            {
                page_array.spec_index(page_ptr2page_index(pt_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::AsPageTableRoot}
            }
            &&&
            forall|pt_ptr:RwLockPageTableRoot, pt_p_ptr:PagePtr|
            #![trigger pagetable_map.spec_index(pt_ptr).view().page_closure().contains(pt_p_ptr)]
            pagetable_map.dom().contains(pt_ptr) && pagetable_map.spec_index(pt_ptr).view().page_closure().contains(pt_p_ptr)
            ==>
            page_ptr_valid(pt_p_ptr)
            &&
            {
                page_array.spec_index(page_ptr2page_index(pt_p_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::PageTable { .. }}
            }

        }
}