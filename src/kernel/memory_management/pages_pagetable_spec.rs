use core::slice;

use vstd::prelude::*;
use crate::*;

verus! {
        #[verifier::opaque]
        pub open spec fn pagetable_pages_wf(pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), (), PAGE_TABLE_HAS_KILL_STATE>, page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>) -> bool {
            &&&
            forall|page_index:PageIndex|
                #![trigger pagetable_map.dom().contains(page_index2page_ptr(page_index))]
                page_index_wf(page_index) && (page_array.spec_index(page_index).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::AsPageTableRoot})
                    ==>
                    pagetable_map.dom().contains(page_index2page_ptr(page_index))
            &&&
            forall|page_index:PageIndex|
                #![trigger pagetable_map.dom().contains(page_array.spec_index(page_index).view().view().state->Allocated4k_state->PageTable_pagetable_root)]
                #![trigger pagetable_map.spec_index(page_array.spec_index(page_index).view().view().state->Allocated4k_state->PageTable_pagetable_root).view().page_closure().contains(page_index2page_ptr(page_index))]
                page_index_wf(page_index) && (page_array.spec_index(page_index).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::PageTable { pagetable_root }})
                    ==>
                    pagetable_map.dom().contains(page_array.spec_index(page_index).view().view().state->Allocated4k_state->PageTable_pagetable_root)
                    &&
                    pagetable_map.spec_index(page_array.spec_index(page_index).view().view().state->Allocated4k_state->PageTable_pagetable_root).view().page_closure().contains(page_index2page_ptr(page_index))
            &&&
            forall|pt_ptr:RwLockPageTableRoot|
                // #![trigger page_array.spec_index(page_ptr2page_index(pt_ptr))]
                #![trigger pagetable_map.dom().contains(pt_ptr)]
                pagetable_map.dom().contains(pt_ptr)
                    ==>
                    page_ptr_valid(pt_ptr)
                    &&
                    page_array.spec_index(page_ptr2page_index(pt_ptr)).view().view().state is Allocated4k
                    &&
                    page_array.spec_index(page_ptr2page_index(pt_ptr)).view().view().state->Allocated4k_state is AsPageTableRoot
            &&&
            forall|pt_ptr:RwLockPageTableRoot, pt_p_ptr:PagePtr|
                #![trigger pagetable_map.spec_index(pt_ptr).view().page_closure().contains(pt_p_ptr)]
                pagetable_map.dom().contains(pt_ptr) && pagetable_map.spec_index(pt_ptr).view().page_closure().contains(pt_p_ptr)
                    ==>
                    page_ptr_valid(pt_p_ptr)
                    &&
                    page_array.spec_index(page_ptr2page_index(pt_p_ptr)).view().view().state is Allocated4k
                    &&
                    page_array.spec_index(page_ptr2page_index(pt_p_ptr)).view().view().state->Allocated4k_state is PageTable
                    &&
                    page_array.spec_index(page_ptr2page_index(pt_p_ptr)).view().view().state->Allocated4k_state->PageTable_pagetable_root == pt_ptr
            

        }
}
