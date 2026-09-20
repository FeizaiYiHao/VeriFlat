use core::slice;

use vstd::prelude::*;
use crate::*;

verus! {
        pub open spec fn pagetable_root_page_forward_wf(
            pagetable_map: PageTableLockedMap,
            page_array: PageLockedArray,
        ) -> bool {
            forall|page_index:PageIndex|
                #![trigger pagetable_map.dom().contains(page_index2page_ptr(page_index))]
                index_valid(NUM_PAGES, page_index) && (page_array.spec_index(page_index).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::AsPageTableRoot})
                    ==>
                    pagetable_map.dom().contains(page_index2page_ptr(page_index))
        }

        pub open spec fn pagetable_closure_page_forward_wf(
            pagetable_map: PageTableLockedMap,
            page_array: PageLockedArray,
        ) -> bool {
            forall|page_index:PageIndex|
                #![trigger pagetable_map.dom().contains(page_array.spec_index(page_index).view().view().state->Allocated4k_state->PageTable_pagetable_root)]
                #![trigger pagetable_map.spec_index(page_array.spec_index(page_index).view().view().state->Allocated4k_state->PageTable_pagetable_root).view().page_closure().contains(page_index2page_ptr(page_index))]
                index_valid(NUM_PAGES, page_index) && (page_array.spec_index(page_index).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::PageTable { pagetable_root }})
                    ==>
                    pagetable_map.dom().contains(page_array.spec_index(page_index).view().view().state->Allocated4k_state->PageTable_pagetable_root)
                    &&
                    pagetable_map.spec_index(page_array.spec_index(page_index).view().view().state->Allocated4k_state->PageTable_pagetable_root).view().page_closure().contains(page_index2page_ptr(page_index))
        }

        pub open spec fn pagetable_root_page_backward_wf(
            pagetable_map: PageTableLockedMap,
            page_array: PageLockedArray,
        ) -> bool {
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
        }

        pub open spec fn pagetable_closure_page_backward_wf(
            pagetable_map: PageTableLockedMap,
            page_array: PageLockedArray,
        ) -> bool {
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

        #[verifier::opaque]
        pub open spec fn pagetable_pages_wf(
            pagetable_map: PageTableLockedMap,
            page_array: PageLockedArray,
        ) -> bool {
            &&& pagetable_root_page_forward_wf(pagetable_map, page_array)
            &&& pagetable_closure_page_forward_wf(pagetable_map, page_array)
            &&& pagetable_root_page_backward_wf(pagetable_map, page_array)
            &&& pagetable_closure_page_backward_wf(pagetable_map, page_array)
        }

        pub proof fn pagetable_pages_wf_closure_entry_at(
            pagetable_map: PageTableLockedMap,
            page_array: PageLockedArray,
            pagetable_ptr: RwLockPageTableRoot,
            page_ptr: PagePtr,
        )
            requires
                pagetable_pages_wf(pagetable_map, page_array),
                pagetable_map.dom().contains(pagetable_ptr),
                pagetable_map.spec_index(pagetable_ptr).view()
                    .page_closure().contains(page_ptr),
            ensures
                page_ptr_valid(page_ptr),
                page_array.spec_index(page_ptr2page_index(page_ptr))
                    .view().view().state is Allocated4k,
                page_array.spec_index(page_ptr2page_index(page_ptr))
                    .view().view().state->Allocated4k_state is PageTable,
                page_array.spec_index(page_ptr2page_index(page_ptr))
                    .view().view().state->Allocated4k_state
                    ->PageTable_pagetable_root == pagetable_ptr,
        {
            reveal(pagetable_pages_wf);
        }
}
