use core::slice;

use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn process_pages_wf(page_array: PageLockedArray, process_map: ProcessLockedMap) -> bool{
        &&&
        forall|page_index:PageIndex|
        #![trigger page_array.spec_index(page_index).view().view().state]
        #![trigger process_map.dom().contains(page_index2page_ptr(page_index))]
        page_index_wf(page_index)
        ==>
        {
            page_array.spec_index(page_index).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::AsProcess}
            ==>
            process_map.dom().contains(page_index2page_ptr(page_index))
        }

        &&&
        forall|c_ptr:RwLockContainerPtr|
        #![trigger page_array.spec_index(page_ptr2page_index(c_ptr)).view().view().state]
        #![trigger process_map.dom().contains(c_ptr)]
        process_map.dom().contains(c_ptr)
        ==>
        page_ptr_valid(c_ptr)
        &&
        {
            page_array.spec_index(page_ptr2page_index(c_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::AsProcess}
        }

    }
}
