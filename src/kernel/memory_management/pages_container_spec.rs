use core::slice;

use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn container_pages_wf(page_array: PageLockedArray, container_map: ContainerLockedMap) -> bool{
        &&&
        forall|page_index:PageIndex|
        #![trigger page_array.spec_index(page_index).view().view().state]
        #![trigger container_map.dom().contains(page_index2page_ptr(page_index))]
        index_valid(NUM_PAGES, page_index)
        ==>
        {
            page_array.spec_index(page_index).view().view().state matches PageState::Allocated2m{state: Allocated2MPageState::AsContainer}
            ==>
            container_map.dom().contains(page_index2page_ptr(page_index))
        }

        &&&
        forall|c_ptr:RwLockContainerPtr|
        #![trigger page_array.spec_index(page_ptr2page_index(c_ptr)).view().view().state]
        #![trigger container_map.dom().contains(c_ptr)]
        container_map.dom().contains(c_ptr)
        ==>
        page_ptr_2m_valid(c_ptr)
        &&
        {
            page_array.spec_index(page_ptr2page_index(c_ptr)).view().view().state matches PageState::Allocated2m{state: Allocated2MPageState::AsContainer}
        }

    }
    
}
