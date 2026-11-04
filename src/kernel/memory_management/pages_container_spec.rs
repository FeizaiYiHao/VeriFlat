use vstd::prelude::*;
use crate::*;

verus! {
    pub open spec fn container_pages_forward_wf(page_array: PageLockedArray, container_map: ContainerLockedMap) -> bool {
        forall|pg_idx:PageIndex|
            #![trigger page_array.spec_index(pg_idx).view().view().state]
            #![trigger container_map.dom().contains(page_index2page_ptr(pg_idx))]
            index_valid(NUM_PAGES, pg_idx) ==> { page_array.spec_index(pg_idx).view().view().state matches PageState::Allocated2m{state: Allocated2MPageState::AsContainer} ==> container_map.dom().contains(page_index2page_ptr(pg_idx)) }
    }

    pub open spec fn container_pages_backward_wf(page_array: PageLockedArray, container_map: ContainerLockedMap) -> bool {
        forall|c_ptr:RwLockContainerPtr|
            #![trigger page_array.spec_index(page_ptr2page_index(c_ptr)).view().view().state]
            #![trigger container_map.dom().contains(c_ptr)]
            container_map.dom().contains(c_ptr) ==> page_ptr_2m_valid(c_ptr) && { page_array.spec_index(page_ptr2page_index(c_ptr)).view().view().state matches PageState::Allocated2m{state: Allocated2MPageState::AsContainer} }
    }

    #[verifier::opaque]
    pub open spec fn container_pages_wf(page_array: PageLockedArray, container_map: ContainerLockedMap) -> bool {
        &&& container_pages_forward_wf(page_array, container_map)
        &&& container_pages_backward_wf(page_array, container_map)
    }

    pub proof fn container_pages_backward_at(page_array: PageLockedArray, container_map: ContainerLockedMap, ctn_ptr: RwLockContainerPtr)
        requires
            container_pages_wf(page_array, container_map),
        ensures
            container_map.dom().contains(ctn_ptr) ==> page_ptr_2m_valid(ctn_ptr) && (page_array.spec_index(page_ptr2page_index(ctn_ptr)).view().view().state matches PageState::Allocated2m { state: Allocated2MPageState::AsContainer }),
    { reveal(container_pages_wf); }
}
