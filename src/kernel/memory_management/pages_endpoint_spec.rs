use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn endpoint_pages_wf(endpoint_map: EndpointLockedMap, page_array: PageLockedArray) -> bool {
        &&& forall|pg_idx:PageIndex|
            #![trigger page_array.spec_index(pg_idx)]
            #![trigger endpoint_map.dom().contains(page_index2page_ptr(pg_idx))]
            index_valid(NUM_PAGES, pg_idx) && {page_array.spec_index(pg_idx).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::AsEndpoint}}
                ==> endpoint_map.dom().contains(page_index2page_ptr(pg_idx))
        &&& forall|e_ptr:RwLockEndpointPtr|
            #![trigger page_array.spec_index(page_ptr2page_index(e_ptr))]
            #![trigger endpoint_map.dom().contains(e_ptr)]
            endpoint_map.dom().contains(e_ptr) ==> page_ptr_valid(e_ptr) && { page_array.spec_index(page_ptr2page_index(e_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::AsEndpoint} }
    }

    /// Page `e_ptr` is an endpoint only if it is a valid page marked as an endpoint page.
    pub proof fn endpoint_pages_wf_page_at(endpoint_map: EndpointLockedMap, page_array: PageLockedArray, e_ptr: RwLockEndpointPtr)
        requires endpoint_pages_wf(endpoint_map, page_array),
        ensures endpoint_map.dom().contains(e_ptr) ==> page_ptr_valid(e_ptr) && (page_array.spec_index(page_ptr2page_index(e_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::AsEndpoint}),
    { reveal(endpoint_pages_wf); }
}
