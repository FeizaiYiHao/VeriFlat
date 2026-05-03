use core::slice;

use vstd::prelude::*;
use crate::*;

verus! {
        pub proof fn endpoint_pages_wf_proof()
            ensures 
                forall|endpoint_map: LockedMap<RwLockEndpointPtr, Endpoint, ENDPOINT_HAS_KILL_STATE>, page_array: LockedArray<Page, NUM_PAGES, NO_KILL_STATE>|
                    endpoint_pages_wf_inner(endpoint_map, page_array) <==> endpoint_pages_wf(endpoint_map, page_array)
        {}

        pub closed spec fn endpoint_pages_wf(endpoint_map: LockedMap<RwLockEndpointPtr, Endpoint, ENDPOINT_HAS_KILL_STATE>, page_array: LockedArray<Page, NUM_PAGES, NO_KILL_STATE>) -> bool {
            &&&
            endpoint_pages_wf_inner(endpoint_map, page_array)
        }

        pub open spec fn endpoint_pages_wf_inner(endpoint_map: LockedMap<RwLockEndpointPtr, Endpoint, ENDPOINT_HAS_KILL_STATE>, page_array: LockedArray<Page, NUM_PAGES, NO_KILL_STATE>) -> bool{
            &&&
            forall|page_index:PageIndex|
            #![trigger page_array.spec_index(page_index)]
            #![trigger endpoint_map.dom().contains(page_index2page_ptr(page_index))]
            page_index_wf(page_index)
            ==>
            {
                page_array.spec_index(page_index).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::AsEndpoint}
                ==>
                endpoint_map.dom().contains(page_index2page_ptr(page_index))
            }

            &&&
            forall|e_ptr:RwLockEndpointPtr|
            #![trigger page_array.spec_index(page_ptr2page_index(e_ptr))]
            #![trigger endpoint_map.dom().contains(e_ptr)]
            endpoint_map.dom().contains(e_ptr)
            ==>
            page_ptr_valid(e_ptr)
            &&
            {
                page_array.spec_index(page_ptr2page_index(e_ptr)).view().view().state matches PageState::Allocated4k{state: Allocated4KPageState::AsEndpoint}
            }

        }
}