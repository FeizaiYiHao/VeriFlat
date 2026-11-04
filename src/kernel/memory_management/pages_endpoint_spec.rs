use vstd::prelude::*;
use crate::*;

verus! {
/// Endpoints and AsEndpoint pages agree in both directions.
#[verifier::opaque]
pub open spec fn endpoint_pages_wf(ep_mp: EndpointLockedMap, pg_arr: PageLockedArray) -> bool {
    // Page -> endpoint.
    &&& forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i)]
        #![trigger ep_mp.dom().contains(page_index2page_ptr(p_i))]
        index_valid(NUM_PAGES, p_i)
            && (pg_arr.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint })
            ==>
            ep_mp.dom().contains(page_index2page_ptr(p_i))
    // Endpoint -> page.
    &&& forall|e: RwLockEndpointPtr|
        #![trigger pg_arr.spec_index(page_ptr2page_index(e))]
        #![trigger ep_mp.dom().contains(e)]
        ep_mp.dom().contains(e)
            ==>
            page_ptr_valid(e)
            && (pg_arr.spec_index(page_ptr2page_index(e)).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint })
}

/// Page `ep_ptr` is an endpoint only if it is a valid page marked as an endpoint page.
pub proof fn endpoint_pages_wf_page_at(ep_mp: EndpointLockedMap, pg_arr: PageLockedArray, ep_ptr: RwLockEndpointPtr)
    requires endpoint_pages_wf(ep_mp, pg_arr),
    ensures
        ep_mp.dom().contains(ep_ptr)
            ==> page_ptr_valid(ep_ptr)
            && (pg_arr.spec_index(page_ptr2page_index(ep_ptr)).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint }),
{ reveal(endpoint_pages_wf); }
}
