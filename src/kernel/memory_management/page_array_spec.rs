use vstd::prelude::*;
use crate::*;
verus! {
    #[verifier::opaque]
    pub open spec fn page_array_wf(page_array: PageLockedArray) -> bool {
        &&&
        page_array.inv()
        &&&
        forall|p_i:PageIndex|
            #![trigger page_index_wf(p_i)]
            #![trigger page_array.spec_index(p_i).view().inv()]
            page_index_wf(p_i)
            ==>
            page_array.spec_index(p_i).view().inv()
            && page_array.spec_index(p_i).view().view().addr == page_index2page_ptr(p_i)
    }

    /// Addr consistency: each page's addr field matches its index.
    /// Separated from page_array_wf to avoid cascading proof obligations.
    #[verifier::opaque]
    pub open spec fn page_array_addr_wf(page_array: PageLockedArray) -> bool {
        forall|p_i:PageIndex|
            #![trigger page_array.spec_index(p_i).view().view().addr]
            page_index_wf(p_i)
            ==>
            page_array.spec_index(p_i).view().view().addr == page_index2page_ptr(p_i)
    }
}