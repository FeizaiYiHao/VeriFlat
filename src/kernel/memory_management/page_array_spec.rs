use vstd::prelude::*;
use crate::*;
verus! {
    #[verifier::opaque]
    pub open spec fn page_array_wf(page_array: PageLockedArray) -> bool {
        &&&
        page_array.inv()
        &&&
        forall|p_i:PageIndex|
            #![trigger index_valid(NUM_PAGES, p_i)]
            #![trigger page_array.spec_index(p_i).view().inv()]
            index_valid(NUM_PAGES, p_i)
            ==>
            page_array.spec_index(p_i).view().inv()
            && page_array.spec_index(p_i).view().view().addr == page_index2page_ptr(p_i)
    }
}
