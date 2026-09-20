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

    pub proof fn page_array_wf_at(page_array: PageLockedArray, page_index: PageIndex)
        requires
            page_array_wf(page_array),
            index_valid(NUM_PAGES, page_index),
        ensures
            page_array.inv(),
            page_array.spec_index(page_index).view().inv(),
            page_array.spec_index(page_index).view().is_init(),
            page_array.spec_index(page_index).view().view().inv(),
            page_array.spec_index(page_index).view().view().addr == page_index2page_ptr(page_index),
    {
        reveal(page_array_wf);
    }
}
