use vstd::prelude::*;
use crate::*;
verus! {
    pub open spec fn page_array_wf(page_array: LockedArray<Page, NUM_PAGES, NO_KILL_STATE>) -> bool {
        &&&
        page_array.inv()
        &&&
        forall|p_i:PageIndex|
            #![auto]
            page_index_wf(p_i)
            ==>
            page_array[p_i]@.inv()
    }
}