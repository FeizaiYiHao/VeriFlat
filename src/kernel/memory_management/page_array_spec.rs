use vstd::prelude::*;
use crate::*;
verus! {
/// Every page slot satisfies inv() and holds the page at its own index's address.
#[verifier::opaque]
pub open spec fn page_array_wf(pg_arr: PageLockedArray) -> bool {
    &&& pg_arr.inv()
    &&& forall|p_i: PageIndex|
        #![trigger index_valid(NUM_PAGES, p_i)]
        #![trigger pg_arr.spec_index(p_i).view().inv()]
        index_valid(NUM_PAGES, p_i)
            ==>
            pg_arr.spec_index(p_i).view().inv()
            && pg_arr.spec_index(p_i).view().view().addr == page_index2page_ptr(p_i)
}

pub proof fn page_array_wf_at(pg_arr: PageLockedArray, pg_idx: PageIndex)
    requires
        page_array_wf(pg_arr),
        index_valid(NUM_PAGES, pg_idx),
    ensures
        pg_arr.spec_index(pg_idx).view().inv(),
        pg_arr.spec_index(pg_idx).view().is_init(),
        pg_arr.spec_index(pg_idx).view().view().inv(),
        pg_arr.spec_index(pg_idx).view().view().addr == page_index2page_ptr(pg_idx),
{ reveal(page_array_wf); }

pub proof fn page_array_wf_map(pg_arr: PageLockedArray)
    requires page_array_wf(pg_arr)
    ensures pg_arr.inv()
{ reveal(page_array_wf); }
}
