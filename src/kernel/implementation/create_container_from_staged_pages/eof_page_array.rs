use vstd::prelude::*;
use crate::*;

verus! {
/// EOF closure of the page-writing loops of container creation: every entry is unchanged or keeps its address with a valid lock view.
pub proof fn create_container_from_staged_pages_eof_page_array_wf(pre: PageLockedArray, post: PageLockedArray)
    requires
        page_array_wf(pre),
        post.inv(),
        forall|index: PageIndex|
            #![trigger post.spec_index(index)]
            index_valid(NUM_PAGES, index) ==> post.spec_index(index) == pre.spec_index(index) || (post.spec_index(index).view().inv() && post.spec_index(index).view().view().addr == pre.spec_index(index).view().view().addr),
    ensures
        page_array_wf(post),
{ reveal(page_array_wf); }
}
