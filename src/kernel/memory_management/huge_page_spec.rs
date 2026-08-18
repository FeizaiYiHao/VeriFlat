use core::slice;

use vstd::prelude::*;
use crate::*;

verus! {
    // A page slot participates in the 2m hugepage invariant iff its state is one
    // of the 2m variants (the leaf 2m states or a 2m merge tail). Used to scope
    // the `hugepage_2m_wf` framing lemma to exactly the slots that invariant reads.
    pub open spec fn page_state_2m_related(s: PageState) -> bool {
        ||| s is Free2m
        ||| s is Allocated2m
        ||| s is Mapped2m
        ||| s is Merged2m
    }

    // 1g twin of `page_state_2m_related`.
    pub open spec fn page_state_1g_related(s: PageState) -> bool {
        ||| s is Free1g
        ||| s is Mapped1g
        ||| s is Merged1g
    }

    #[verifier::opaque]
    pub open spec fn hugepage_2m_wf(page_array: PageLockedArray) -> bool {
        &&&
        forall|p_i:PageIndex|
            #![trigger page_array.spec_index(p_i).view().view().state is Free2m]
            #![trigger page_array.spec_index(p_i).view().view().state is Allocated2m]
            #![trigger page_array.spec_index(p_i).view().view().state is Mapped2m]
            #![trigger page_index_2m_valid(p_i)]
            index_valid(NUM_PAGES, p_i)
            && {
                |||
                page_array.spec_index(p_i).view().view().state is Free2m
                ||| 
                page_array.spec_index(p_i).view().view().state is Allocated2m 
                |||
                page_array.spec_index(p_i).view().view().state is Mapped2m 
            }
            ==>
            page_index_2m_valid(p_i)
        &&&
        forall|p_i:PageIndex, p_j:PageIndex|
            #![trigger spec_page_index_merge_2m_valid(p_i, p_j)]
            #![trigger page_array.spec_index(p_i).view().view().state is Free2m, page_array.spec_index(p_j).view().view().state is Merged2m]
            #![trigger page_array.spec_index(p_i).view().view().state is Allocated2m, page_array.spec_index(p_j).view().view().state is Merged2m]
            #![trigger page_array.spec_index(p_i).view().view().state is Mapped2m, page_array.spec_index(p_j).view().view().state is Merged2m]
            index_valid(NUM_PAGES, p_i)
            && index_valid(NUM_PAGES, p_j)
            && {
                |||
                page_array.spec_index(p_i).view().view().state is Free2m 
                ||| 
                page_array.spec_index(p_i).view().view().state is Allocated2m 
                |||
                page_array.spec_index(p_i).view().view().state is Mapped2m 
            }
            &&
            spec_page_index_merge_2m_valid(p_i, p_j)
            ==>
            {
                &&&
                page_array.spec_index(p_j).view().view().state is Merged2m
                &&&
                page_array.spec_index(p_j).view().view().owning_container == page_array.spec_index(p_i).view().view().owning_container
            }
        &&&
        forall|p_i:PageIndex|
            #![trigger page_array.spec_index(p_i).view().view().state is Merged2m]
            #![trigger spec_page_index_truncate_2m(p_i)]
            index_valid(NUM_PAGES, p_i) && (page_array.spec_index(p_i).view().view().state is Merged2m)
            ==>
            {
                |||
                page_array.spec_index(spec_page_index_truncate_2m(p_i)).view().view().state is Free2m 
                |||
                page_array.spec_index(spec_page_index_truncate_2m(p_i)).view().view().state is Allocated2m 
                ||| 
                page_array.spec_index(spec_page_index_truncate_2m(p_i)).view().view().state is Mapped2m 
            }
    }

    #[verifier::opaque]
    pub open spec fn hugepage_1g_wf(page_array: PageLockedArray) -> bool {
        &&&
        forall|p_i:PageIndex|
            #![trigger page_array.spec_index(p_i).view().view().state is Free1g]
            #![trigger page_array.spec_index(p_i).view().view().state is Mapped1g]
            #![trigger page_index_1g_valid(p_i)]
            index_valid(NUM_PAGES, p_i)
            && {
                page_array.spec_index(p_i).view().view().state is Free1g
                ||
                page_array.spec_index(p_i).view().view().state is Mapped1g 
            }
            ==>
            page_index_1g_valid(p_i) 
        &&&
        forall|p_i:PageIndex, p_j:PageIndex|
            #![trigger spec_page_index_merge_1g_valid(p_i, p_j)]
            #![trigger page_array.spec_index(p_i).view().view().state is Free1g, page_array.spec_index(p_j).view().view().state is Merged1g]
            #![trigger page_array.spec_index(p_i).view().view().state is Mapped1g, page_array.spec_index(p_j).view().view().state is Merged1g]
            index_valid(NUM_PAGES, p_i)
            && index_valid(NUM_PAGES, p_j)
            && {
                |||
                page_array.spec_index(p_i).view().view().state is Free1g 
                |||
                page_array.spec_index(p_i).view().view().state is Mapped1g 
            }
            &&
            spec_page_index_merge_1g_valid(p_i, p_j)
            ==>
            {
                &&&
                page_array.spec_index(p_j).view().view().state is Merged1g
                &&&
                page_array.spec_index(p_j).view().view().owning_container == page_array.spec_index(p_i).view().view().owning_container
            }
        &&&
        forall|p_i:PageIndex|
            #![trigger page_array.spec_index(p_i).view().view().state is Merged1g]
            #![trigger spec_page_index_truncate_1g(p_i)]
            index_valid(NUM_PAGES, p_i) && (page_array.spec_index(p_i).view().view().state is Merged1g)
            ==>
            {
                |||
                page_array.spec_index(spec_page_index_truncate_1g(p_i)).view().view().state is Free1g 
                ||| 
                page_array.spec_index(spec_page_index_truncate_1g(p_i)).view().view().state is Mapped1g 
            }
    }
}
