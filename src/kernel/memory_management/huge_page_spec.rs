use core::slice;

use vstd::prelude::*;
use crate::*;

verus! {
    pub proof fn hugepage_2m_wf_proof()
        ensures 
            forall|pa:LockedArray<Page, NUM_PAGES, NO_KILL_STATE>|
                hugepage_2m_wf(pa) <==> hugepage_2m_wf_inner(pa)
    {}

    pub closed spec fn hugepage_2m_wf(page_array: LockedArray<Page, NUM_PAGES, NO_KILL_STATE>) -> bool {
        &&&
        hugepage_2m_wf_inner(page_array)
    }

    pub open spec fn hugepage_2m_wf_inner(page_array: LockedArray<Page, NUM_PAGES, NO_KILL_STATE>) -> bool {
        &&&
        forall|p_i:PageIndex|
            #![trigger page_array.spec_index(p_i).view().view().state]
            page_index_wf(p_i) 
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
            #![trigger spec_page_index_merge_2m_vaild(p_i, p_j)]
            page_index_wf(p_i)
            && {
                |||
                page_array.spec_index(p_i).view().view().state is Free2m 
                ||| 
                page_array.spec_index(p_i).view().view().state is Allocated2m 
                |||
                page_array.spec_index(p_i).view().view().state is Mapped2m 
            }
            &&
            spec_page_index_merge_2m_vaild(p_i, p_j)
            ==>
            {
                &&&
                page_array.spec_index(p_j).view().view().state is Merged2m
                &&&
                page_array.spec_index(p_j).view().view().owning_container == page_array.spec_index(p_i).view().view().owning_container
            }
        &&&
        forall|p_i:PageIndex|
            #![trigger page_array.spec_index(p_i).view().view().state]
            page_index_wf(p_i) && (page_array.spec_index(p_i).view().view().state is Merged2m)
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

    pub proof fn hugepage_1g_wf_proof()
        ensures 
            forall|pa:LockedArray<Page, NUM_PAGES, NO_KILL_STATE>|
                hugepage_1g_wf(pa) <==> hugepage_1g_wf_inner(pa)
    {}

    pub closed spec fn hugepage_1g_wf(page_array: LockedArray<Page, NUM_PAGES, NO_KILL_STATE>) -> bool {
        &&&
        hugepage_1g_wf_inner(page_array)
    }


    pub open spec fn hugepage_1g_wf_inner(page_array: LockedArray<Page, NUM_PAGES, NO_KILL_STATE>) -> bool {
        &&&
        forall|p_i:PageIndex|
            #![trigger page_array.spec_index(p_i).view().view().state]
            page_index_wf(p_i) 
            && {
                page_array.spec_index(p_i).view().view().state is Free1g
                ||
                page_array.spec_index(p_i).view().view().state is Mapped1g 
            }
            ==>
            page_index_1g_valid(p_i) 
        &&&
        forall|p_i:PageIndex, p_j:PageIndex|
            #![trigger spec_page_index_merge_1g_vaild(p_i, p_j)]
            page_index_wf(p_i)
            && {
                |||
                page_array.spec_index(p_i).view().view().state is Free1g 
                |||
                page_array.spec_index(p_i).view().view().state is Mapped1g 
            }
            &&
            spec_page_index_merge_1g_vaild(p_i, p_j)
            ==>
            {
                &&&
                page_array.spec_index(p_j).view().view().state is Merged1g
                &&&
                page_array.spec_index(p_j).view().view().owning_container == page_array.spec_index(p_i).view().view().owning_container
            }
        &&&
        forall|p_i:PageIndex|
            #![trigger page_array.spec_index(p_i).view().view().state]
            page_index_wf(p_i) && (page_array.spec_index(p_i).view().view().state is Merged1g)            
            ==>
            {
                |||
                page_array.spec_index(spec_page_index_truncate_1g(p_i)).view().view().state is Free1g 
                ||| 
                page_array.spec_index(spec_page_index_truncate_1g(p_i)).view().view().state is Mapped1g 
            }
    }
}