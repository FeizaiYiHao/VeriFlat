use core::slice;

use vstd::prelude::*;
use crate::*;

verus! {
    pub proof fn hugepage_2m_wf_proof()
        ensures 
            forall|pa:PageArray|
                hugepage_2m_wf(pa) <==> hugepage_2m_wf_inner(pa)
    {}

    pub closed spec fn hugepage_2m_wf(page_array: PageArray) -> bool {
        &&&
        hugepage_2m_wf_inner(page_array)
    }

    pub open spec fn hugepage_2m_wf_inner(page_array: PageArray) -> bool {
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
            page_index_2m_valid(p_i) || page_array.spec_index(p_i).view().wlocked()
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
            write_locked_by_same_thread(page_array.spec_index(p_i).view(), page_array.spec_index(p_j).view())
            ||
            {
                &&&
                page_array.spec_index(p_j).view().view().state is Merged2m
            }
        &&&
        forall|p_i:PageIndex|
            #![trigger page_array.spec_index(p_i).view().view().state]
            page_index_wf(p_i) && (page_array.spec_index(p_i).view().view().state is Merged2m)
            ==>
            write_locked_by_same_thread(page_array.spec_index(p_i).view(), page_array.spec_index(spec_page_index_truncate_2m(p_i)).view())
            ||
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
            forall|pa:PageArray|
                hugepage_1g_wf(pa) <==> hugepage_1g_wf_inner(pa)
    {}

    pub closed spec fn hugepage_1g_wf(page_array: PageArray) -> bool {
        &&&
        hugepage_1g_wf_inner(page_array)
    }


    pub open spec fn hugepage_1g_wf_inner(page_array: PageArray) -> bool {
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
            page_index_1g_valid(p_i) || page_array.spec_index(p_i).view().wlocked()
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
            write_locked_by_same_thread(page_array.spec_index(p_i).view(), page_array.spec_index(p_j).view())
            ||
            {
                &&&
                page_array.spec_index(p_j).view().view().state is Merged1g
            }
        &&&
        forall|p_i:PageIndex|
            #![trigger page_array.spec_index(p_i).view().view().state]
            page_index_wf(p_i) && (page_array.spec_index(p_i).view().view().state is Merged1g)
            ==>
            write_locked_by_same_thread(page_array.spec_index(p_i).view(), page_array.spec_index(spec_page_index_truncate_1g(p_i)).view())
            ||
            {
                |||
                page_array.spec_index(spec_page_index_truncate_1g(p_i)).view().view().state is Free1g 
                ||| 
                page_array.spec_index(spec_page_index_truncate_1g(p_i)).view().view().state is Mapped1g 
            }
    }
}