use vstd::prelude::*;
use crate::*;

verus! {
/// Page -> process: a page in state AsProcess holds a process.
pub open spec fn process_pages_forward_wf(prc_mp: ProcessLockedMap, pg_arr: PageLockedArray) -> bool {
    forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i).view().view().state]
        #![trigger prc_mp.dom().contains(page_index2page_ptr(p_i))]
        index_valid(NUM_PAGES, p_i)
            && (pg_arr.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsProcess })
            ==>
            prc_mp.dom().contains(page_index2page_ptr(p_i))
}

/// Process -> page: every process sits on a valid page in state AsProcess.
pub open spec fn process_pages_backward_wf(prc_mp: ProcessLockedMap, pg_arr: PageLockedArray) -> bool {
    forall|p: RwLockProcessPtr|
        #![trigger pg_arr.spec_index(page_ptr2page_index(p)).view().view().state]
        #![trigger prc_mp.dom().contains(p)]
        prc_mp.dom().contains(p)
            ==>
            page_ptr_valid(p)
            && (pg_arr.spec_index(page_ptr2page_index(p)).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsProcess })
}

/// Processes and AsProcess pages agree in both directions.
#[verifier::opaque]
pub open spec fn process_pages_wf(prc_mp: ProcessLockedMap, pg_arr: PageLockedArray) -> bool {
    &&& process_pages_forward_wf(prc_mp, pg_arr)
    &&& process_pages_backward_wf(prc_mp, pg_arr)
}

pub proof fn process_pages_wf_process_at(prc_mp: ProcessLockedMap, pg_arr: PageLockedArray, prc_ptr: RwLockProcessPtr)
    requires
        process_pages_wf(prc_mp, pg_arr),
        prc_mp.dom().contains(prc_ptr),
    ensures
        page_ptr_valid(prc_ptr),
        pg_arr.spec_index(page_ptr2page_index(prc_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsProcess }),
{ reveal(process_pages_wf); }
}
