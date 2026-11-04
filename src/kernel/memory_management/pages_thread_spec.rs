use vstd::prelude::*;
use crate::*;

verus! {
/// Threads and AsThread pages agree in both directions.
#[verifier::opaque]
pub open spec fn thread_pages_wf(thrd_mp: ThreadLockedMap, pg_arr: PageLockedArray) -> bool {
    // Page -> thread.
    &&& forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i)]
        #![trigger thrd_mp.dom().contains(page_index2page_ptr(p_i))]
        index_valid(NUM_PAGES, p_i)
            && (pg_arr.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsThread })
            ==>
            thrd_mp.dom().contains(page_index2page_ptr(p_i))
    // Thread -> page.
    &&& forall|t: RwLockThreadPtr|
        #![trigger pg_arr.spec_index(page_ptr2page_index(t))]
        #![trigger thrd_mp.dom().contains(t)]
        thrd_mp.dom().contains(t)
            ==>
            page_ptr_valid(t)
            && (pg_arr.spec_index(page_ptr2page_index(t)).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsThread })
}

/// Thread `thrd_ptr` sits on a valid page marked as a thread page.
pub proof fn thread_pages_wf_at(thrd_mp: ThreadLockedMap, pg_arr: PageLockedArray, thrd_ptr: RwLockThreadPtr)
    requires
        thread_pages_wf(thrd_mp, pg_arr),
        thrd_mp.dom().contains(thrd_ptr),
    ensures
        page_ptr_valid(thrd_ptr),
        pg_arr.spec_index(page_ptr2page_index(thrd_ptr)).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsThread },
{ reveal(thread_pages_wf); }

/// Page `pg_ptr` is a thread only if it is a valid page marked as a thread page.
pub proof fn thread_pages_wf_page_at(thrd_mp: ThreadLockedMap, pg_arr: PageLockedArray, pg_ptr: PagePtr)
    requires thread_pages_wf(thrd_mp, pg_arr),
    ensures thrd_mp.dom().contains(pg_ptr) ==> page_ptr_valid(pg_ptr) && (pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsThread }),
{ reveal(thread_pages_wf); }
}
