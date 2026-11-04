use vstd::prelude::*;
use crate::*;

verus! {
/// Schedulers and AsScheduler pages agree in both directions.
#[verifier::opaque]
pub open spec fn scheduler_pages_wf(sched_mp: SchedulerUnLockedMap, pg_arr: PageLockedArray) -> bool {
    // Page -> scheduler.
    &&& forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i).view().view().state]
        #![trigger sched_mp.dom().contains(page_index2page_ptr(p_i))]
        index_valid(NUM_PAGES, p_i)
            && (pg_arr.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsScheduler })
            ==>
            sched_mp.dom().contains(page_index2page_ptr(p_i))
    // Scheduler -> page.
    &&& forall|s: RwLockSchedulerPtr|
        #![trigger sched_mp.dom().contains(s)]
        #![trigger pg_arr.spec_index(page_ptr2page_index(s)).view().view().state]
        sched_mp.dom().contains(s)
            ==>
            page_ptr_valid(s)
            && (pg_arr.spec_index(page_ptr2page_index(s)).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsScheduler })
}

pub proof fn scheduler_pages_wf_at(sched_mp: SchedulerUnLockedMap, pg_arr: PageLockedArray, sched_ptr: RwLockSchedulerPtr)
    requires scheduler_pages_wf(sched_mp, pg_arr)
    ensures
        sched_mp.dom().contains(sched_ptr)
            ==> page_ptr_valid(sched_ptr) && (pg_arr.spec_index(page_ptr2page_index(sched_ptr)).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsScheduler }),
{ reveal(scheduler_pages_wf); }
}
