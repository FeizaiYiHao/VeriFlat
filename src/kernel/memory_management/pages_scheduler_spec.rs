use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
pub open spec fn scheduler_pages_wf(scheduler_map: SchedulerUnLockedMap, page_array: PageLockedArray) -> bool {
    // Page -> scheduler.
    &&& forall|pg_idx: PageIndex|
        #![trigger page_array.spec_index(pg_idx).view().view().state]
        #![trigger scheduler_map.dom().contains(page_index2page_ptr(pg_idx))]
        index_valid(NUM_PAGES, pg_idx) && (page_array.spec_index(pg_idx).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsScheduler })
            ==> scheduler_map.dom().contains(page_index2page_ptr(pg_idx))
    // Scheduler -> page.
    &&& forall|sched_ptr: RwLockSchedulerPtr| #![trigger scheduler_map.dom().contains(sched_ptr)] #![trigger page_array.spec_index(page_ptr2page_index(sched_ptr)).view().view().state]
        scheduler_map.dom().contains(sched_ptr)
            ==> page_ptr_valid(sched_ptr) && (page_array.spec_index(page_ptr2page_index(sched_ptr)).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsScheduler })
}

pub proof fn scheduler_pages_wf_at(scheduler_map: SchedulerUnLockedMap, page_array: PageLockedArray, sched_ptr: RwLockSchedulerPtr)
    requires scheduler_pages_wf(scheduler_map, page_array)
    ensures
        scheduler_map.dom().contains(sched_ptr)
            ==> page_ptr_valid(sched_ptr) && (page_array.spec_index(page_ptr2page_index(sched_ptr)).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsScheduler }),
{ reveal(scheduler_pages_wf); }
}
