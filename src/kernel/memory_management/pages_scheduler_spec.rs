use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
pub open spec fn scheduler_pages_wf(scheduler_map: SchedulerUnLockedMap, page_array: PageLockedArray) -> bool {
    // Page -> scheduler.
    &&& forall|page_index: PageIndex|
        #![trigger page_array.spec_index(page_index).view().view().state]
        #![trigger scheduler_map.dom().contains(page_index2page_ptr(page_index))]
        index_valid(NUM_PAGES, page_index) && (page_array.spec_index(page_index).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsScheduler })
            ==> scheduler_map.dom().contains(page_index2page_ptr(page_index))
    // Scheduler -> page.
    &&& forall|scheduler_ptr: RwLockSchedulerPtr| #![trigger scheduler_map.dom().contains(scheduler_ptr)] #![trigger page_array.spec_index(page_ptr2page_index(scheduler_ptr)).view().view().state]
        scheduler_map.dom().contains(scheduler_ptr)
            ==> page_ptr_valid(scheduler_ptr) && (page_array.spec_index(page_ptr2page_index(scheduler_ptr)).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsScheduler })
}

pub proof fn scheduler_pages_wf_at(scheduler_map: SchedulerUnLockedMap, page_array: PageLockedArray, scheduler_ptr: RwLockSchedulerPtr)
    requires scheduler_pages_wf(scheduler_map, page_array)
    ensures
        scheduler_map.dom().contains(scheduler_ptr)
            ==> page_ptr_valid(scheduler_ptr) && (page_array.spec_index(page_ptr2page_index(scheduler_ptr)).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::AsScheduler }),
{ reveal(scheduler_pages_wf); }
}
