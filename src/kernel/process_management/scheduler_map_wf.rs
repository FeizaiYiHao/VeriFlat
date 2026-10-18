use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn scheduler_perms_wf(scheduler_map: SchedulerUnLockedMap) -> bool {
        &&& scheduler_map.perms_wf()
        &&& schedulers_inv(scheduler_map)
    }

    pub proof fn scheduler_perms_wf_map(scheduler_map: SchedulerUnLockedMap)
        requires scheduler_perms_wf(scheduler_map)
        ensures scheduler_map.perms_wf()
    { reveal(scheduler_perms_wf); }
    pub open spec fn schedulers_inv(scheduler_map: SchedulerUnLockedMap) -> bool {
        forall|scheduler_p: RwLockSchedulerPtr| #![trigger scheduler_map.spec_index(scheduler_p)] scheduler_map.dom().contains(scheduler_p) ==> scheduler_map.spec_index(scheduler_p).inv()
    }

    pub proof fn scheduler_perms_wf_at(scheduler_map: SchedulerUnLockedMap, scheduler_ptr: RwLockSchedulerPtr)
        requires
            scheduler_perms_wf(scheduler_map),
            scheduler_map.dom().contains(scheduler_ptr),
        ensures
            scheduler_map.spec_index(scheduler_ptr).inv(),
    { reveal(scheduler_perms_wf); }
}
