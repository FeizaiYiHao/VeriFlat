use vstd::prelude::*;
use crate::*;

verus! {
/// The scheduler map's permissions are well formed and every scheduler satisfies its own invariant.
#[verifier::opaque]
pub open spec fn scheduler_perms_wf(sched_mp: SchedulerUnLockedMap) -> bool {
    &&& sched_mp.perms_wf()
    &&& forall|s: RwLockSchedulerPtr|
        #![trigger sched_mp.spec_index(s)]
        sched_mp.dom().contains(s) ==> sched_mp.spec_index(s).inv()
}

pub proof fn scheduler_perms_wf_map(sched_mp: SchedulerUnLockedMap)
    requires scheduler_perms_wf(sched_mp)
    ensures sched_mp.perms_wf()
{ reveal(scheduler_perms_wf); }

pub proof fn scheduler_perms_wf_at(sched_mp: SchedulerUnLockedMap, sched_ptr: RwLockSchedulerPtr)
    requires
        scheduler_perms_wf(sched_mp),
        sched_mp.dom().contains(sched_ptr),
    ensures
        sched_mp.spec_index(sched_ptr).inv(),
{ reveal(scheduler_perms_wf); }
}
