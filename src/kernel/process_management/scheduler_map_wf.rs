use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn scheduler_perms_wf(scheduler_map: LockedMap<RwLockSchedulerPtr, Scheduler, (), (), (), SCHEDULER_HAS_KILL_STATE>) -> bool{
        &&&
        scheduler_map.perms_wf()
        &&&
        schedulers_inv(scheduler_map)
    }
    pub open spec fn schedulers_inv(scheduler_map: LockedMap<RwLockSchedulerPtr, Scheduler, (), (), (), SCHEDULER_HAS_KILL_STATE>) -> bool{
        &&&
        forall|scheduler_p:RwLockSchedulerPtr|
            #![auto]
            scheduler_map.dom().contains(scheduler_p)
            ==>
            scheduler_map[scheduler_p].inv()
    }
}
