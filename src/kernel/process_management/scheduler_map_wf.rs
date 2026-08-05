use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn scheduler_perms_wf(scheduler_map: SchedulerLockedMap) -> bool{
        &&&
        scheduler_map.perms_wf()
        &&&
        schedulers_inv(scheduler_map)
    }
    pub open spec fn schedulers_inv(scheduler_map: SchedulerLockedMap) -> bool{
        &&&
        forall|scheduler_p:RwLockSchedulerPtr|
            #![auto]
            scheduler_map.dom().contains(scheduler_p)
            ==>
            scheduler_map.spec_index(scheduler_p).inv()
    }
}
