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

    pub proof fn scheduler_perms_wf_at(
        scheduler_map: SchedulerLockedMap,
        scheduler_ptr: RwLockSchedulerPtr,
    )
        requires
            scheduler_perms_wf(scheduler_map),
            scheduler_map.dom().contains(scheduler_ptr),
        ensures
            scheduler_map.perms_wf(),
            scheduler_map.view().spec_index(scheduler_ptr).is_init(),
            scheduler_map.view().spec_index(scheduler_ptr).addr()
                == scheduler_ptr,
            scheduler_map.spec_index(scheduler_ptr).inv(),
            scheduler_map.spec_index(scheduler_ptr).is_init(),
            scheduler_map.spec_index(scheduler_ptr).view().inv(),
    {
        reveal(scheduler_perms_wf);
    }
}
