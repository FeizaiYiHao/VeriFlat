use vstd::prelude::*;
use crate::*;

verus! {
    impl Kernel{
        pub open spec fn scheduler_perms_wf(&self) -> bool{
            &&&
            self.scheduler_map.perms_wf()
            &&&
            self.schedulers_wlocked_or_inv()
        }
        pub open spec fn schedulers_wlocked_or_inv(&self) -> bool{
        &&&
        forall|scheduler_p:RwLockSchedulerPtr|
            #![auto]
            self.scheduler_map.dom().contains(scheduler_p)
            ==>
            self.scheduler_map[scheduler_p].wlocked() || self.scheduler_map[scheduler_p].inv()
    }
    }
}