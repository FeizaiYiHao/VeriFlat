use vstd::prelude::*;
use crate::*;

verus! {
    impl Kernel{
        pub open spec fn process_perms_wf(&self) -> bool{
            &&&
            self.process_map.perms_wf()
            &&&
            self.processs_wlocked_or_inv()
        }
        pub open spec fn processs_wlocked_or_inv(&self) -> bool{
        &&&
        forall|process_p:RwLockProcessPtr|
            #![auto]
            self.process_map.dom().contains(process_p)
            ==>
            self.process_map[process_p].wlocked() || self.process_map[process_p].inv()
    }
    }
}