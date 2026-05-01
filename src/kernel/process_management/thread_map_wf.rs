use vstd::prelude::*;
use crate::*;

verus! {
    impl Kernel{
        pub open spec fn thread_perms_wf(&self) -> bool{
            &&&
            self.thread_map.perms_wf()
            &&&
            self.threads_inv()
        }
        pub open spec fn threads_inv(&self) -> bool{
        &&&
        forall|thread_p:RwLockThreadPtr|
            #![auto]
            self.thread_map.dom().contains(thread_p)
            ==>
            self.thread_map[thread_p].inv()
    }
    }
}