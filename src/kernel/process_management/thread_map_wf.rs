use vstd::prelude::*;
use crate::*;

verus! {
    impl KernelK{
        #[verifier::opaque]
        pub open spec fn thread_perms_wf(&self) -> bool{
            &&&
            self.thread_map.perms_wf()
            &&&
            self.threads_inv()
            &&&
            thread_free_quota_pending_empty_unless_wlocked(self.thread_map)
        }
        pub open spec fn threads_inv(&self) -> bool{
        &&&
        forall|thread_p:RwLockThreadPtr|
            #![auto]
            self.thread_map.dom().contains(thread_p)
            ==>
            self.thread_map.spec_index(thread_p).inv()
    }
    }
}
