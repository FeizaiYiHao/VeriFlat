use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn thread_perms_wf(thread_map: ThreadLockedMap) -> bool{
        &&&
        thread_map.perms_wf()
        &&&
        threads_inv(thread_map)
        &&&
        thread_free_quota_pending_empty_unless_wlocked(thread_map)
        &&&
        thread_temp_alloc_empty_unless_wlocked(thread_map)
    }
    pub open spec fn threads_inv(thread_map: ThreadLockedMap) -> bool{
        &&&
        forall|thread_p:RwLockThreadPtr|
            #![auto]
            thread_map.dom().contains(thread_p)
            ==>
            thread_map.spec_index(thread_p).inv()
    }
}
