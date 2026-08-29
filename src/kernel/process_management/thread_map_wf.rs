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
        &&&
        thread_endpoint_transit_only_when_wlocked(thread_map)
    }
    pub open spec fn threads_inv(thread_map: ThreadLockedMap) -> bool{
        &&&
        forall|thread_p:RwLockThreadPtr|
            #![trigger thread_map.dom().contains(thread_p)]
            thread_map.dom().contains(thread_p)
            ==>
            thread_map.spec_index(thread_p).inv()
    }

    pub open spec fn thread_endpoint_transit_only_when_wlocked(
        thread_map: ThreadLockedMap,
    ) -> bool {
        forall|thread_ptr: RwLockThreadPtr|
            #![trigger thread_map.spec_index(thread_ptr).view().state]
            thread_map.dom().contains(thread_ptr)
                && thread_map.spec_index(thread_ptr).view().state
                    is IPC_ENDPOINT_TRANSIT
            ==> thread_map.spec_index(thread_ptr).locking_thread() is Write
    }
}
