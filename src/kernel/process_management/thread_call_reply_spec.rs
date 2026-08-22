use vstd::prelude::*;
use crate::*;

verus! {

/// Every active synchronous call is represented twice: the waiting caller
/// points to its callee, and the callee points back to that caller.  Call and
/// reply are restricted to one container so reply can perform a direct CPU
/// handoff without crossing scheduler ownership domains.
#[verifier::opaque]
pub open spec fn thread_caller_callee_wf(thread_map: ThreadLockedMap) -> bool {
    &&& forall|caller_ptr: RwLockThreadPtr|
        #![trigger thread_map.spec_index(caller_ptr).view().callee]
        thread_map.dom().contains(caller_ptr)
            && thread_map.spec_index(caller_ptr).view().callee is Some
        ==> {
            let callee_ptr = thread_map.spec_index(caller_ptr).view()
                .callee.unwrap();
            &&& thread_map.dom().contains(callee_ptr)
            &&& caller_ptr != callee_ptr
            &&& thread_map.spec_index(caller_ptr).view().state
                is WAITING_REPLY
            &&& thread_map.spec_index(callee_ptr).view().caller
                == Some(caller_ptr)
            &&& thread_map.spec_index(caller_ptr).view().owning_container
                == thread_map.spec_index(callee_ptr).view().owning_container
        }
    &&& forall|callee_ptr: RwLockThreadPtr|
        #![trigger thread_map.spec_index(callee_ptr).view().caller]
        thread_map.dom().contains(callee_ptr)
            && thread_map.spec_index(callee_ptr).view().caller is Some
        ==> {
            let caller_ptr = thread_map.spec_index(callee_ptr).view()
                .caller.unwrap();
            &&& thread_map.dom().contains(caller_ptr)
            &&& caller_ptr != callee_ptr
            &&& thread_map.spec_index(caller_ptr).view().state
                is WAITING_REPLY
            &&& thread_map.spec_index(caller_ptr).view().callee
                == Some(callee_ptr)
            &&& thread_map.spec_index(caller_ptr).view().owning_container
                == thread_map.spec_index(callee_ptr).view().owning_container
        }
}

} // verus!
