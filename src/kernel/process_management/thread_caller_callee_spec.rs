use vstd::prelude::*;
use crate::*;

verus! {
/// Every active synchronous call is represented twice: the waiting caller
/// points to its callee, and the callee points back to that caller.  Call and
/// reply are restricted to one container so reply can perform a direct CPU
/// handoff without crossing scheduler ownership domains.
#[verifier::opaque]
pub open spec fn thread_caller_callee_wf(thrd_mp: ThreadLockedMap) -> bool {
    // Caller -> callee.
    &&& forall|caller_ptr: RwLockThreadPtr|
        #![trigger thrd_mp.spec_index(caller_ptr).view().callee]
        thrd_mp.dom().contains(caller_ptr) && thrd_mp.spec_index(caller_ptr).view().callee is Some ==> {
            let callee_ptr = thrd_mp.spec_index(caller_ptr).view().callee.unwrap();
            &&& thrd_mp.dom().contains(callee_ptr)
            &&& caller_ptr != callee_ptr
            &&& thrd_mp.spec_index(caller_ptr).view().state.is_reply_waiting()
            &&& thrd_mp.spec_index(callee_ptr).view().caller == Some(caller_ptr)
            &&& thrd_mp.spec_index(caller_ptr).view().owning_container == thrd_mp.spec_index(callee_ptr).view().owning_container
        }
    // Callee -> caller.
    &&& forall|callee_ptr: RwLockThreadPtr|
        #![trigger thrd_mp.spec_index(callee_ptr).view().caller]
        thrd_mp.dom().contains(callee_ptr) && thrd_mp.spec_index(callee_ptr).view().caller is Some ==> {
            let caller_ptr = thrd_mp.spec_index(callee_ptr).view().caller.unwrap();
            &&& thrd_mp.dom().contains(caller_ptr)
            &&& caller_ptr != callee_ptr
            &&& thrd_mp.spec_index(caller_ptr).view().state.is_reply_waiting()
            &&& thrd_mp.spec_index(caller_ptr).view().callee == Some(callee_ptr)
            &&& thrd_mp.spec_index(caller_ptr).view().owning_container == thrd_mp.spec_index(callee_ptr).view().owning_container
            &&& thrd_mp.spec_index(callee_ptr).view().call_depth.view() == thrd_mp.spec_index(caller_ptr).view().call_depth.view() + 1
        }
}

pub proof fn thread_caller_callee_wf_at(thrd_mp: ThreadLockedMap, thrd_ptr: RwLockThreadPtr)
    requires
        thread_caller_callee_wf(thrd_mp),
    ensures
        thrd_mp.dom().contains(thrd_ptr) && thrd_mp.spec_index(thrd_ptr).view().callee is Some ==> ({
            let callee_ptr = thrd_mp.spec_index(thrd_ptr).view().callee.unwrap();
            &&& thrd_mp.dom().contains(callee_ptr)
            &&& thrd_ptr != callee_ptr
            &&& thrd_mp.spec_index(thrd_ptr).view().state.is_reply_waiting()
            &&& thrd_mp.spec_index(callee_ptr).view().caller == Some(thrd_ptr)
            &&& thrd_mp.spec_index(thrd_ptr).view().owning_container == thrd_mp.spec_index(callee_ptr).view().owning_container
        }),
        thrd_mp.dom().contains(thrd_ptr) && thrd_mp.spec_index(thrd_ptr).view().caller is Some ==> ({
            let caller_ptr = thrd_mp.spec_index(thrd_ptr).view().caller.unwrap();
            &&& thrd_mp.dom().contains(caller_ptr)
            &&& caller_ptr != thrd_ptr
            &&& thrd_mp.spec_index(caller_ptr).view().state.is_reply_waiting()
            &&& thrd_mp.spec_index(caller_ptr).view().callee == Some(thrd_ptr)
            &&& thrd_mp.spec_index(caller_ptr).view().owning_container == thrd_mp.spec_index(thrd_ptr).view().owning_container
            &&& thrd_mp.spec_index(thrd_ptr).view().call_depth.view() == thrd_mp.spec_index(caller_ptr).view().call_depth.view() + 1
        }),
{ reveal(thread_caller_callee_wf); }
} // verus!
