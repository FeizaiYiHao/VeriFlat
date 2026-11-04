use vstd::prelude::*;
use crate::*;

verus! {
/// A process outside its holder's critical section is running or a zombie, and a process in state Killing is marked.
#[verifier::opaque]
pub open spec fn process_state_lock_wf(prc_mp: ProcessLockedMap) -> bool {
    forall|p: RwLockProcessPtr|
        #![trigger prc_mp.spec_index(p)]
        prc_mp.dom().contains(p) ==> {
            let state = prc_mp.spec_index(p).view().state.view();
            &&& !prc_mp.spec_index(p).wlocked() ==> state is Running || state is Zombie
            &&& state is Killing ==> prc_mp.spec_index(p).being_killed()
        }
}

pub proof fn process_state_lock_wf_at(prc_mp: ProcessLockedMap, prc_ptr: RwLockProcessPtr)
    requires
        process_state_lock_wf(prc_mp),
    ensures
        prc_mp.dom().contains(prc_ptr) && !prc_mp.spec_index(prc_ptr).wlocked()
            ==> prc_mp.spec_index(prc_ptr).view().state.view() is Running || prc_mp.spec_index(prc_ptr).view().state.view() is Zombie,
        prc_mp.dom().contains(prc_ptr) && prc_mp.spec_index(prc_ptr).view().state.view() is Killing ==> prc_mp.spec_index(prc_ptr).being_killed(),
{ reveal(process_state_lock_wf); }

/// Every thread still owned by a TablesEmptied process is in the thread map and exited.
// Proof dependencies (confirmed): process_thread_wf.
#[verifier::opaque]
pub open spec fn process_emptied_threads_wf(prc_mp: ProcessLockedMap, thrd_mp: ThreadLockedMap) -> bool {
    forall|p: RwLockProcessPtr, t: RwLockThreadPtr|
        #![trigger prc_mp.spec_index(p).view().owned_threads.view().contains(t)]
        prc_mp.dom().contains(p)
            && prc_mp.spec_index(p).view().state.view() is TablesEmptied
            && prc_mp.spec_index(p).view().owned_threads.view().contains(t)
            ==>
            thrd_mp.dom().contains(t)
            && thrd_mp.spec_index(t).view_ghost().exited
}

pub proof fn process_emptied_threads_wf_at(prc_mp: ProcessLockedMap, thrd_mp: ThreadLockedMap, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr)
    requires
        process_emptied_threads_wf(prc_mp, thrd_mp),
    ensures
        prc_mp.dom().contains(prc_ptr) && prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied && prc_mp.spec_index(prc_ptr).view().owned_threads.view().contains(thrd_ptr)
            ==> thrd_mp.dom().contains(thrd_ptr) && thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
{ reveal(process_emptied_threads_wf); }
}
