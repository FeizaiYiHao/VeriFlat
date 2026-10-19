use vstd::prelude::*;
use crate::*;

verus! {
/// A process outside its holder's critical section is running or a zombie, and only a marked process is being killed.
#[verifier::opaque]
pub open spec fn process_state_lock_wf(process_map: ProcessLockedMap) -> bool {
    forall|p_ptr: RwLockProcessPtr|
        #![trigger process_map.spec_index(p_ptr)]
        process_map.dom().contains(p_ptr) ==> {
            &&& !process_map.spec_index(p_ptr).wlocked() ==> process_map.spec_index(p_ptr).view().state.view() is Running || process_map.spec_index(p_ptr).view().state.view() is Zombie
            &&& process_map.spec_index(p_ptr).view().state.view() is Killing ==> process_map.spec_index(p_ptr).being_killed()
        }
}

pub proof fn process_state_lock_wf_at(process_map: ProcessLockedMap, p_ptr: RwLockProcessPtr)
    requires
        process_state_lock_wf(process_map),
    ensures
        process_map.dom().contains(p_ptr) && !process_map.spec_index(p_ptr).wlocked() ==> process_map.spec_index(p_ptr).view().state.view() is Running || process_map.spec_index(p_ptr).view().state.view() is Zombie,
        process_map.dom().contains(p_ptr) && process_map.spec_index(p_ptr).view().state.view() is Killing ==> process_map.spec_index(p_ptr).being_killed(),
{ reveal(process_state_lock_wf); }

/// Every thread left in a process whose tables were emptied is the exiting thread, marked exited after its tables were released.
// Proof dependencies (confirmed): process_thread_wf.
#[verifier::opaque]
pub open spec fn process_emptied_threads_wf(process_map: ProcessLockedMap, thread_map: ThreadLockedMap) -> bool {
    forall|p_ptr: RwLockProcessPtr, t_ptr: RwLockThreadPtr|
        #![trigger process_map.spec_index(p_ptr).view().owned_threads.view().contains(t_ptr)]
        process_map.dom().contains(p_ptr) && process_map.spec_index(p_ptr).view().state.view() is TablesEmptied && process_map.spec_index(p_ptr).view().owned_threads.view().contains(t_ptr)
            ==> thread_map.dom().contains(t_ptr) && thread_map.spec_index(t_ptr).view_ghost().exited
}

pub proof fn process_emptied_threads_wf_at(process_map: ProcessLockedMap, thread_map: ThreadLockedMap, p_ptr: RwLockProcessPtr, t_ptr: RwLockThreadPtr)
    requires
        process_emptied_threads_wf(process_map, thread_map),
    ensures
        process_map.dom().contains(p_ptr) && process_map.spec_index(p_ptr).view().state.view() is TablesEmptied && process_map.spec_index(p_ptr).view().owned_threads.view().contains(t_ptr)
            ==> thread_map.dom().contains(t_ptr) && thread_map.spec_index(t_ptr).view_ghost().exited,
{ reveal(process_emptied_threads_wf); }
}
