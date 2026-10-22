use vstd::prelude::*;
use crate::*;

verus! {
    // Proof dependencies (confirmed):
    // thread_free_quota_pending_empty_unless_wlocked,
    // thread_temp_alloc_empty_unless_wlocked,
    // thread_syscall_progress_only_when_wlocked,
    // thread_exited_only_when_wlocked.
    #[verifier::opaque]
    pub open spec fn thread_perms_wf(thread_map: ThreadLockedMap) -> bool {
        &&& thread_map.perms_wf()
        &&& threads_inv(thread_map)
        &&& thread_free_quota_pending_empty_unless_wlocked(thread_map)
        &&& thread_temp_alloc_empty_unless_wlocked(thread_map)
        &&& thread_killed_only_when_wlocked(thread_map)
        &&& thread_syscall_progress_only_when_wlocked(thread_map)
        &&& thread_exited_only_when_wlocked(thread_map)
        &&& thread_ipc_transit_wf(thread_map)
    }

    pub proof fn thread_perms_wf_map(thread_map: ThreadLockedMap)
        requires thread_perms_wf(thread_map)
        ensures thread_map.perms_wf()
    { reveal(thread_perms_wf); }
    pub open spec fn threads_inv(thread_map: ThreadLockedMap) -> bool {
        &&& forall|thread_p:RwLockThreadPtr| #![trigger thread_map.dom().contains(thread_p)] thread_map.dom().contains(thread_p) ==> thread_map.spec_index(thread_p).inv()
    }

    pub proof fn thread_perms_wf_at(thread_map: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
        requires
            thread_perms_wf(thread_map),
            thread_map.dom().contains(thread_ptr),
        ensures
            thread_map.view().spec_index(thread_ptr).is_init(),
            thread_map.view().spec_index(thread_ptr).addr() == thread_ptr,
            thread_map.spec_index(thread_ptr).inv(),
            thread_map.spec_index(thread_ptr).is_init(),
            thread_map.spec_index(thread_ptr).view().inv(),
    { reveal(thread_perms_wf); }

    /// A killed thread is write-held.
    pub open spec fn thread_killed_only_when_wlocked(thread_map: ThreadLockedMap) -> bool {
        forall|thread_ptr: RwLockThreadPtr|
            #![trigger thread_map.spec_index(thread_ptr).view().state]
            thread_map.dom().contains(thread_ptr) && thread_map.spec_index(thread_ptr).view().state is KILLED ==> thread_map.spec_index(thread_ptr).locking_thread() is Write
    }

    /// A thread in IPC transit is write-held and unmarked, and its partner is a running thread whose rendezvous names it as its peer.
    #[verifier::opaque]
    pub open spec fn thread_ipc_transit_wf(thread_map: ThreadLockedMap) -> bool {
        forall|thread_ptr: RwLockThreadPtr|
            #![trigger thread_map.spec_index(thread_ptr).view().state]
            thread_map.dom().contains(thread_ptr) && thread_map.spec_index(thread_ptr).view().state is IPC_TRANSIT ==> {
                let partner_ptr = thread_map.spec_index(thread_ptr).view().state->IPC_TRANSIT_partner;
                &&& thread_map.spec_index(thread_ptr).locking_thread() is Write
                &&& !thread_map.spec_index(thread_ptr).being_killed()
                &&& thread_map.dom().contains(partner_ptr)
                &&& thread_map.spec_index(partner_ptr).view().state is RUNNING
                &&& progress_peer_of(thread_map.spec_index(partner_ptr).view().syscall_progress.view()) == Some(thread_ptr)
            }
    }

    /// Thread `thread_ptr` in IPC transit is write-held and unmarked, and its running partner's rendezvous names it as its peer.
    pub proof fn thread_ipc_transit_wf_at(thread_map: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
        requires
            thread_perms_wf(thread_map),
            thread_map.dom().contains(thread_ptr),
        ensures
            thread_map.spec_index(thread_ptr).view().state is IPC_TRANSIT ==> {
                let partner_ptr = thread_map.spec_index(thread_ptr).view().state->IPC_TRANSIT_partner;
                &&& thread_map.spec_index(thread_ptr).locking_thread() is Write
                &&& !thread_map.spec_index(thread_ptr).being_killed()
                &&& thread_map.dom().contains(partner_ptr)
                &&& thread_map.spec_index(partner_ptr).view().state is RUNNING
                &&& progress_peer_of(thread_map.spec_index(partner_ptr).view().syscall_progress.view()) == Some(thread_ptr)
            },
    { reveal(thread_perms_wf); reveal(thread_ipc_transit_wf); }

    #[verifier::opaque]
    pub open spec fn thread_syscall_progress_only_when_wlocked(thread_map: ThreadLockedMap) -> bool {
        forall|thread_ptr: RwLockThreadPtr|
            #![trigger thread_map.spec_index(thread_ptr).view().syscall_progress]
            thread_map.dom().contains(thread_ptr) && thread_map.spec_index(thread_ptr).view().syscall_progress.view() is Some ==> thread_map.spec_index(thread_ptr).locking_thread() is Write
    }

    /// An exited thread stays write-held by its exiting syscall until it is destroyed.
    #[verifier::opaque]
    pub open spec fn thread_exited_only_when_wlocked(thread_map: ThreadLockedMap) -> bool {
        forall|thread_ptr: RwLockThreadPtr|
            #![trigger thread_map.spec_index(thread_ptr).view_ghost()]
            thread_map.dom().contains(thread_ptr) && thread_map.spec_index(thread_ptr).view_ghost().exited ==> thread_map.spec_index(thread_ptr).locking_thread() is Write
    }

    /// Exited thread `thread_ptr` is write-held.
    pub proof fn thread_exited_only_when_wlocked_at(thread_map: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
        requires
            thread_perms_wf(thread_map),
            thread_map.dom().contains(thread_ptr),
        ensures thread_map.spec_index(thread_ptr).view_ghost().exited ==> thread_map.spec_index(thread_ptr).locking_thread() is Write,
    { reveal(thread_perms_wf); reveal(thread_exited_only_when_wlocked); }

    /// Killed thread `thread_ptr` is write-held.
    pub proof fn thread_killed_only_when_wlocked_at(thread_map: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
        requires
            thread_perms_wf(thread_map),
            thread_map.dom().contains(thread_ptr),
        ensures thread_map.spec_index(thread_ptr).view().state is KILLED ==> thread_map.spec_index(thread_ptr).locking_thread() is Write,
    { reveal(thread_perms_wf); }
}
