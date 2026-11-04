use vstd::prelude::*;
use crate::*;

verus! {
/// The thread map's permissions are well formed, every thread satisfies its own invariant, and the per-thread state that
/// only a holder may set (pending free quota, temporary allocations, KILLED, syscall progress, exited, IPC transit) is
/// present only on write-held threads.
#[verifier::opaque]
pub open spec fn thread_perms_wf(thrd_mp: ThreadLockedMap) -> bool {
    &&& thrd_mp.perms_wf()
    &&& forall|t: RwLockThreadPtr|
        #![trigger thrd_mp.dom().contains(t)]
        thrd_mp.dom().contains(t) ==> thrd_mp.spec_index(t).inv()
    &&& thread_free_quota_pending_empty_unless_wlocked(thrd_mp)
    &&& thread_temp_alloc_empty_unless_wlocked(thrd_mp)
    &&& thread_killed_only_when_wlocked(thrd_mp)
    &&& thread_syscall_progress_only_when_wlocked(thrd_mp)
    &&& thread_exited_only_when_wlocked(thrd_mp)
    &&& thread_ipc_transit_wf(thrd_mp)
}

pub proof fn thread_perms_wf_map(thrd_mp: ThreadLockedMap)
    requires thread_perms_wf(thrd_mp)
    ensures thrd_mp.perms_wf()
{ reveal(thread_perms_wf); }

pub proof fn thread_perms_wf_at(thrd_mp: ThreadLockedMap, thrd_ptr: RwLockThreadPtr)
    requires
        thread_perms_wf(thrd_mp),
        thrd_mp.dom().contains(thrd_ptr),
    ensures
        thrd_mp.view().spec_index(thrd_ptr).is_init(),
        thrd_mp.view().spec_index(thrd_ptr).addr() == thrd_ptr,
        thrd_mp.spec_index(thrd_ptr).inv(),
        thrd_mp.spec_index(thrd_ptr).is_init(),
        thrd_mp.spec_index(thrd_ptr).view().inv(),
{ reveal(thread_perms_wf); }

/// A killed thread is write-held.
pub open spec fn thread_killed_only_when_wlocked(thrd_mp: ThreadLockedMap) -> bool {
    forall|t: RwLockThreadPtr|
        #![trigger thrd_mp.spec_index(t).view().state]
        thrd_mp.dom().contains(t) && thrd_mp.spec_index(t).view().state is KILLED
            ==> thrd_mp.spec_index(t).locking_thread() is Write
}

/// A thread in IPC transit is write-held and unmarked, and its partner is a running thread whose rendezvous names it as its peer.
#[verifier::opaque]
pub open spec fn thread_ipc_transit_wf(thrd_mp: ThreadLockedMap) -> bool {
    forall|t: RwLockThreadPtr|
        #![trigger thrd_mp.spec_index(t).view().state]
        thrd_mp.dom().contains(t) && thrd_mp.spec_index(t).view().state is IPC_TRANSIT ==> {
            let partner_ptr = thrd_mp.spec_index(t).view().state->IPC_TRANSIT_partner;
            &&& thrd_mp.spec_index(t).locking_thread() is Write
            &&& !thrd_mp.spec_index(t).being_killed()
            &&& thrd_mp.dom().contains(partner_ptr)
            &&& thrd_mp.spec_index(partner_ptr).view().state is RUNNING
            &&& progress_peer_of(thrd_mp.spec_index(partner_ptr).view().syscall_progress.view()) == Some(t)
        }
}

/// Thread `thrd_ptr` in IPC transit is write-held and unmarked, and its running partner's rendezvous names it as its peer.
pub proof fn thread_ipc_transit_wf_at(thrd_mp: ThreadLockedMap, thrd_ptr: RwLockThreadPtr)
    requires
        thread_perms_wf(thrd_mp),
        thrd_mp.dom().contains(thrd_ptr),
    ensures
        thrd_mp.spec_index(thrd_ptr).view().state is IPC_TRANSIT ==> {
            let partner_ptr = thrd_mp.spec_index(thrd_ptr).view().state->IPC_TRANSIT_partner;
            &&& thrd_mp.spec_index(thrd_ptr).locking_thread() is Write
            &&& !thrd_mp.spec_index(thrd_ptr).being_killed()
            &&& thrd_mp.dom().contains(partner_ptr)
            &&& thrd_mp.spec_index(partner_ptr).view().state is RUNNING
            &&& progress_peer_of(thrd_mp.spec_index(partner_ptr).view().syscall_progress.view()) == Some(thrd_ptr)
        },
{ reveal(thread_perms_wf); reveal(thread_ipc_transit_wf); }

/// A thread inside a syscall is write-held.
#[verifier::opaque]
pub open spec fn thread_syscall_progress_only_when_wlocked(thrd_mp: ThreadLockedMap) -> bool {
    forall|t: RwLockThreadPtr|
        #![trigger thrd_mp.spec_index(t).view().syscall_progress]
        thrd_mp.dom().contains(t) && thrd_mp.spec_index(t).view().syscall_progress.view() is Some
            ==> thrd_mp.spec_index(t).locking_thread() is Write
}

/// An exited thread stays write-held by its exiting syscall until it is destroyed.
#[verifier::opaque]
pub open spec fn thread_exited_only_when_wlocked(thrd_mp: ThreadLockedMap) -> bool {
    forall|t: RwLockThreadPtr|
        #![trigger thrd_mp.spec_index(t).view_ghost()]
        thrd_mp.dom().contains(t) && thrd_mp.spec_index(t).view_ghost().exited
            ==> thrd_mp.spec_index(t).locking_thread() is Write
}

/// Exited thread `thrd_ptr` is write-held.
pub proof fn thread_exited_only_when_wlocked_at(thrd_mp: ThreadLockedMap, thrd_ptr: RwLockThreadPtr)
    requires
        thread_perms_wf(thrd_mp),
        thrd_mp.dom().contains(thrd_ptr),
    ensures thrd_mp.spec_index(thrd_ptr).view_ghost().exited ==> thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
{ reveal(thread_perms_wf); reveal(thread_exited_only_when_wlocked); }

/// Killed thread `thrd_ptr` is write-held.
pub proof fn thread_killed_only_when_wlocked_at(thrd_mp: ThreadLockedMap, thrd_ptr: RwLockThreadPtr)
    requires
        thread_perms_wf(thrd_mp),
        thrd_mp.dom().contains(thrd_ptr),
    ensures thrd_mp.spec_index(thrd_ptr).view().state is KILLED ==> thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
{ reveal(thread_perms_wf); }
}
