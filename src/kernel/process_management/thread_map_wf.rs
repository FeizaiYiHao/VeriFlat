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
        &&& thread_endpoint_transit_only_when_wlocked(thread_map)
        &&& thread_syscall_progress_only_when_wlocked(thread_map)
        &&& thread_exited_only_when_wlocked(thread_map)
        &&& thread_ipc_partner_only_when_wlocked(thread_map)
        &&& thread_peer_implies_ipc_partner(thread_map)
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

    /// A thread in endpoint transit or killed is write-held.
    pub open spec fn thread_endpoint_transit_only_when_wlocked(thread_map: ThreadLockedMap) -> bool {
        forall|thread_ptr: RwLockThreadPtr|
            #![trigger thread_map.spec_index(thread_ptr).view().state]
            thread_map.dom().contains(thread_ptr) && (thread_map.spec_index(thread_ptr).view().state is IPC_ENDPOINT_TRANSIT || thread_map.spec_index(thread_ptr).view().state is KILLED) ==> thread_map.spec_index(thread_ptr).locking_thread() is Write
    }

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

    /// A thread that another thread's IPC rendezvous names as its peer is write-held, unmarked, and waiting in that
    /// rendezvous: queued as a sender or receiver, or in endpoint transit.
    #[verifier::opaque]
    pub open spec fn thread_ipc_partner_only_when_wlocked(thread_map: ThreadLockedMap) -> bool {
        forall|thread_ptr: RwLockThreadPtr|
            #![trigger thread_map.spec_index(thread_ptr).view_ghost().ipc_partner]
            thread_map.dom().contains(thread_ptr) && thread_map.spec_index(thread_ptr).view_ghost().ipc_partner is Some ==> {
                let thread = thread_map.spec_index(thread_ptr);
                &&& thread.locking_thread() is Write
                &&& !thread.being_killed()
                &&& thread.view().state is SENDING || thread.view().state is RECEIVING || thread.view().state is IPC_ENDPOINT_TRANSIT
            }
    }

    /// The peer that a thread's in-flight IPC rendezvous names is a thread that records it as its partner.
    #[verifier::opaque]
    pub open spec fn thread_peer_implies_ipc_partner(thread_map: ThreadLockedMap) -> bool {
        forall|thread_ptr: RwLockThreadPtr|
            #![trigger thread_map.spec_index(thread_ptr).view().syscall_progress]
            thread_map.dom().contains(thread_ptr) && progress_peer_of(thread_map.spec_index(thread_ptr).view().syscall_progress.view()) is Some ==> {
                let peer_ptr = progress_peer_of(thread_map.spec_index(thread_ptr).view().syscall_progress.view())->Some_0;
                &&& thread_map.dom().contains(peer_ptr)
                &&& thread_map.spec_index(peer_ptr).view_ghost().ipc_partner == Some(thread_ptr)
            }
    }

    /// Thread `thread_ptr`, when another thread's IPC rendezvous names it as its peer, is write-held, unmarked, and waiting
    /// in that rendezvous.
    pub proof fn thread_ipc_partner_only_when_wlocked_at(thread_map: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
        requires
            thread_perms_wf(thread_map),
            thread_map.dom().contains(thread_ptr),
        ensures
            thread_map.spec_index(thread_ptr).view_ghost().ipc_partner is Some ==> {
                let thread = thread_map.spec_index(thread_ptr);
                &&& thread.locking_thread() is Write
                &&& !thread.being_killed()
                &&& thread.view().state is SENDING || thread.view().state is RECEIVING || thread.view().state is IPC_ENDPOINT_TRANSIT
            },
    { reveal(thread_perms_wf); reveal(thread_ipc_partner_only_when_wlocked); }

    /// The peer that thread `thread_ptr`'s in-flight IPC rendezvous names is a thread that records `thread_ptr` as its partner.
    pub proof fn thread_peer_implies_ipc_partner_at(thread_map: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
        requires
            thread_perms_wf(thread_map),
            thread_map.dom().contains(thread_ptr),
        ensures
            progress_peer_of(thread_map.spec_index(thread_ptr).view().syscall_progress.view()) is Some ==> {
                let peer_ptr = progress_peer_of(thread_map.spec_index(thread_ptr).view().syscall_progress.view())->Some_0;
                &&& thread_map.dom().contains(peer_ptr)
                &&& thread_map.spec_index(peer_ptr).view_ghost().ipc_partner == Some(thread_ptr)
            },
    { reveal(thread_perms_wf); reveal(thread_peer_implies_ipc_partner); }

    /// Thread `thread_ptr` in endpoint transit or killed is write-held.
    pub proof fn thread_endpoint_transit_only_when_wlocked_at(thread_map: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
        requires
            thread_perms_wf(thread_map),
            thread_map.dom().contains(thread_ptr),
        ensures
            thread_map.spec_index(thread_ptr).view().state is IPC_ENDPOINT_TRANSIT || thread_map.spec_index(thread_ptr).view().state is KILLED ==> thread_map.spec_index(thread_ptr).locking_thread() is Write,
    { reveal(thread_perms_wf); }
}
