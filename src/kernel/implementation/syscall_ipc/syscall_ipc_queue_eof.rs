use vstd::prelude::*;
use crate::*;

verus! {
/// Closes `thread_perms_wf` after `ipc_block_thread_on_endpoint`: only the write-held thread entry changed, and with no recorded
/// progress it is no transit thread's partner.
pub(super) proof fn ipc_block_thread_on_endpoint_eof(pre: ThreadLockedMap, post: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
    requires
        thread_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, thread_ptr),
        post.spec_index(thread_ptr).is_init(),
        post.spec_index(thread_ptr).view().inv(),
        post.spec_index(thread_ptr).locking_thread() is Write,
        pre.spec_index(thread_ptr).view().syscall_progress.view() is None,
        !(post.spec_index(thread_ptr).view().state is IPC_TRANSIT),
    ensures thread_perms_wf(post),
{
    reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
    reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
}

/// Closes `endpoint_perms_wf` after `ipc_enqueue_endpoint_waiter`: only the write-held endpoint entry changed.
pub(super) proof fn ipc_enqueue_endpoint_waiter_eof(pre: EndpointLockedMap, post: EndpointLockedMap, endpoint_ptr: RwLockEndpointPtr)
    requires
        endpoint_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, endpoint_ptr),
        post.spec_index(endpoint_ptr).is_init(),
        post.spec_index(endpoint_ptr).view().inv(),
        post.spec_index(endpoint_ptr).locking_thread() is Write,
    ensures endpoint_perms_wf(post),
{ reveal(endpoint_perms_wf); }

/// Closes `thread_perms_wf` after `ipc_schedule_endpoint_waiter`: only the write-held waiter entry changed, and a waiter is no transit
/// thread's partner.
pub(super) proof fn ipc_schedule_endpoint_waiter_eof(pre: ThreadLockedMap, post: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
    requires
        thread_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, thread_ptr),
        post.spec_index(thread_ptr).is_init(),
        post.spec_index(thread_ptr).view().inv(),
        post.spec_index(thread_ptr).locking_thread() is Write,
        !(pre.spec_index(thread_ptr).view().state is RUNNING),
        !(post.spec_index(thread_ptr).view().state is IPC_TRANSIT),
    ensures thread_perms_wf(post),
{
    reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
    reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
}

/// Closes `thread_perms_wf` after `ipc_move_endpoint_waiter_to_transit`: only the write-held waiter entry changed, into unmarked transit
/// with the running thread whose progress names it.
pub(super) proof fn ipc_move_endpoint_waiter_to_transit_eof(pre: ThreadLockedMap, post: ThreadLockedMap, thread_ptr: RwLockThreadPtr, current_thread_ptr: RwLockThreadPtr)
    requires
        thread_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, thread_ptr),
        post.spec_index(thread_ptr).is_init(),
        post.spec_index(thread_ptr).view().inv(),
        post.spec_index(thread_ptr).locking_thread() is Write,
        current_thread_ptr != thread_ptr,
        pre.dom().contains(current_thread_ptr),
        pre.spec_index(current_thread_ptr).view().state is RUNNING,
        progress_peer_of(pre.spec_index(current_thread_ptr).view().syscall_progress.view()) == Some(thread_ptr),
        !(pre.spec_index(thread_ptr).view().state is RUNNING),
        post.spec_index(thread_ptr).view().state is IPC_TRANSIT,
        post.spec_index(thread_ptr).view().state->IPC_TRANSIT_partner == current_thread_ptr,
        !post.spec_index(thread_ptr).being_killed(),
    ensures thread_perms_wf(post),
{
    reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
    reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
}

/// Closes `thread_perms_wf` after `ipc_schedule_transit_peer`: only the write-held transit entry changed, and a transit thread is no
/// transit thread's partner.
pub(super) proof fn ipc_schedule_transit_peer_eof(pre: ThreadLockedMap, post: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
    requires
        thread_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, thread_ptr),
        post.spec_index(thread_ptr).is_init(),
        post.spec_index(thread_ptr).view().inv(),
        post.spec_index(thread_ptr).locking_thread() is Write,
        pre.spec_index(thread_ptr).view().state is IPC_TRANSIT,
        !(post.spec_index(thread_ptr).view().state is IPC_TRANSIT),
    ensures thread_perms_wf(post),
{
    reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
    reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
}

/// Closes `endpoint_perms_wf` after `ipc_dequeue_endpoint_waiter`: only the write-held endpoint entry changed.
pub(super) proof fn ipc_dequeue_endpoint_waiter_eof(pre: EndpointLockedMap, post: EndpointLockedMap, endpoint_ptr: RwLockEndpointPtr)
    requires
        endpoint_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, endpoint_ptr),
        post.spec_index(endpoint_ptr).is_init(),
        post.spec_index(endpoint_ptr).view().inv(),
        post.spec_index(endpoint_ptr).locking_thread() is Write,
    ensures endpoint_perms_wf(post),
{ reveal(endpoint_perms_wf); }
} // verus!
