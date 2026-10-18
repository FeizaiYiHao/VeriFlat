use vstd::prelude::*;
use crate::*;

verus! {
/// Closes `thread_perms_wf` after `ipc_block_thread_on_endpoint`: only the write-held thread entry changed.
pub(super) proof fn ipc_block_thread_on_endpoint_eof(pre: ThreadLockedMap, post: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
    requires
        thread_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, thread_ptr),
        post.spec_index(thread_ptr).is_init(),
        post.spec_index(thread_ptr).view().inv(),
        post.spec_index(thread_ptr).locking_thread() is Write,
    ensures thread_perms_wf(post),
{ reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); }

/// Closes `endpoint_perms_wf` after `ipc_enqueue_endpoint_waiter`: only the write-held endpoint entry changed.
pub(super) proof fn ipc_enqueue_endpoint_waiter_eof(pre: EndpointLockedMap, post: EndpointLockedMap, endpoint_ptr: RwLockEndpointPtr)
    requires
        endpoint_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, endpoint_ptr),
        post.spec_index(endpoint_ptr).is_init(),
        post.spec_index(endpoint_ptr).view().inv(),
    ensures endpoint_perms_wf(post),
{ reveal(endpoint_perms_wf); }

/// Closes `thread_perms_wf` after `ipc_schedule_endpoint_waiter`: only the write-held thread entry changed.
pub(super) proof fn ipc_schedule_endpoint_waiter_eof(pre: ThreadLockedMap, post: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
    requires
        thread_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, thread_ptr),
        post.spec_index(thread_ptr).is_init(),
        post.spec_index(thread_ptr).view().inv(),
        post.spec_index(thread_ptr).locking_thread() is Write,
    ensures thread_perms_wf(post),
{ reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); }

/// Closes `thread_perms_wf` after `ipc_move_endpoint_waiter_to_transit`: only the write-held thread entry changed.
pub(super) proof fn ipc_move_endpoint_waiter_to_transit_eof(pre: ThreadLockedMap, post: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
    requires
        thread_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, thread_ptr),
        post.spec_index(thread_ptr).is_init(),
        post.spec_index(thread_ptr).view().inv(),
        post.spec_index(thread_ptr).locking_thread() is Write,
    ensures thread_perms_wf(post),
{ reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); }

/// Closes `thread_perms_wf` after `ipc_schedule_endpoint_transit`: only the write-held thread entry changed.
pub(super) proof fn ipc_schedule_endpoint_transit_eof(pre: ThreadLockedMap, post: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
    requires
        thread_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, thread_ptr),
        post.spec_index(thread_ptr).is_init(),
        post.spec_index(thread_ptr).view().inv(),
        post.spec_index(thread_ptr).locking_thread() is Write,
    ensures thread_perms_wf(post),
{ reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); }

/// Closes `endpoint_perms_wf` after `ipc_dequeue_endpoint_waiter`: only the write-held endpoint entry changed.
pub(super) proof fn ipc_dequeue_endpoint_waiter_eof(pre: EndpointLockedMap, post: EndpointLockedMap, endpoint_ptr: RwLockEndpointPtr)
    requires
        endpoint_perms_wf(pre),
        post.perms_wf(),
        post.unchanged_except(&pre, endpoint_ptr),
        post.spec_index(endpoint_ptr).is_init(),
        post.spec_index(endpoint_ptr).view().inv(),
    ensures endpoint_perms_wf(post),
{ reveal(endpoint_perms_wf); }
} // verus!
