use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;
verus! {

pub(super) fn ipc_block_thread_on_endpoint(
    thread_map: &mut ThreadLockedMap,
    Tracked(lctx): Tracked<&LocalContext>,
    thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx,
    waiting_state: ThreadState,
    payload: IPCPayLoad,
    pt_regs: &Registers,
    thread_lock_perm: Tracked<&LockPerm>,
) -> (ret: (usize, Tracked<PointsTo<Node<RwLockThreadPtr>>>))
    requires
        thread_perms_wf(*old(thread_map)),
        old(thread_map).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        old(thread_map).dom().contains(thread_ptr),
        old(thread_map).spec_index(thread_ptr).wlocked_by(lctx),
        thread_lock_perm.view().state() is WriteLock,
        thread_lock_perm.view().thread_id() == lctx.thread_id(),
        thread_lock_perm.view().lock_id() == old(thread_map).spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(thread_map).spec_index(thread_ptr).view().state is RUNNING,
        waiting_state.is_endpoint_waiting(),
        payload.wf(),
        waiting_state is RECEIVING_CALL ==> old(thread_map).spec_index(thread_ptr).view().caller is None,
        edp_idx_valid(endpoint_index),
        old(thread_map).spec_index(thread_ptr).view().endpoint_descriptors.wf(),
        old(thread_map).spec_index(thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
    ensures
        thread_perms_wf(*final(thread_map)),
        final(thread_map).typed_lock_map_aligned(
            lctx.thread_lock_map().insert(thread_ptr, TypedHeldLock {
                lock_id: final(thread_map).lock_id_by_key(thread_ptr),
                mode: lctx.thread_lock_map().index(thread_ptr).mode,
            }), lctx.thread_id()),
        lctx.thread_lock_map().index(thread_ptr).lock_id == old(thread_map).lock_id_by_key(thread_ptr),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        final(thread_map).unchanged_except(old(thread_map), thread_ptr),
        final(thread_map).spec_index(thread_ptr).wlocked_by(lctx),
        final(thread_map).spec_index(thread_ptr).locking_thread() == old(thread_map).spec_index(thread_ptr).locking_thread(),
        final(thread_map).spec_index(thread_ptr).being_killed() == old(thread_map).spec_index(thread_ptr).being_killed(),
        final(thread_map).spec_index(thread_ptr).view().ipc_framed_fields_equal(&old(thread_map).spec_index(thread_ptr).view()),
        final(thread_map).spec_index(thread_ptr).view().caller == old(thread_map).spec_index(thread_ptr).view().caller,
        final(thread_map).spec_index(thread_ptr).view().callee == old(thread_map).spec_index(thread_ptr).view().callee,
        final(thread_map).spec_index(thread_ptr).view().state == waiting_state,
        final(thread_map).spec_index(thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        final(thread_map).spec_index(thread_ptr).view().blocking_endpoint_index == Some(endpoint_index),
        final(thread_map).spec_index(thread_ptr).view().ipc_payload =~= payload,
        final(thread_map).spec_index(thread_ptr).view().trap_frame.is_some(),
        final(thread_map).spec_index(thread_ptr).view().trap_frame.get_some_0() =~= pt_regs,
        ret.0 == final(thread_map).spec_index(thread_ptr).view().endpoint_linkedlist_node.addr(),
        ret.1.view().is_init(),
        ret.1.view().addr() == ret.0,
        ret.1.view().value().view() == thread_ptr,
{
    proof {
        assert(
            old(thread_map).perms_wf()
            && old(thread_map).spec_index(thread_ptr).is_init()
            && old(thread_map).spec_index(thread_ptr).view().inv()
        ) by { reveal(thread_perms_wf); };
    }
    let ret = {
        let thread_mut = thread_map.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), thread_lock_perm);
        thread_mut.block_on_endpoint(thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, pt_regs)
    };
    proof {
        assert(thread_perms_wf(*thread_map)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); };
    }
    ret
}

pub(super) fn ipc_enqueue_endpoint_waiter(
    endpoint_map: &mut EndpointLockedMap,
    Tracked(lctx): Tracked<&LocalContext>,
    endpoint_ptr: RwLockEndpointPtr,
    thread_ptr: RwLockThreadPtr,
    waiting_state: ThreadState,
    node_addr: usize,
    node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>,
    endpoint_lock_perm: Tracked<&LockPerm>,
)
    requires
        endpoint_perms_wf(*old(endpoint_map)),
        old(endpoint_map).typed_lock_map_aligned(lctx.endpoint_lock_map(), lctx.thread_id()),
        old(endpoint_map).dom().contains(endpoint_ptr),
        old(endpoint_map).spec_index(endpoint_ptr).wlocked_by(lctx),
        endpoint_lock_perm.view().state() is WriteLock,
        endpoint_lock_perm.view().thread_id() == lctx.thread_id(),
        endpoint_lock_perm.view().lock_id() == old(endpoint_map).spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
        waiting_state.is_endpoint_waiting(),
        node_perm.view().is_init(),
        node_perm.view().addr() == node_addr,
        node_perm.view().value().view() == thread_ptr,
        !old(endpoint_map).spec_index(endpoint_ptr).view().queue.view().contains(thread_ptr),
        old(endpoint_map).spec_index(endpoint_ptr).view().queue.length != usize::MAX,
    ensures
        endpoint_perms_wf(*final(endpoint_map)),
        final(endpoint_map).typed_lock_map_aligned(lctx.endpoint_lock_map(), lctx.thread_id()),
        final(endpoint_map).unchanged_except(old(endpoint_map), endpoint_ptr),
        final(endpoint_map).spec_index(endpoint_ptr).wlocked_by(lctx),
        final(endpoint_map).spec_index(endpoint_ptr).locking_thread() == old(endpoint_map).spec_index(endpoint_ptr).locking_thread(),
        final(endpoint_map).lock_id_by_key(endpoint_ptr) == old(endpoint_map).lock_id_by_key(endpoint_ptr),
        final(endpoint_map).spec_index(endpoint_ptr).view().rf_counter == old(endpoint_map).spec_index(endpoint_ptr).view().rf_counter,
        final(endpoint_map).spec_index(endpoint_ptr).view().owning_threads == old(endpoint_map).spec_index(endpoint_ptr).view().owning_threads,
        final(endpoint_map).spec_index(endpoint_ptr).view().owning_container == old(endpoint_map).spec_index(endpoint_ptr).view().owning_container,
        final(endpoint_map).spec_index(endpoint_ptr).view().queue.view() == old(endpoint_map).spec_index(endpoint_ptr).view().queue.view().push(thread_ptr),
        final(endpoint_map).spec_index(endpoint_ptr).view().queue.map() == old(endpoint_map).spec_index(endpoint_ptr).view().queue.map().insert(node_addr, thread_ptr),
        !old(endpoint_map).spec_index(endpoint_ptr).view().queue.map().dom().contains(node_addr),
        final(endpoint_map).spec_index(endpoint_ptr).view().queue_state
            == if old(endpoint_map).spec_index(endpoint_ptr).view()
                .queue.length == 0 {
                match waiting_state {
                    ThreadState::SENDING | ThreadState::CALLING =>
                        EndpointState::SEND,
                    _ => EndpointState::RECEIVE,
                }
            } else {
                old(endpoint_map).spec_index(endpoint_ptr).view().queue_state
            },
{
    proof {
        assert(
            old(endpoint_map).perms_wf()
            && old(endpoint_map).spec_index(endpoint_ptr).is_init()
            && old(endpoint_map).spec_index(endpoint_ptr).view().inv()
        ) by { reveal(endpoint_perms_wf); reveal(endpoints_inv); };
    }
    {
        let endpoint_mut = endpoint_map.borrow_mut_typed(endpoint_ptr, Ghost(lctx.endpoint_lock_map()), Tracked(lctx), endpoint_lock_perm);
        endpoint_mut.enqueue_waiter(thread_ptr, waiting_state, node_addr, node_perm);
    }
    proof {
        assert(endpoint_perms_wf(*endpoint_map)) by { reveal(endpoint_perms_wf); reveal(endpoints_inv); };
    }
}

pub(super) fn ipc_schedule_endpoint_waiter(
    thread_map: &mut ThreadLockedMap,
    Tracked(lctx): Tracked<&LocalContext>,
    thread_ptr: RwLockThreadPtr,
    current_thread_ptr: RwLockThreadPtr,
    result: RetValueType,
    endpoint_node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>,
    thread_lock_perm: Tracked<&LockPerm>,
) -> (ret: (usize, Tracked<PointsTo<Node<RwLockThreadPtr>>>))
    requires
        thread_perms_wf(*old(thread_map)),
        old(thread_map).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        old(thread_map).dom().contains(thread_ptr),
        old(thread_map).spec_index(thread_ptr).wlocked_by(lctx),
        old(thread_map).dom().contains(current_thread_ptr),
        current_thread_ptr != thread_ptr,
        thread_lock_perm.view().state() is WriteLock,
        thread_lock_perm.view().thread_id() == lctx.thread_id(),
        thread_lock_perm.view().lock_id() == old(thread_map).spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(thread_map).spec_index(thread_ptr).view().state.is_endpoint_waiting(),
        endpoint_node_perm.view().is_init(),
        endpoint_node_perm.view().addr() == old(thread_map).spec_index(thread_ptr).view().endpoint_linkedlist_node.addr(),
        endpoint_node_perm.view().value().view() == thread_ptr,
    ensures
        thread_perms_wf(*final(thread_map)),
        final(thread_map).typed_lock_map_aligned(
            lctx.thread_lock_map().insert(thread_ptr, TypedHeldLock {
                lock_id: final(thread_map).lock_id_by_key(thread_ptr),
                mode: lctx.thread_lock_map().index(thread_ptr).mode,
            }), lctx.thread_id()),
        lctx.thread_lock_map().index(thread_ptr).lock_id == old(thread_map).lock_id_by_key(thread_ptr),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        final(thread_map).unchanged_except(old(thread_map), thread_ptr),
        final(thread_map).spec_index(thread_ptr).wlocked_by(lctx),
        final(thread_map).spec_index(thread_ptr).locking_thread() == old(thread_map).spec_index(thread_ptr).locking_thread(),
        final(thread_map).spec_index(thread_ptr).being_killed() == old(thread_map).spec_index(thread_ptr).being_killed(),
        final(thread_map).spec_index(current_thread_ptr) == old(thread_map).spec_index(current_thread_ptr),
        final(thread_map).lock_id_by_key(current_thread_ptr) == old(thread_map).lock_id_by_key(current_thread_ptr),
        final(thread_map).spec_index(thread_ptr).view().ipc_framed_fields_equal(&old(thread_map).spec_index(thread_ptr).view()),
        final(thread_map).spec_index(thread_ptr).view().caller == old(thread_map).spec_index(thread_ptr).view().caller,
        final(thread_map).spec_index(thread_ptr).view().callee == old(thread_map).spec_index(thread_ptr).view().callee,
        final(thread_map).spec_index(thread_ptr).view().state is SCHEDULED,
        final(thread_map).spec_index(thread_ptr).view().blocking_endpoint_ptr is None,
        final(thread_map).spec_index(thread_ptr).view().blocking_endpoint_index is None,
        final(thread_map).spec_index(thread_ptr).view().endpoint_linkedlist_node.is_init(),
        final(thread_map).spec_index(thread_ptr).view().scheduler_linkedlist_node.is_init() == false,
        final(thread_map).spec_index(thread_ptr).view().error_code == Some(result),
        ret.0 == final(thread_map).spec_index(thread_ptr).view().scheduler_linkedlist_node.addr(),
        ret.1.view().is_init(),
        ret.1.view().addr() == ret.0,
        ret.1.view().value().view() == thread_ptr,
{
    proof {
        assert(
            old(thread_map).perms_wf()
            && old(thread_map).spec_index(thread_ptr).is_init()
            && old(thread_map).spec_index(thread_ptr).view().inv()
        ) by { reveal(thread_perms_wf); };
    }
    let ret = {
        let thread_mut = thread_map.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), thread_lock_perm);
        thread_mut.endpoint_waiter_to_scheduled(thread_ptr, result, endpoint_node_perm)
    };
    proof {
        assert(thread_perms_wf(*thread_map)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); };
        assert({
            &&& final(thread_map).spec_index(current_thread_ptr) == old(thread_map).spec_index(current_thread_ptr)
            &&& final(thread_map).lock_id_by_key(current_thread_ptr) == old(thread_map).lock_id_by_key(current_thread_ptr)
        }) by { lock_id_fields_eq_imply_eq(); };
    }
    ret
}

pub(super) fn ipc_move_endpoint_waiter_to_transit(
    thread_map: &mut ThreadLockedMap,
    Tracked(lctx): Tracked<&LocalContext>,
    thread_ptr: RwLockThreadPtr,
    current_thread_ptr: RwLockThreadPtr,
    endpoint_node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>,
    thread_lock_perm: Tracked<&LockPerm>,
)
    requires
        thread_perms_wf(*old(thread_map)),
        old(thread_map).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        old(thread_map).dom().contains(thread_ptr),
        old(thread_map).spec_index(thread_ptr).wlocked_by(lctx),
        old(thread_map).dom().contains(current_thread_ptr),
        current_thread_ptr != thread_ptr,
        thread_lock_perm.view().state() is WriteLock,
        thread_lock_perm.view().thread_id() == lctx.thread_id(),
        thread_lock_perm.view().lock_id() == old(thread_map).spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(thread_map).spec_index(thread_ptr).view().state is SENDING || old(thread_map).spec_index(thread_ptr).view().state is RECEIVING,
        old(thread_map).spec_index(thread_ptr).view().ipc_payload is Endpoint,
        endpoint_node_perm.view().is_init(),
        endpoint_node_perm.view().addr() == old(thread_map).spec_index(thread_ptr).view().endpoint_linkedlist_node.addr(),
        endpoint_node_perm.view().value().view() == thread_ptr,
    ensures
        thread_perms_wf(*final(thread_map)),
        final(thread_map).typed_lock_map_aligned(
            lctx.thread_lock_map().insert(thread_ptr, TypedHeldLock {
                lock_id: final(thread_map).lock_id_by_key(thread_ptr),
                mode: lctx.thread_lock_map().index(thread_ptr).mode,
            }), lctx.thread_id()),
        lctx.thread_lock_map().index(thread_ptr).lock_id == old(thread_map).lock_id_by_key(thread_ptr),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        final(thread_map).unchanged_except(old(thread_map), thread_ptr),
        final(thread_map).spec_index(thread_ptr).wlocked_by(lctx),
        final(thread_map).spec_index(thread_ptr).locking_thread() == old(thread_map).spec_index(thread_ptr).locking_thread(),
        final(thread_map).spec_index(thread_ptr).being_killed() == old(thread_map).spec_index(thread_ptr).being_killed(),
        final(thread_map).spec_index(current_thread_ptr) == old(thread_map).spec_index(current_thread_ptr),
        final(thread_map).lock_id_by_key(current_thread_ptr) == old(thread_map).lock_id_by_key(current_thread_ptr),
        final(thread_map).spec_index(thread_ptr).view().ipc_framed_fields_equal(&old(thread_map).spec_index(thread_ptr).view()),
        final(thread_map).spec_index(thread_ptr).view().caller == old(thread_map).spec_index(thread_ptr).view().caller,
        final(thread_map).spec_index(thread_ptr).view().callee == old(thread_map).spec_index(thread_ptr).view().callee,
        final(thread_map).spec_index(thread_ptr).view().state is IPC_ENDPOINT_TRANSIT,
        final(thread_map).spec_index(thread_ptr).view().blocking_endpoint_ptr is None,
        final(thread_map).spec_index(thread_ptr).view().blocking_endpoint_index is None,
        final(thread_map).spec_index(thread_ptr).view().endpoint_linkedlist_node.is_init(),
        final(thread_map).spec_index(thread_ptr).view().scheduler_linkedlist_node == old(thread_map).spec_index(thread_ptr).view().scheduler_linkedlist_node,
        final(thread_map).spec_index(thread_ptr).view().ipc_payload == old(thread_map).spec_index(thread_ptr).view().ipc_payload,
{
    proof {
        assert({
            &&& old(thread_map).perms_wf()
            &&& old(thread_map).spec_index(thread_ptr).is_init()
            &&& old(thread_map).spec_index(thread_ptr).view().inv()
        }) by { reveal(thread_perms_wf); };
    }
    {
        let thread_mut = thread_map.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), thread_lock_perm);
        thread_mut.endpoint_waiter_to_endpoint_transit(thread_ptr, endpoint_node_perm);
    }
    proof {
        assert(thread_perms_wf(*thread_map)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); };
        assert({
            &&& final(thread_map).spec_index(current_thread_ptr) == old(thread_map).spec_index(current_thread_ptr)
            &&& final(thread_map).lock_id_by_key(current_thread_ptr) == old(thread_map).lock_id_by_key(current_thread_ptr)
        }) by { lock_id_fields_eq_imply_eq(); };
    }
}

pub(super) fn ipc_schedule_endpoint_transit(
    thread_map: &mut ThreadLockedMap,
    Tracked(lctx): Tracked<&LocalContext>,
    thread_ptr: RwLockThreadPtr,
    current_thread_ptr: RwLockThreadPtr,
    result: RetValueType,
    thread_lock_perm: Tracked<&LockPerm>,
) -> (ret: (usize, Tracked<PointsTo<Node<RwLockThreadPtr>>>))
    requires
        thread_perms_wf(*old(thread_map)),
        old(thread_map).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        old(thread_map).dom().contains(thread_ptr),
        old(thread_map).spec_index(thread_ptr).wlocked_by(lctx),
        old(thread_map).dom().contains(current_thread_ptr),
        current_thread_ptr != thread_ptr,
        thread_lock_perm.view().state() is WriteLock,
        thread_lock_perm.view().thread_id() == lctx.thread_id(),
        thread_lock_perm.view().lock_id() == old(thread_map).spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(thread_map).spec_index(thread_ptr).view().state is IPC_ENDPOINT_TRANSIT,
    ensures
        thread_perms_wf(*final(thread_map)),
        final(thread_map).typed_lock_map_aligned(
            lctx.thread_lock_map().insert(thread_ptr, TypedHeldLock {
                lock_id: final(thread_map).lock_id_by_key(thread_ptr),
                mode: lctx.thread_lock_map().index(thread_ptr).mode,
            }), lctx.thread_id()),
        lctx.thread_lock_map().index(thread_ptr).lock_id == old(thread_map).lock_id_by_key(thread_ptr),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        final(thread_map).unchanged_except(old(thread_map), thread_ptr),
        final(thread_map).spec_index(thread_ptr).wlocked_by(lctx),
        final(thread_map).spec_index(thread_ptr).locking_thread() == old(thread_map).spec_index(thread_ptr).locking_thread(),
        final(thread_map).spec_index(thread_ptr).being_killed() == old(thread_map).spec_index(thread_ptr).being_killed(),
        final(thread_map).spec_index(current_thread_ptr) == old(thread_map).spec_index(current_thread_ptr),
        final(thread_map).lock_id_by_key(current_thread_ptr) == old(thread_map).lock_id_by_key(current_thread_ptr),
        final(thread_map).spec_index(thread_ptr).view().ipc_framed_fields_equal(&old(thread_map).spec_index(thread_ptr).view()),
        final(thread_map).spec_index(thread_ptr).view().caller == old(thread_map).spec_index(thread_ptr).view().caller,
        final(thread_map).spec_index(thread_ptr).view().callee == old(thread_map).spec_index(thread_ptr).view().callee,
        final(thread_map).spec_index(thread_ptr).view().state is SCHEDULED,
        final(thread_map).spec_index(thread_ptr).view().blocking_endpoint_ptr is None,
        final(thread_map).spec_index(thread_ptr).view().blocking_endpoint_index is None,
        final(thread_map).spec_index(thread_ptr).view().endpoint_linkedlist_node.is_init(),
        final(thread_map).spec_index(thread_ptr).view().scheduler_linkedlist_node.is_init() == false,
        final(thread_map).spec_index(thread_ptr).view().error_code == Some(result),
        final(thread_map).spec_index(thread_ptr).view().ipc_payload is Empty,
        ret.0 == final(thread_map).spec_index(thread_ptr).view().scheduler_linkedlist_node.addr(),
        ret.1.view().is_init(),
        ret.1.view().addr() == ret.0,
        ret.1.view().value().view() == thread_ptr,
{
    proof {
        assert({
            &&& old(thread_map).perms_wf()
            &&& old(thread_map).spec_index(thread_ptr).is_init()
            &&& old(thread_map).spec_index(thread_ptr).view().inv()
        }) by { reveal(thread_perms_wf); };
    }
    let ret = {
        let thread_mut = thread_map.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), thread_lock_perm);
        thread_mut.endpoint_transit_to_scheduled(thread_ptr, result)
    };
    proof {
        assert(thread_perms_wf(*thread_map)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); };
        assert({
            &&& final(thread_map).spec_index(current_thread_ptr) == old(thread_map).spec_index(current_thread_ptr)
            &&& final(thread_map).lock_id_by_key(current_thread_ptr) == old(thread_map).lock_id_by_key(current_thread_ptr)
        }) by { lock_id_fields_eq_imply_eq(); };
    }
    ret
}

pub(super) fn ipc_dequeue_endpoint_waiter(
    endpoint_map: &mut EndpointLockedMap,
    Tracked(lctx): Tracked<&LocalContext>,
    endpoint_ptr: RwLockEndpointPtr,
    thread_ptr: RwLockThreadPtr,
    endpoint_lock_perm: Tracked<&LockPerm>,
) -> (ret: (usize, Tracked<PointsTo<Node<RwLockThreadPtr>>>))
    requires
        endpoint_perms_wf(*old(endpoint_map)),
        old(endpoint_map).typed_lock_map_aligned(lctx.endpoint_lock_map(), lctx.thread_id()),
        old(endpoint_map).dom().contains(endpoint_ptr),
        old(endpoint_map).spec_index(endpoint_ptr).wlocked_by(lctx),
        endpoint_lock_perm.view().state() is WriteLock,
        endpoint_lock_perm.view().thread_id() == lctx.thread_id(),
        endpoint_lock_perm.view().lock_id() == old(endpoint_map).spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
        old(endpoint_map).spec_index(endpoint_ptr).view().queue.len() != 0,
        old(endpoint_map).spec_index(endpoint_ptr).view().queue.view().spec_index(0) == thread_ptr,
    ensures
        endpoint_perms_wf(*final(endpoint_map)),
        final(endpoint_map).typed_lock_map_aligned(lctx.endpoint_lock_map(), lctx.thread_id()),
        final(endpoint_map).unchanged_except(old(endpoint_map), endpoint_ptr),
        final(endpoint_map).spec_index(endpoint_ptr).wlocked_by(lctx),
        final(endpoint_map).spec_index(endpoint_ptr).locking_thread() == old(endpoint_map).spec_index(endpoint_ptr).locking_thread(),
        final(endpoint_map).lock_id_by_key(endpoint_ptr) == old(endpoint_map).lock_id_by_key(endpoint_ptr),
        final(endpoint_map).spec_index(endpoint_ptr).view().rf_counter == old(endpoint_map).spec_index(endpoint_ptr).view().rf_counter,
        final(endpoint_map).spec_index(endpoint_ptr).view().owning_threads == old(endpoint_map).spec_index(endpoint_ptr).view().owning_threads,
        final(endpoint_map).spec_index(endpoint_ptr).view().owning_container == old(endpoint_map).spec_index(endpoint_ptr).view().owning_container,
        final(endpoint_map).spec_index(endpoint_ptr).view().queue.view() == old(endpoint_map).spec_index(endpoint_ptr).view().queue.view().skip(1),
        final(endpoint_map).spec_index(endpoint_ptr).view().queue.map() == old(endpoint_map).spec_index(endpoint_ptr).view().queue.map().remove(ret.0),
        final(endpoint_map).spec_index(endpoint_ptr).view().queue_state == old(endpoint_map).spec_index(endpoint_ptr).view().queue_state,
        ret.1.view().is_init(),
        ret.1.view().addr() == ret.0,
        ret.1.view().value().view() == thread_ptr,
        old(endpoint_map).spec_index(endpoint_ptr).view().queue.map().dom().contains(ret.0),
        old(endpoint_map).spec_index(endpoint_ptr).view().queue.map().spec_index(ret.0) == thread_ptr,
        !final(endpoint_map).spec_index(endpoint_ptr).view().queue.view().contains(thread_ptr),
        forall|t_ptr: RwLockThreadPtr|
            #![trigger old(endpoint_map).spec_index(endpoint_ptr).view().queue.view().contains(t_ptr)]
            #![trigger final(endpoint_map).spec_index(endpoint_ptr).view().queue.view().contains(t_ptr)]
            old(endpoint_map).spec_index(endpoint_ptr).view().queue.view().contains(t_ptr) && t_ptr != thread_ptr ==>
                final(endpoint_map).spec_index(endpoint_ptr).view().queue.view().contains(t_ptr),
        forall|t_ptr: RwLockThreadPtr|
            #![trigger old(endpoint_map).spec_index(endpoint_ptr).view().queue.view().contains(t_ptr)]
            #![trigger final(endpoint_map).spec_index(endpoint_ptr).view().queue.view().contains(t_ptr)]
            final(endpoint_map).spec_index(endpoint_ptr).view().queue.view().contains(t_ptr) ==>
                old(endpoint_map).spec_index(endpoint_ptr).view().queue.view().contains(t_ptr),
        forall|node_addr: usize|
            #![trigger old(endpoint_map).spec_index(endpoint_ptr).view().queue.map().dom().contains(node_addr)]
            #![trigger final(endpoint_map).spec_index(endpoint_ptr).view().queue.map().dom().contains(node_addr)]
            old(endpoint_map).spec_index(endpoint_ptr).view().queue.map().dom().contains(node_addr) && node_addr != ret.0 ==> {
                &&& final(endpoint_map).spec_index(endpoint_ptr).view().queue.map().dom().contains(node_addr)
                &&& final(endpoint_map).spec_index(endpoint_ptr).view().queue.map().spec_index(node_addr) == old(endpoint_map).spec_index(endpoint_ptr).view().queue.map().spec_index(node_addr)
            },
{
    proof {
        assert(
            old(endpoint_map).perms_wf()
            && old(endpoint_map).spec_index(endpoint_ptr).is_init()
            && old(endpoint_map).spec_index(endpoint_ptr).view().inv()
        ) by { reveal(endpoint_perms_wf); reveal(endpoints_inv); };
    }
    let ret = {
        let endpoint_mut = endpoint_map.borrow_mut_typed(endpoint_ptr, Ghost(lctx.endpoint_lock_map()), Tracked(lctx), endpoint_lock_perm);
        endpoint_mut.dequeue_waiter(thread_ptr)
    };
    proof {
        assert(endpoint_perms_wf(*endpoint_map)) by { reveal(endpoint_perms_wf); reveal(endpoints_inv); };
    }
    ret
}

pub(super) fn ipc_enqueue_scheduled_thread(
    scheduler_map: &mut SchedulerLockedMap,
    Tracked(lctx): Tracked<&LocalContext>,
    scheduler_ptr: RwLockSchedulerPtr,
    thread_ptr: RwLockThreadPtr,
    node_addr: usize,
    node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>,
    scheduler_lock_perm: Tracked<&LockPerm>,
)
    requires
        scheduler_perms_wf(*old(scheduler_map)),
        old(scheduler_map).typed_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
        old(scheduler_map).dom().contains(scheduler_ptr),
        old(scheduler_map).spec_index(scheduler_ptr).wlocked_by(lctx),
        scheduler_lock_perm.view().state() is WriteLock,
        scheduler_lock_perm.view().thread_id() == lctx.thread_id(),
        scheduler_lock_perm.view().lock_id() == old(scheduler_map).spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
        node_perm.view().is_init(),
        node_perm.view().addr() == node_addr,
        node_perm.view().value().view() == thread_ptr,
        !old(scheduler_map).spec_index(scheduler_ptr).view().queue.view().contains(thread_ptr),
        old(scheduler_map).spec_index(scheduler_ptr).view().queue.length != usize::MAX,
    ensures
        scheduler_perms_wf(*final(scheduler_map)),
        final(scheduler_map).typed_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id()),
        final(scheduler_map).unchanged_except(old(scheduler_map), scheduler_ptr),
        final(scheduler_map).spec_index(scheduler_ptr).wlocked_by(lctx),
        final(scheduler_map).spec_index(scheduler_ptr).locking_thread() == old(scheduler_map).spec_index(scheduler_ptr).locking_thread(),
        final(scheduler_map).lock_id_by_key(scheduler_ptr) == old(scheduler_map).lock_id_by_key(scheduler_ptr),
        final(scheduler_map).spec_index(scheduler_ptr).view().owning_container == old(scheduler_map).spec_index(scheduler_ptr).view().owning_container,
        final(scheduler_map).spec_index(scheduler_ptr).view().queue.view() == old(scheduler_map).spec_index(scheduler_ptr).view().queue.view().push(thread_ptr),
        final(scheduler_map).spec_index(scheduler_ptr).view().queue.map() == old(scheduler_map).spec_index(scheduler_ptr).view().queue.map().insert(node_addr, thread_ptr),
        !old(scheduler_map).spec_index(scheduler_ptr).view().queue.map().dom().contains(node_addr),
        forall|t_ptr: RwLockThreadPtr|
            #![trigger old(scheduler_map).spec_index(scheduler_ptr).view().queue.view().contains(t_ptr)]
            #![trigger final(scheduler_map).spec_index(scheduler_ptr).view().queue.view().contains(t_ptr)]
            old(scheduler_map).spec_index(scheduler_ptr).view().queue.view().contains(t_ptr) ==>
                final(scheduler_map).spec_index(scheduler_ptr).view().queue.view().contains(t_ptr),
        forall|old_node_addr: usize|
            #![trigger old(scheduler_map).spec_index(scheduler_ptr).view().queue.map().dom().contains(old_node_addr)]
            #![trigger final(scheduler_map).spec_index(scheduler_ptr).view().queue.map().dom().contains(old_node_addr)]
            old(scheduler_map).spec_index(scheduler_ptr).view().queue.map().dom().contains(old_node_addr) ==> {
                &&& final(scheduler_map).spec_index(scheduler_ptr).view().queue.map().dom().contains(old_node_addr)
                &&& final(scheduler_map).spec_index(scheduler_ptr).view().queue.map().spec_index(old_node_addr) == old(scheduler_map).spec_index(scheduler_ptr).view().queue.map().spec_index(old_node_addr)
            },
{
    proof {
        assert(
            old(scheduler_map).perms_wf()
            && old(scheduler_map).spec_index(scheduler_ptr).is_init()
            && old(scheduler_map).spec_index(scheduler_ptr).view().inv()
        ) by { reveal(scheduler_perms_wf); };
    }
    {
        let scheduler_mut = scheduler_map.borrow_mut_typed(scheduler_ptr, Ghost(lctx.scheduler_lock_map()), Tracked(lctx), scheduler_lock_perm);
        scheduler_mut.enqueue_scheduled_thread(thread_ptr, node_addr, node_perm);
    }
    proof {
        assert(scheduler_perms_wf(*scheduler_map)) by { reveal(scheduler_perms_wf); };
    }
}

} // verus!
