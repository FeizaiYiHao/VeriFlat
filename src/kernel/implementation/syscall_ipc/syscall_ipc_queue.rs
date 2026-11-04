use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_queue_eof::*;
verus! {
pub(super) fn ipc_block_thread_on_endpoint(
    thread_map: &mut ThreadLockedMap, Tracked(lctx): Tracked<&LocalContext>, thrd_ptr: RwLockThreadPtr,
    ep_ptr: RwLockEndpointPtr, ep_idx: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, pt_regs: &Registers,
    thread_lock_perm: Tracked<&LockPerm>,
) -> (ret: (usize, Tracked<PointsTo<Node<RwLockThreadPtr>>>))
    requires
        thread_perms_wf(*old(thread_map)),
        old(thread_map).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        old(thread_map).dom().contains(thrd_ptr),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_lock_perm.view().state() is WriteLock,
        thread_lock_perm.view().thread_id() == lctx.thread_id(),
        thread_lock_perm.view().lock_id() == old(thread_map).spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(thread_map).spec_index(thrd_ptr).view().state is RUNNING,
        old(thread_map).spec_index(thrd_ptr).view().syscall_progress.view() is None,
        waiting_state.is_endpoint_waiting(),
        payload.wf(),
        waiting_state is RECEIVING_CALL ==> old(thread_map).spec_index(thrd_ptr).view().caller is None,
        edp_idx_valid(ep_idx),
        old(thread_map).spec_index(thrd_ptr).view().endpoint_descriptors.wf(),
        old(thread_map).spec_index(thrd_ptr).view().endpoint_descriptors.spec_index(ep_idx) == Some(ep_ptr),
    ensures
        thread_perms_wf(*final(thread_map)),
        final(thread_map).typed_lock_map_aligned(
            lctx.thread_lock_map().insert(thrd_ptr, TypedHeldLock { lock_id: final(thread_map).lock_id_by_key(thrd_ptr), mode: lctx.thread_lock_map().index(thrd_ptr).mode }), lctx.thread_id()),
        lctx.thread_lock_map().index(thrd_ptr).lock_id == old(thread_map).lock_id_by_key(thrd_ptr),
        final(thread_map).unchanged_except(old(thread_map), thrd_ptr),
        final(thread_map).spec_index(thrd_ptr).locking_thread() == old(thread_map).spec_index(thrd_ptr).locking_thread(),
        final(thread_map).spec_index(thrd_ptr).being_killed() == old(thread_map).spec_index(thrd_ptr).being_killed(),
        final(thread_map).spec_index(thrd_ptr).view_ghost() == old(thread_map).spec_index(thrd_ptr).view_ghost(),
        final(thread_map).spec_index(thrd_ptr).view().non_ipc_fields_unchanged(&old(thread_map).spec_index(thrd_ptr).view()),
        final(thread_map).spec_index(thrd_ptr).view().caller == old(thread_map).spec_index(thrd_ptr).view().caller,
        final(thread_map).spec_index(thrd_ptr).view().syscall_progress == old(thread_map).spec_index(thrd_ptr).view().syscall_progress,
        final(thread_map).spec_index(thrd_ptr).view().callee == old(thread_map).spec_index(thrd_ptr).view().callee,
        final(thread_map).spec_index(thrd_ptr).view().error_code == old(thread_map).spec_index(thrd_ptr).view().error_code,
        final(thread_map).spec_index(thrd_ptr).view().state == waiting_state,
        final(thread_map).spec_index(thrd_ptr).view().blocking_endpoint_ptr == Some(ep_ptr),
        final(thread_map).spec_index(thrd_ptr).view().blocking_endpoint_index == Some(ep_idx),
        final(thread_map).spec_index(thrd_ptr).view().ipc_payload =~= payload,
        final(thread_map).spec_index(thrd_ptr).view().trap_frame.is_some(),
        final(thread_map).spec_index(thrd_ptr).view().trap_frame.get_some_0() =~= pt_regs,
        ret.0 == final(thread_map).spec_index(thrd_ptr).view().endpoint_linkedlist_node.addr(),
        ret.1.view().is_init(),
        ret.1.view().addr() == ret.0,
        ret.1.view().value().view() == thrd_ptr,
{
    proof { thread_perms_wf_map(*old(thread_map)); thread_perms_wf_at(*old(thread_map), thrd_ptr); }
    let ret = {
        let thread_mut = thread_map.borrow_mut_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), thread_lock_perm);
        thread_mut.block_on_endpoint(thrd_ptr, ep_ptr, ep_idx, waiting_state, payload, pt_regs)
    };
    proof { ipc_block_thread_on_endpoint_eof(*old(thread_map), *thread_map, thrd_ptr); }
    ret
}

pub(super) fn ipc_enqueue_endpoint_waiter(
    endpoint_map: &mut EndpointLockedMap, Tracked(lctx): Tracked<&LocalContext>, ep_ptr: RwLockEndpointPtr,
    thrd_ptr: RwLockThreadPtr, waiting_state: ThreadState, node_addr: usize, node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>,
    endpoint_lock_perm: Tracked<&LockPerm>,
)
    requires
        endpoint_perms_wf(*old(endpoint_map)),
        old(endpoint_map).typed_lock_map_aligned(lctx.endpoint_lock_map(), lctx.thread_id()),
        old(endpoint_map).dom().contains(ep_ptr),
        typed_lock_map_contains_mode(lctx.endpoint_lock_map(), ep_ptr, TypedLockMode::Write),
        endpoint_lock_perm.view().state() is WriteLock,
        endpoint_lock_perm.view().thread_id() == lctx.thread_id(),
        endpoint_lock_perm.view().lock_id() == old(endpoint_map).spec_index(ep_ptr).locking_thread()->Write_lock_id,
        waiting_state.is_endpoint_waiting(),
        node_perm.view().is_init(),
        node_perm.view().addr() == node_addr,
        node_perm.view().value().view() == thrd_ptr,
        !old(endpoint_map).spec_index(ep_ptr).view().queue.view().contains(thrd_ptr),
        old(endpoint_map).spec_index(ep_ptr).view().queue.length != usize::MAX,
    ensures
        forall|key: usize| #![trigger old(endpoint_map).view().spec_index(key)] #![trigger final(endpoint_map).view().spec_index(key)] old(endpoint_map).dom().contains(key) ==> {
            &&& final(endpoint_map).view().spec_index(key).is_init() == old(endpoint_map).view().spec_index(key).is_init()
            &&& final(endpoint_map).view().spec_index(key).addr() == old(endpoint_map).view().spec_index(key).addr()
        },
        final(endpoint_map).spec_index(ep_ptr).is_init() == old(endpoint_map).spec_index(ep_ptr).is_init(),
        final(endpoint_map).spec_index(ep_ptr).view_rodata() == old(endpoint_map).spec_index(ep_ptr).view_rodata(),
        final(endpoint_map).spec_index(ep_ptr).view_ghost() == old(endpoint_map).spec_index(ep_ptr).view_ghost(),
        final(endpoint_map).spec_index(ep_ptr).view().queue.wf(),
        final(endpoint_map).spec_index(ep_ptr).view().queue.container_depth == old(endpoint_map).spec_index(ep_ptr).view().queue.container_depth,
        final(endpoint_map).spec_index(ep_ptr).view().queue.lock_minor() == old(endpoint_map).spec_index(ep_ptr).view().queue.lock_minor(),
        final(endpoint_map).spec_index(ep_ptr).view().queue.length as int == old(endpoint_map).spec_index(ep_ptr).view().queue.length as int + 1,
        final(endpoint_map).spec_index(ep_ptr).view().queue.dom() == old(endpoint_map).spec_index(ep_ptr).view().queue.dom().insert(node_addr),
        endpoint_perms_wf(*final(endpoint_map)),
        final(endpoint_map).typed_lock_map_aligned(lctx.endpoint_lock_map(), lctx.thread_id()),
        final(endpoint_map).unchanged_except(old(endpoint_map), ep_ptr),
        final(endpoint_map).spec_index(ep_ptr).locking_thread() == old(endpoint_map).spec_index(ep_ptr).locking_thread(),
        final(endpoint_map).spec_index(ep_ptr).being_killed() == old(endpoint_map).spec_index(ep_ptr).being_killed(),
        final(endpoint_map).lock_id_by_key(ep_ptr) == old(endpoint_map).lock_id_by_key(ep_ptr),
        final(endpoint_map).spec_index(ep_ptr).view().rf_counter == old(endpoint_map).spec_index(ep_ptr).view().rf_counter,
        final(endpoint_map).spec_index(ep_ptr).view().owning_threads == old(endpoint_map).spec_index(ep_ptr).view().owning_threads,
        final(endpoint_map).spec_index(ep_ptr).view().owning_container == old(endpoint_map).spec_index(ep_ptr).view().owning_container,
        final(endpoint_map).spec_index(ep_ptr).view().queue.view() == old(endpoint_map).spec_index(ep_ptr).view().queue.view().push(thrd_ptr),
        final(endpoint_map).spec_index(ep_ptr).view().queue.map() == old(endpoint_map).spec_index(ep_ptr).view().queue.map().insert(node_addr, thrd_ptr),
        !old(endpoint_map).spec_index(ep_ptr).view().queue.map().dom().contains(node_addr),
        final(endpoint_map).spec_index(ep_ptr).view().queue_state == if old(endpoint_map).spec_index(ep_ptr).view().queue.length == 0 {
            match waiting_state { ThreadState::SENDING | ThreadState::CALLING => EndpointState::SEND, _ => EndpointState::RECEIVE }
        } else {
            old(endpoint_map).spec_index(ep_ptr).view().queue_state
        },
{
    proof { endpoint_perms_wf_map(*old(endpoint_map)); endpoint_perms_wf_at(*old(endpoint_map), ep_ptr); }
    {
        let endpoint_mut = endpoint_map.borrow_mut_typed(ep_ptr, Ghost(lctx.endpoint_lock_map()), Tracked(lctx), endpoint_lock_perm);
        endpoint_mut.enqueue_waiter(thrd_ptr, waiting_state, node_addr, node_perm);
    }
    proof { ipc_enqueue_endpoint_waiter_eof(*old(endpoint_map), *endpoint_map, ep_ptr); assert(endpoint_map.lock_id_by_key(ep_ptr) == old(endpoint_map).lock_id_by_key(ep_ptr)) by { lock_id_fields_eq_imply_eq(); }; }
}

pub(super) fn ipc_schedule_endpoint_waiter(
    thread_map: &mut ThreadLockedMap, Tracked(lctx): Tracked<&LocalContext>, thrd_ptr: RwLockThreadPtr, wake_cpu: CpuId,
    current_thrd_ptr: RwLockThreadPtr, result: RetValueType, endpoint_node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>,
    thread_lock_perm: Tracked<&LockPerm>,
) -> (ret: (usize, Tracked<PointsTo<Node<RwLockThreadPtr>>>))
    requires
        index_valid(NUM_CPUS, wake_cpu),
        thread_perms_wf(*old(thread_map)),
        old(thread_map).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        old(thread_map).dom().contains(thrd_ptr),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        old(thread_map).dom().contains(current_thrd_ptr),
        current_thrd_ptr != thrd_ptr,
        thread_lock_perm.view().state() is WriteLock,
        thread_lock_perm.view().thread_id() == lctx.thread_id(),
        thread_lock_perm.view().lock_id() == old(thread_map).spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(thread_map).spec_index(thrd_ptr).view().state.is_endpoint_waiting(),
        endpoint_node_perm.view().is_init(),
        endpoint_node_perm.view().addr() == old(thread_map).spec_index(thrd_ptr).view().endpoint_linkedlist_node.addr(),
        endpoint_node_perm.view().value().view() == thrd_ptr,
    ensures
        forall|key: usize| #![trigger old(thread_map).view().spec_index(key)] #![trigger final(thread_map).view().spec_index(key)] old(thread_map).dom().contains(key) ==> {
            &&& final(thread_map).view().spec_index(key).is_init() == old(thread_map).view().spec_index(key).is_init()
            &&& final(thread_map).view().spec_index(key).addr() == old(thread_map).view().spec_index(key).addr()
        },
        final(thread_map).spec_index(thrd_ptr).is_init() == old(thread_map).spec_index(thrd_ptr).is_init(),
        final(thread_map).spec_index(thrd_ptr).view_rodata() == old(thread_map).spec_index(thrd_ptr).view_rodata(),
        final(thread_map).spec_index(thrd_ptr).view_ghost() == old(thread_map).spec_index(thrd_ptr).view_ghost(),
        thread_perms_wf(*final(thread_map)),
        final(thread_map).typed_lock_map_aligned(
            lctx.thread_lock_map().insert(thrd_ptr, TypedHeldLock { lock_id: final(thread_map).lock_id_by_key(thrd_ptr), mode: lctx.thread_lock_map().index(thrd_ptr).mode }), lctx.thread_id()),
        lctx.thread_lock_map().index(thrd_ptr).lock_id == old(thread_map).lock_id_by_key(thrd_ptr),
        final(thread_map).unchanged_except(old(thread_map), thrd_ptr),
        final(thread_map).spec_index(thrd_ptr).locking_thread() == old(thread_map).spec_index(thrd_ptr).locking_thread(),
        final(thread_map).spec_index(thrd_ptr).being_killed() == old(thread_map).spec_index(thrd_ptr).being_killed(),
        final(thread_map).spec_index(current_thrd_ptr) == old(thread_map).spec_index(current_thrd_ptr),
        final(thread_map).spec_index(thrd_ptr).view().non_ipc_fields_unchanged(&old(thread_map).spec_index(thrd_ptr).view()),
        final(thread_map).spec_index(thrd_ptr).view().caller == old(thread_map).spec_index(thrd_ptr).view().caller,
        final(thread_map).spec_index(thrd_ptr).view().syscall_progress == old(thread_map).spec_index(thrd_ptr).view().syscall_progress,
        final(thread_map).spec_index(thrd_ptr).view().callee == old(thread_map).spec_index(thrd_ptr).view().callee,
        final(thread_map).spec_index(thrd_ptr).view().state == (ThreadState::SCHEDULED { cpu_id: wake_cpu }),
        final(thread_map).spec_index(thrd_ptr).view().blocking_endpoint_ptr is None,
        final(thread_map).spec_index(thrd_ptr).view().blocking_endpoint_index is None,
        final(thread_map).spec_index(thrd_ptr).view().endpoint_linkedlist_node.is_init(),
        final(thread_map).spec_index(thrd_ptr).view().scheduler_linkedlist_node.is_init() == false,
        final(thread_map).spec_index(thrd_ptr).view().error_code == Some(result),
        final(thread_map).spec_index(thrd_ptr).view().ipc_payload is Empty,
        final(thread_map).spec_index(thrd_ptr).view().trap_frame == old(thread_map).spec_index(thrd_ptr).view().trap_frame,
        final(thread_map).spec_index(thrd_ptr).view().proc_linkedlist_node == old(thread_map).spec_index(thrd_ptr).view().proc_linkedlist_node,
        ret.0 == final(thread_map).spec_index(thrd_ptr).view().scheduler_linkedlist_node.addr(),
        ret.1.view().is_init(),
        ret.1.view().addr() == ret.0,
        ret.1.view().value().view() == thrd_ptr,
{
    proof { thread_perms_wf_map(*old(thread_map)); thread_perms_wf_at(*old(thread_map), thrd_ptr); }
    let ret = {
        let thread_mut = thread_map.borrow_mut_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), thread_lock_perm);
        thread_mut.endpoint_waiter_to_scheduled(thrd_ptr, wake_cpu, result, endpoint_node_perm)
    };
    proof { ipc_schedule_endpoint_waiter_eof(*old(thread_map), *thread_map, thrd_ptr); }
    ret
}

/// Moves the dequeued waiter `thrd_ptr` into transit with the running thread `current_thrd_ptr`, whose progress already names it.
pub(super) fn ipc_move_endpoint_waiter_to_transit(
    thread_map: &mut ThreadLockedMap, Tracked(lctx): Tracked<&LocalContext>, thrd_ptr: RwLockThreadPtr, current_thrd_ptr: RwLockThreadPtr,
    endpoint_node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>, thread_lock_perm: Tracked<&LockPerm>,
)
    requires
        thread_perms_wf(*old(thread_map)),
        old(thread_map).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        old(thread_map).dom().contains(thrd_ptr),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        old(thread_map).dom().contains(current_thrd_ptr),
        current_thrd_ptr != thrd_ptr,
        thread_lock_perm.view().state() is WriteLock,
        thread_lock_perm.view().thread_id() == lctx.thread_id(),
        thread_lock_perm.view().lock_id() == old(thread_map).spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(thread_map).spec_index(thrd_ptr).view().state is SENDING || old(thread_map).spec_index(thrd_ptr).view().state is RECEIVING,
        !old(thread_map).spec_index(thrd_ptr).being_killed(),
        old(thread_map).spec_index(current_thrd_ptr).view().state is RUNNING,
        progress_peer_of(old(thread_map).spec_index(current_thrd_ptr).view().syscall_progress.view()) == Some(thrd_ptr),
        endpoint_node_perm.view().is_init(),
        endpoint_node_perm.view().addr() == old(thread_map).spec_index(thrd_ptr).view().endpoint_linkedlist_node.addr(),
        endpoint_node_perm.view().value().view() == thrd_ptr,
    ensures
        final(thread_map).spec_index(thrd_ptr).view().error_code == old(thread_map).spec_index(thrd_ptr).view().error_code,
        final(thread_map).spec_index(thrd_ptr).view().trap_frame == old(thread_map).spec_index(thrd_ptr).view().trap_frame,
        thread_perms_wf(*final(thread_map)),
        final(thread_map).typed_lock_map_aligned(
            lctx.thread_lock_map().insert(thrd_ptr, TypedHeldLock { lock_id: final(thread_map).lock_id_by_key(thrd_ptr), mode: lctx.thread_lock_map().index(thrd_ptr).mode }), lctx.thread_id()),
        lctx.thread_lock_map().index(thrd_ptr).lock_id == old(thread_map).lock_id_by_key(thrd_ptr),
        final(thread_map).unchanged_except(old(thread_map), thrd_ptr),
        final(thread_map).spec_index(thrd_ptr).locking_thread() == old(thread_map).spec_index(thrd_ptr).locking_thread(),
        final(thread_map).spec_index(thrd_ptr).being_killed() == old(thread_map).spec_index(thrd_ptr).being_killed(),
        final(thread_map).spec_index(thrd_ptr).view_ghost() == old(thread_map).spec_index(thrd_ptr).view_ghost(),
        final(thread_map).spec_index(current_thrd_ptr) == old(thread_map).spec_index(current_thrd_ptr),
        final(thread_map).spec_index(thrd_ptr).view().non_ipc_fields_unchanged(&old(thread_map).spec_index(thrd_ptr).view()),
        final(thread_map).spec_index(thrd_ptr).view().caller == old(thread_map).spec_index(thrd_ptr).view().caller,
        final(thread_map).spec_index(thrd_ptr).view().syscall_progress == old(thread_map).spec_index(thrd_ptr).view().syscall_progress,
        final(thread_map).spec_index(thrd_ptr).view().callee == old(thread_map).spec_index(thrd_ptr).view().callee,
        final(thread_map).spec_index(thrd_ptr).view().state
            == (ThreadState::IPC_TRANSIT { partner: current_thrd_ptr, wait: if old(thread_map).spec_index(thrd_ptr).view().state is SENDING { IpcWait::Send } else { IpcWait::Receive } }),
        final(thread_map).spec_index(thrd_ptr).view().blocking_endpoint_ptr is None,
        final(thread_map).spec_index(thrd_ptr).view().blocking_endpoint_index is None,
        final(thread_map).spec_index(thrd_ptr).view().endpoint_linkedlist_node.is_init(),
        final(thread_map).spec_index(thrd_ptr).view().scheduler_linkedlist_node == old(thread_map).spec_index(thrd_ptr).view().scheduler_linkedlist_node,
        final(thread_map).spec_index(thrd_ptr).view().ipc_payload == old(thread_map).spec_index(thrd_ptr).view().ipc_payload,
{
    proof { thread_perms_wf_map(*old(thread_map)); thread_perms_wf_at(*old(thread_map), thrd_ptr); }
    {
        let thread_mut = thread_map.borrow_mut_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), thread_lock_perm);
        thread_mut.endpoint_waiter_to_ipc_transit(thrd_ptr, current_thrd_ptr, endpoint_node_perm);
    }
    proof { ipc_move_endpoint_waiter_to_transit_eof(*old(thread_map), *thread_map, thrd_ptr, current_thrd_ptr); }
}

/// Schedules the transit peer `thrd_ptr` on `wake_cpu` with the rendezvous result.
pub(super) fn ipc_schedule_transit_peer(
    thread_map: &mut ThreadLockedMap, Tracked(lctx): Tracked<&LocalContext>, thrd_ptr: RwLockThreadPtr, wake_cpu: CpuId,
    current_thrd_ptr: RwLockThreadPtr, result: RetValueType, thread_lock_perm: Tracked<&LockPerm>,
) -> (ret: (usize, Tracked<PointsTo<Node<RwLockThreadPtr>>>))
    requires
        index_valid(NUM_CPUS, wake_cpu),
        thread_perms_wf(*old(thread_map)),
        old(thread_map).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        old(thread_map).dom().contains(thrd_ptr),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        old(thread_map).dom().contains(current_thrd_ptr),
        current_thrd_ptr != thrd_ptr,
        thread_lock_perm.view().state() is WriteLock,
        thread_lock_perm.view().thread_id() == lctx.thread_id(),
        thread_lock_perm.view().lock_id() == old(thread_map).spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(thread_map).spec_index(thrd_ptr).view().state is IPC_TRANSIT,
    ensures
        final(thread_map).spec_index(thrd_ptr).view().trap_frame == old(thread_map).spec_index(thrd_ptr).view().trap_frame,
        thread_perms_wf(*final(thread_map)),
        final(thread_map).typed_lock_map_aligned(
            lctx.thread_lock_map().insert(thrd_ptr, TypedHeldLock { lock_id: final(thread_map).lock_id_by_key(thrd_ptr), mode: lctx.thread_lock_map().index(thrd_ptr).mode }), lctx.thread_id()),
        lctx.thread_lock_map().index(thrd_ptr).lock_id == old(thread_map).lock_id_by_key(thrd_ptr),
        final(thread_map).unchanged_except(old(thread_map), thrd_ptr),
        final(thread_map).spec_index(thrd_ptr).locking_thread() == old(thread_map).spec_index(thrd_ptr).locking_thread(),
        final(thread_map).spec_index(thrd_ptr).being_killed() == old(thread_map).spec_index(thrd_ptr).being_killed(),
        final(thread_map).spec_index(thrd_ptr).view_ghost() == old(thread_map).spec_index(thrd_ptr).view_ghost(),
        final(thread_map).spec_index(current_thrd_ptr) == old(thread_map).spec_index(current_thrd_ptr),
        final(thread_map).spec_index(thrd_ptr).view().non_ipc_fields_unchanged(&old(thread_map).spec_index(thrd_ptr).view()),
        final(thread_map).spec_index(thrd_ptr).view().caller == old(thread_map).spec_index(thrd_ptr).view().caller,
        final(thread_map).spec_index(thrd_ptr).view().syscall_progress == old(thread_map).spec_index(thrd_ptr).view().syscall_progress,
        final(thread_map).spec_index(thrd_ptr).view().callee == old(thread_map).spec_index(thrd_ptr).view().callee,
        final(thread_map).spec_index(thrd_ptr).view().state == (ThreadState::SCHEDULED { cpu_id: wake_cpu }),
        final(thread_map).spec_index(thrd_ptr).view().blocking_endpoint_ptr is None,
        final(thread_map).spec_index(thrd_ptr).view().blocking_endpoint_index is None,
        final(thread_map).spec_index(thrd_ptr).view().endpoint_linkedlist_node.is_init(),
        final(thread_map).spec_index(thrd_ptr).view().scheduler_linkedlist_node.is_init() == false,
        final(thread_map).spec_index(thrd_ptr).view().error_code == Some(result),
        final(thread_map).spec_index(thrd_ptr).view().ipc_payload is Empty,
        ret.0 == final(thread_map).spec_index(thrd_ptr).view().scheduler_linkedlist_node.addr(),
        ret.1.view().is_init(),
        ret.1.view().addr() == ret.0,
        ret.1.view().value().view() == thrd_ptr,
{
    proof { thread_perms_wf_map(*old(thread_map)); thread_perms_wf_at(*old(thread_map), thrd_ptr); }
    let ret = {
        let thread_mut = thread_map.borrow_mut_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), thread_lock_perm);
        thread_mut.ipc_transit_to_scheduled(thrd_ptr, wake_cpu, result)
    };
    proof { ipc_schedule_transit_peer_eof(*old(thread_map), *thread_map, thrd_ptr); }
    ret
}

pub(super) fn ipc_dequeue_endpoint_waiter(endpoint_map: &mut EndpointLockedMap, Tracked(lctx): Tracked<&LocalContext>, ep_ptr: RwLockEndpointPtr, thrd_ptr: RwLockThreadPtr, endpoint_lock_perm: Tracked<&LockPerm>) -> (ret: (usize, Tracked<PointsTo<Node<RwLockThreadPtr>>>))
    requires
        endpoint_perms_wf(*old(endpoint_map)),
        old(endpoint_map).typed_lock_map_aligned(lctx.endpoint_lock_map(), lctx.thread_id()),
        old(endpoint_map).dom().contains(ep_ptr),
        typed_lock_map_contains_mode(lctx.endpoint_lock_map(), ep_ptr, TypedLockMode::Write),
        endpoint_lock_perm.view().state() is WriteLock,
        endpoint_lock_perm.view().thread_id() == lctx.thread_id(),
        endpoint_lock_perm.view().lock_id() == old(endpoint_map).spec_index(ep_ptr).locking_thread()->Write_lock_id,
        old(endpoint_map).spec_index(ep_ptr).view().queue.len() != 0,
        old(endpoint_map).spec_index(ep_ptr).view().queue.view().spec_index(0) == thrd_ptr,
    ensures
        forall|key: usize| #![trigger old(endpoint_map).view().spec_index(key)] #![trigger final(endpoint_map).view().spec_index(key)] old(endpoint_map).dom().contains(key) ==> {
            &&& final(endpoint_map).view().spec_index(key).is_init() == old(endpoint_map).view().spec_index(key).is_init()
            &&& final(endpoint_map).view().spec_index(key).addr() == old(endpoint_map).view().spec_index(key).addr()
        },
        final(endpoint_map).spec_index(ep_ptr).is_init() == old(endpoint_map).spec_index(ep_ptr).is_init(),
        final(endpoint_map).spec_index(ep_ptr).view_rodata() == old(endpoint_map).spec_index(ep_ptr).view_rodata(),
        final(endpoint_map).spec_index(ep_ptr).view_ghost() == old(endpoint_map).spec_index(ep_ptr).view_ghost(),
        final(endpoint_map).spec_index(ep_ptr).being_killed() == old(endpoint_map).spec_index(ep_ptr).being_killed(),
        final(endpoint_map).spec_index(ep_ptr).view().queue.wf(),
        final(endpoint_map).spec_index(ep_ptr).view().queue.container_depth == old(endpoint_map).spec_index(ep_ptr).view().queue.container_depth,
        final(endpoint_map).spec_index(ep_ptr).view().queue.lock_minor() == old(endpoint_map).spec_index(ep_ptr).view().queue.lock_minor(),
        final(endpoint_map).spec_index(ep_ptr).view().queue.length as int == old(endpoint_map).spec_index(ep_ptr).view().queue.length as int - 1,
        final(endpoint_map).spec_index(ep_ptr).view().queue.dom() == old(endpoint_map).spec_index(ep_ptr).view().queue.dom().remove(ret.0),
        endpoint_perms_wf(*final(endpoint_map)),
        final(endpoint_map).typed_lock_map_aligned(lctx.endpoint_lock_map(), lctx.thread_id()),
        final(endpoint_map).unchanged_except(old(endpoint_map), ep_ptr),
        final(endpoint_map).spec_index(ep_ptr).locking_thread() == old(endpoint_map).spec_index(ep_ptr).locking_thread(),
        final(endpoint_map).lock_id_by_key(ep_ptr) == old(endpoint_map).lock_id_by_key(ep_ptr),
        final(endpoint_map).spec_index(ep_ptr).view().rf_counter == old(endpoint_map).spec_index(ep_ptr).view().rf_counter,
        final(endpoint_map).spec_index(ep_ptr).view().owning_threads == old(endpoint_map).spec_index(ep_ptr).view().owning_threads,
        final(endpoint_map).spec_index(ep_ptr).view().owning_container == old(endpoint_map).spec_index(ep_ptr).view().owning_container,
        final(endpoint_map).spec_index(ep_ptr).view().queue.view() == old(endpoint_map).spec_index(ep_ptr).view().queue.view().skip(1),
        final(endpoint_map).spec_index(ep_ptr).view().queue.map() == old(endpoint_map).spec_index(ep_ptr).view().queue.map().remove(ret.0),
        final(endpoint_map).spec_index(ep_ptr).view().queue_state == old(endpoint_map).spec_index(ep_ptr).view().queue_state,
        ret.1.view().is_init(),
        ret.1.view().addr() == ret.0,
        ret.1.view().value().view() == thrd_ptr,
        old(endpoint_map).spec_index(ep_ptr).view().queue.map().dom().contains(ret.0),
        old(endpoint_map).spec_index(ep_ptr).view().queue.map().spec_index(ret.0) == thrd_ptr,
        !final(endpoint_map).spec_index(ep_ptr).view().queue.view().contains(thrd_ptr),
        forall|t_ptr: RwLockThreadPtr| #![trigger old(endpoint_map).spec_index(ep_ptr).view().queue.view().contains(t_ptr)] #![trigger final(endpoint_map).spec_index(ep_ptr).view().queue.view().contains(t_ptr)]
            old(endpoint_map).spec_index(ep_ptr).view().queue.view().contains(t_ptr) && t_ptr != thrd_ptr ==>
                final(endpoint_map).spec_index(ep_ptr).view().queue.view().contains(t_ptr),
        forall|t_ptr: RwLockThreadPtr| #![trigger old(endpoint_map).spec_index(ep_ptr).view().queue.view().contains(t_ptr)] #![trigger final(endpoint_map).spec_index(ep_ptr).view().queue.view().contains(t_ptr)]
            final(endpoint_map).spec_index(ep_ptr).view().queue.view().contains(t_ptr) ==>
                old(endpoint_map).spec_index(ep_ptr).view().queue.view().contains(t_ptr),
{
    proof { endpoint_perms_wf_map(*old(endpoint_map)); endpoint_perms_wf_at(*old(endpoint_map), ep_ptr); }
    let ret = {
        let endpoint_mut = endpoint_map.borrow_mut_typed(ep_ptr, Ghost(lctx.endpoint_lock_map()), Tracked(lctx), endpoint_lock_perm);
        endpoint_mut.dequeue_waiter(thrd_ptr)
    };
    proof { ipc_dequeue_endpoint_waiter_eof(*old(endpoint_map), *endpoint_map, ep_ptr); }
    ret
}
} // verus!
