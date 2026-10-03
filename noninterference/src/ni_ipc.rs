use vstd::prelude::*;
use crate::*;
use veriflat_syscall_ipc::syscall_ipc::syscall_ipc_spec::*;

verus! {
/// Blocking a running thread of `a` on an endpoint it holds leaves the view of `b` unchanged.
pub proof fn ipc_block_step_lr(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers,
    flushed_default_pcid: bool, a: RwLockContainerPtr, b: RwLockContainerPtr,
)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        ipc_block_step_pre(old_u, cpu_id, endpoint_index, waiting_state),
        ipc_block_step(old_u, new_u, cpu_id, endpoint_index, waiting_state, payload, regs, flushed_default_pcid),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kernel_u_ipc_block_changed); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_endpoint_ownership_wf); }

/// The step of `ipc_block_step_lr` preserves isolation.
pub proof fn ipc_block_step_iso(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers,
    flushed_default_pcid: bool, a: RwLockContainerPtr, b: RwLockContainerPtr,
)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        ipc_block_step_pre(old_u, cpu_id, endpoint_index, waiting_state),
        ipc_block_step(old_u, new_u, cpu_id, endpoint_index, waiting_state, payload, regs, flushed_default_pcid),
    ensures isolated(new_u, a, b),
{ reveal(kernel_u_ipc_block_changed); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_endpoint_ownership_wf); }

/// A rendezvous of a running thread of `a` with the queue head of an endpoint it holds touches only that
/// endpoint, the head, which is outside `b`, and a cpu moving between the head's container and `a`, so it
/// leaves the view of `b` unchanged.
pub proof fn ipc_rendezvous_step_lr(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad,
    a: RwLockContainerPtr, b: RwLockContainerPtr,
)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        ipc_rendezvous_step_pre(old_u, cpu_id, endpoint_index, waiting_state, payload),
        ipc_rendezvous_step(old_u, new_u, cpu_id, endpoint_index, waiting_state, payload),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kernel_u_ipc_rendezvous_changed); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_endpoint_ownership_wf); }

/// The step of `ipc_rendezvous_step_lr` preserves isolation.
pub proof fn ipc_rendezvous_step_iso(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad,
    a: RwLockContainerPtr, b: RwLockContainerPtr,
)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        ipc_rendezvous_step_pre(old_u, cpu_id, endpoint_index, waiting_state, payload),
        ipc_rendezvous_step(old_u, new_u, cpu_id, endpoint_index, waiting_state, payload),
    ensures isolated(new_u, a, b),
{ reveal(kernel_u_ipc_rendezvous_changed); reveal(kernel_u_endpoint_ownership_wf); }

/// Moving the queue head of an endpoint a running thread of `a` holds into transit locks only objects of `a`
/// and that head, which is outside `b`, and records it as the thread's peer.
pub proof fn ipc_endpoint_transit_step_lr(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload_index: EndpointIdx,
    a: RwLockContainerPtr, b: RwLockContainerPtr,
)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        ipc_endpoint_transit_step_pre(old_u, cpu_id, endpoint_index, waiting_state, payload_index),
        ipc_endpoint_transit_step(old_u, new_u, cpu_id, endpoint_index, waiting_state, payload_index),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(ipc_endpoint_transit_step_pre); reveal(ipc_rendezvous_step_pre); reveal(ipc_step_pre); reveal(ipc_endpoint_transit_step);
    reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_endpoint_ownership_wf);
}

/// The step of `ipc_endpoint_transit_step_lr` preserves isolation.
pub proof fn ipc_endpoint_transit_step_iso(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload_index: EndpointIdx,
    a: RwLockContainerPtr, b: RwLockContainerPtr,
)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        ipc_endpoint_transit_step_pre(old_u, cpu_id, endpoint_index, waiting_state, payload_index),
        ipc_endpoint_transit_step(old_u, new_u, cpu_id, endpoint_index, waiting_state, payload_index),
    ensures isolated(new_u, a, b),
{
    reveal(ipc_endpoint_transit_step_pre); reveal(ipc_rendezvous_step_pre); reveal(ipc_step_pre); reveal(ipc_endpoint_transit_step);
    reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_endpoint_ownership_wf);
}

/// Finishing an endpoint transfer on a cpu of `a` hands an endpoint between its running thread and its
/// in-transit `peer` outside `b`. `payload` is the endpoint at the peer's payload descriptor; when the
/// running thread receives from a peer outside `a`, no thread of `b` holds `payload`.
pub proof fn ipc_endpoint_finish_step_lr(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, peer: RwLockThreadPtr, payload: RwLockEndpointPtr, a: RwLockContainerPtr, b: RwLockContainerPtr,
)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        ipc_endpoint_finish_step_pre(old_u, cpu_id), ipc_endpoint_finish_step(old_u, new_u, cpu_id),
        peer == old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].syscall_progress->Some_0->IpcEndpoint_peer,
        payload == old_u.thread_map[peer].endpoint_descriptors[old_u.thread_map[peer].ipc_payload->Endpoint_endpoint_index as int]->Some_0,
        !old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].syscall_progress->Some_0->IpcEndpoint_caller_sends
            && !in_domain(old_u, a, old_u.thread_map[peer].owning_container) ==> forall|t: RwLockThreadPtr, i: EndpointIdx|
            #![trigger old_u.endpoint_map[payload].owning_threads.contains((t, i))]
            old_u.endpoint_map[payload].owning_threads.contains((t, i)) ==> !in_domain(old_u, b, old_u.thread_map[t].owning_container),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(ipc_endpoint_finish_step_pre); reveal(ipc_endpoint_finish_step); reveal(kernel_u_cpu_ownership_wf);
    reveal(kernel_u_endpoint_ownership_wf); reveal(kernel_u_container_tree_wf);
}

/// The step of `ipc_endpoint_finish_step_lr` preserves isolation. When the running thread receives from a
/// peer outside `a`, no thread of `b` holds or waits on `payload`, and no peer of a rendezvous `b` has in
/// flight waits on it.
pub proof fn ipc_endpoint_finish_step_iso(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, peer: RwLockThreadPtr, payload: RwLockEndpointPtr, a: RwLockContainerPtr, b: RwLockContainerPtr,
)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        ipc_endpoint_finish_step_pre(old_u, cpu_id), ipc_endpoint_finish_step(old_u, new_u, cpu_id),
        peer == old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].syscall_progress->Some_0->IpcEndpoint_peer,
        payload == old_u.thread_map[peer].endpoint_descriptors[old_u.thread_map[peer].ipc_payload->Endpoint_endpoint_index as int]->Some_0,
        !old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].syscall_progress->Some_0->IpcEndpoint_caller_sends
            && !in_domain(old_u, a, old_u.thread_map[peer].owning_container) ==> {
            &&& forall|t: RwLockThreadPtr, i: EndpointIdx| #![trigger old_u.endpoint_map[payload].owning_threads.contains((t, i))]
                old_u.endpoint_map[payload].owning_threads.contains((t, i)) ==> !in_domain(old_u, b, old_u.thread_map[t].owning_container)
            &&& forall|j: int| #![trigger old_u.endpoint_map[payload].queue[j]]
                0 <= j < old_u.endpoint_map[payload].queue.len() ==> !in_domain(old_u, b, old_u.thread_map[old_u.endpoint_map[payload].queue[j]].owning_container)
            &&& forall|t: RwLockThreadPtr| #![trigger old_u.thread_map[t].syscall_progress]
                old_u.thread_map.dom().contains(t) && in_domain(old_u, b, old_u.thread_map[t].owning_container) && progress_peer(old_u.thread_map[t].syscall_progress) is Some
                ==> old_u.thread_map[progress_peer(old_u.thread_map[t].syscall_progress)->Some_0].blocking_endpoint_ptr != Some(payload)
        },
    ensures isolated(new_u, a, b),
{
    reveal(ipc_endpoint_finish_step_pre); reveal(ipc_endpoint_finish_step); reveal(kernel_u_cpu_ownership_wf);
    reveal(kernel_u_endpoint_ownership_wf); reveal(kernel_u_container_tree_wf);
}

/// Entering a pages rendezvous on a cpu of `a` locks only objects of `a`, the queue head of a channel its
/// running thread holds, which is outside `b`, and that channel, and records the head as its peer.
pub proof fn ipc_pages_enter_step_lr(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, range: VaRange4K,
    a: RwLockContainerPtr, b: RwLockContainerPtr,
)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        ipc_pages_enter_step_pre(old_u, cpu_id, endpoint_index, waiting_state, range), ipc_pages_enter_step(old_u, new_u, cpu_id, endpoint_index, waiting_state, range),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(ipc_pages_enter_step_pre); reveal(ipc_rendezvous_step_pre); reveal(ipc_step_pre); reveal(ipc_pages_enter_step);
    reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_endpoint_ownership_wf);
}

/// The step of `ipc_pages_enter_step_lr` preserves isolation.
pub proof fn ipc_pages_enter_step_iso(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, range: VaRange4K,
    a: RwLockContainerPtr, b: RwLockContainerPtr,
)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        ipc_pages_enter_step_pre(old_u, cpu_id, endpoint_index, waiting_state, range), ipc_pages_enter_step(old_u, new_u, cpu_id, endpoint_index, waiting_state, range),
    ensures isolated(new_u, a, b),
{
    reveal(ipc_pages_enter_step_pre); reveal(ipc_rendezvous_step_pre); reveal(ipc_step_pre); reveal(ipc_pages_enter_step);
    reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_endpoint_ownership_wf);
}

/// Locking the page tables of a pages rendezvous on a cpu of `a` locks tables of `a` and of its peer outside `b`.
pub proof fn ipc_pages_lock_tables_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        ipc_pages_lock_tables_step_pre(old_u, cpu_id), ipc_pages_lock_tables_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(ipc_pages_lock_tables_step_pre); reveal(ipc_pages_lock_tables_step); reveal(kernel_u_cpu_ownership_wf);
    reveal(kernel_u_thread_ownership_wf);
}

/// The step of `ipc_pages_lock_tables_step_lr` preserves isolation.
pub proof fn ipc_pages_lock_tables_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        ipc_pages_lock_tables_step_pre(old_u, cpu_id), ipc_pages_lock_tables_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(ipc_pages_lock_tables_step_pre); reveal(ipc_pages_lock_tables_step); reveal(kernel_u_thread_ownership_wf); }

/// Checking a pages rendezvous on a cpu of `a` records its result and may unlock tables of `a` and of its
/// peer outside `b`.
pub proof fn ipc_pages_check_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        ipc_pages_check_step_pre(old_u, cpu_id), ipc_pages_check_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(ipc_pages_check_step_pre); reveal(ipc_pages_check_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// The step of `ipc_pages_check_step_lr` preserves isolation.
pub proof fn ipc_pages_check_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        ipc_pages_check_step_pre(old_u, cpu_id), ipc_pages_check_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(ipc_pages_check_step_pre); reveal(ipc_pages_check_step); reveal(kernel_u_cpu_ownership_wf); }

/// Unlocking the page tables of a shared pages rendezvous on a cpu of `a` unlocks tables of `a` and of its
/// peer outside `b`.
pub proof fn ipc_pages_unlock_tables_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        ipc_pages_unlock_tables_step_pre(old_u, cpu_id), ipc_pages_unlock_tables_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(ipc_pages_unlock_tables_step_pre); reveal(ipc_pages_unlock_tables_step); reveal(kernel_u_cpu_ownership_wf);
    reveal(kernel_u_thread_ownership_wf);
}

/// The step of `ipc_pages_unlock_tables_step_lr` preserves isolation.
pub proof fn ipc_pages_unlock_tables_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        ipc_pages_unlock_tables_step_pre(old_u, cpu_id), ipc_pages_unlock_tables_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(ipc_pages_unlock_tables_step_pre); reveal(ipc_pages_unlock_tables_step); reveal(kernel_u_cpu_ownership_wf);
    reveal(kernel_u_thread_ownership_wf);
}

/// Finishing a pages rendezvous on a cpu of `a` schedules its peer outside `b` and dequeues it from a channel
/// that `b` neither owns nor holds.
pub proof fn ipc_pages_finish_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        ipc_pages_finish_step_pre(old_u, cpu_id), ipc_pages_finish_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(ipc_pages_finish_step_pre); reveal(ipc_pages_finish_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_endpoint_ownership_wf); }

/// The step of `ipc_pages_finish_step_lr` preserves isolation.
pub proof fn ipc_pages_finish_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        ipc_pages_finish_step_pre(old_u, cpu_id), ipc_pages_finish_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(ipc_pages_finish_step_pre); reveal(ipc_pages_finish_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_endpoint_ownership_wf); }

/// The IPC entry rejection of a running cpu of `b` reads only the view of `b` and whether the head of the
/// endpoint queue, the peer, is killed.
pub proof fn ipc_entry_result_oc(
    u1: KernelU, u2: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, blocking: bool, b: RwLockContainerPtr,
)
    requires
        kernel_u_ownership_wf(u1), steps_in_domain(u1, cpu_id, b), u1.cpu_array[cpu_id as int].state is Running, edp_idx_valid(endpoint_index),
        domain_view(u1, b) =~~= domain_view(u2, b),
        ({
            let thread = u1.thread_map[u1.cpu_array[cpu_id as int].current_thread->Some_0];
            let peer = u1.endpoint_map[thread.endpoint_descriptors[endpoint_index as int]->Some_0].queue[0];
            u1.thread_map[peer].killed == u2.thread_map[peer].killed
        }),
    ensures ipc_entry_result(u1, cpu_id, endpoint_index, waiting_state, blocking) == ipc_entry_result(u2, cpu_id, endpoint_index, waiting_state, blocking),
{
    reveal(ipc_entry_result);
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        let cpu = u1.cpu_array[cpu_id as int];
        let thread_ptr = cpu.current_thread->Some_0;
        &&& v1.cpus[cpu_id as int] == Some(cpu)
        &&& v1.processes.dom().contains(cpu.current_process->Some_0) && v1.processes[cpu.current_process->Some_0] == v2.processes[cpu.current_process->Some_0]
        &&& v1.threads.dom().contains(thread_ptr) && v1.threads[thread_ptr] == v2.threads[thread_ptr]
        &&& v1.held_endpoints.dom().contains(thread_ptr) && v1.held_endpoints[thread_ptr][endpoint_index as int] == v2.held_endpoints[thread_ptr][endpoint_index as int]
    }) by { reveal(kernel_u_cpu_ownership_wf); };
}

/// The rendezvous result of a cpu of `b` reads only the view of `b`, the queue head it meets, and the cpu a
/// Cpu payload hands over.
pub proof fn ipc_rendezvous_result_oc(
    u1: KernelU, u2: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, b: RwLockContainerPtr,
)
    requires
        kernel_u_ownership_wf(u1), steps_in_domain(u1, cpu_id, b), ipc_rendezvous_step_pre(u1, cpu_id, endpoint_index, waiting_state, payload),
        domain_view(u1, b) =~~= domain_view(u2, b),
        ({
            let thread = u1.thread_map[u1.cpu_array[cpu_id as int].current_thread->Some_0];
            let peer_ptr = u1.endpoint_map[thread.endpoint_descriptors[endpoint_index as int]->Some_0].queue[0];
            let sent = if waiting_state is SENDING { payload } else { u1.thread_map[peer_ptr].ipc_payload };
            &&& u1.thread_map[peer_ptr] == u2.thread_map[peer_ptr]
            &&& sent matches IPCPayLoad::Cpu { cpu_id: transfer } ==> u1.cpu_array[transfer as int] == u2.cpu_array[transfer as int]
        }),
    ensures ipc_rendezvous_result(u1, cpu_id, endpoint_index, waiting_state, payload) == ipc_rendezvous_result(u2, cpu_id, endpoint_index, waiting_state, payload),
{
    reveal(ipc_rendezvous_step_pre); reveal(ipc_step_pre);
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        let cpu = u1.cpu_array[cpu_id as int];
        let thread_ptr = cpu.current_thread->Some_0;
        &&& v1.cpus[cpu_id as int] == Some(cpu)
        &&& v1.threads.dom().contains(thread_ptr) && v1.threads[thread_ptr] == v2.threads[thread_ptr]
        &&& v1.held_endpoints.dom().contains(thread_ptr) && v1.held_endpoints[thread_ptr][endpoint_index as int] == v2.held_endpoints[thread_ptr][endpoint_index as int]
    }) by { reveal(kernel_u_cpu_ownership_wf); };
}

/// The endpoint transfer result of a cpu of `b` reads only the view of `b`, the peer, and either the peer's
/// payload endpoint when the peer sends or the peer's container when the caller sends.
pub proof fn ipc_endpoint_finish_result_oc(u1: KernelU, u2: KernelU, cpu_id: CpuId, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u1), steps_in_domain(u1, cpu_id, b), ipc_endpoint_finish_step_pre(u1, cpu_id), domain_view(u1, b) =~~= domain_view(u2, b),
        ({
            let progress = u1.thread_map[u1.cpu_array[cpu_id as int].current_thread->Some_0].syscall_progress->Some_0;
            let peer = u1.thread_map[progress->IpcEndpoint_peer];
            let source_endpoint = peer.endpoint_descriptors[peer.ipc_payload->Endpoint_endpoint_index as int]->Some_0;
            &&& peer == u2.thread_map[progress->IpcEndpoint_peer]
            &&& progress->IpcEndpoint_caller_sends ==> u1.container_map[peer.owning_container] == u2.container_map[peer.owning_container]
            &&& !progress->IpcEndpoint_caller_sends ==> u1.endpoint_map[source_endpoint] == u2.endpoint_map[source_endpoint]
        }),
    ensures ipc_endpoint_finish_result(u1, cpu_id) == ipc_endpoint_finish_result(u2, cpu_id),
{
    reveal(ipc_endpoint_finish_step_pre);
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        let cpu = u1.cpu_array[cpu_id as int];
        let thread_ptr = cpu.current_thread->Some_0;
        let thread = u1.thread_map[thread_ptr];
        let source_index = thread.syscall_progress->Some_0->IpcEndpoint_payload_index;
        &&& v1.cpus[cpu_id as int] == Some(cpu)
        &&& v1.threads.dom().contains(thread_ptr) && v1.threads[thread_ptr] == v2.threads[thread_ptr]
        &&& v1.held_endpoints.dom().contains(thread_ptr) && v1.held_endpoints[thread_ptr][source_index as int] == v2.held_endpoints[thread_ptr][source_index as int]
        &&& thread.owning_container == cpu.owning_container && v1.containers.dom().contains(thread.owning_container)
        &&& v1.containers[thread.owning_container] == v2.containers[thread.owning_container]
    }) by { reveal(kernel_u_cpu_ownership_wf); };
}

/// The pages check result of a cpu of `b` reads only the view of `b`, the peer, the peer's process, and the
/// peer's container.
pub proof fn ipc_pages_check_result_oc(u1: KernelU, u2: KernelU, cpu_id: CpuId, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u1), kernel_u_ownership_wf(u2), steps_in_domain(u1, cpu_id, b), ipc_pages_check_step_pre(u1, cpu_id),
        domain_view(u1, b) =~~= domain_view(u2, b),
        ({
            let peer_ptr = u1.thread_map[u1.cpu_array[cpu_id as int].current_thread->Some_0].syscall_progress->Some_0->IpcPages_peer;
            let peer = u1.thread_map[peer_ptr];
            &&& u2.thread_map.dom().contains(peer_ptr) && peer == u2.thread_map[peer_ptr]
            &&& u1.process_map[peer.owning_proc] == u2.process_map[peer.owning_proc]
            &&& u1.container_map[peer.owning_container] == u2.container_map[peer.owning_container]
        }),
    ensures ipc_pages_check_result(u1, cpu_id) == ipc_pages_check_result(u2, cpu_id),
{
    reveal(kernel_u_container_tree_wf);
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        let cpu = u1.cpu_array[cpu_id as int];
        let thread_ptr = cpu.current_thread->Some_0;
        let thread = u1.thread_map[thread_ptr];
        let peer_container = u1.thread_map[thread.syscall_progress->Some_0->IpcPages_peer].owning_container;
        &&& v1.cpus[cpu_id as int] == Some(cpu)
        &&& v1.threads.dom().contains(thread_ptr) && v1.threads[thread_ptr] == v2.threads[thread_ptr]
        &&& v1.processes.dom().contains(thread.owning_proc) && v1.processes[thread.owning_proc] == v2.processes[thread.owning_proc]
        &&& thread.owning_container == cpu.owning_container && v1.containers.dom().contains(thread.owning_container)
        &&& v1.containers[thread.owning_container] == v2.containers[thread.owning_container]
        &&& u2.container_map.dom().contains(thread.owning_container)
        &&& u1.container_map.dom().contains(peer_container) && u2.container_map.dom().contains(peer_container)
    }) by { reveal(ipc_pages_check_step_pre); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); };
}
} // verus!
