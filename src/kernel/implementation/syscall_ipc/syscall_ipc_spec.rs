use vstd::prelude::*;
use crate::*;

verus! {
/// Blocking on `cpu_id` flushes the `(cpu_id, KERNEL_DEFAULT_PCID)` TLB entry when the kernel PCID is dirty.
pub open spec fn ipc_block_flushes_default_pcid(pre: KernelK, cpu_id: CpuId) -> bool {
    pre.pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).view().needflush
}

/// Return values that record exactly one rendezvous step for the Empty, Usize, Cpu, ReceiveCpu, and Pci payloads.
pub open spec fn ipc_rendezvous_ret(ret: RetValueType) -> bool {
    ||| ret is Success
    ||| ret is SuccessUsize
    ||| ret is ErrorIpcTypeMismatch
    ||| ret is ErrorCallAcrossContainers
    ||| ret is ErrorIpcSameContainer
    ||| ret is ErrorIpcCpuOwnerMismatch
    ||| ret is ErrorIpcCpuNotOff
    ||| ret is ErrorIpcSameProcess
    ||| ret is ErrorIpcPciOwnerMismatch
}

/// The rejection decided before any rendezvous from the state at entry: a cpu no longer Running or marked by a killer, a killed caller, a receive-call
/// caller that still holds a caller, a missing descriptor, an empty or same-direction queue (where a blocking
/// caller waits instead), or a killed queue head.
#[verifier::opaque]
pub open spec fn ipc_entry_result(pre: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, blocking: bool) -> Option<RetValueType> {
    let cpu = pre.cpu_array[cpu_id as int];
    let thread = pre.thread_map[cpu.current_thread->Some_0];
    let endpoint = pre.endpoint_map[thread.endpoint_descriptors[endpoint_index as int]->Some_0];
    if !(cpu.state is Running) || cpu.killed { Some(RetValueType::CpuIdle) }
    else if thread.killed { Some(RetValueType::ErrorThreadKilled) }
    else if waiting_state is RECEIVING_CALL && thread.caller is Some { Some(RetValueType::ErrorReplyOutOfPhase) }
    else if thread.endpoint_descriptors[endpoint_index as int] is None { Some(RetValueType::ErrorInvalidEndpoint) }
    else if endpoint.queue.len() == 0 || (endpoint.queue_state is SEND) == waiting_state.is_endpoint_send_waiting() {
        if blocking { Some(RetValueType::CpuIdle) } else if endpoint.queue.len() == 0 { Some(RetValueType::ErrorIpcNoPeer) } else { Some(RetValueType::ErrorIpcSameDirection) }
    } else if pre.thread_map[endpoint.queue[0]].killed { Some(RetValueType::ErrorIpcPeerKilled) }
    else { None }
}

/// The entry rejection that `ret` reports, or None when `ret` comes from a rendezvous.
pub open spec fn ipc_rejection(ret: RetValueType) -> Option<RetValueType> {
    if ret is CpuIdle || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcNoPeer
        || ret is ErrorIpcSameDirection || ret is ErrorIpcPeerKilled || ret is ErrorReplyOutOfPhase { Some(ret) } else { None }
}

/// A Pages call with an empty, overflowing, or invalid user range fails with Error before entering IPC.
pub open spec fn ipc_pages_args_invalid(va: VAddr, range: usize) -> bool {
    range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range)
}

/// The result written into the scheduled peer for the caller's `payload` and return value `ret`.
pub open spec fn ipc_peer_result(payload: IPCPayLoad, ret: RetValueType) -> RetValueType {
    if ret is Success {
        if payload is Cpu { RetValueType::SuccessUsize { value: payload->Cpu_cpu_id } } else { RetValueType::Success }
    } else if ret is SuccessUsize { RetValueType::Success } else { ret }
}

/// The Off CPU handed over by a successful CPU rendezvous and the receiving thread whose container takes it.
pub open spec fn ipc_cpu_transfer(old_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, payload: IPCPayLoad, ret: RetValueType) -> Option<(CpuId, RwLockThreadPtr)> {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread.unwrap();
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let endpoint = old_u.endpoint_map.spec_index(thread.endpoint_descriptors[endpoint_index as int].unwrap());
    if payload is Cpu && ret is Success { Some((payload->Cpu_cpu_id, endpoint.queue[0])) }
    else if payload is ReceiveCpu && ret is SuccessUsize { Some((ret->SuccessUsize_value, thread_ptr)) }
    else { None }
}

/// The PCI function handed over by a successful PCI rendezvous with its sending and receiving processes.
pub open spec fn ipc_pci_transfer(old_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, ret: RetValueType) -> Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)> {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread.unwrap());
    let peer = old_u.thread_map.spec_index(old_u.endpoint_map.spec_index(thread.endpoint_descriptors[endpoint_index as int].unwrap()).queue[0]);
    let sends = waiting_state is SENDING;
    match payload {
        IPCPayLoad::Pci { bus, dev, fun } if ret is Success => Some(((bus as usize, dev as usize, fun as usize),
            if sends { thread.owning_proc } else { peer.owning_proc }, if sends { peer.owning_proc } else { thread.owning_proc })),
        _ => None,
    }
}

/// The running thread on `cpu_id` has no syscall in progress, belongs to a live container, and holds a live
/// endpoint descriptor at `endpoint_index`; the cpu, the thread, and the endpoint are unlocked.
#[verifier::opaque]
pub open spec fn ipc_step_pre(old_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(cpu.current_thread.unwrap());
    let endpoint_ptr = thread.endpoint_descriptors[endpoint_index as int];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& edp_idx_valid(endpoint_index)
    &&& cpu.state is Running
    &&& cpu.current_process is Some
    &&& cpu.current_thread is Some
    &&& old_u.process_map.dom().contains(cpu.current_process.unwrap())
    &&& old_u.thread_map.dom().contains(cpu.current_thread.unwrap())
    &&& thread.lock_state is Unlocked
    &&& thread.syscall_progress is None
    &&& !thread.killed
    &&& thread.state == (ThreadState::RUNNING { cpu_id })
    &&& thread.owning_proc == cpu.current_process.unwrap()
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& endpoint_ptr is Some
    &&& old_u.endpoint_map.dom().contains(endpoint_ptr.unwrap())
    &&& old_u.endpoint_map.spec_index(endpoint_ptr.unwrap()).lock_state is Unlocked
    &&& !old_u.endpoint_map.spec_index(endpoint_ptr.unwrap()).queue.contains(cpu.current_thread.unwrap())
}

/// The endpoint queue is empty or waits in the caller's direction, so the caller blocks.
#[verifier::opaque]
pub open spec fn ipc_block_step_pre(old_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(cpu.current_thread.unwrap());
    let endpoint = old_u.endpoint_map.spec_index(thread.endpoint_descriptors[endpoint_index as int].unwrap());
    &&& ipc_step_pre(old_u, cpu_id, endpoint_index)
    &&& waiting_state.is_endpoint_waiting()
    &&& endpoint.queue.len() == 0 || (endpoint.queue_state is SEND) == waiting_state.is_endpoint_send_waiting()
}

/// User-visible blocking step: the caller waits on the endpoint with `payload` and its CPU goes idle.
pub open spec fn ipc_block_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread.unwrap();
    let endpoint_ptr = old_u.thread_map.spec_index(thread_ptr).endpoint_descriptors[endpoint_index as int].unwrap();
    kernel_u_ipc_block_changed(old_u, new_u, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid)
}

/// The unlocked endpoint queue head waits in the opposite direction, so the caller rendezvous with it; a CPU
/// rendezvous between different containers also needs both containers' cpu sets unlocked, a handover
/// needs the handed-over CPU unlocked, and a PCI handover of an attached function needs the sender's IOMMU table unlocked.
#[verifier::opaque]
pub open spec fn ipc_rendezvous_step_pre(old_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(cpu.current_thread.unwrap());
    let endpoint_ptr = thread.endpoint_descriptors[endpoint_index as int].unwrap();
    let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
    let peer = old_u.thread_map.spec_index(endpoint.queue[0]);
    let result = ipc_rendezvous_result(old_u, cpu_id, endpoint_index, waiting_state, payload);
    &&& ipc_step_pre(old_u, cpu_id, endpoint_index)
    &&& waiting_state.is_endpoint_waiting()
    &&& endpoint.queue.len() > 0
    &&& (endpoint.queue_state is SEND) != waiting_state.is_endpoint_send_waiting()
    &&& old_u.thread_map.dom().contains(endpoint.queue[0])
    &&& peer.lock_state is Unlocked
    &&& endpoint.queue[0] != cpu.current_thread.unwrap()
    &&& !peer.killed
    &&& peer.state.is_endpoint_waiting()
    &&& peer.blocking_endpoint_ptr == Some(endpoint_ptr)
    &&& old_u.container_map.dom().contains(peer.owning_container)
    &&& (payload is Cpu || payload is ReceiveCpu) && !(result is ErrorIpcTypeMismatch) && !(result is ErrorIpcSameContainer) ==> {
        &&& old_u.container_map[thread.owning_container].cpu_set_lock is Unlocked
        &&& old_u.container_map[peer.owning_container].cpu_set_lock is Unlocked
    }
    &&& ipc_cpu_transfer(old_u, cpu_id, endpoint_index, payload, result) matches Some((transfer, _)) ==> old_u.cpu_array[transfer as int].lock_state is Unlocked
    &&& ipc_pci_transfer(old_u, cpu_id, endpoint_index, waiting_state, payload, result) matches Some((bdf, sender, _)) ==> old_u.iommu_root_table.attached[bdf.0 as int][bdf.1 as int][bdf.2 as int]
        && old_u.process_map[sender].iommu_table is Some ==> old_u.process_map[sender].iommu_table->Some_0.lock_state is Unlocked
}

/// User-visible rendezvous step: the queue head is scheduled with the peer's side of the rendezvous result,
/// a successful CPU handover moves the Off CPU to the receiving thread's container, and a successful PCI
/// handover moves the detached function to the receiving process.
pub open spec fn ipc_rendezvous_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad) -> bool {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread.unwrap();
    let endpoint_ptr = old_u.thread_map.spec_index(thread_ptr).endpoint_descriptors[endpoint_index as int].unwrap();
    let result = ipc_rendezvous_result(old_u, cpu_id, endpoint_index, waiting_state, payload);
    kernel_u_ipc_rendezvous_changed(old_u, new_u, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, old_u.endpoint_map.spec_index(endpoint_ptr).queue[0], ipc_peer_result(payload, result),
        ipc_cpu_transfer(old_u, cpu_id, endpoint_index, payload, result), ipc_pci_transfer(old_u, cpu_id, endpoint_index, waiting_state, payload, result))
}

/// Ordinary IPC is one block/rendezvous transition, or a stuttering rejection; a cpu no longer Running or marked by a killer stutters with CpuIdle.
#[verifier::opaque]
pub open spec fn ipc_ordinary_syscall_trace(
    trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx,
    waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool, ret: RetValueType,
) -> bool {
    if ret is CpuIdle && (!(pre.cpu_array[cpu_id as int].state is Running) || pre.cpu_array[cpu_id as int].killed) {
        &&& trace.len() == 0
        &&& post == pre
    } else if ret is CpuIdle {
        &&& trace.len() == 1
        &&& trace[0].old_u == pre
        &&& trace[0].new_u == post
        &&& ipc_block_step_pre(pre, cpu_id, endpoint_index, waiting_state)
        &&& ipc_block_step(pre, post, cpu_id, endpoint_index, waiting_state, payload, regs, flushed_default_pcid)
    } else if ipc_rendezvous_ret(ret) {
        &&& trace.len() == 1
        &&& trace[0].old_u == pre
        &&& trace[0].new_u == post
        &&& ret == ipc_rendezvous_result(pre, cpu_id, endpoint_index, waiting_state, payload)
        &&& ipc_rendezvous_step_pre(pre, cpu_id, endpoint_index, waiting_state, payload)
        &&& ipc_rendezvous_step(pre, post, cpu_id, endpoint_index, waiting_state, payload)
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}
/// The endpoint queue head waits in the opposite direction with an Endpoint payload; the sender holds a
/// descriptor at its source index and the receiver's target index is free.
#[verifier::opaque]
pub open spec fn ipc_endpoint_transit_step_pre(old_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload_index: EndpointIdx) -> bool {
    let thread = old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread.unwrap()];
    let peer = old_u.thread_map[old_u.endpoint_map[thread.endpoint_descriptors[endpoint_index as int].unwrap()].queue[0]];
    let caller_sends = waiting_state is SENDING;
    let peer_index = peer.ipc_payload->Endpoint_endpoint_index;
    let sender = if caller_sends { thread } else { peer };
    let receiver = if caller_sends { peer } else { thread };
    &&& ipc_rendezvous_step_pre(old_u, cpu_id, endpoint_index, waiting_state, IPCPayLoad::Endpoint { endpoint_index: payload_index })
    &&& edp_idx_valid(payload_index)
    &&& peer.state == if caller_sends { ThreadState::RECEIVING } else { ThreadState::SENDING }
    &&& peer.ipc_payload is Endpoint
    &&& sender.endpoint_descriptors[(if caller_sends { payload_index } else { peer_index }) as int] is Some
    &&& receiver.endpoint_descriptors[(if caller_sends { peer_index } else { payload_index }) as int] is None
}

/// Write-lock the cpu, the caller, and the queue head, move the head into transit with the caller as its partner, and record it
/// in the caller's progress with the direction and `payload_index`.
#[verifier::opaque]
pub open spec fn ipc_endpoint_transit_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload_index: EndpointIdx) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread_ptr = cpu.current_thread.unwrap();
    let channel_ptr = old_u.thread_map[thread_ptr].endpoint_descriptors[endpoint_index as int].unwrap();
    let channel = old_u.endpoint_map[channel_ptr];
    let peer_ptr = channel.queue[0];
    let progress = SyscallProgress::IpcEndpoint { peer: peer_ptr, caller_sends: waiting_state is SENDING, payload_index };
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..cpu }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, syscall_progress: Some(progress), ..old_u.thread_map[thread_ptr] })
            .insert(peer_ptr, ThreadU { lock_state: LockStateU::WriteLocked, blocking_endpoint_ptr: None,
                state: ThreadState::IPC_TRANSIT { partner: thread_ptr, wait: if old_u.thread_map[peer_ptr].state is SENDING { IpcWait::Send } else { IpcWait::Receive } }, ..old_u.thread_map[peer_ptr] }),
        endpoint_map: old_u.endpoint_map.insert(channel_ptr, EndpointU { queue: channel.queue.skip(1), ..channel }),
        ..old_u
    })
}

/// The result of the endpoint transfer recorded by the running thread: Success when the payload endpoint's
/// container is the receiver's container or one of its ancestors.
pub open spec fn ipc_endpoint_finish_result(old_u: KernelU, cpu_id: CpuId) -> RetValueType {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread.unwrap();
    let progress = old_u.thread_map[thread_ptr].syscall_progress.unwrap();
    let peer_ptr = progress->IpcEndpoint_peer;
    let caller_sends = progress->IpcEndpoint_caller_sends;
    let sender = if caller_sends { thread_ptr } else { peer_ptr };
    let source_index = if caller_sends { progress->IpcEndpoint_payload_index } else { old_u.thread_map[peer_ptr].ipc_payload->Endpoint_endpoint_index };
    let owner = old_u.endpoint_map[old_u.thread_map[sender].endpoint_descriptors[source_index as int].unwrap()].owning_container;
    let container = old_u.thread_map[if caller_sends { peer_ptr } else { thread_ptr }].owning_container;
    if owner == container || old_u.container_map[container].uppertree_seq.contains(owner) { RetValueType::Success } else { RetValueType::ErrorIpcEndpointOwnerMismatch }
}

/// Finishing runs while the running thread records an endpoint transfer and holds the cpu, itself, and the
/// peer; both threads' containers are live and the sender's payload endpoint, at a valid
/// descriptor index, is unlocked.
#[verifier::opaque]
pub open spec fn ipc_endpoint_finish_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread_ptr = cpu.current_thread.unwrap();
    let thread = old_u.thread_map[thread_ptr];
    let progress = thread.syscall_progress.unwrap();
    let peer_ptr = progress->IpcEndpoint_peer;
    let caller_sends = progress->IpcEndpoint_caller_sends;
    let sender = if caller_sends { thread_ptr } else { peer_ptr };
    let source_index = if caller_sends { progress->IpcEndpoint_payload_index } else { old_u.thread_map[peer_ptr].ipc_payload->Endpoint_endpoint_index };
    let payload = old_u.thread_map[sender].endpoint_descriptors[source_index as int];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is WriteLocked
    &&& cpu.current_process is Some
    &&& cpu.current_thread is Some
    &&& old_u.thread_map.dom().contains(thread_ptr)
    &&& thread.lock_state is WriteLocked
    &&& thread.syscall_progress is Some
    &&& progress is IpcEndpoint
    &&& old_u.thread_map.dom().contains(peer_ptr)
    &&& old_u.thread_map[peer_ptr].lock_state is WriteLocked
    &&& old_u.thread_map[peer_ptr].state is IPC_TRANSIT
    &&& old_u.thread_map[peer_ptr].state->IPC_TRANSIT_partner == thread_ptr
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& old_u.container_map.dom().contains(old_u.thread_map[peer_ptr].owning_container)
    &&& edp_idx_valid(source_index)
    &&& payload is Some
    &&& old_u.endpoint_map.dom().contains(payload.unwrap())
    &&& old_u.endpoint_map[payload.unwrap()].lock_state is Unlocked
}

/// On Success the receiver's target descriptor takes the payload endpoint; the peer is scheduled with the
/// result, the caller's progress is cleared, and the cpu, both threads, and the payload
/// endpoint are released.
#[verifier::opaque]
pub open spec fn ipc_endpoint_finish_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread_ptr = cpu.current_thread.unwrap();
    let progress = old_u.thread_map[thread_ptr].syscall_progress.unwrap();
    let peer_ptr = progress->IpcEndpoint_peer;
    let caller_sends = progress->IpcEndpoint_caller_sends;
    let peer_index = old_u.thread_map[peer_ptr].ipc_payload->Endpoint_endpoint_index;
    let sender = if caller_sends { thread_ptr } else { peer_ptr };
    let receiver = if caller_sends { peer_ptr } else { thread_ptr };
    let source_index = if caller_sends { progress->IpcEndpoint_payload_index } else { peer_index };
    let target_index = if caller_sends { peer_index } else { progress->IpcEndpoint_payload_index };
    let payload = old_u.thread_map[sender].endpoint_descriptors[source_index as int].unwrap();
    let result = ipc_endpoint_finish_result(old_u, cpu_id);
    let received = ThreadU { endpoint_descriptors: old_u.thread_map[receiver].endpoint_descriptors.update(target_index as int, Some(payload)), ..old_u.thread_map[receiver] };
    let threads = if result is Success { old_u.thread_map.insert(receiver, received) } else { old_u.thread_map };
    let endpoint = old_u.endpoint_map[payload];
    let container = old_u.thread_map[peer_ptr].owning_container;
    let wake_cpu = if container == old_u.thread_map[thread_ptr].owning_container { cpu_id } else { old_u.thread_map[peer_ptr].last_cpu };
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: cpu_op_after_step(cpu.state), ..cpu }),
        thread_map: threads.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..threads[thread_ptr] })
            .insert(peer_ptr, ThreadU { lock_state: LockStateU::Unlocked, state: ThreadState::SCHEDULED { cpu_id: wake_cpu },
                blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: Some(result), ..threads[peer_ptr] }),
        endpoint_map: old_u.endpoint_map.insert(payload, EndpointU { lock_state: LockStateU::Unlocked,
            owning_threads: if result is Success { endpoint.owning_threads.insert((receiver, target_index)) } else { endpoint.owning_threads }, ..endpoint }),
        container_map: old_u.container_map.insert(container, ContainerU {
            scheduler: old_u.container_map[container].scheduler.update(wake_cpu as int, old_u.container_map[container].scheduler[wake_cpu as int].push(peer_ptr)), ..old_u.container_map[container]
        }),
        ..old_u
    })
}

/// The sender of the pages rendezvous recorded by the thread running on `cpu_id`: the caller exactly when
/// its recorded peer was dequeued while receiving.
pub open spec fn ipc_pages_sender(u: KernelU, cpu_id: CpuId) -> RwLockThreadPtr {
    let caller = u.cpu_array[cpu_id as int].current_thread->Some_0;
    let peer = u.thread_map[caller].syscall_progress->Some_0->IpcPages_peer;
    if u.thread_map[peer].state->IPC_TRANSIT_wait is Receive { caller } else { peer }
}

/// The receiver of the pages rendezvous recorded by the thread running on `cpu_id`.
pub open spec fn ipc_pages_receiver(u: KernelU, cpu_id: CpuId) -> RwLockThreadPtr {
    let caller = u.cpu_array[cpu_id as int].current_thread->Some_0;
    let peer = u.thread_map[caller].syscall_progress->Some_0->IpcPages_peer;
    if u.thread_map[peer].state->IPC_TRANSIT_wait is Receive { peer } else { caller }
}

/// The running thread on `cpu_id` records a pages rendezvous and holds the cpu, itself, the recorded peer in
/// transit with it, and the channel at its descriptor `endpoint_index`.
pub open spec fn ipc_pages_held(u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx) -> bool {
    let cpu = u.cpu_array[cpu_id as int];
    let caller = u.thread_map[cpu.current_thread->Some_0];
    let peer = caller.syscall_progress->Some_0->IpcPages_peer;
    let channel = caller.endpoint_descriptors[endpoint_index as int]->Some_0;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is WriteLocked
    &&& cpu.current_process is Some
    &&& cpu.current_thread is Some
    &&& u.thread_map.dom().contains(cpu.current_thread->Some_0)
    &&& caller.lock_state is WriteLocked
    &&& caller.syscall_progress is Some
    &&& caller.syscall_progress->Some_0 is IpcPages
    &&& u.thread_map.dom().contains(peer)
    &&& u.thread_map[peer].lock_state is WriteLocked
    &&& u.thread_map[peer].state is IPC_TRANSIT
    &&& u.thread_map[peer].state->IPC_TRANSIT_partner == cpu.current_thread->Some_0
    &&& edp_idx_valid(endpoint_index)
    &&& caller.endpoint_descriptors[endpoint_index as int] is Some
    &&& u.endpoint_map.dom().contains(channel)
    &&& u.endpoint_map[channel].lock_state is WriteLocked
}

/// The sender's and receiver's processes differ and both have page tables.
pub open spec fn ipc_pages_tables_present(u: KernelU, cpu_id: CpuId) -> bool {
    let source = u.thread_map[ipc_pages_sender(u, cpu_id)].owning_proc;
    let target = u.thread_map[ipc_pages_receiver(u, cpu_id)].owning_proc;
    &&& source != target
    &&& u.process_map.dom().contains(source)
    &&& u.process_map.dom().contains(target)
    &&& u.process_map[source].pagetable is Some
    &&& u.process_map[target].pagetable is Some
}

/// Every page of `range` is mapped in `table`.
pub open spec fn ipc_pages_source_mapped(table: PageTableU, range: VaRange4K) -> bool {
    forall|i: int| #![trigger range.view()[i]] 0 <= i < range.len ==> table.mapping_4k.dom().contains(range.view()[i])
}

/// As the implementation checks, no 4K leaf lies from the first to the last page of `range`, and no 1G,
/// 2M, or 4K leaf covers a page of `range`.
pub open spec fn ipc_pages_target_free(table: PageTableU, range: VaRange4K) -> bool {
    let first = spec_va2index(range.start);
    let last = spec_va2index(range.view()[range.len - 1]);
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger table.mapping_4k.dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
        pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l4_index_path_le(first, (l4i, l3i, l2i, l1i)) && spec_l4_index_path_le((l4i, l3i, l2i, l1i), last)
            ==> !table.mapping_4k.dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
    &&& forall|i: int| #![trigger range.view()[i]] 0 <= i < range.len ==> {
        let indices = spec_va2index(range.view()[i]);
        &&& !table.mapping_1g.dom().contains(spec_index2va((indices.0, indices.1, 0, 0)))
        &&& !table.mapping_2m.dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0)))
        &&& !table.mapping_4k.dom().contains(range.view()[i])
    }
}

/// Every page of `range` in `table` is owned by `container` or one of its ancestors.
pub open spec fn ipc_pages_owners_compatible(u: KernelU, table: PageTableU, container: RwLockContainerPtr, range: VaRange4K) -> bool {
    forall|i: int| #![trigger range.view()[i]] 0 <= i < range.len ==> {
        let owner = table.mapping_4k[range.view()[i]].owning_container.view();
        &&& u.container_map.dom().contains(container)
        &&& u.container_map.dom().contains(owner)
        &&& (container == owner || u.container_map[container].uppertree_seq.contains(owner))
    }
}

/// The checks a pages rendezvous makes under both locked page tables, in the implementation's order:
/// the source range lies above the user-VA bound, every source page is mapped, the receiver has 4K quota for
/// the worst-case target directories, the target range lies above the user-VA bound and is free, and every
/// source page is owned by the receiver's container or one of its ancestors.
pub open spec fn ipc_pages_check_result(u: KernelU, cpu_id: CpuId) -> RetValueType {
    let progress = u.thread_map[u.cpu_array[cpu_id as int].current_thread->Some_0].syscall_progress->Some_0;
    let source = progress->IpcPages_source_range;
    let target = progress->IpcPages_target_range;
    let receiver = u.thread_map[ipc_pages_receiver(u, cpu_id)];
    let source_table = u.process_map[u.thread_map[ipc_pages_sender(u, cpu_id)].owning_proc].pagetable->Some_0;
    let target_table = u.process_map[receiver.owning_proc].pagetable->Some_0;
    if !user_va_range(u, source) { RetValueType::Error }
    else if !ipc_pages_source_mapped(source_table, source) { RetValueType::ErrorIpcSourceUnmapped }
    else if receiver.quota_4k < 3 * target.len { RetValueType::ErrorNoQuota }
    else if !user_va_range(u, target) { RetValueType::Error }
    else if !ipc_pages_target_free(target_table, target) { RetValueType::ErrorVaInUse }
    else if !ipc_pages_owners_compatible(u, source_table, receiver.owning_container, source) { RetValueType::ErrorIpcPageOwnerMismatch }
    else { RetValueType::Success }
}

/// A pages rendezvous enters when the queue head of the endpoint at `endpoint_index` waits in the opposite
/// direction with a Pages payload of the same length from another process.
#[verifier::opaque]
pub open spec fn ipc_pages_enter_step_pre(old_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, range: VaRange4K) -> bool {
    &&& range.wf()
    &&& range.len > 0
    &&& ipc_rendezvous_step_pre(old_u, cpu_id, endpoint_index, waiting_state, IPCPayLoad::Pages { va_range: range })
    &&& ipc_rendezvous_result(old_u, cpu_id, endpoint_index, waiting_state, IPCPayLoad::Pages { va_range: range }) is Success
}

/// Entering write-locks the cpu, the caller, the queue head, and the channel, moves the queue head off the channel into
/// transit with the caller as its partner, and records both ranges with the queue head as the peer.
#[verifier::opaque]
pub open spec fn ipc_pages_enter_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, range: VaRange4K) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let caller = cpu.current_thread->Some_0;
    let channel = old_u.thread_map[caller].endpoint_descriptors[endpoint_index as int]->Some_0;
    let peer = old_u.endpoint_map[channel].queue[0];
    let peer_range = old_u.thread_map[peer].ipc_payload->Pages_va_range;
    let sends = waiting_state is SENDING;
    let progress = SyscallProgress::IpcPages { source_range: if sends { range } else { peer_range }, target_range: if sends { peer_range } else { range }, peer, tables: IpcPagesTables::Unlocked, released: None };
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..cpu }),
        thread_map: old_u.thread_map.insert(caller, ThreadU { lock_state: LockStateU::WriteLocked, syscall_progress: Some(progress), ..old_u.thread_map[caller] })
            .insert(peer, ThreadU { lock_state: LockStateU::WriteLocked, blocking_endpoint_ptr: None,
                state: ThreadState::IPC_TRANSIT { partner: caller, wait: if old_u.thread_map[peer].state is SENDING { IpcWait::Send } else { IpcWait::Receive } }, ..old_u.thread_map[peer] }),
        endpoint_map: old_u.endpoint_map.insert(channel, EndpointU { lock_state: LockStateU::WriteLocked, queue: old_u.endpoint_map[channel].queue.skip(1), ..old_u.endpoint_map[channel] }),
        ..old_u
    })
}

/// Locking runs after entering, while no other thread write-locks the sender's page table, and no other thread write-locks
/// the receiver's page table to read it or holds it at all to fill it.
#[verifier::opaque]
pub open spec fn ipc_pages_lock_tables_step_pre(old_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, tables: IpcPagesTables) -> bool {
    let progress = old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].syscall_progress->Some_0;
    let source = old_u.process_map[old_u.thread_map[ipc_pages_sender(old_u, cpu_id)].owning_proc].pagetable->Some_0;
    let target = old_u.process_map[old_u.thread_map[ipc_pages_receiver(old_u, cpu_id)].owning_proc].pagetable->Some_0;
    &&& ipc_pages_held(old_u, cpu_id, endpoint_index)
    &&& progress->IpcPages_tables is Unlocked
    &&& progress->IpcPages_released is None
    &&& tables is Read || tables is Fill
    &&& ipc_pages_tables_present(old_u, cpu_id)
    &&& !(source.lock_state is WriteLocked)
    &&& if tables is Fill { target.lock_state is Unlocked } else { !(target.lock_state is WriteLocked) }
}

/// Locking read-locks the sender's page table, read-locks the receiver's or write-locks it to fill it, write-locks the existing 2M
/// windows of both ranges when both are user ranges, and records `tables`.
#[verifier::opaque]
pub open spec fn ipc_pages_lock_tables_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, tables: IpcPagesTables) -> bool {
    let caller = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let progress = old_u.thread_map[caller].syscall_progress->Some_0;
    let source = old_u.thread_map[ipc_pages_sender(old_u, cpu_id)].owning_proc;
    let target = old_u.thread_map[ipc_pages_receiver(old_u, cpu_id)].owning_proc;
    let locked = SyscallProgress::IpcPages { source_range: progress->IpcPages_source_range, target_range: progress->IpcPages_target_range, peer: progress->IpcPages_peer, tables, released: None };
    let user = user_va_range(old_u, progress->IpcPages_source_range) && user_va_range(old_u, progress->IpcPages_target_range);
    let source_table = old_u.process_map[source].pagetable->Some_0;
    let target_table = old_u.process_map[target].pagetable->Some_0;
    let source_windows = if user { pagetable_window_locks_after_locking_range(source_table.pagetable_window_locks, progress->IpcPages_source_range) } else { source_table.pagetable_window_locks };
    let target_windows = if user { pagetable_window_locks_after_locking_range(target_table.pagetable_window_locks, progress->IpcPages_target_range) } else { target_table.pagetable_window_locks };
    new_u == (KernelU {
        thread_map: old_u.thread_map.insert(caller, ThreadU { syscall_progress: Some(locked), ..old_u.thread_map[caller] }),
        process_map: old_u.process_map.insert(source, ProcessU {
            pagetable: Some(PageTableU { lock_state: LockStateU::ReadLocked, pagetable_window_locks: source_windows, ..source_table }), ..old_u.process_map[source]
        }).insert(target, ProcessU {
            pagetable: Some(PageTableU { lock_state: if tables is Fill { LockStateU::WriteLocked } else { LockStateU::ReadLocked }, pagetable_window_locks: target_windows, ..target_table }),
            ..old_u.process_map[target]
        }),
        ..old_u
    })
}

/// Checking runs after locking, while the sender's page table is read-locked, the receiver's is read-locked or write-locked
/// to fill it as recorded, and nothing is released.
#[verifier::opaque]
pub open spec fn ipc_pages_check_step_pre(old_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx) -> bool {
    let progress = old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].syscall_progress->Some_0;
    let source = old_u.process_map[old_u.thread_map[ipc_pages_sender(old_u, cpu_id)].owning_proc].pagetable->Some_0;
    let target = old_u.process_map[old_u.thread_map[ipc_pages_receiver(old_u, cpu_id)].owning_proc].pagetable->Some_0;
    &&& ipc_pages_held(old_u, cpu_id, endpoint_index)
    &&& progress->IpcPages_tables is Read || progress->IpcPages_tables is Fill
    &&& progress->IpcPages_released is None
    &&& ipc_pages_tables_present(old_u, cpu_id)
    &&& source.lock_state is ReadLocked
    &&& target.lock_state == if progress->IpcPages_tables is Fill { LockStateU::WriteLocked } else { LockStateU::ReadLocked }
}

/// A passed check starts sharing the recorded ranges at their first page; a failed check releases both page tables, which
/// other readers may still hold, and the 2M windows of both ranges when both are user ranges, and records its result.
#[verifier::opaque]
pub open spec fn ipc_pages_check_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let caller = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let progress = old_u.thread_map[caller].syscall_progress->Some_0;
    let result = ipc_pages_check_result(old_u, cpu_id);
    let source = old_u.thread_map[ipc_pages_sender(old_u, cpu_id)].owning_proc;
    let target = old_u.thread_map[ipc_pages_receiver(old_u, cpu_id)].owning_proc;
    let source_state = new_u.process_map[source].pagetable->Some_0.lock_state;
    let target_state = new_u.process_map[target].pagetable->Some_0.lock_state;
    let user = user_va_range(old_u, progress->IpcPages_source_range) && user_va_range(old_u, progress->IpcPages_target_range);
    let source_table = old_u.process_map[source].pagetable->Some_0;
    let target_table = old_u.process_map[target].pagetable->Some_0;
    let source_windows = if user { pagetable_window_locks_after_unlocking_range(source_table.pagetable_window_locks, progress->IpcPages_source_range) } else { source_table.pagetable_window_locks };
    let target_windows = if user { pagetable_window_locks_after_unlocking_range(target_table.pagetable_window_locks, progress->IpcPages_target_range) } else { target_table.pagetable_window_locks };
    let next = if result is Success {
        SyscallProgress::Share4k { source_range: progress->IpcPages_source_range, target_range: progress->IpcPages_target_range, shared: 0, directory: Mmap4kDirectory::None, origin: Share4kOrigin::IpcPages { peer: progress->IpcPages_peer } }
    } else {
        SyscallProgress::IpcPages { source_range: progress->IpcPages_source_range, target_range: progress->IpcPages_target_range, peer: progress->IpcPages_peer, tables: IpcPagesTables::Unlocked, released: Some(result) }
    };
    let threads = old_u.thread_map.insert(caller, ThreadU { syscall_progress: Some(next), ..old_u.thread_map[caller] });
    if result is Success { new_u == (KernelU { thread_map: threads, ..old_u }) } else {
        &&& source_state is Unlocked || source_state is ReadLocked
        &&& target_state is Unlocked || target_state is ReadLocked
        &&& new_u == (KernelU {
            thread_map: threads,
            process_map: old_u.process_map.insert(source, ProcessU {
                pagetable: Some(PageTableU { lock_state: source_state, pagetable_window_locks: source_windows, ..source_table }), ..old_u.process_map[source]
            }).insert(target, ProcessU {
                pagetable: Some(PageTableU { lock_state: target_state, pagetable_window_locks: target_windows, ..target_table }), ..old_u.process_map[target]
            }),
            ..old_u
        })
    }
}

/// Downgrading runs after the receiver's missing directories are installed and before the first page is shared, while the
/// sender's page table is read-locked and the receiver's is write-locked.
#[verifier::opaque]
pub open spec fn ipc_pages_downgrade_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let progress = old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].syscall_progress->Some_0;
    let objects = share_4k_objects(old_u, cpu_id);
    let source = old_u.thread_map[objects.source_thread].owning_proc;
    &&& share_4k_locked(old_u, cpu_id)
    &&& progress->Share4k_origin is IpcPages
    &&& progress->Share4k_shared == 0
    &&& source != objects.target
    &&& old_u.process_map.dom().contains(source)
    &&& old_u.process_map.dom().contains(objects.target)
    &&& old_u.process_map[source].pagetable is Some
    &&& old_u.process_map[objects.target].pagetable is Some
    &&& old_u.process_map[source].pagetable->Some_0.lock_state is ReadLocked
    &&& old_u.process_map[objects.target].pagetable->Some_0.lock_state is WriteLocked
}

/// Downgrading turns the write lock on the receiver's page table into a read lock.
#[verifier::opaque]
pub open spec fn ipc_pages_downgrade_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let target = share_4k_objects(old_u, cpu_id).target;
    new_u == (KernelU {
        process_map: old_u.process_map.insert(target, ProcessU {
            pagetable: Some(PageTableU { lock_state: LockStateU::ReadLocked, ..old_u.process_map[target].pagetable->Some_0 }), ..old_u.process_map[target]
        }),
        ..old_u
    })
}

/// Unlocking runs after every page of a pages rendezvous is shared, while both page tables are read-locked.
#[verifier::opaque]
pub open spec fn ipc_pages_unlock_tables_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let progress = old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].syscall_progress->Some_0;
    let objects = share_4k_objects(old_u, cpu_id);
    let source = old_u.thread_map[objects.source_thread].owning_proc;
    &&& share_4k_locked(old_u, cpu_id)
    &&& progress->Share4k_origin is IpcPages
    &&& old_u.thread_map[progress->Share4k_origin->IpcPages_peer].state is IPC_TRANSIT
    &&& progress->Share4k_shared == progress->Share4k_source_range.len
    &&& source != objects.target
    &&& old_u.process_map.dom().contains(source)
    &&& old_u.process_map.dom().contains(objects.target)
    &&& old_u.process_map[source].pagetable is Some
    &&& old_u.process_map[objects.target].pagetable is Some
    &&& old_u.process_map[source].pagetable->Some_0.lock_state is ReadLocked
    &&& old_u.process_map[objects.target].pagetable->Some_0.lock_state is ReadLocked
}

/// Releasing both page tables, which other readers may still hold, and the 2M windows of both ranges records that the rendezvous
/// succeeded.
#[verifier::opaque]
pub open spec fn ipc_pages_unlock_tables_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let caller = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let progress = old_u.thread_map[caller].syscall_progress->Some_0;
    let objects = share_4k_objects(old_u, cpu_id);
    let source = old_u.thread_map[objects.source_thread].owning_proc;
    let source_state = new_u.process_map[source].pagetable->Some_0.lock_state;
    let target_state = new_u.process_map[objects.target].pagetable->Some_0.lock_state;
    let source_table = old_u.process_map[source].pagetable->Some_0;
    let target_table = old_u.process_map[objects.target].pagetable->Some_0;
    let source_windows = pagetable_window_locks_after_unlocking_range(source_table.pagetable_window_locks, progress->Share4k_source_range);
    let target_windows = pagetable_window_locks_after_unlocking_range(target_table.pagetable_window_locks, progress->Share4k_target_range);
    let released = SyscallProgress::IpcPages {
        source_range: progress->Share4k_source_range, target_range: progress->Share4k_target_range, peer: progress->Share4k_origin->IpcPages_peer,
        tables: IpcPagesTables::Unlocked, released: Some(RetValueType::Success),
    };
    &&& source_state is Unlocked || source_state is ReadLocked
    &&& target_state is Unlocked || target_state is ReadLocked
    &&& new_u == (KernelU {
        thread_map: old_u.thread_map.insert(caller, ThreadU { syscall_progress: Some(released), ..old_u.thread_map[caller] }),
        process_map: old_u.process_map.insert(source, ProcessU {
            pagetable: Some(PageTableU { lock_state: source_state, pagetable_window_locks: source_windows, ..source_table }), ..old_u.process_map[source]
        }).insert(objects.target, ProcessU {
            pagetable: Some(PageTableU { lock_state: target_state, pagetable_window_locks: target_windows, ..target_table }), ..old_u.process_map[objects.target]
        }),
        ..old_u
    })
}

/// The one step of a pages transfer recorded after entering.
#[verifier::opaque]
pub open spec fn ipc_pages_trace_after_enter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, range: VaRange4K) -> bool {
    &&& trace.len() == 1
    &&& trace[0].old_u == pre
    &&& ipc_pages_enter_step_pre(pre, cpu_id, endpoint_index, waiting_state, range)
    &&& ipc_pages_enter_step(pre, trace[0].new_u, cpu_id, endpoint_index, waiting_state, range)
}

/// The two steps of a pages transfer recorded after locking both page tables in mode `tables`.
#[verifier::opaque]
pub open spec fn ipc_pages_trace_after_lock(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, range: VaRange4K, tables: IpcPagesTables) -> bool {
    &&& trace.len() == 2
    &&& trace[0].old_u == pre
    &&& ipc_pages_enter_step_pre(pre, cpu_id, endpoint_index, waiting_state, range)
    &&& ipc_pages_enter_step(pre, trace[0].new_u, cpu_id, endpoint_index, waiting_state, range)
    &&& ipc_pages_lock_tables_step_pre(trace[1].old_u, cpu_id, endpoint_index, tables)
    &&& ipc_pages_lock_tables_step(trace[1].old_u, trace[1].new_u, cpu_id, tables)
}

/// The steps of a pages transfer recorded from `start` on after a passed check and every directory, downgrade, and share
/// step.
#[verifier::opaque]
pub open spec fn ipc_pages_trace_after_share(trace: Seq<KernelStep>, start: int, pre: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, range: VaRange4K) -> bool {
    &&& 0 <= start
    &&& start + range.len + 3 <= trace.len() <= start + 4 * range.len + 4
    &&& trace[start].old_u == pre
    &&& ipc_pages_enter_step_pre(pre, cpu_id, endpoint_index, waiting_state, range)
    &&& ipc_pages_enter_step(pre, trace[start].new_u, cpu_id, endpoint_index, waiting_state, range)
    &&& (ipc_pages_lock_tables_step_pre(trace[start + 1].old_u, cpu_id, endpoint_index, IpcPagesTables::Read) && ipc_pages_lock_tables_step(trace[start + 1].old_u, trace[start + 1].new_u, cpu_id, IpcPagesTables::Read)
        || ipc_pages_lock_tables_step_pre(trace[start + 1].old_u, cpu_id, endpoint_index, IpcPagesTables::Fill) && ipc_pages_lock_tables_step(trace[start + 1].old_u, trace[start + 1].new_u, cpu_id, IpcPagesTables::Fill))
    &&& ipc_pages_check_step_pre(trace[start + 2].old_u, cpu_id, endpoint_index)
    &&& ipc_pages_check_step(trace[start + 2].old_u, trace[start + 2].new_u, cpu_id)
    &&& ipc_pages_check_result(trace[start + 2].old_u, cpu_id) is Success
    &&& forall|j: int| #![trigger trace[j]] start + 3 <= j < trace.len()
        ==> share_4k_range_step(trace[j], cpu_id) || ipc_pages_downgrade_step_pre(trace[j].old_u, cpu_id) && ipc_pages_downgrade_step(trace[j].old_u, trace[j].new_u, cpu_id)
}

/// The steps of a pages transfer before it finishes: enter, lock both page tables to read or to fill, and check, then on a
/// passed check the directory, downgrade, and share steps and unlocking both page tables. `result` is the check result.
#[verifier::opaque]
pub open spec fn ipc_pages_mapping_trace(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, range: VaRange4K, result: RetValueType) -> bool {
    &&& if result is Success { range.len + 4 <= trace.len() <= 4 * range.len + 5 } else { trace.len() == 3 }
    &&& trace[0].old_u == pre
    &&& ipc_pages_enter_step_pre(pre, cpu_id, endpoint_index, waiting_state, range)
    &&& ipc_pages_enter_step(pre, trace[0].new_u, cpu_id, endpoint_index, waiting_state, range)
    &&& (ipc_pages_lock_tables_step_pre(trace[1].old_u, cpu_id, endpoint_index, IpcPagesTables::Read) && ipc_pages_lock_tables_step(trace[1].old_u, trace[1].new_u, cpu_id, IpcPagesTables::Read)
        || ipc_pages_lock_tables_step_pre(trace[1].old_u, cpu_id, endpoint_index, IpcPagesTables::Fill) && ipc_pages_lock_tables_step(trace[1].old_u, trace[1].new_u, cpu_id, IpcPagesTables::Fill))
    &&& ipc_pages_check_step_pre(trace[2].old_u, cpu_id, endpoint_index)
    &&& ipc_pages_check_step(trace[2].old_u, trace[2].new_u, cpu_id)
    &&& result == ipc_pages_check_result(trace[2].old_u, cpu_id)
    &&& result is Success ==> {
        &&& forall|j: int| #![trigger trace[j]] 3 <= j < trace.len() - 1
            ==> share_4k_range_step(trace[j], cpu_id) || ipc_pages_downgrade_step_pre(trace[j].old_u, cpu_id) && ipc_pages_downgrade_step(trace[j].old_u, trace[j].new_u, cpu_id)
        &&& ipc_pages_unlock_tables_step_pre(trace.last().old_u, cpu_id)
        &&& ipc_pages_unlock_tables_step(trace.last().old_u, trace.last().new_u, cpu_id)
    }
}

/// A pages rendezvous is one rendezvous error step on TypeMismatch or SameProcess, the mapping steps and a
/// finish step after a passed rendezvous, or a stuttering rejection.
#[verifier::opaque]
pub open spec fn ipc_pages_rendezvous_syscall_trace(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, range: VaRange4K, result: RetValueType) -> bool {
    if result is ErrorIpcSameProcess || result is ErrorIpcTypeMismatch {
        &&& range.wf()
        &&& range.len > 0
        &&& trace.len() == 1
        &&& trace[0].old_u == pre && trace[0].new_u == post
        &&& result == ipc_rendezvous_result(pre, cpu_id, endpoint_index, waiting_state, IPCPayLoad::Pages { va_range: range })
        &&& ipc_rendezvous_step_pre(pre, cpu_id, endpoint_index, waiting_state, IPCPayLoad::Pages { va_range: range })
        &&& ipc_rendezvous_step(pre, post, cpu_id, endpoint_index, waiting_state, IPCPayLoad::Pages { va_range: range })
    } else if result is Success || result is ErrorIpcSourceUnmapped || result is ErrorIpcPageOwnerMismatch || result is ErrorNoQuota
        || result is ErrorVaInUse || result is Error && trace.len() > 0 {
        &&& trace.len() >= 2
        &&& trace.last().new_u == post
        &&& ipc_pages_mapping_trace(trace.subrange(0, trace.len() - 1), pre, cpu_id, endpoint_index, waiting_state, range, result)
        &&& ipc_pages_finish_step_pre(trace.last().old_u, cpu_id, endpoint_index)
        &&& ipc_pages_finish_step(trace.last().old_u, post, cpu_id, endpoint_index)
    } else { trace.len() == 0 && post == pre }
}

#[verifier::opaque]
pub open spec fn ipc_pages_syscall_trace(
    trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu: CpuId, channel_index: EndpointIdx,
    waiting: ThreadState, range: VaRange4K, regs: Registers, flushed_default_pcid: bool, result: RetValueType,
) -> bool {
    if result is CpuIdle {
        &&& range.wf()
        &&& range.len > 0
        &&& ipc_ordinary_syscall_trace(trace, pre, post, cpu, channel_index, waiting, IPCPayLoad::Pages { va_range: range }, regs, flushed_default_pcid, result)
    } else { ipc_pages_rendezvous_syscall_trace(trace, pre, post, cpu, channel_index, waiting, range, result) }
}

/// Finishing runs after the page tables are released with a result, while the caller holds the cpu, itself,
/// the peer in transit with it, and the channel, but no page table.
#[verifier::opaque]
pub open spec fn ipc_pages_finish_step_pre(old_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx) -> bool {
    let progress = old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].syscall_progress->Some_0;
    let peer = old_u.thread_map[progress->IpcPages_peer];
    &&& ipc_pages_held(old_u, cpu_id, endpoint_index)
    &&& progress->IpcPages_released is Some
    &&& progress->IpcPages_tables is Unlocked
    &&& old_u.container_map.dom().contains(peer.owning_container)
}

/// Finishing schedules the transit peer with the recorded result, clears the caller's progress, and releases the
/// cpu, both threads, and the channel.
#[verifier::opaque]
pub open spec fn ipc_pages_finish_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let caller = cpu.current_thread->Some_0;
    let progress = old_u.thread_map[caller].syscall_progress->Some_0;
    let peer = progress->IpcPages_peer;
    let channel = old_u.thread_map[caller].endpoint_descriptors[endpoint_index as int]->Some_0;
    let container = old_u.thread_map[peer].owning_container;
    let wake_cpu = if container == old_u.thread_map[caller].owning_container { cpu_id } else { old_u.thread_map[peer].last_cpu };
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: cpu_op_after_step(cpu.state), ..cpu }),
        thread_map: old_u.thread_map.insert(caller, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..old_u.thread_map[caller] })
            .insert(peer, ThreadU { lock_state: LockStateU::Unlocked, state: ThreadState::SCHEDULED { cpu_id: wake_cpu },
                blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: Some(progress->IpcPages_released->Some_0), ..old_u.thread_map[peer] }),
        endpoint_map: old_u.endpoint_map.insert(channel, EndpointU { lock_state: LockStateU::Unlocked, ..old_u.endpoint_map[channel] }),
        container_map: old_u.container_map.insert(container, ContainerU {
            scheduler: old_u.container_map[container].scheduler.update(wake_cpu as int, old_u.container_map[container].scheduler[wake_cpu as int].push(peer)), ..old_u.container_map[container]
        }),
        ..old_u
    })
}

/// The one step of an endpoint transfer recorded after moving the queue head into transit.
#[verifier::opaque]
pub open spec fn ipc_endpoint_trace_after_transit(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload_index: EndpointIdx) -> bool {
    &&& trace.len() == 1
    &&& trace[0].old_u == pre
    &&& ipc_endpoint_transit_step_pre(pre, cpu_id, endpoint_index, waiting_state, payload_index)
    &&& ipc_endpoint_transit_step(pre, trace[0].new_u, cpu_id, endpoint_index, waiting_state, payload_index)
}

/// Endpoint rendezvous is the transit and finish steps on Success or EndpointOwnerMismatch, one rendezvous
/// error step, or a stuttering rejection.
#[verifier::opaque]
pub open spec fn ipc_endpoint_rendezvous_trace(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload_index: EndpointIdx, ret: RetValueType) -> bool {
    if ret is Success || ret is ErrorIpcEndpointOwnerMismatch {
        &&& trace.len() == 2
        &&& trace[0].old_u == pre
        &&& trace[1].new_u == post
        &&& ipc_endpoint_transit_step_pre(pre, cpu_id, endpoint_index, waiting_state, payload_index)
        &&& ipc_endpoint_transit_step(pre, trace[0].new_u, cpu_id, endpoint_index, waiting_state, payload_index)
        &&& ipc_endpoint_finish_step_pre(trace[1].old_u, cpu_id)
        &&& ipc_endpoint_finish_step(trace[1].old_u, post, cpu_id)
        &&& ret == ipc_endpoint_finish_result(trace[1].old_u, cpu_id)
    } else if ret is ErrorIpcEndpointSourceInvalid || ret is ErrorIpcEndpointTargetInUse || ret is ErrorIpcTypeMismatch {
        &&& trace.len() == 1
        &&& trace[0].old_u == pre
        &&& trace[0].new_u == post
        &&& ret == ipc_rendezvous_result(pre, cpu_id, endpoint_index, waiting_state, IPCPayLoad::Endpoint { endpoint_index: payload_index })
        &&& ipc_rendezvous_step_pre(pre, cpu_id, endpoint_index, waiting_state, IPCPayLoad::Endpoint { endpoint_index: payload_index })
        &&& ipc_rendezvous_step(pre, post, cpu_id, endpoint_index, waiting_state, IPCPayLoad::Endpoint { endpoint_index: payload_index })
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}

#[verifier::opaque]
pub open spec fn ipc_endpoint_syscall_trace(
    trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx,
    waiting_state: ThreadState, payload_index: EndpointIdx, regs: Registers, flushed_default_pcid: bool, ret: RetValueType,
) -> bool {
    if ret is CpuIdle {
        ipc_ordinary_syscall_trace(trace, pre, post, cpu_id, endpoint_index, waiting_state,
            IPCPayLoad::Endpoint { endpoint_index: payload_index }, regs, flushed_default_pcid, ret)
    } else { ipc_endpoint_rendezvous_trace(trace, pre, post, cpu_id, endpoint_index, waiting_state, payload_index, ret) }
}
}
