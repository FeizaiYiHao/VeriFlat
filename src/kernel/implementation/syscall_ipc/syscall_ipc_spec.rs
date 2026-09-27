use vstd::prelude::*;
use crate::*;

verus! {
/// Blocking on `cpu_id` flushes the `(cpu_id, KERNEL_DEFAULT_PCID)` TLB entry when the kernel PCID is dirty.
pub open spec fn ipc_block_flushes_default_pcid(pre: KernelK, cpu_id: CpuId) -> bool {
    pre.pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).view().needflush
}

/// Return values that record exactly one rendezvous step for the Empty, Cpu, and ReceiveCpu payloads.
pub open spec fn ipc_rendezvous_ret(ret: RetValueType) -> bool {
    ||| ret is Success
    ||| ret is SuccessUsize
    ||| ret is ErrorIpcTypeMismatch
    ||| ret is ErrorIpcSameContainer
    ||| ret is ErrorIpcCpuOwnerMismatch
    ||| ret is ErrorIpcCpuNotOff
}

/// The result written into the scheduled peer for the caller's `payload` and return value `ret`.
pub open spec fn ipc_peer_result(payload: IPCPayLoad, ret: RetValueType) -> RetValueType {
    if ret is Success {
        if payload is Cpu { RetValueType::SuccessUsize { value: payload->Cpu_cpu_id } } else { RetValueType::Success }
    } else if ret is SuccessUsize { RetValueType::Success } else { ret }
}

/// The Off CPU handed over by a successful CPU rendezvous and the receiving thread whose container takes it.
pub open spec fn ipc_cpu_transfer(
    old_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, payload: IPCPayLoad, ret: RetValueType,
) -> Option<(CpuId, RwLockThreadPtr)> {
    let thread_ptr = old_u.cpu_array[cpu_id as int].current_thread.unwrap();
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let endpoint = old_u.endpoint_map.spec_index(thread.endpoint_descriptors[endpoint_index as int].unwrap());
    if payload is Cpu && ret is Success { Some((payload->Cpu_cpu_id, endpoint.queue[0])) }
    else if payload is ReceiveCpu && ret is SuccessUsize { Some((ret->SuccessUsize_value, thread_ptr)) }
    else { None }
}

/// The running thread on `cpu_id` holds a live endpoint descriptor at `endpoint_index`.
pub open spec fn ipc_step_pre(old_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(cpu.current_thread.unwrap());
    let endpoint_ptr = thread.endpoint_descriptors[endpoint_index as int];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& edp_idx_valid(endpoint_index)
    &&& cpu.state is Running
    &&& cpu.current_process is Some
    &&& cpu.current_thread is Some
    &&& old_u.process_map.dom().contains(cpu.current_process.unwrap())
    &&& !old_u.process_map.spec_index(cpu.current_process.unwrap()).killed
    &&& old_u.thread_map.dom().contains(cpu.current_thread.unwrap())
    &&& !thread.killed
    &&& thread.state == (ThreadState::RUNNING { cpu_id })
    &&& thread.owning_proc == cpu.current_process.unwrap()
    &&& endpoint_ptr is Some
    &&& old_u.endpoint_map.dom().contains(endpoint_ptr.unwrap())
    &&& !old_u.endpoint_map.spec_index(endpoint_ptr.unwrap()).queue.contains(cpu.current_thread.unwrap())
}

/// The endpoint queue is empty or waits in the caller's direction, so the caller blocks.
pub open spec fn ipc_block_step_pre(old_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(cpu.current_thread.unwrap());
    let endpoint = old_u.endpoint_map.spec_index(thread.endpoint_descriptors[endpoint_index as int].unwrap());
    &&& ipc_step_pre(old_u, cpu_id, endpoint_index)
    &&& waiting_state.is_endpoint_waiting()
    &&& endpoint.queue.len() == 0 || (endpoint.queue_state is SEND) == waiting_state.is_endpoint_send_waiting()
}

/// User-visible blocking step: the caller waits on the endpoint with `payload` and its CPU goes idle.
pub open spec fn ipc_block_step(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad,
    regs: Registers, flushed_default_pcid: bool,
) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread_ptr = cpu.current_thread.unwrap();
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let endpoint_ptr = thread.endpoint_descriptors[endpoint_index as int].unwrap();
    let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { state: CpuState::Idle, current_process: None, current_thread: None, ..cpu }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU {
            state: waiting_state, blocking_endpoint_ptr: Some(endpoint_ptr), ipc_payload: payload, trap_frame: Some(regs), ..thread
        }),
        endpoint_map: old_u.endpoint_map.insert(endpoint_ptr, EndpointU {
            queue: endpoint.queue.push(thread_ptr),
            queue_state: if endpoint.queue.len() == 0 {
                match waiting_state { ThreadState::SENDING | ThreadState::CALLING => EndpointState::SEND, _ => EndpointState::RECEIVE }
            } else { endpoint.queue_state },
            ..endpoint
        }),
        cpu_tlb: if flushed_default_pcid { old_u.cpu_tlb.insert((cpu_id, KERNEL_DEFAULT_PCID), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }) } else { old_u.cpu_tlb },
        ..old_u
    })
}

/// The endpoint queue head waits in the opposite direction, so the caller rendezvous with it.
pub open spec fn ipc_rendezvous_step_pre(old_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(cpu.current_thread.unwrap());
    let endpoint_ptr = thread.endpoint_descriptors[endpoint_index as int].unwrap();
    let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
    let peer = old_u.thread_map.spec_index(endpoint.queue[0]);
    &&& ipc_step_pre(old_u, cpu_id, endpoint_index)
    &&& waiting_state is SENDING || waiting_state is RECEIVING
    &&& endpoint.queue.len() > 0
    &&& (endpoint.queue_state is SEND) != (waiting_state is SENDING)
    &&& old_u.thread_map.dom().contains(endpoint.queue[0])
    &&& endpoint.queue[0] != cpu.current_thread.unwrap()
    &&& !peer.killed
    &&& peer.state.is_endpoint_waiting()
    &&& peer.blocking_endpoint_ptr == Some(endpoint_ptr)
    &&& old_u.container_map.dom().contains(peer.owning_container)
}

/// User-visible rendezvous step: the queue head is scheduled with `peer_result` and an Off CPU may move
/// to the receiving thread's container.
pub open spec fn ipc_rendezvous_step(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, peer_result: RetValueType,
    cpu_transfer: Option<(CpuId, RwLockThreadPtr)>,
) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(cpu.current_thread.unwrap());
    let endpoint_ptr = thread.endpoint_descriptors[endpoint_index as int].unwrap();
    let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
    let peer_thread_ptr = endpoint.queue[0];
    let peer = old_u.thread_map.spec_index(peer_thread_ptr);
    let container = old_u.container_map.spec_index(peer.owning_container);
    new_u == (KernelU {
        cpu_array: match cpu_transfer {
            Some((transfer_cpu, receiver)) => old_u.cpu_array.update(transfer_cpu as int, CpuU {
                owning_container: old_u.thread_map.spec_index(receiver).owning_container, ..old_u.cpu_array[transfer_cpu as int]
            }),
            None => old_u.cpu_array,
        },
        container_map: old_u.container_map.insert(peer.owning_container, ContainerU { scheduler: container.scheduler.push(peer_thread_ptr), ..container }),
        thread_map: old_u.thread_map.insert(peer_thread_ptr, ThreadU {
            state: ThreadState::SCHEDULED, blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: Some(peer_result), ..peer
        }),
        endpoint_map: old_u.endpoint_map.insert(endpoint_ptr, EndpointU { queue: endpoint.queue.skip(1), ..endpoint }),
        ..old_u
    })
}
}
