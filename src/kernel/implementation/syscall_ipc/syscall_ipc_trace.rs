use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_spec::*;
verus! {
/// The block wrapper's user-view facts are exactly the block step on `pre`/`post`.
pub(super) proof fn ipc_block_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool,
)
    requires
        kernel_u_ipc_block_changed(pre, post, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thread_ptr);
            let endpoint = pre.endpoint_map.spec_index(endpoint_ptr);
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& cpu.current_thread == Some(thread_ptr)
            &&& cpu.current_process == Some(thread.owning_proc)
            &&& pre.process_map.dom().contains(thread.owning_proc)
            &&& pre.process_map.spec_index(thread.owning_proc).lock_state is Unlocked
            &&& !pre.process_map.spec_index(thread.owning_proc).killed
            &&& pre.container_map.dom().contains(thread.owning_container)
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is Unlocked
            &&& thread.syscall_progress is None
            &&& !thread.killed
            &&& thread.state == (ThreadState::RUNNING { cpu_id })
            &&& edp_idx_valid(endpoint_index)
            &&& thread.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
            &&& pre.endpoint_map.dom().contains(endpoint_ptr)
            &&& endpoint.lock_state is Unlocked
            &&& !endpoint.queue.contains(thread_ptr)
            &&& waiting_state.is_endpoint_waiting()
            &&& endpoint.queue.len() == 0 || (endpoint.queue_state is SEND) == waiting_state.is_endpoint_send_waiting()
        },
    ensures
        ipc_block_step_pre(pre, cpu_id, endpoint_index, waiting_state),
        ipc_block_step(pre, post, cpu_id, endpoint_index, waiting_state, payload, regs, flushed_default_pcid),
{ reveal(ipc_block_step_pre); reveal(ipc_step_pre); }

/// The rendezvous wrapper's user-view facts are exactly the rendezvous step on `pre`/`post`.
pub(super) proof fn ipc_rendezvous_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, caller_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    waiting_state: ThreadState, peer_thread_ptr: RwLockThreadPtr, peer_result: RetValueType, cpu_transfer: Option<(CpuId, RwLockThreadPtr)>,
    payload: IPCPayLoad, cpu_sets_locked: bool,
)
    requires
        kernel_u_ipc_rendezvous_changed(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer),
        {
            let result = ipc_rendezvous_result(pre, cpu_id, endpoint_index, waiting_state, payload);
            &&& peer_result == ipc_peer_result(payload, result)
            &&& cpu_transfer == ipc_cpu_transfer(pre, cpu_id, endpoint_index, payload, result)
            &&& (payload is Cpu || payload is ReceiveCpu) && !(result is ErrorIpcTypeMismatch) && !(result is ErrorIpcSameContainer) ==> cpu_sets_locked
        },
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let caller = pre.thread_map.spec_index(caller_thread_ptr);
            let peer = pre.thread_map.spec_index(peer_thread_ptr);
            let endpoint = pre.endpoint_map.spec_index(endpoint_ptr);
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& cpu.current_thread == Some(caller_thread_ptr)
            &&& cpu.current_process == Some(caller.owning_proc)
            &&& pre.process_map.dom().contains(caller.owning_proc)
            &&& pre.process_map.spec_index(caller.owning_proc).lock_state is Unlocked
            &&& !pre.process_map.spec_index(caller.owning_proc).killed
            &&& pre.thread_map.dom().contains(caller_thread_ptr)
            &&& caller.lock_state is Unlocked
            &&& caller.syscall_progress is None
            &&& !caller.killed
            &&& caller.state == (ThreadState::RUNNING { cpu_id })
            &&& edp_idx_valid(endpoint_index)
            &&& caller.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
            &&& pre.endpoint_map.dom().contains(endpoint_ptr)
            &&& endpoint.lock_state is Unlocked
            &&& !endpoint.queue.contains(caller_thread_ptr)
            &&& waiting_state is SENDING || waiting_state is RECEIVING
            &&& endpoint.queue.len() > 0
            &&& endpoint.queue[0] == peer_thread_ptr
            &&& (endpoint.queue_state is SEND) != (waiting_state is SENDING)
            &&& pre.thread_map.dom().contains(peer_thread_ptr)
            &&& peer.lock_state is Unlocked
            &&& peer_thread_ptr != caller_thread_ptr
            &&& !peer.killed
            &&& peer.state.is_endpoint_waiting()
            &&& peer.blocking_endpoint_ptr == Some(endpoint_ptr)
            &&& pre.container_map.dom().contains(peer.owning_container)
            &&& pre.container_map.dom().contains(caller.owning_container)
            &&& cpu_sets_locked ==> pre.container_map[caller.owning_container].cpu_set_lock is Unlocked && pre.container_map[peer.owning_container].cpu_set_lock is Unlocked
            &&& cpu_transfer matches Some((transfer, _)) ==> pre.cpu_array[transfer as int].lock_state is Unlocked
        },
    ensures
        ipc_rendezvous_step_pre(pre, cpu_id, endpoint_index, waiting_state, payload),
        ipc_rendezvous_step(pre, post, cpu_id, endpoint_index, waiting_state, payload),
{ reveal(ipc_rendezvous_step_pre); reveal(ipc_step_pre); }

/// The unlocked rendezvous context on `pre` whose queue head carries an Endpoint payload is the transit pre.
pub(super) proof fn ipc_endpoint_transit_step_pre_from_u(
    pre: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, channel_ptr: RwLockEndpointPtr, peer_ptr: RwLockThreadPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, source_index: EndpointIdx, target_index: EndpointIdx,
)
    requires
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let caller = pre.thread_map.spec_index(thread_ptr);
            let peer = pre.thread_map.spec_index(peer_ptr);
            let channel = pre.endpoint_map.spec_index(channel_ptr);
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& cpu.current_process == Some(process_ptr)
            &&& cpu.current_thread == Some(thread_ptr)
            &&& pre.process_map.dom().contains(process_ptr)
            &&& pre.process_map.spec_index(process_ptr).lock_state is Unlocked
            &&& !pre.process_map.spec_index(process_ptr).killed
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& caller.lock_state is Unlocked
            &&& caller.syscall_progress is None
            &&& !caller.killed
            &&& caller.state == (ThreadState::RUNNING { cpu_id })
            &&& caller.owning_proc == process_ptr
            &&& pre.container_map.dom().contains(caller.owning_container)
            &&& edp_idx_valid(endpoint_index)
            &&& caller.endpoint_descriptors[endpoint_index as int] == Some(channel_ptr)
            &&& pre.endpoint_map.dom().contains(channel_ptr)
            &&& channel.lock_state is Unlocked
            &&& !channel.queue.contains(thread_ptr)
            &&& waiting_state is SENDING || waiting_state is RECEIVING
            &&& channel.queue.len() > 0
            &&& channel.queue[0] == peer_ptr
            &&& (channel.queue_state is SEND) != (waiting_state is SENDING)
            &&& pre.thread_map.dom().contains(peer_ptr)
            &&& peer.lock_state is Unlocked
            &&& peer_ptr != thread_ptr
            &&& !peer.killed
            &&& peer.state == (if waiting_state is SENDING { ThreadState::RECEIVING } else { ThreadState::SENDING })
            &&& peer.blocking_endpoint_ptr == Some(channel_ptr)
            &&& pre.container_map.dom().contains(peer.owning_container)
            &&& edp_idx_valid(source_index)
            &&& edp_idx_valid(target_index)
            &&& peer.ipc_payload == (IPCPayLoad::Endpoint { endpoint_index: if waiting_state is SENDING { target_index } else { source_index } })
            &&& pre.thread_map.spec_index(if waiting_state is SENDING { thread_ptr } else { peer_ptr }).endpoint_descriptors[source_index as int] is Some
            &&& pre.thread_map.spec_index(if waiting_state is SENDING { peer_ptr } else { thread_ptr }).endpoint_descriptors[target_index as int] is None
        },
    ensures
        ipc_endpoint_transit_step_pre(pre, cpu_id, endpoint_index, waiting_state, if waiting_state is SENDING { source_index } else { target_index }),
{ reveal(ipc_endpoint_transit_step_pre); reveal(ipc_rendezvous_step_pre); reveal(ipc_step_pre); }

/// Dequeuing the peer into transit under the caller's locks is the transit step on `pre`/`post`.
pub(super) proof fn ipc_endpoint_transit_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, channel_ptr: RwLockEndpointPtr,
    peer_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload_index: EndpointIdx,
)
    requires
        pre.cpu_array[cpu_id as int].current_process == Some(process_ptr),
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map[thread_ptr].endpoint_descriptors[endpoint_index as int] == Some(channel_ptr),
        pre.endpoint_map[channel_ptr].queue[0] == peer_ptr,
        post == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, ..pre.cpu_array[cpu_id as int] }),
            process_map: pre.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::WriteLocked, ..pre.process_map[process_ptr] }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU {
                lock_state: LockStateU::WriteLocked,
                syscall_progress: Some(SyscallProgress::IpcEndpoint { peer: peer_ptr, caller_sends: waiting_state is SENDING, payload_index }),
                ..pre.thread_map[thread_ptr]
            }).insert(peer_ptr, ThreadU { lock_state: LockStateU::WriteLocked, state: ThreadState::IPC_ENDPOINT_TRANSIT, blocking_endpoint_ptr: None, ..pre.thread_map[peer_ptr] }),
            endpoint_map: pre.endpoint_map.insert(channel_ptr, EndpointU { queue: pre.endpoint_map[channel_ptr].queue.skip(1), ..pre.endpoint_map[channel_ptr] }),
            ..pre
        }),
    ensures
        ipc_endpoint_transit_step(pre, post, cpu_id, endpoint_index, waiting_state, payload_index),
{ reveal(ipc_endpoint_transit_step); }

/// The write-held transfer context on `pre` with the payload endpoint unlocked is the finish pre.
pub(super) proof fn ipc_endpoint_finish_step_pre_from_u(
    pre: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, peer_ptr: RwLockThreadPtr, payload_ptr: RwLockEndpointPtr,
    receiver: RwLockThreadPtr, source_index: EndpointIdx, target_index: EndpointIdx,
)
    requires
        receiver == thread_ptr || receiver == peer_ptr,
        thread_ptr != peer_ptr,
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map[thread_ptr];
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& cpu.lock_state is WriteLocked
            &&& cpu.current_process == Some(process_ptr)
            &&& cpu.current_thread == Some(thread_ptr)
            &&& pre.process_map.dom().contains(process_ptr)
            &&& pre.process_map[process_ptr].lock_state is WriteLocked
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is WriteLocked
            &&& thread.syscall_progress == Some(SyscallProgress::IpcEndpoint {
                peer: peer_ptr, caller_sends: receiver == peer_ptr, payload_index: if receiver == peer_ptr { source_index } else { target_index },
            })
            &&& pre.thread_map.dom().contains(peer_ptr)
            &&& pre.thread_map[peer_ptr].lock_state is WriteLocked
            &&& pre.thread_map[peer_ptr].ipc_payload == (IPCPayLoad::Endpoint { endpoint_index: if receiver == peer_ptr { target_index } else { source_index } })
            &&& pre.container_map.dom().contains(thread.owning_container)
            &&& pre.container_map.dom().contains(pre.thread_map[peer_ptr].owning_container)
            &&& pre.thread_map[if receiver == peer_ptr { thread_ptr } else { peer_ptr }].endpoint_descriptors[source_index as int] == Some(payload_ptr)
            &&& pre.endpoint_map.dom().contains(payload_ptr)
            &&& pre.endpoint_map[payload_ptr].lock_state is Unlocked
        },
    ensures
        ipc_endpoint_finish_step_pre(pre, cpu_id),
{ reveal(ipc_endpoint_finish_step_pre); }

/// Scheduling the transit peer with `result` while releasing the transfer context is the finish step on `pre`/`post`.
pub(super) proof fn ipc_endpoint_finish_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, peer_ptr: RwLockThreadPtr,
    payload_ptr: RwLockEndpointPtr, receiver: RwLockThreadPtr, source_index: EndpointIdx, target_index: EndpointIdx, result: RetValueType,
    descriptor: Option<(RwLockThreadPtr, EndpointIdx)>,
)
    requires
        receiver == thread_ptr || receiver == peer_ptr,
        thread_ptr != peer_ptr,
        pre.cpu_array[cpu_id as int].current_process == Some(process_ptr),
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map[thread_ptr].syscall_progress == Some(SyscallProgress::IpcEndpoint {
            peer: peer_ptr, caller_sends: receiver == peer_ptr, payload_index: if receiver == peer_ptr { source_index } else { target_index },
        }),
        pre.thread_map[peer_ptr].ipc_payload == (IPCPayLoad::Endpoint { endpoint_index: if receiver == peer_ptr { target_index } else { source_index } }),
        pre.thread_map[if receiver == peer_ptr { thread_ptr } else { peer_ptr }].endpoint_descriptors[source_index as int] == Some(payload_ptr),
        result == ipc_endpoint_finish_result(pre, cpu_id),
        descriptor == (if result is Success { Some((receiver, target_index)) } else { None }),
        {
            let threads = match descriptor {
                Some((r, index)) => pre.thread_map.insert(r, ThreadU { endpoint_descriptors: pre.thread_map[r].endpoint_descriptors.update(index as int, Some(payload_ptr)), ..pre.thread_map[r] }),
                None => pre.thread_map,
            };
            let container = pre.thread_map[peer_ptr].owning_container;
            post == (KernelU {
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..pre.cpu_array[cpu_id as int] }),
                process_map: pre.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::Unlocked, ..pre.process_map[process_ptr] }),
                container_map: pre.container_map.insert(container, ContainerU { scheduler: pre.container_map[container].scheduler.push(peer_ptr), ..pre.container_map[container] }),
                thread_map: threads.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..threads[thread_ptr] }).insert(peer_ptr, ThreadU {
                    lock_state: LockStateU::Unlocked, state: ThreadState::SCHEDULED, blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: Some(result), ..threads[peer_ptr]
                }),
                endpoint_map: pre.endpoint_map.insert(payload_ptr, EndpointU { lock_state: LockStateU::Unlocked, queue: pre.endpoint_map[payload_ptr].queue,
                    owning_threads: if descriptor is Some { pre.endpoint_map[payload_ptr].owning_threads.insert(descriptor->Some_0) } else { pre.endpoint_map[payload_ptr].owning_threads },
                    ..pre.endpoint_map[payload_ptr]
                }),
                ..pre
            })
        },
    ensures
        ipc_endpoint_finish_step(pre, post, cpu_id),
{ reveal(ipc_endpoint_finish_step); }

/// The unlocked rendezvous context on `pre` whose queue head carries a same-length Pages payload from another
/// process is the pages enter pre.
pub(super) proof fn ipc_pages_enter_step_pre_from_u(
    pre: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, channel_ptr: RwLockEndpointPtr, peer_ptr: RwLockThreadPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, range: VaRange4K, peer_range: VaRange4K,
)
    requires
        range.wf(),
        range.len > 0,
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let caller = pre.thread_map.spec_index(thread_ptr);
            let peer = pre.thread_map.spec_index(peer_ptr);
            let channel = pre.endpoint_map.spec_index(channel_ptr);
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& cpu.current_process == Some(process_ptr)
            &&& cpu.current_thread == Some(thread_ptr)
            &&& pre.process_map.dom().contains(process_ptr)
            &&& pre.process_map.spec_index(process_ptr).lock_state is Unlocked
            &&& !pre.process_map.spec_index(process_ptr).killed
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& caller.lock_state is Unlocked
            &&& caller.syscall_progress is None
            &&& !caller.killed
            &&& caller.state == (ThreadState::RUNNING { cpu_id })
            &&& caller.owning_proc == process_ptr
            &&& pre.container_map.dom().contains(caller.owning_container)
            &&& edp_idx_valid(endpoint_index)
            &&& caller.endpoint_descriptors[endpoint_index as int] == Some(channel_ptr)
            &&& pre.endpoint_map.dom().contains(channel_ptr)
            &&& channel.lock_state is Unlocked
            &&& !channel.queue.contains(thread_ptr)
            &&& waiting_state is SENDING || waiting_state is RECEIVING
            &&& channel.queue.len() > 0
            &&& channel.queue[0] == peer_ptr
            &&& (channel.queue_state is SEND) != (waiting_state is SENDING)
            &&& pre.thread_map.dom().contains(peer_ptr)
            &&& peer.lock_state is Unlocked
            &&& peer_ptr != thread_ptr
            &&& !peer.killed
            &&& peer.state == (if waiting_state is SENDING { ThreadState::RECEIVING } else { ThreadState::SENDING })
            &&& peer.blocking_endpoint_ptr == Some(channel_ptr)
            &&& pre.container_map.dom().contains(peer.owning_container)
            &&& peer.ipc_payload == (IPCPayLoad::Pages { va_range: peer_range })
            &&& peer_range.len == range.len
            &&& peer.owning_proc != process_ptr
        },
    ensures
        ipc_pages_enter_step_pre(pre, cpu_id, endpoint_index, waiting_state, range),
{ reveal(ipc_pages_enter_step_pre); reveal(ipc_rendezvous_step_pre); reveal(ipc_step_pre); }

/// Write-locking the rendezvous context and recording both ranges is the pages enter step on `pre`/`post`.
pub(super) proof fn ipc_pages_enter_step_from_u(
    pre: KernelU, locked: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, channel_ptr: RwLockEndpointPtr,
    peer_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx, waiting_state: ThreadState, source_range: VaRange4K, target_range: VaRange4K,
)
    requires
        pre.cpu_array[cpu_id as int].current_process == Some(process_ptr),
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map[thread_ptr].endpoint_descriptors[endpoint_index as int] == Some(channel_ptr),
        pre.endpoint_map[channel_ptr].queue[0] == peer_ptr,
        pre.thread_map[peer_ptr].ipc_payload == (IPCPayLoad::Pages { va_range: if waiting_state is SENDING { target_range } else { source_range } }),
        locked == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, ..pre.cpu_array[cpu_id as int] }),
            process_map: pre.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::WriteLocked, ..pre.process_map[process_ptr] }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, ..pre.thread_map[thread_ptr] })
                .insert(peer_ptr, ThreadU { lock_state: LockStateU::WriteLocked, ..pre.thread_map[peer_ptr] }),
            endpoint_map: pre.endpoint_map.insert(channel_ptr, EndpointU { lock_state: LockStateU::WriteLocked, ..pre.endpoint_map[channel_ptr] }),
            ..pre
        }),
        post == (KernelU {
            thread_map: locked.thread_map.insert(thread_ptr, ThreadU {
                syscall_progress: Some(SyscallProgress::IpcPages { source_range, target_range, peer: peer_ptr, locked: false, released: None }), ..locked.thread_map[thread_ptr]
            }),
            ..locked
        }),
    ensures
        ipc_pages_enter_step(pre, post, cpu_id, endpoint_index, waiting_state, if waiting_state is SENDING { source_range } else { target_range }),
{ reveal(ipc_pages_enter_step); }

/// The held pages context on `pre` with both page tables unlocked is the lock-tables pre.
pub(super) proof fn ipc_pages_lock_tables_step_pre_from_u(pre: KernelU, cpu_id: CpuId)
    requires
        {
            let progress = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0].syscall_progress->Some_0;
            &&& ipc_pages_held(pre, cpu_id)
            &&& !progress->IpcPages_locked
            &&& progress->IpcPages_released is None
            &&& ipc_pages_tables_in(pre, cpu_id, LockStateU::Unlocked)
        },
    ensures
        ipc_pages_lock_tables_step_pre(pre, cpu_id),
{ reveal(ipc_pages_lock_tables_step_pre); }

/// Write-locking both page tables and recording it is the lock-tables step on `pre`/`post`.
pub(super) proof fn ipc_pages_lock_tables_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, source_range: VaRange4K, target_range: VaRange4K, peer_ptr: RwLockThreadPtr,
    source: RwLockProcessPtr, target: RwLockProcessPtr,
)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map[thread_ptr].syscall_progress == Some(SyscallProgress::IpcPages { source_range, target_range, peer: peer_ptr, locked: false, released: None }),
        pre.thread_map[ipc_pages_sender(pre, cpu_id)].owning_proc == source,
        pre.thread_map[ipc_pages_receiver(pre, cpu_id)].owning_proc == target,
        post == (KernelU {
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU {
                syscall_progress: Some(SyscallProgress::IpcPages { source_range, target_range, peer: peer_ptr, locked: true, released: None }), ..pre.thread_map[thread_ptr]
            }),
            process_map: pre.process_map.insert(source, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..pre.process_map[source].pagetable->Some_0 }), ..pre.process_map[source]
            }).insert(target, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..pre.process_map[target].pagetable->Some_0 }), ..pre.process_map[target]
            }),
            ..pre
        }),
    ensures
        ipc_pages_lock_tables_step(pre, post, cpu_id),
{ reveal(ipc_pages_lock_tables_step); }

/// The held pages context on `pre` with both page tables write-locked and nothing released is the check pre.
pub(super) proof fn ipc_pages_check_step_pre_from_u(pre: KernelU, cpu_id: CpuId)
    requires
        {
            let progress = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0].syscall_progress->Some_0;
            &&& ipc_pages_held(pre, cpu_id)
            &&& progress->IpcPages_locked
            &&& progress->IpcPages_released is None
            &&& ipc_pages_tables_in(pre, cpu_id, LockStateU::WriteLocked)
        },
    ensures
        ipc_pages_check_step_pre(pre, cpu_id),
{ reveal(ipc_pages_check_step_pre); }

/// Recording a passed check as the start of sharing is the check step on `pre`/`post`.
pub(super) proof fn ipc_pages_passed_check_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, source_range: VaRange4K, target_range: VaRange4K, peer_ptr: RwLockThreadPtr,
)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map[thread_ptr].syscall_progress == Some(SyscallProgress::IpcPages { source_range, target_range, peer: peer_ptr, locked: true, released: None }),
        ipc_pages_check_result(pre, cpu_id) is Success,
        post == (KernelU {
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU {
                syscall_progress: Some(SyscallProgress::Share4k { source_range, target_range, shared: 0, origin: Share4kOrigin::IpcPages { peer: peer_ptr } }),
                ..pre.thread_map[thread_ptr]
            }),
            ..pre
        }),
    ensures
        ipc_pages_check_step(pre, post, cpu_id),
{ reveal(ipc_pages_check_step); }

/// Recording a failed check with both page tables released is the check step on `pre`/`post`.
pub(super) proof fn ipc_pages_failed_check_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, source_range: VaRange4K, target_range: VaRange4K, peer_ptr: RwLockThreadPtr,
    result: RetValueType, source: RwLockProcessPtr, target: RwLockProcessPtr,
)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map[thread_ptr].syscall_progress == Some(SyscallProgress::IpcPages { source_range, target_range, peer: peer_ptr, locked: true, released: None }),
        result == ipc_pages_check_result(pre, cpu_id),
        !(result is Success),
        pre.thread_map[ipc_pages_sender(pre, cpu_id)].owning_proc == source,
        pre.thread_map[ipc_pages_receiver(pre, cpu_id)].owning_proc == target,
        post == (KernelU {
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU {
                syscall_progress: Some(SyscallProgress::IpcPages { source_range, target_range, peer: peer_ptr, locked: false, released: Some(result) }),
                ..pre.thread_map[thread_ptr]
            }),
            process_map: pre.process_map.insert(source, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..pre.process_map[source].pagetable->Some_0 }), ..pre.process_map[source]
            }).insert(target, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..pre.process_map[target].pagetable->Some_0 }), ..pre.process_map[target]
            }),
            ..pre
        }),
    ensures
        ipc_pages_check_step(pre, post, cpu_id),
{ reveal(ipc_pages_check_step); }

/// The fully shared pages context on `pre` with both page tables write-locked is the unlock-tables pre.
pub(super) proof fn ipc_pages_unlock_tables_step_pre_from_u(pre: KernelU, cpu_id: CpuId)
    requires
        {
            let progress = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0].syscall_progress->Some_0;
            let objects = share_4k_objects(pre, cpu_id);
            let source = pre.thread_map[objects.source_thread].owning_proc;
            &&& share_4k_locked(pre, cpu_id)
            &&& progress->Share4k_origin is IpcPages
            &&& progress->Share4k_shared == progress->Share4k_source_range.len
            &&& source != objects.target
            &&& pre.process_map.dom().contains(source)
            &&& pre.process_map.dom().contains(objects.target)
            &&& pre.process_map[source].pagetable is Some
            &&& pre.process_map[objects.target].pagetable is Some
            &&& pre.process_map[source].pagetable->Some_0.lock_state is WriteLocked
            &&& pre.process_map[objects.target].pagetable->Some_0.lock_state is WriteLocked
        },
    ensures
        ipc_pages_unlock_tables_step_pre(pre, cpu_id),
{ reveal(ipc_pages_unlock_tables_step_pre); }

/// Releasing both page tables after sharing and recording Success is the unlock-tables step on `pre`/`post`.
pub(super) proof fn ipc_pages_unlock_tables_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, source_range: VaRange4K, target_range: VaRange4K, peer_ptr: RwLockThreadPtr,
    source: RwLockProcessPtr, target: RwLockProcessPtr,
)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map[thread_ptr].syscall_progress == Some(SyscallProgress::Share4k {
            source_range, target_range, shared: source_range.len, origin: Share4kOrigin::IpcPages { peer: peer_ptr },
        }),
        share_4k_objects(pre, cpu_id).target == target,
        pre.thread_map[share_4k_objects(pre, cpu_id).source_thread].owning_proc == source,
        post == (KernelU {
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU {
                syscall_progress: Some(SyscallProgress::IpcPages { source_range, target_range, peer: peer_ptr, locked: false, released: Some(RetValueType::Success) }),
                ..pre.thread_map[thread_ptr]
            }),
            process_map: pre.process_map.insert(source, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..pre.process_map[source].pagetable->Some_0 }), ..pre.process_map[source]
            }).insert(target, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..pre.process_map[target].pagetable->Some_0 }), ..pre.process_map[target]
            }),
            ..pre
        }),
    ensures
        ipc_pages_unlock_tables_step(pre, post, cpu_id),
{ reveal(ipc_pages_unlock_tables_step); }

/// Scheduling the recorded peer with the released result while releasing the pages context is the pages
/// finish step on `pre`/`post`.
pub(super) proof fn ipc_pages_finish_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, peer_ptr: RwLockThreadPtr,
    channel_ptr: RwLockEndpointPtr, result: RetValueType,
)
    requires
        {
            let progress = pre.thread_map[thread_ptr].syscall_progress;
            &&& ipc_pages_held(pre, cpu_id)
            &&& pre.cpu_array[cpu_id as int].current_process == Some(process_ptr)
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& progress->Some_0->IpcPages_peer == peer_ptr
            &&& progress->Some_0->IpcPages_released == Some(result)
            &&& !progress->Some_0->IpcPages_locked
            &&& pre.thread_map[peer_ptr].blocking_endpoint_ptr == Some(channel_ptr)
            &&& pre.endpoint_map[channel_ptr].queue.len() > 0
            &&& pre.endpoint_map[channel_ptr].queue[0] == peer_ptr
            &&& pre.container_map.dom().contains(pre.thread_map[peer_ptr].owning_container)
        },
        {
            let container = pre.thread_map[peer_ptr].owning_container;
            post == (KernelU {
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..pre.cpu_array[cpu_id as int] }),
                process_map: pre.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::Unlocked, ..pre.process_map[process_ptr] }),
                container_map: pre.container_map.insert(container, ContainerU { scheduler: pre.container_map[container].scheduler.push(peer_ptr), ..pre.container_map[container] }),
                thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..pre.thread_map[thread_ptr] }).insert(peer_ptr, ThreadU {
                    lock_state: LockStateU::Unlocked, state: ThreadState::SCHEDULED, blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: Some(result), ..pre.thread_map[peer_ptr]
                }),
                endpoint_map: pre.endpoint_map.insert(channel_ptr, EndpointU { lock_state: LockStateU::Unlocked, queue: pre.endpoint_map[channel_ptr].queue.skip(1),
                    owning_threads: pre.endpoint_map[channel_ptr].owning_threads, ..pre.endpoint_map[channel_ptr]
                }),
                ..pre
            })
        },
    ensures
        ipc_pages_finish_step_pre(pre, cpu_id),
        ipc_pages_finish_step(pre, post, cpu_id),
{ reveal(ipc_pages_finish_step_pre); reveal(ipc_pages_finish_step); }

/// The one block step pushed since `before` is the complete blocking trace.
pub(super) proof fn ipc_ordinary_trace_block_step(
    steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState,
    payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool,
)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        ipc_block_step_pre(pre, cpu_id, endpoint_index, waiting_state),
        ipc_block_step(pre, post, cpu_id, endpoint_index, waiting_state, payload, regs, flushed_default_pcid),
    ensures
        ipc_ordinary_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index, waiting_state,
            payload, regs, flushed_default_pcid, RetValueType::CpuIdle),
{ reveal(ipc_ordinary_syscall_trace); }

/// A blocking trace since `before` is the payload's syscall trace.
pub(super) proof fn ipc_syscall_trace_from_block(
    steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState,
    payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool,
)
    requires
        payload is Pages ==> payload->Pages_va_range.wf() && payload->Pages_va_range.len > 0,
        ipc_ordinary_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index, waiting_state,
            payload, regs, flushed_default_pcid, RetValueType::CpuIdle),
    ensures
        payload is Pages ==> ipc_pages_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index,
            waiting_state, payload->Pages_va_range, regs, flushed_default_pcid, RetValueType::CpuIdle),
        payload is Endpoint ==> ipc_endpoint_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index,
            waiting_state, payload->Endpoint_endpoint_index, regs, flushed_default_pcid, RetValueType::CpuIdle),
{ reveal(ipc_pages_syscall_trace); reveal(ipc_endpoint_syscall_trace); }

/// The rendezvous outcome since `before`, per payload kind, is the payload's syscall trace.
pub(super) proof fn ipc_syscall_trace_from_rendezvous(
    steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState,
    payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool, ret: RetValueType,
)
    requires
        !(ret is CpuIdle),
        payload is Pages ==> ipc_pages_rendezvous_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index,
            waiting_state, payload->Pages_va_range, ret),
        payload is Endpoint ==> ipc_endpoint_rendezvous_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index,
            waiting_state, payload->Endpoint_endpoint_index, ret),
        (payload is Empty || payload is Cpu || payload is ReceiveCpu) ==> if ipc_rendezvous_ret(ret) {
            &&& steps.view() == before.push(KernelStep { old_u: pre, new_u: post })
            &&& ret == ipc_rendezvous_result(pre, cpu_id, endpoint_index, waiting_state, payload)
            &&& ipc_rendezvous_step_pre(pre, cpu_id, endpoint_index, waiting_state, payload)
            &&& ipc_rendezvous_step(pre, post, cpu_id, endpoint_index, waiting_state, payload)
        } else {
            &&& steps.view() == before
            &&& post == pre
        },
    ensures
        payload is Pages ==> ipc_pages_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index,
            waiting_state, payload->Pages_va_range, regs, flushed_default_pcid, ret),
        payload is Endpoint ==> ipc_endpoint_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index,
            waiting_state, payload->Endpoint_endpoint_index, regs, flushed_default_pcid, ret),
        (payload is Empty || payload is Cpu || payload is ReceiveCpu) ==> ipc_ordinary_syscall_trace(
            steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index, waiting_state, payload, regs, flushed_default_pcid, ret),
{ reveal(ipc_pages_syscall_trace); reveal(ipc_endpoint_syscall_trace); reveal(ipc_ordinary_syscall_trace); }

/// A call rejected before any visible change records no step for any payload kind.
pub(super) proof fn ipc_syscall_trace_stutter(
    trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers,
    flushed_default_pcid: bool, ret: RetValueType,
)
    requires
        trace.len() == 0,
        ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcNoPeer || ret is ErrorIpcSameDirection || ret is ErrorIpcPeerKilled,
    ensures
        payload is Pages ==> ipc_pages_syscall_trace(trace, pre, pre, cpu_id, endpoint_index, waiting_state, payload->Pages_va_range, regs, flushed_default_pcid, ret),
        payload is Endpoint ==> ipc_endpoint_syscall_trace(trace, pre, pre, cpu_id, endpoint_index, waiting_state, payload->Endpoint_endpoint_index, regs, flushed_default_pcid, ret),
        (payload is Empty || payload is Cpu || payload is ReceiveCpu) ==> ipc_ordinary_syscall_trace(trace, pre, pre, cpu_id, endpoint_index, waiting_state, payload, regs, flushed_default_pcid, ret),
{
    reveal(ipc_pages_syscall_trace); reveal(ipc_endpoint_syscall_trace); reveal(ipc_ordinary_syscall_trace);
    reveal(ipc_pages_rendezvous_syscall_trace); reveal(ipc_endpoint_rendezvous_trace);
}

/// A rendezvous abandoned because the queue head died records no step for the Pages and Endpoint payloads.
pub(super) proof fn ipc_rendezvous_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, ret: RetValueType)
    requires
        trace.len() == 0,
        ret is ErrorIpcPeerKilled,
    ensures
        payload is Pages ==> ipc_pages_rendezvous_syscall_trace(trace, pre, pre, cpu_id, endpoint_index, waiting_state, payload->Pages_va_range, ret),
        payload is Endpoint ==> ipc_endpoint_rendezvous_trace(trace, pre, pre, cpu_id, endpoint_index, waiting_state, payload->Endpoint_endpoint_index, ret),
{ reveal(ipc_pages_rendezvous_syscall_trace); reveal(ipc_endpoint_rendezvous_trace); }

/// The one rendezvous error step pushed since `before` is the Pages or Endpoint rendezvous trace.
pub(super) proof fn ipc_rendezvous_trace_error_step(
    steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState,
    payload: IPCPayLoad, ret: RetValueType,
)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        ret == ipc_rendezvous_result(pre, cpu_id, endpoint_index, waiting_state, payload),
        ipc_rendezvous_step_pre(pre, cpu_id, endpoint_index, waiting_state, payload),
        ipc_rendezvous_step(pre, post, cpu_id, endpoint_index, waiting_state, payload),
        payload is Pages ==> payload->Pages_va_range.wf() && payload->Pages_va_range.len > 0 && (ret is ErrorIpcSameProcess || ret is ErrorIpcTypeMismatch),
        payload is Endpoint ==> ret is ErrorIpcEndpointSourceInvalid || ret is ErrorIpcEndpointTargetInUse || ret is ErrorIpcTypeMismatch,
    ensures
        payload is Pages ==> ipc_pages_rendezvous_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index,
            waiting_state, payload->Pages_va_range, ret),
        payload is Endpoint ==> ipc_endpoint_rendezvous_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index,
            waiting_state, payload->Endpoint_endpoint_index, ret),
{ reveal(ipc_pages_rendezvous_syscall_trace); reveal(ipc_endpoint_rendezvous_trace); }

/// The transit step pushed since `before` is the partial endpoint trace after transit.
pub(super) proof fn ipc_endpoint_trace_transit_step(
    steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload_index: EndpointIdx,
)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        ipc_endpoint_transit_step_pre(pre, cpu_id, endpoint_index, waiting_state, payload_index),
        ipc_endpoint_transit_step(pre, post, cpu_id, endpoint_index, waiting_state, payload_index),
    ensures
        ipc_endpoint_trace_after_transit(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, cpu_id, endpoint_index, waiting_state, payload_index),
{ reveal(ipc_endpoint_trace_after_transit); }

/// The finish step pushed after the partial trace that starts at `start` completes the endpoint rendezvous trace.
pub(super) proof fn ipc_endpoint_trace_finish_step(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, finish_pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx,
    waiting_state: ThreadState, payload_index: EndpointIdx, ret: RetValueType,
)
    requires
        0 <= start <= before.len(),
        ipc_endpoint_trace_after_transit(before.subrange(start, before.len() as int), pre, cpu_id, endpoint_index, waiting_state, payload_index),
        steps.view() == before.push(KernelStep { old_u: finish_pre, new_u: post }),
        ipc_endpoint_finish_step_pre(finish_pre, cpu_id),
        ipc_endpoint_finish_step(finish_pre, post, cpu_id),
        ret == ipc_endpoint_finish_result(finish_pre, cpu_id),
    ensures
        ipc_endpoint_rendezvous_trace(steps.view().subrange(start, steps.view().len() as int), pre, post, cpu_id, endpoint_index, waiting_state, payload_index, ret),
{ reveal(ipc_endpoint_rendezvous_trace); reveal(ipc_endpoint_trace_after_transit); }

/// The enter step pushed since `before` is the partial pages trace after entering.
pub(super) proof fn ipc_pages_trace_enter_step(
    steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, range: VaRange4K,
)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        ipc_pages_enter_step_pre(pre, cpu_id, endpoint_index, waiting_state, range),
        ipc_pages_enter_step(pre, post, cpu_id, endpoint_index, waiting_state, range),
    ensures
        ipc_pages_trace_after_enter(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, cpu_id, endpoint_index, waiting_state, range),
{ reveal(ipc_pages_trace_after_enter); }

/// The lock-tables step pushed after the partial trace that starts at `start` is the partial trace after locking.
pub(super) proof fn ipc_pages_trace_lock_step(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, lock_pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx,
    waiting_state: ThreadState, range: VaRange4K,
)
    requires
        0 <= start <= before.len(),
        ipc_pages_trace_after_enter(before.subrange(start, before.len() as int), pre, cpu_id, endpoint_index, waiting_state, range),
        steps.view() == before.push(KernelStep { old_u: lock_pre, new_u: post }),
        ipc_pages_lock_tables_step_pre(lock_pre, cpu_id),
        ipc_pages_lock_tables_step(lock_pre, post, cpu_id),
    ensures
        ipc_pages_trace_after_lock(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, endpoint_index, waiting_state, range),
{ reveal(ipc_pages_trace_after_enter); reveal(ipc_pages_trace_after_lock); }

/// A failed check step pushed after the partial trace that starts at `start` completes the mapping trace.
pub(super) proof fn ipc_pages_trace_failed_check_step(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, check_pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx,
    waiting_state: ThreadState, range: VaRange4K, result: RetValueType,
)
    requires
        0 <= start <= before.len(),
        ipc_pages_trace_after_lock(before.subrange(start, before.len() as int), pre, cpu_id, endpoint_index, waiting_state, range),
        steps.view() == before.push(KernelStep { old_u: check_pre, new_u: post }),
        ipc_pages_check_step_pre(check_pre, cpu_id),
        ipc_pages_check_step(check_pre, post, cpu_id),
        result == ipc_pages_check_result(check_pre, cpu_id),
        !(result is Success),
    ensures
        ipc_pages_mapping_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, endpoint_index, waiting_state, range, result),
{ reveal(ipc_pages_trace_after_lock); reveal(ipc_pages_mapping_trace); }

/// A passed check step and the share steps pushed after the partial trace that starts at `start` are the
/// partial trace after sharing.
pub(super) proof fn ipc_pages_trace_share_steps(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, range: VaRange4K,
)
    requires
        0 <= start <= before.len(),
        ipc_pages_trace_after_lock(before.subrange(start, before.len() as int), pre, cpu_id, endpoint_index, waiting_state, range),
        before.len() + range.len + 1 <= steps.view().len() <= before.len() + 4 * range.len + 1,
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        ipc_pages_check_result(steps.view()[before.len() as int].old_u, cpu_id) is Success,
        ipc_pages_check_step_pre(steps.view()[before.len() as int].old_u, cpu_id),
        ipc_pages_check_step(steps.view()[before.len() as int].old_u, steps.view()[before.len() as int].new_u, cpu_id),
        forall|j: int| #![trigger steps.view()[j]] before.len() < j < steps.view().len() ==> share_4k_range_step(steps.view()[j], cpu_id),
    ensures
        ipc_pages_trace_after_share(steps.view(), start, pre, cpu_id, endpoint_index, waiting_state, range),
{ reveal(ipc_pages_trace_after_lock); reveal(ipc_pages_trace_after_share); }

/// The unlock-tables step pushed after the partial trace that starts at `start` completes the successful mapping trace.
pub(super) proof fn ipc_pages_trace_unlock_step(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, unlock_pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx,
    waiting_state: ThreadState, range: VaRange4K,
)
    requires
        0 <= start <= before.len(),
        ipc_pages_trace_after_share(before, start, pre, cpu_id, endpoint_index, waiting_state, range),
        steps.view() == before.push(KernelStep { old_u: unlock_pre, new_u: post }),
        ipc_pages_unlock_tables_step_pre(unlock_pre, cpu_id),
        ipc_pages_unlock_tables_step(unlock_pre, post, cpu_id),
    ensures
        ipc_pages_mapping_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, endpoint_index, waiting_state, range, RetValueType::Success),
{ reveal(ipc_pages_trace_after_share); reveal(ipc_pages_mapping_trace); }

/// The finish step pushed after the mapping trace that starts at `start` completes the pages rendezvous trace.
pub(super) proof fn ipc_pages_rendezvous_trace_finish_step(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, finish_pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx,
    waiting_state: ThreadState, range: VaRange4K, result: RetValueType,
)
    requires
        0 <= start <= before.len(),
        ipc_pages_mapping_trace(before.subrange(start, before.len() as int), pre, cpu_id, endpoint_index, waiting_state, range, result),
        steps.view() == before.push(KernelStep { old_u: finish_pre, new_u: post }),
        ipc_pages_finish_step_pre(finish_pre, cpu_id),
        ipc_pages_finish_step(finish_pre, post, cpu_id),
        result is Success || result is ErrorIpcSourceUnmapped || result is ErrorIpcPageOwnerMismatch || result is ErrorNoQuota || result is ErrorVaInUse || result is Error,
    ensures
        ipc_pages_rendezvous_syscall_trace(steps.view().subrange(start, steps.view().len() as int), pre, post, cpu_id, endpoint_index, waiting_state, range, result),
{
    reveal(ipc_pages_rendezvous_syscall_trace); reveal(ipc_pages_mapping_trace);
    let trace = steps.view().subrange(start, steps.view().len() as int);
    vstd::assert_seqs_equal!(trace.subrange(0, trace.len() - 1) == before.subrange(start, before.len() as int));
}

/// A pages call rejected before any visible change records no step.
pub(super) proof fn ipc_pages_syscall_trace_stutter(
    trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, range: VaRange4K, regs: Registers,
    flushed_default_pcid: bool, ret: RetValueType,
)
    requires
        trace.len() == 0,
        ret is Error,
    ensures
        ipc_pages_syscall_trace(trace, pre, pre, cpu_id, endpoint_index, waiting_state, range, regs, flushed_default_pcid, ret),
{ reveal(ipc_pages_syscall_trace); reveal(ipc_pages_rendezvous_syscall_trace); }
} // verus!
