use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_dispatch::endpoint_queue_member_thread_facts;
pub(super) use super::syscall_ipc_pages_trace::*;
verus! {
/// The entry rejection on the user projection of `krnl` is `ret` when `ret` follows the same checks on `krnl`.
pub(super) proof fn ipc_entry_result_from_k(krnl: &KernelK, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, blocking: bool, ret: Option<RetValueType>)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        ({
            let cpu = krnl.cpu_arr.spec_index(cpu_id).value;
            let thread = krnl.thr_mp.spec_index(cpu.view().view().current_thread->Some_0);
            let endpoint_ptr = thread.view().endpoint_descriptors.view()[endpoint_index as int];
            let queue = krnl.ep_mp.spec_index(endpoint_ptr->Some_0).view().queue.view();
            let same_direction = (krnl.ep_mp.spec_index(endpoint_ptr->Some_0).view().queue_state is SEND) == waiting_state.is_endpoint_send_waiting();
            if !(cpu.view().view().state is Running) || cpu.being_killed() { ret == Some(RetValueType::CpuIdle) }
            else if !krnl.thr_mp.dom().contains(cpu.view().view().current_thread->Some_0) { false }
            else if thread.being_killed() { ret == Some(RetValueType::ErrorThreadKilled) }
            else if waiting_state is RECEIVING_CALL && thread.view().caller is Some { ret == Some(RetValueType::ErrorReplyOutOfPhase) }
            else if endpoint_ptr is None { ret == Some(RetValueType::ErrorInvalidEndpoint) }
            else if !krnl.ep_mp.dom().contains(endpoint_ptr->Some_0) { false }
            else if queue.len() == 0 || same_direction {
                ret == if blocking { Some(RetValueType::CpuIdle) } else if queue.len() == 0 { Some(RetValueType::ErrorIpcNoPeer) } else { Some(RetValueType::ErrorIpcSameDirection) }
            } else { ret == if krnl.thr_mp.spec_index(queue[0]).being_killed() { Some(RetValueType::ErrorIpcPeerKilled) } else { None } }
        }),
    ensures ipc_entry_result(kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index, waiting_state, blocking) == ret,
{
    reveal(ipc_entry_result); kernel_cpu_projection_at(krnl, cpu_id);
    let thread_ptr = krnl.cpu_arr.spec_index(cpu_id).value.view().view().current_thread->Some_0;
    let endpoint_ptr = krnl.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int];
    let queue = krnl.ep_mp.spec_index(endpoint_ptr->Some_0).view().queue.view();
    if krnl.thr_mp.dom().contains(thread_ptr) { kernel_thread_projection_at(krnl, thread_ptr); }
    if endpoint_ptr is Some && krnl.ep_mp.dom().contains(endpoint_ptr->Some_0) {
        kernel_endpoint_projection_at(krnl, endpoint_ptr->Some_0);
        if queue.len() > 0 { assert(queue.contains(queue[0])); endpoint_queue_member_thread_facts(krnl, endpoint_ptr->Some_0, queue[0]); kernel_thread_projection_at(krnl, queue[0]); }
    }
}

/// The rendezvous result on the user projection of `krnl` is `ret` when the queue head `peer_ptr` meets the running `thread_ptr` as `ret` records.
pub(super) proof fn ipc_rendezvous_result_from_k(
    krnl: &KernelK, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr, peer_ptr: RwLockThreadPtr, ret: RetValueType,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        krnl.thr_mp.dom().contains(thread_ptr),
        krnl.thr_mp.dom().contains(peer_ptr),
        krnl.ep_mp.dom().contains(endpoint_ptr),
        krnl.cpu_arr.spec_index(cpu_id).value.view().view().current_thread == Some(thread_ptr),
        krnl.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int] == Some(endpoint_ptr),
        krnl.ep_mp.spec_index(endpoint_ptr).view().queue.view()[0] == peer_ptr,
        ({
            let peer = krnl.thr_mp.spec_index(peer_ptr).view();
            let sends = waiting_state.is_endpoint_send_waiting();
            let sent = if sends { payload } else { peer.ipc_payload };
            let received = if sends { peer.ipc_payload } else { payload };
            if waiting_state is CALLING || waiting_state is RECEIVING_CALL {
                ret == if peer.state == (if sends { ThreadState::RECEIVING_CALL } else { ThreadState::CALLING }) { RetValueType::ErrorCallAcrossContainers } else { RetValueType::ErrorIpcTypeMismatch }
            } else if peer.state != (if sends { ThreadState::RECEIVING } else { ThreadState::SENDING }) { ret is ErrorIpcTypeMismatch }
            else {
                match (sent, received) {
                    (IPCPayLoad::Empty, IPCPayLoad::Empty) => ret is Success,
                    (IPCPayLoad::Cpu { cpu_id: transfer }, IPCPayLoad::ReceiveCpu) => {
                        let sender = krnl.thr_mp.spec_index(if sends { thread_ptr } else { peer_ptr }).view();
                        let cpu = krnl.cpu_arr.spec_index(transfer).value.view().view();
                        ret == if sender.owning_container == krnl.thr_mp.spec_index(if sends { peer_ptr } else { thread_ptr }).view().owning_container { RetValueType::ErrorIpcSameContainer }
                            else if !index_valid(NUM_CPUS, transfer) || cpu.owning_container != sender.owning_container { RetValueType::ErrorIpcCpuOwnerMismatch }
                            else if !(cpu.state is Off) { RetValueType::ErrorIpcCpuNotOff }
                            else if sends { RetValueType::Success } else { RetValueType::SuccessUsize { value: transfer } }
                    },
                    (IPCPayLoad::Endpoint { endpoint_index: source }, IPCPayLoad::Endpoint { endpoint_index: target }) => ret == if krnl.thr_mp.spec_index(if sends { thread_ptr } else { peer_ptr }).view().endpoint_descriptors.view()[source as int] is None {
                        RetValueType::ErrorIpcEndpointSourceInvalid
                    } else if krnl.thr_mp.spec_index(if sends { peer_ptr } else { thread_ptr }).view().endpoint_descriptors.view()[target as int] is Some {
                        RetValueType::ErrorIpcEndpointTargetInUse
                    } else { RetValueType::Success },
                    (IPCPayLoad::Pages { va_range: source }, IPCPayLoad::Pages { va_range: target }) => ret == if source.len != target.len { RetValueType::ErrorIpcTypeMismatch }
                        else if krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == krnl.thr_mp.spec_index(peer_ptr).view().owning_proc { RetValueType::ErrorIpcSameProcess }
                        else { RetValueType::Success },
                    (IPCPayLoad::Pci { bus: sent_bus, dev: sent_dev, fun: sent_fun }, IPCPayLoad::Pci { bus: received_bus, dev: received_dev, fun: received_fun }) => {
                        let sender_proc = krnl.thr_mp.spec_index(if sends { thread_ptr } else { peer_ptr }).view().owning_proc;
                        &&& ret == if sent_bus != received_bus || sent_dev != received_dev || sent_fun != received_fun { RetValueType::ErrorIpcTypeMismatch }
                            else if krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == krnl.thr_mp.spec_index(peer_ptr).view().owning_proc { RetValueType::ErrorIpcSameProcess }
                            else if !krnl.prc_mp.spec_index(sender_proc).view_ghost().owned_pci_functions.view().contains((sent_bus as usize, sent_dev as usize, sent_fun as usize)) {
                                RetValueType::ErrorIpcPciOwnerMismatch
                            } else { RetValueType::Success }
                        &&& (ret is Success || ret is ErrorIpcPciOwnerMismatch) ==> krnl.prc_mp.dom().contains(sender_proc)
                    },
                    _ => ret is ErrorIpcTypeMismatch,
                }
            }
        }),
    ensures
        ipc_rendezvous_result(kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index, waiting_state, payload) == ret,
        ipc_cpu_transfer(kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index, payload, ret) == if payload is Cpu && ret is Success { Some((payload->Cpu_cpu_id, peer_ptr)) }
            else if payload is ReceiveCpu && ret is SuccessUsize { Some((ret->SuccessUsize_value, thread_ptr)) } else { None },
        ipc_pci_transfer(kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index, waiting_state, payload, ret) == if payload is Pci && ret is Success {
            let sends = waiting_state is SENDING;
            Some(((payload->Pci_bus as usize, payload->Pci_dev as usize, payload->Pci_fun as usize), krnl.thr_mp.spec_index(if sends { thread_ptr } else { peer_ptr }).view().owning_proc,
                krnl.thr_mp.spec_index(if sends { peer_ptr } else { thread_ptr }).view().owning_proc))
        } else { None },
{
    kernel_cpu_projection_at(krnl, cpu_id); kernel_thread_projection_at(krnl, thread_ptr); kernel_thread_projection_at(krnl, peer_ptr); kernel_endpoint_queue_projection_at(krnl, endpoint_ptr);
    let sent = if waiting_state.is_endpoint_send_waiting() { payload } else { krnl.thr_mp.spec_index(peer_ptr).view().ipc_payload };
    let sender_proc = krnl.thr_mp.spec_index(if waiting_state.is_endpoint_send_waiting() { thread_ptr } else { peer_ptr }).view().owning_proc;
    if sent is Cpu && index_valid(NUM_CPUS, sent->Cpu_cpu_id) { kernel_cpu_projection_at(krnl, sent->Cpu_cpu_id); }
    if krnl.prc_mp.dom().contains(sender_proc) { kernel_process_projection_at(krnl, sender_proc); }
}

/// The block wrapper's user-view facts are exactly the block step on `pre`/`post`.
pub(super) proof fn ipc_block_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool)
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
    pci_transfer: Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)>, payload: IPCPayLoad, cpu_sets_locked: bool,
)
    requires
        kernel_u_ipc_rendezvous_changed(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer),
        {
            let result = ipc_rendezvous_result(pre, cpu_id, endpoint_index, waiting_state, payload);
            &&& peer_result == ipc_peer_result(payload, result)
            &&& cpu_transfer == ipc_cpu_transfer(pre, cpu_id, endpoint_index, payload, result)
            &&& pci_transfer == ipc_pci_transfer(pre, cpu_id, endpoint_index, waiting_state, payload, result)
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
            &&& waiting_state.is_endpoint_waiting()
            &&& endpoint.queue.len() > 0
            &&& endpoint.queue[0] == peer_thread_ptr
            &&& (endpoint.queue_state is SEND) != waiting_state.is_endpoint_send_waiting()
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
            &&& pci_transfer matches Some((bdf, sender, _)) ==> pre.iommu_root_table.attached[bdf.0 as int][bdf.1 as int][bdf.2 as int] && pre.process_map[sender].iommu_table is Some
                ==> pre.process_map[sender].iommu_table->Some_0.lock_state is Unlocked
        },
    ensures
        ipc_rendezvous_step_pre(pre, cpu_id, endpoint_index, waiting_state, payload),
        ipc_rendezvous_step(pre, post, cpu_id, endpoint_index, waiting_state, payload),
{ reveal(ipc_rendezvous_step_pre); reveal(ipc_step_pre); }

/// The unlocked rendezvous context on `krnl` whose queue head carries an Endpoint payload gives the transit pre and the user-view context of the
/// transit step.
pub(super) proof fn ipc_endpoint_transit_step_pre_from_k(
    krnl: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, channel_ptr: RwLockEndpointPtr, peer_ptr: RwLockThreadPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, source_index: EndpointIdx, target_index: EndpointIdx,
)
    requires
        ({
            let cpu = krnl.cpu_arr.spec_index(cpu_id).value;
            let caller = krnl.thr_mp.spec_index(thread_ptr);
            let peer = krnl.thr_mp.spec_index(peer_ptr);
            let channel = krnl.ep_mp.spec_index(channel_ptr);
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& cpu.locking_thread() is None
            &&& cpu.view().view().state is Running
            &&& cpu.view().view().current_process == Some(process_ptr)
            &&& cpu.view().view().current_thread == Some(thread_ptr)
            &&& krnl.prc_mp.dom().contains(process_ptr)
            &&& krnl.thr_mp.dom().contains(thread_ptr)
            &&& caller.locking_thread() is None
            &&& caller.view().syscall_progress.view() is None
            &&& !caller.being_killed()
            &&& caller.view().state == (ThreadState::RUNNING { cpu_id })
            &&& caller.view().owning_proc == process_ptr
            &&& krnl.ctn_mp.dom().contains(caller.view().owning_container)
            &&& edp_idx_valid(endpoint_index)
            &&& caller.view().endpoint_descriptors.view()[endpoint_index as int] == Some(channel_ptr)
            &&& krnl.ep_mp.dom().contains(channel_ptr)
            &&& channel.locking_thread() is None
            &&& !channel.view().queue.view().contains(thread_ptr)
            &&& waiting_state is SENDING || waiting_state is RECEIVING
            &&& channel.view().queue.view().len() > 0
            &&& channel.view().queue.view()[0] == peer_ptr
            &&& (channel.view().queue_state is SEND) != (waiting_state is SENDING)
            &&& krnl.thr_mp.dom().contains(peer_ptr)
            &&& peer.locking_thread() is None
            &&& peer_ptr != thread_ptr
            &&& !peer.being_killed()
            &&& peer.view().state == (if waiting_state is SENDING { ThreadState::RECEIVING } else { ThreadState::SENDING })
            &&& peer.view().blocking_endpoint_ptr == Some(channel_ptr)
            &&& krnl.ctn_mp.dom().contains(peer.view().owning_container)
            &&& edp_idx_valid(source_index)
            &&& edp_idx_valid(target_index)
            &&& peer.view().ipc_payload == (IPCPayLoad::Endpoint { endpoint_index: if waiting_state is SENDING { target_index } else { source_index } })
            &&& krnl.thr_mp.spec_index(if waiting_state is SENDING { thread_ptr } else { peer_ptr }).view().endpoint_descriptors.view()[source_index as int] is Some
            &&& krnl.thr_mp.spec_index(if waiting_state is SENDING { peer_ptr } else { thread_ptr }).view().endpoint_descriptors.view()[target_index as int] is None
        }),
    ensures
        ipc_endpoint_transit_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index, waiting_state, if waiting_state is SENDING { source_index } else { target_index }),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_process == Some(process_ptr),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thread_ptr].endpoint_descriptors[endpoint_index as int] == Some(channel_ptr),
        kernel_k_to_kernel_u(*krnl).endpoint_map[channel_ptr].queue[0] == peer_ptr,
{
    kernel_cpu_thread_projection_at(krnl, cpu_id, process_ptr, thread_ptr, Some(channel_ptr)); kernel_thread_projection_at(krnl, peer_ptr);
    ipc_endpoint_transit_step_pre_from_u(kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, thread_ptr, channel_ptr, peer_ptr, endpoint_index, waiting_state, source_index, target_index);
}

/// The cpu, the running thread recording an endpoint transfer, and its peer write-held on `krnl` with the payload endpoint unlocked give the finish pre
/// and the user-view context of the finish step.
pub(super) proof fn ipc_endpoint_finish_step_pre_from_k(
    krnl: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, peer_ptr: RwLockThreadPtr, payload_ptr: RwLockEndpointPtr,
    receiver: RwLockThreadPtr, source_index: EndpointIdx, target_index: EndpointIdx, result: RetValueType, wake_cpu: CpuId,
)
    requires
        receiver == thread_ptr || receiver == peer_ptr,
        thread_ptr != peer_ptr,
        edp_idx_valid(source_index),
        ({
            let cpu = krnl.cpu_arr.spec_index(cpu_id).value;
            let thread = krnl.thr_mp.spec_index(thread_ptr);
            let peer = krnl.thr_mp.spec_index(peer_ptr);
            let owner = krnl.ep_mp.spec_index(payload_ptr).view().owning_container;
            let container = krnl.thr_mp.spec_index(receiver).view().owning_container;
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& cpu.locking_thread() is Write
            &&& cpu.view().view().current_process == Some(process_ptr)
            &&& cpu.view().view().current_thread == Some(thread_ptr)
            &&& krnl.prc_mp.dom().contains(process_ptr)
            &&& krnl.thr_mp.dom().contains(thread_ptr)
            &&& thread.locking_thread() is Write
            &&& thread.view().syscall_progress.view() == Some(SyscallProgress::IpcEndpoint {
                peer: peer_ptr, caller_sends: receiver == peer_ptr, payload_index: if receiver == peer_ptr { source_index } else { target_index },
            })
            &&& krnl.thr_mp.dom().contains(peer_ptr)
            &&& peer.locking_thread() is Write
            &&& peer.view().state is IPC_TRANSIT
            &&& peer.view().state->IPC_TRANSIT_partner == thread_ptr
            &&& peer.view().ipc_payload == (IPCPayLoad::Endpoint { endpoint_index: if receiver == peer_ptr { target_index } else { source_index } })
            &&& krnl.ctn_mp.dom().contains(thread.view().owning_container)
            &&& krnl.ctn_mp.dom().contains(peer.view().owning_container)
            &&& krnl.thr_mp.spec_index(if receiver == peer_ptr { thread_ptr } else { peer_ptr }).view().endpoint_descriptors.view()[source_index as int] == Some(payload_ptr)
            &&& krnl.ep_mp.dom().contains(payload_ptr)
            &&& krnl.ep_mp.spec_index(payload_ptr).locking_thread() is None
            &&& result == if owner == container || krnl.ctn_mp.spec_index(container).view_ghost().uppertree_seq.view().contains(owner) { RetValueType::Success } else { RetValueType::ErrorIpcEndpointOwnerMismatch }
            &&& wake_cpu == if peer.view().owning_container == thread.view().owning_container { cpu_id } else { peer.view().last_cpu }
        }),
    ensures
        ipc_endpoint_finish_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        ({
            let pre = kernel_k_to_kernel_u(*krnl);
            &&& pre.cpu_array[cpu_id as int].current_process == Some(process_ptr)
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& pre.cpu_array[cpu_id as int].state == krnl.cpu_arr.spec_index(cpu_id).view().view().view().state
            &&& pre.thread_map[thread_ptr].syscall_progress == Some(SyscallProgress::IpcEndpoint {
                peer: peer_ptr, caller_sends: receiver == peer_ptr, payload_index: if receiver == peer_ptr { source_index } else { target_index },
            })
            &&& pre.thread_map[peer_ptr].ipc_payload == (IPCPayLoad::Endpoint { endpoint_index: if receiver == peer_ptr { target_index } else { source_index } })
            &&& pre.thread_map[if receiver == peer_ptr { thread_ptr } else { peer_ptr }].endpoint_descriptors[source_index as int] == Some(payload_ptr)
            &&& result == ipc_endpoint_finish_result(pre, cpu_id)
            &&& wake_cpu == if pre.thread_map[peer_ptr].owning_container == pre.thread_map[thread_ptr].owning_container { cpu_id } else { pre.thread_map[peer_ptr].last_cpu }
        }),
{
    kernel_cpu_thread_projection_at(krnl, cpu_id, process_ptr, thread_ptr, Some(payload_ptr)); kernel_thread_projection_at(krnl, peer_ptr);
    kernel_container_ancestry_projection_at(krnl, krnl.thr_mp.spec_index(receiver).view().owning_container);
    ipc_endpoint_finish_step_pre_from_u(kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, thread_ptr, peer_ptr, payload_ptr, receiver, source_index, target_index);
}

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
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..pre.cpu_array[cpu_id as int] }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU {
                lock_state: LockStateU::WriteLocked,
                syscall_progress: Some(SyscallProgress::IpcEndpoint { peer: peer_ptr, caller_sends: waiting_state is SENDING, payload_index }),
                ..pre.thread_map[thread_ptr]
            }).insert(peer_ptr, ThreadU { lock_state: LockStateU::WriteLocked, blocking_endpoint_ptr: None,
                state: ThreadState::IPC_TRANSIT { partner: thread_ptr, wait: if pre.thread_map[peer_ptr].state is SENDING { IpcWait::Send } else { IpcWait::Receive } }, ..pre.thread_map[peer_ptr] }),
            endpoint_map: pre.endpoint_map.insert(channel_ptr, EndpointU { queue: pre.endpoint_map[channel_ptr].queue.skip(1), ..pre.endpoint_map[channel_ptr] }),
            ..pre
        }),
    ensures
        ipc_endpoint_transit_step(pre, post, cpu_id, endpoint_index, waiting_state, payload_index),
{ reveal(ipc_endpoint_transit_step); }

/// The write-held transfer context on `pre` with the payload endpoint unlocked is the finish pre.
pub(super) proof fn ipc_endpoint_finish_step_pre_from_u(pre: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, peer_ptr: RwLockThreadPtr, payload_ptr: RwLockEndpointPtr, receiver: RwLockThreadPtr, source_index: EndpointIdx, target_index: EndpointIdx)
    requires
        receiver == thread_ptr || receiver == peer_ptr,
        thread_ptr != peer_ptr,
        edp_idx_valid(source_index),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map[thread_ptr];
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& cpu.lock_state is WriteLocked
            &&& cpu.current_process == Some(process_ptr)
            &&& cpu.current_thread == Some(thread_ptr)
            &&& pre.process_map.dom().contains(process_ptr)
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is WriteLocked
            &&& thread.syscall_progress == Some(SyscallProgress::IpcEndpoint { peer: peer_ptr, caller_sends: receiver == peer_ptr, payload_index: if receiver == peer_ptr { source_index } else { target_index } })
            &&& pre.thread_map.dom().contains(peer_ptr)
            &&& pre.thread_map[peer_ptr].lock_state is WriteLocked
            &&& pre.thread_map[peer_ptr].state is IPC_TRANSIT
            &&& pre.thread_map[peer_ptr].state->IPC_TRANSIT_partner == thread_ptr
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
    descriptor: Option<(RwLockThreadPtr, EndpointIdx)>, wake_cpu: CpuId,
)
    requires
        wake_cpu == if pre.thread_map[peer_ptr].owning_container == pre.thread_map[thread_ptr].owning_container { cpu_id } else { pre.thread_map[peer_ptr].last_cpu },
        receiver == thread_ptr || receiver == peer_ptr,
        thread_ptr != peer_ptr,
        pre.cpu_array[cpu_id as int].current_process == Some(process_ptr),
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map[thread_ptr].syscall_progress == Some(SyscallProgress::IpcEndpoint { peer: peer_ptr, caller_sends: receiver == peer_ptr, payload_index: if receiver == peer_ptr { source_index } else { target_index } }),
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
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: cpu_op_after_step(pre.cpu_array[cpu_id as int].state), ..pre.cpu_array[cpu_id as int] }),
                container_map: pre.container_map.insert(container, ContainerU {
                    scheduler: pre.container_map[container].scheduler.update(wake_cpu as int, pre.container_map[container].scheduler[wake_cpu as int].push(peer_ptr)), ..pre.container_map[container]
                }),
                thread_map: threads.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..threads[thread_ptr] }).insert(peer_ptr, ThreadU {
                    lock_state: LockStateU::Unlocked, state: ThreadState::SCHEDULED { cpu_id: wake_cpu }, blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: Some(result), ..threads[peer_ptr]
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

/// The one block step pushed since `before` is the complete blocking trace.
pub(super) proof fn ipc_ordinary_trace_block_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        ipc_block_step_pre(pre, cpu_id, endpoint_index, waiting_state),
        !pre.cpu_array[cpu_id as int].killed,
        ipc_block_step(pre, post, cpu_id, endpoint_index, waiting_state, payload, regs, flushed_default_pcid),
    ensures
        ipc_ordinary_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index, waiting_state,
            payload, regs, flushed_default_pcid, RetValueType::CpuIdle),
{ reveal(ipc_ordinary_syscall_trace); reveal(ipc_block_step_pre); reveal(ipc_step_pre); }

/// A blocking trace since `before` is the payload's syscall trace.
pub(super) proof fn ipc_syscall_trace_from_block(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool)
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
pub(super) proof fn ipc_syscall_trace_from_rendezvous(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool, ret: RetValueType)
    requires
        !(ret is CpuIdle),
        payload is Pages ==> ipc_pages_rendezvous_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index,
            waiting_state, payload->Pages_va_range, ret),
        payload is Endpoint ==> ipc_endpoint_rendezvous_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index,
            waiting_state, payload->Endpoint_endpoint_index, ret),
        (payload is Empty || payload is Usize || payload is Cpu || payload is ReceiveCpu || payload is Pci) ==> if ipc_rendezvous_ret(ret) {
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
        (payload is Empty || payload is Usize || payload is Cpu || payload is ReceiveCpu || payload is Pci) ==> ipc_ordinary_syscall_trace(
            steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index, waiting_state, payload, regs, flushed_default_pcid, ret),
{ reveal(ipc_pages_syscall_trace); reveal(ipc_endpoint_syscall_trace); reveal(ipc_ordinary_syscall_trace); }

/// A call rejected before any visible change records no step for any payload kind.
pub(super) proof fn ipc_syscall_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool, ret: RetValueType)
    requires
        trace.len() == 0,
        ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcNoPeer || ret is ErrorIpcSameDirection || ret is ErrorIpcPeerKilled || ret is ErrorReplyOutOfPhase
            || (ret is CpuIdle && ipc_entry_result(pre, cpu_id, endpoint_index, waiting_state, false) == Some(RetValueType::CpuIdle)),
        ret is CpuIdle && payload is Pages ==> payload->Pages_va_range.wf() && payload->Pages_va_range.len > 0,
    ensures
        payload is Pages ==> ipc_pages_syscall_trace(trace, pre, pre, cpu_id, endpoint_index, waiting_state, payload->Pages_va_range, regs, flushed_default_pcid, ret),
        payload is Endpoint ==> ipc_endpoint_syscall_trace(trace, pre, pre, cpu_id, endpoint_index, waiting_state, payload->Endpoint_endpoint_index, regs, flushed_default_pcid, ret),
        (payload is Empty || payload is Usize || payload is Cpu || payload is ReceiveCpu || payload is Pci) ==> ipc_ordinary_syscall_trace(trace, pre, pre, cpu_id, endpoint_index, waiting_state, payload, regs, flushed_default_pcid, ret),
{ reveal(ipc_entry_result); reveal(ipc_pages_syscall_trace); reveal(ipc_endpoint_syscall_trace); reveal(ipc_ordinary_syscall_trace); reveal(ipc_pages_rendezvous_syscall_trace); reveal(ipc_endpoint_rendezvous_trace); }

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
pub(super) proof fn ipc_rendezvous_trace_error_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, ret: RetValueType)
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
pub(super) proof fn ipc_endpoint_trace_transit_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload_index: EndpointIdx)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        ipc_endpoint_transit_step_pre(pre, cpu_id, endpoint_index, waiting_state, payload_index),
        ipc_endpoint_transit_step(pre, post, cpu_id, endpoint_index, waiting_state, payload_index),
    ensures
        ipc_endpoint_trace_after_transit(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, cpu_id, endpoint_index, waiting_state, payload_index),
{ reveal(ipc_endpoint_trace_after_transit); }

/// The finish step pushed after the partial trace that starts at `start` completes the endpoint rendezvous trace.
pub(super) proof fn ipc_endpoint_trace_finish_step(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, finish_pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload_index: EndpointIdx, ret: RetValueType)
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
} // verus!
