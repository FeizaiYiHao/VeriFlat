use vstd::prelude::*;
use crate::*;

verus! {
/// The live process running on `cpu_id` takes `delta` 4K quota from its live container without overflow.
#[verifier::opaque]
pub open spec fn kernel_u_only_process_quota_4k_changed(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, delta: int) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let container = old_u.container_map.spec_index(container_ptr);
    let process = old_u.process_map.spec_index(process_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_process == Some(process_ptr)
    &&& cpu.owning_container == container_ptr
    &&& old_u.container_map.dom().contains(container_ptr)
    &&& !container.killed
    &&& !container.zombie
    &&& container.quota_4k >= delta
    &&& old_u.process_map.dom().contains(process_ptr)
    &&& !process.killed
    &&& process.quota_4k + delta <= usize::MAX
    &&& delta > 0
    &&& new_u == (KernelU {
        container_map: old_u.container_map.insert(container_ptr, ContainerU { quota_4k: (container.quota_4k as int - delta) as usize, ..container }),
        process_map: old_u.process_map.insert(process_ptr, ProcessU { quota_4k: (process.quota_4k as int + delta) as usize, ..process }),
        ..old_u
    })
}

/// The live process running on `cpu_id` moves `delta` 4K quota to its live running thread without overflow.
#[verifier::opaque]
pub open spec fn kernel_u_only_process2thread_quota_4k_changed(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, delta: int) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let process = old_u.process_map.spec_index(process_ptr);
    let thread = old_u.thread_map.spec_index(thread_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_process == Some(process_ptr)
    &&& cpu.current_thread == Some(thread_ptr)
    &&& old_u.process_map.dom().contains(process_ptr)
    &&& !process.killed
    &&& process.quota_4k >= delta
    &&& old_u.thread_map.dom().contains(thread_ptr)
    &&& !thread.killed
    &&& thread.quota_4k + delta <= usize::MAX
    &&& delta > 0
    &&& new_u == (KernelU {
        process_map: old_u.process_map.insert(process_ptr, ProcessU { quota_4k: (process.quota_4k as int - delta) as usize, ..process }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { quota_4k: (thread.quota_4k as int + delta) as usize, ..thread }),
        ..old_u
    })
}

/// The live process running on `cpu_id` takes `delta` 2M quota from its live container without overflow.
#[verifier::opaque]
pub open spec fn kernel_u_only_process_quota_2m_changed(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, delta: int) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let container = old_u.container_map.spec_index(container_ptr);
    let process = old_u.process_map.spec_index(process_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_process == Some(process_ptr)
    &&& cpu.owning_container == container_ptr
    &&& old_u.container_map.dom().contains(container_ptr)
    &&& !container.killed
    &&& !container.zombie
    &&& container.quota_2m >= delta
    &&& old_u.process_map.dom().contains(process_ptr)
    &&& !process.killed
    &&& process.quota_2m + delta <= usize::MAX
    &&& delta > 0
    &&& new_u == (KernelU {
        container_map: old_u.container_map.insert(container_ptr, ContainerU { quota_2m: (container.quota_2m as int - delta) as usize, ..container }),
        process_map: old_u.process_map.insert(process_ptr, ProcessU { quota_2m: (process.quota_2m as int + delta) as usize, ..process }),
        ..old_u
    })
}

/// The live process running on `cpu_id` moves `delta` 2M quota to its live running thread without overflow.
#[verifier::opaque]
pub open spec fn kernel_u_only_process2thread_quota_2m_changed(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, delta: int) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let process = old_u.process_map.spec_index(process_ptr);
    let thread = old_u.thread_map.spec_index(thread_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_process == Some(process_ptr)
    &&& cpu.current_thread == Some(thread_ptr)
    &&& old_u.process_map.dom().contains(process_ptr)
    &&& !process.killed
    &&& process.quota_2m >= delta
    &&& old_u.thread_map.dom().contains(thread_ptr)
    &&& !thread.killed
    &&& thread.quota_2m + delta <= usize::MAX
    &&& delta > 0
    &&& new_u == (KernelU {
        process_map: old_u.process_map.insert(process_ptr, ProcessU { quota_2m: (process.quota_2m as int - delta) as usize, ..process }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { quota_2m: (thread.quota_2m as int + delta) as usize, ..thread }),
        ..old_u
    })
}

/// The live head `next_thread` of shard `cpu_id` replaces the live thread running on `cpu_id`, which is requeued at
/// the tail of that shard.
#[verifier::opaque]
pub open spec fn kernel_u_context_switch_changed(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, next_thread: RwLockThreadPtr, entry_regs: Registers, flushed_pcid: Option<Pcid>) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let container = old_u.container_map.spec_index(cpu.owning_container);
    let next = old_u.thread_map.spec_index(next_thread);
    let requeued = match cpu.current_thread {
        Some(prev) => old_u.thread_map.insert(prev, ThreadU {
            state: ThreadState::SCHEDULED { cpu_id }, error_code: None, trap_frame: Some(entry_regs), ..old_u.thread_map.spec_index(prev)
        }),
        None => old_u.thread_map,
    };
    let run_queue = container.scheduler[cpu_id as int];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& !(cpu.state is Off)
    &&& old_u.container_map.dom().contains(cpu.owning_container)
    &&& run_queue.len() > 0
    &&& run_queue[0] == next_thread
    &&& old_u.thread_map.dom().contains(next_thread)
    &&& !next.killed
    &&& next.state is SCHEDULED
    &&& next.owning_container == cpu.owning_container
    &&& old_u.process_map.dom().contains(next.owning_proc)
    &&& cpu.current_thread != Some(next_thread)
    &&& cpu.current_process is Some == cpu.current_thread is Some
    &&& (cpu.current_thread is Some ==> {
        let prev = old_u.thread_map.spec_index(cpu.current_thread.unwrap());
        &&& old_u.thread_map.dom().contains(cpu.current_thread.unwrap())
        &&& !prev.killed
        &&& prev.state == (ThreadState::RUNNING { cpu_id })
        &&& prev.owning_proc == cpu.current_process.unwrap()
        &&& old_u.process_map.dom().contains(cpu.current_process.unwrap())
        &&& !old_u.process_map.spec_index(cpu.current_process.unwrap()).killed
    })
    &&& new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU {
            state: CpuState::Running, op: CpuOpState::Trap, current_process: Some(next.owning_proc), current_thread: Some(next_thread), ..cpu
        }),
        container_map: old_u.container_map.insert(cpu.owning_container, ContainerU {
            scheduler: container.scheduler.update(cpu_id as int, match cpu.current_thread { Some(prev) => run_queue.skip(1).push(prev), None => run_queue.skip(1) }),
            ..container
        }),
        thread_map: requeued.insert(next_thread, ThreadU { state: ThreadState::RUNNING { cpu_id }, last_cpu: cpu_id, error_code: None, trap_frame: None, ..next }),
        cpu_tlb: match flushed_pcid {
            Some(pcid) => old_u.cpu_tlb.insert((cpu_id, pcid), new_u.cpu_tlb[(cpu_id, pcid)]),
            None => old_u.cpu_tlb,
        },
        ..old_u
    })
    &&& flushed_pcid matches Some(pcid) ==> cpu_tlb_within_may_cache_u(new_u, cpu_id, pcid, new_u.cpu_tlb[(cpu_id, pcid)])
}

/// The Idle cpu `cpu_id`, whose own shard is empty, takes the live head `thread` of shard `victim`, the lowest
/// other nonempty shard of its container's scheduler, onto shard `cpu_id`.
#[verifier::opaque]
pub open spec fn kernel_u_rebalance_pull_changed(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, victim: CpuId, thread: RwLockThreadPtr) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let container = old_u.container_map.spec_index(cpu.owning_container);
    let queues = container.scheduler;
    let t = old_u.thread_map.spec_index(thread);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& index_valid(NUM_CPUS, victim)
    &&& victim != cpu_id
    &&& cpu.state is Idle
    &&& old_u.container_map.dom().contains(cpu.owning_container)
    &&& queues[cpu_id as int].len() == 0
    &&& first_nonempty_shard(queues, 0, cpu_id) == Some(victim)
    &&& queues[victim as int].len() > 0
    &&& queues[victim as int][0] == thread
    &&& old_u.thread_map.dom().contains(thread)
    &&& !t.killed
    &&& t.state == (ThreadState::SCHEDULED { cpu_id: victim })
    &&& t.owning_container == cpu.owning_container
    &&& new_u == (KernelU {
        container_map: old_u.container_map.insert(cpu.owning_container, ContainerU {
            scheduler: queues.update(victim as int, queues[victim as int].skip(1)).update(cpu_id as int, queues[cpu_id as int].push(thread)),
            ..container
        }),
        thread_map: old_u.thread_map.insert(thread, ThreadU { state: ThreadState::SCHEDULED { cpu_id }, ..t }),
        ..old_u
    })
}

/// The live thread running on `cpu_id` blocks on the live endpoint at `endpoint_index` and the CPU goes idle.
#[verifier::opaque]
pub open spec fn kernel_u_ipc_block_changed(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool,
) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_thread == Some(thread_ptr)
    &&& cpu.current_process == Some(thread.owning_proc)
    &&& old_u.process_map.dom().contains(thread.owning_proc)
    &&& old_u.thread_map.dom().contains(thread_ptr)
    &&& !thread.killed
    &&& thread.state == (ThreadState::RUNNING { cpu_id })
    &&& edp_idx_valid(endpoint_index)
    &&& thread.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
    &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
    &&& !endpoint.queue.contains(thread_ptr)
    &&& waiting_state.is_endpoint_waiting()
    &&& endpoint.queue.len() == 0 || (endpoint.queue_state is SEND) == waiting_state.is_endpoint_send_waiting()
    &&& new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { state: CpuState::Idle, op: CpuOpState::Idle, current_process: None, current_thread: None, ..cpu }),
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
        cpu_tlb: if flushed_default_pcid {
            old_u.cpu_tlb.insert((cpu_id, KERNEL_DEFAULT_PCID), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
        } else { old_u.cpu_tlb },
        ..old_u
    })
}

/// The live caller running on `cpu_id` hands its CPU to the live receive-call head `callee_ptr` of the
/// endpoint at `endpoint_index`, which records the caller and runs; the caller saves `regs` and waits for the
/// reply.
#[verifier::opaque]
pub open spec fn kernel_u_ipc_call_handoff_changed(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, caller_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    callee_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>,
) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let caller = old_u.thread_map.spec_index(caller_ptr);
    let callee = old_u.thread_map.spec_index(callee_ptr);
    let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_thread == Some(caller_ptr)
    &&& cpu.current_process == Some(caller.owning_proc)
    &&& old_u.process_map.dom().contains(caller.owning_proc)
    &&& old_u.thread_map.dom().contains(caller_ptr)
    &&& !caller.killed
    &&& caller.state == (ThreadState::RUNNING { cpu_id })
    &&& caller.callee is None
    &&& edp_idx_valid(endpoint_index)
    &&& caller.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
    &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
    &&& !endpoint.queue.contains(caller_ptr)
    &&& endpoint.queue.len() > 0
    &&& endpoint.queue[0] == callee_ptr
    &&& endpoint.queue_state is RECEIVE
    &&& callee_ptr != caller_ptr
    &&& old_u.thread_map.dom().contains(callee_ptr)
    &&& !callee.killed
    &&& callee.state is RECEIVING_CALL
    &&& callee.caller is None
    &&& callee.callee is None
    &&& callee.blocking_endpoint_ptr == Some(endpoint_ptr)
    &&& callee.owning_container == caller.owning_container
    &&& old_u.process_map.dom().contains(callee.owning_proc)
    &&& new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { current_process: Some(callee.owning_proc), current_thread: Some(callee_ptr), ..cpu }),
        thread_map: old_u.thread_map.insert(caller_ptr, ThreadU { state: ThreadState::WAITING_REPLY, callee: Some(callee_ptr), trap_frame: Some(regs), ..caller })
            .insert(callee_ptr, ThreadU { state: ThreadState::RUNNING { cpu_id }, caller: Some(caller_ptr), last_cpu: cpu_id, blocking_endpoint_ptr: None, trap_frame: None, ..callee }),
        endpoint_map: old_u.endpoint_map.insert(endpoint_ptr, EndpointU { queue: endpoint.queue.skip(1), ..endpoint }),
        cpu_tlb: match flushed_pcid {
            Some(pcid) => old_u.cpu_tlb.insert((cpu_id, pcid), new_u.cpu_tlb[(cpu_id, pcid)]),
            None => old_u.cpu_tlb,
        },
        ..old_u
    })
    &&& flushed_pcid matches Some(pcid) ==> cpu_tlb_within_may_cache_u(new_u, cpu_id, pcid, new_u.cpu_tlb[(cpu_id, pcid)])
}

/// The live receive-call thread running on `cpu_id` accepts the live calling head `caller_ptr` of the endpoint
/// at `endpoint_index`: the caller is dequeued and waits for the reply, and the callee records it.
#[verifier::opaque]
pub open spec fn kernel_u_ipc_accept_call_changed(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    caller_ptr: RwLockThreadPtr,
) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let callee = old_u.thread_map.spec_index(callee_ptr);
    let caller = old_u.thread_map.spec_index(caller_ptr);
    let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_thread == Some(callee_ptr)
    &&& cpu.current_process == Some(callee.owning_proc)
    &&& old_u.process_map.dom().contains(callee.owning_proc)
    &&& old_u.thread_map.dom().contains(callee_ptr)
    &&& !callee.killed
    &&& callee.state == (ThreadState::RUNNING { cpu_id })
    &&& callee.caller is None
    &&& callee.callee is None
    &&& edp_idx_valid(endpoint_index)
    &&& callee.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
    &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
    &&& !endpoint.queue.contains(callee_ptr)
    &&& endpoint.queue.len() > 0
    &&& endpoint.queue[0] == caller_ptr
    &&& endpoint.queue_state is SEND
    &&& caller_ptr != callee_ptr
    &&& old_u.thread_map.dom().contains(caller_ptr)
    &&& !caller.killed
    &&& caller.state is CALLING
    &&& caller.callee is None
    &&& caller.blocking_endpoint_ptr == Some(endpoint_ptr)
    &&& caller.owning_container == callee.owning_container
    &&& new_u == (KernelU {
        thread_map: old_u.thread_map.insert(callee_ptr, ThreadU { caller: Some(caller_ptr), ..callee }).insert(caller_ptr, ThreadU { state: ThreadState::WAITING_REPLY, callee: Some(callee_ptr), blocking_endpoint_ptr: None, ..caller }),
        endpoint_map: old_u.endpoint_map.insert(endpoint_ptr, EndpointU { queue: endpoint.queue.skip(1), ..endpoint }),
        ..old_u
    })
}

/// The live callee running on `cpu_id` replies to its recorded caller `caller_ptr`, which resumes on `cpu_id`,
/// and waits with `regs` for the next call on the endpoint at `endpoint_index`.
#[verifier::opaque]
pub open spec fn kernel_u_ipc_reply_handoff_changed(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    caller_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>,
) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let callee = old_u.thread_map.spec_index(callee_ptr);
    let caller = old_u.thread_map.spec_index(caller_ptr);
    let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_thread == Some(callee_ptr)
    &&& cpu.current_process == Some(callee.owning_proc)
    &&& old_u.process_map.dom().contains(callee.owning_proc)
    &&& old_u.thread_map.dom().contains(callee_ptr)
    &&& !callee.killed
    &&& callee.state == (ThreadState::RUNNING { cpu_id })
    &&& callee.caller == Some(caller_ptr)
    &&& callee.callee is None
    &&& edp_idx_valid(endpoint_index)
    &&& callee.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
    &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
    &&& !endpoint.queue.contains(callee_ptr)
    &&& endpoint.queue.len() == 0 || endpoint.queue_state is RECEIVE
    &&& caller_ptr != callee_ptr
    &&& old_u.thread_map.dom().contains(caller_ptr)
    &&& !caller.killed
    &&& caller.state is WAITING_REPLY
    &&& caller.callee == Some(callee_ptr)
    &&& caller.owning_container == callee.owning_container
    &&& old_u.process_map.dom().contains(caller.owning_proc)
    &&& new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { current_process: Some(caller.owning_proc), current_thread: Some(caller_ptr), ..cpu }),
        thread_map: old_u.thread_map.insert(callee_ptr, ThreadU {
            state: ThreadState::RECEIVING_CALL, caller: None, blocking_endpoint_ptr: Some(endpoint_ptr), ipc_payload: IPCPayLoad::Empty, trap_frame: Some(regs), ..callee
        }).insert(caller_ptr, ThreadU { state: ThreadState::RUNNING { cpu_id }, callee: None, last_cpu: cpu_id, trap_frame: None, ..caller }),
        endpoint_map: old_u.endpoint_map.insert(endpoint_ptr, EndpointU {
            queue: endpoint.queue.push(callee_ptr), queue_state: if endpoint.queue.len() == 0 { EndpointState::RECEIVE } else { endpoint.queue_state }, ..endpoint
        }),
        cpu_tlb: match flushed_pcid {
            Some(pcid) => old_u.cpu_tlb.insert((cpu_id, pcid), new_u.cpu_tlb[(cpu_id, pcid)]),
            None => old_u.cpu_tlb,
        },
        ..old_u
    })
    &&& flushed_pcid matches Some(pcid) ==> cpu_tlb_within_may_cache_u(new_u, cpu_id, pcid, new_u.cpu_tlb[(cpu_id, pcid)])
}

/// The live endpoint head waiting opposite to the live caller running on `cpu_id` is dequeued and scheduled
/// with `peer_result` on shard `cpu_id` of a same-container peer, else on the peer's `last_cpu` shard; an Off
/// CPU may move to the receiver's container, and a detached PCI function may move to the receiver process. Detaching an
/// attached function empties the sender table's old DID domain, and the sender table's DID follows `pci_handoff_table_did`.
#[verifier::opaque]
pub open spec fn kernel_u_ipc_rendezvous_changed(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, caller_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, peer_thread_ptr: RwLockThreadPtr, peer_result: RetValueType,
    cpu_transfer: Option<(CpuId, RwLockThreadPtr)>, pci_transfer: Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)>,
) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let caller = old_u.thread_map.spec_index(caller_thread_ptr);
    let peer = old_u.thread_map.spec_index(peer_thread_ptr);
    let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
    let container = old_u.container_map.spec_index(peer.owning_container);
    let wake_cpu = if peer.owning_container == caller.owning_container { cpu_id } else { peer.last_cpu };
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_thread == Some(caller_thread_ptr)
    &&& cpu.current_process == Some(caller.owning_proc)
    &&& old_u.process_map.dom().contains(caller.owning_proc)
    &&& old_u.thread_map.dom().contains(caller_thread_ptr)
    &&& !caller.killed
    &&& caller.state == (ThreadState::RUNNING { cpu_id })
    &&& edp_idx_valid(endpoint_index)
    &&& caller.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
    &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
    &&& !endpoint.queue.contains(caller_thread_ptr)
    &&& waiting_state.is_endpoint_waiting()
    &&& endpoint.queue.len() > 0
    &&& endpoint.queue[0] == peer_thread_ptr
    &&& (endpoint.queue_state is SEND) != waiting_state.is_endpoint_send_waiting()
    &&& old_u.thread_map.dom().contains(peer_thread_ptr)
    &&& peer_thread_ptr != caller_thread_ptr
    &&& !peer.killed
    &&& peer.state.is_endpoint_waiting()
    &&& peer.blocking_endpoint_ptr == Some(endpoint_ptr)
    &&& old_u.container_map.dom().contains(peer.owning_container)
    &&& (cpu_transfer is Some ==> index_valid(NUM_CPUS, cpu_transfer.unwrap().0) && old_u.thread_map.dom().contains(cpu_transfer.unwrap().1))
    &&& pci_transfer matches Some((bdf, sender, receiver)) ==> {
        &&& pci_bdf_valid(bdf.0, bdf.1, bdf.2)
        &&& old_u.process_map.dom().contains(sender)
        &&& old_u.process_map.dom().contains(receiver)
        &&& sender != receiver
        &&& old_u.process_map.spec_index(sender).iommu_table matches Some(t) ==> pci_handoff_table_did(old_u.iommu_root_table.owners, old_u.iommu_root_table.attached, sender, bdf,
            t.did, new_u.process_map.spec_index(sender).iommu_table->Some_0.did)
    }
    &&& new_u == (KernelU {
        cpu_array: match cpu_transfer {
            Some((transfer_cpu, receiver)) => old_u.cpu_array.update(transfer_cpu as int, CpuU {
                owning_container: old_u.thread_map.spec_index(receiver).owning_container, ..old_u.cpu_array[transfer_cpu as int]
            }),
            None => old_u.cpu_array,
        },
        container_map: old_u.container_map.insert(peer.owning_container, ContainerU {
            scheduler: container.scheduler.update(wake_cpu as int, container.scheduler[wake_cpu as int].push(peer_thread_ptr)), ..container
        }),
        thread_map: old_u.thread_map.insert(peer_thread_ptr, ThreadU {
            state: ThreadState::SCHEDULED { cpu_id: wake_cpu }, blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: Some(peer_result), ..peer
        }),
        endpoint_map: old_u.endpoint_map.insert(endpoint_ptr, EndpointU { queue: endpoint.queue.skip(1), ..endpoint }),
        process_map: match pci_transfer {
            Some((bdf, sender, receiver)) => {
                let s = old_u.process_map.spec_index(sender);
                let r = old_u.process_map.spec_index(receiver);
                let s_table = match s.iommu_table { Some(t) => Some(PageTableU { did: new_u.process_map.spec_index(sender).iommu_table->Some_0.did, ..t }), None => None };
                old_u.process_map.insert(sender, ProcessU { iommu_table: s_table, owned_pci_functions: s.owned_pci_functions.remove(bdf), ..s })
                    .insert(receiver, ProcessU { owned_pci_functions: r.owned_pci_functions.insert(bdf), ..r })
            },
            None => old_u.process_map,
        },
        iommu_root_table: match pci_transfer {
            Some((bdf, _, receiver)) => IommuRootTableU {
                owners: seq3_update(old_u.iommu_root_table.owners, bdf.0 as int, bdf.1 as int, bdf.2 as int, receiver),
                attached: seq3_update(old_u.iommu_root_table.attached, bdf.0 as int, bdf.1 as int, bdf.2 as int, false),
            },
            None => old_u.iommu_root_table,
        },
        iommu_tlb: match pci_transfer {
            Some((bdf, sender, _)) => {
                let old_did = match old_u.process_map.spec_index(sender).iommu_table { Some(t) => t.did, None => None };
                if old_u.iommu_root_table.attached[bdf.0 as int][bdf.1 as int][bdf.2 as int] && old_did is Some {
                    old_u.iommu_tlb.insert(old_did->Some_0, new_u.iommu_tlb[old_did->Some_0])
                } else { old_u.iommu_tlb }
            },
            None => old_u.iommu_tlb,
        },
        ..old_u
    })
    &&& pci_transfer matches Some((bdf, sender, _)) ==> {
        let old_did = match old_u.process_map.spec_index(sender).iommu_table { Some(t) => t.did, None => None };
        old_u.iommu_root_table.attached[bdf.0 as int][bdf.1 as int][bdf.2 as int] && old_did is Some
            ==> iommu_tlb_within_may_cache_u(new_u, old_did->Some_0, new_u.iommu_tlb[old_did->Some_0])
    }
}

/// The caller's result of meeting the queue head of the endpoint at `endpoint_index`, decided from the two
/// payloads as the implementation does. Empty payloads in opposite directions succeed. A CPU handover needs
/// different containers and an Off CPU of the sender's container; an endpoint transfer needs the sender's
/// source descriptor and a free receiver target descriptor; a pages transfer needs equal lengths and different
/// processes; a PCI handover needs the same function named on both sides, different processes, and a sender
/// process that owns the function. Any other pairing is a type mismatch. Success on Endpoint and Pages
/// payloads starts their multi-step transfer. A calling or receive-call caller only reaches this error step:
/// CallAcrossContainers when the head waits in the matching call state, else a type mismatch.
pub open spec fn ipc_rendezvous_result(old_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad) -> RetValueType {
    let caller = old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0];
    let peer = old_u.thread_map[old_u.endpoint_map[caller.endpoint_descriptors[endpoint_index as int]->Some_0].queue[0]];
    let sends = waiting_state.is_endpoint_send_waiting();
    let sender = if sends { caller } else { peer };
    let receiver = if sends { peer } else { caller };
    let sent = if sends { payload } else { peer.ipc_payload };
    let received = if sends { peer.ipc_payload } else { payload };
    if waiting_state is CALLING || waiting_state is RECEIVING_CALL {
        if peer.state == (if sends { ThreadState::RECEIVING_CALL } else { ThreadState::CALLING }) { RetValueType::ErrorCallAcrossContainers } else { RetValueType::ErrorIpcTypeMismatch }
    } else if peer.state != (if sends { ThreadState::RECEIVING } else { ThreadState::SENDING }) { RetValueType::ErrorIpcTypeMismatch } else {
        match (sent, received) {
            (IPCPayLoad::Empty, IPCPayLoad::Empty) => RetValueType::Success,
            (IPCPayLoad::Cpu { cpu_id: transfer }, IPCPayLoad::ReceiveCpu) => {
                let cpu = old_u.cpu_array[transfer as int];
                if sender.owning_container == receiver.owning_container { RetValueType::ErrorIpcSameContainer }
                else if !index_valid(NUM_CPUS, transfer) || cpu.owning_container != sender.owning_container { RetValueType::ErrorIpcCpuOwnerMismatch }
                else if !(cpu.state is Off) { RetValueType::ErrorIpcCpuNotOff }
                else if sends { RetValueType::Success } else { RetValueType::SuccessUsize { value: transfer } }
            },
            (IPCPayLoad::Endpoint { endpoint_index: source }, IPCPayLoad::Endpoint { endpoint_index: target }) => {
                if sender.endpoint_descriptors[source as int] is None { RetValueType::ErrorIpcEndpointSourceInvalid }
                else if receiver.endpoint_descriptors[target as int] is Some { RetValueType::ErrorIpcEndpointTargetInUse }
                else { RetValueType::Success }
            },
            (IPCPayLoad::Pages { va_range: source }, IPCPayLoad::Pages { va_range: target }) => {
                if source.len != target.len { RetValueType::ErrorIpcTypeMismatch }
                else if sender.owning_proc == receiver.owning_proc { RetValueType::ErrorIpcSameProcess }
                else { RetValueType::Success }
            },
            (IPCPayLoad::Pci { bus: sent_bus, dev: sent_dev, fun: sent_fun }, IPCPayLoad::Pci { bus: received_bus, dev: received_dev, fun: received_fun }) => {
                if sent_bus != received_bus || sent_dev != received_dev || sent_fun != received_fun { RetValueType::ErrorIpcTypeMismatch }
                else if sender.owning_proc == receiver.owning_proc { RetValueType::ErrorIpcSameProcess }
                else if !old_u.process_map[sender.owning_proc].owned_pci_functions.contains((sent_bus as usize, sent_dev as usize, sent_fun as usize)) { RetValueType::ErrorIpcPciOwnerMismatch }
                else { RetValueType::Success }
            },
            _ => RetValueType::ErrorIpcTypeMismatch,
        }
    }
}

#[verifier::opaque]
pub open spec fn kernel_u_cpu_tlb_cleared(pre: KernelU, post: KernelU, pcid: Pcid) -> bool {
    let changed = post.cpu_tlb.dom().filter(|key: (CpuId, Pcid)| !pre.cpu_tlb.dom().contains(key) || pre.cpu_tlb[key] != post.cpu_tlb[key]);
    &&& pre.cpu_tlb.dom().subset_of(post.cpu_tlb.dom())
    &&& changed.len() == 1
    &&& forall|key: (CpuId, Pcid)| #![trigger changed.contains(key)] changed.contains(key) ==> {
        &&& index_valid(NUM_CPUS, key.0)
        &&& key.1 == pcid
        &&& cpu_tlb_within_may_cache_u(post, key.0, pcid, post.cpu_tlb[key])
    }
    &&& post == (KernelU { cpu_tlb: post.cpu_tlb, ..pre })
}

#[verifier::opaque]
pub open spec fn kernel_u_container_quota_4k_increased(pre: KernelU, post: KernelU, container: RwLockContainerPtr) -> bool {
    let changed = pre.container_map.dom().filter(|c: RwLockContainerPtr| pre.container_map[c] != post.container_map[c]);
    &&& pre.container_map.dom().contains(container)
    &&& post.container_map != pre.container_map
    &&& post.container_map.dom() == pre.container_map.dom()
    &&& changed.len() == 1
    &&& forall|c: RwLockContainerPtr| #![trigger changed.contains(c)] #![trigger post.container_map[c]] changed.contains(c) ==> {
        &&& c == container || pre.container_map[container].uppertree_seq.contains(c)
        &&& post.container_map[c].quota_4k > pre.container_map[c].quota_4k
        &&& post.container_map[c] == (ContainerU { quota_4k: post.container_map[c].quota_4k, ..pre.container_map[c] })
    }
    &&& post == (KernelU { container_map: post.container_map, ..pre })
}

#[verifier::opaque]
pub open spec fn kernel_u_container_root_published(
    pre: KernelU, post: KernelU, parent: RwLockContainerPtr, child: RwLockContainerPtr,
    process: RwLockProcessPtr, thread: RwLockThreadPtr, transfer_cpu: CpuId, funding: usize, process_quota: usize,
    moved: Set<PagePtr>, thread_page: PagePtr, progress: Option<SyscallProgress>,
) -> bool {
    let actual_moved = pre.container_map[parent].owned_pages.difference(post.container_map[parent].owned_pages);
    let ancestors = pre.container_map[parent].uppertree_seq.push(parent);
    &&& pre.container_map.dom().contains(parent)
    &&& !pre.container_map.dom().contains(child)
    &&& !pre.process_map.dom().contains(process)
    &&& pre.thread_map.dom().contains(thread)
    &&& funding >= process_quota
    &&& pre.thread_map[thread].quota_4k >= 8 + funding
    &&& pre.thread_map[thread].quota_2m >= 2
    &&& pre.cpu_array[transfer_cpu as int].state is Off
    &&& pre.cpu_array[transfer_cpu as int].owning_container == parent
    &&& post.container_map.dom() == pre.container_map.dom().insert(child)
    &&& forall|c: RwLockContainerPtr| #![trigger post.container_map[c]] pre.container_map.dom().contains(c) ==> post.container_map[c] == (ContainerU {
            children: if c == parent { pre.container_map[c].children.push(child) } else { pre.container_map[c].children },
            subtree_set: if ancestors.contains(c) { pre.container_map[c].subtree_set.insert(child) } else { pre.container_map[c].subtree_set },
            owned_pages: if c == parent { post.container_map[parent].owned_pages } else { pre.container_map[c].owned_pages },
            ..pre.container_map[c]
        })
    &&& post.container_map[parent].owned_pages.subset_of(pre.container_map[parent].owned_pages)
    &&& actual_moved == moved
    &&& !moved.contains(thread_page)
    &&& post.container_map[parent].owned_pages.contains(thread_page)
    &&& moved.contains(child) && moved.contains(process) && moved.contains(post.container_map[child].cpu_set)
    &&& post.container_map[child] == (ContainerU {
        lock_state: LockStateU::WriteLocked, lock_process_owner: Some(LockOwnerId::Some(0)), zombie: false, children: Seq::empty(), uppertree_seq: ancestors, subtree_set: Set::empty(),
        root_process: process, owned_processes: set![process], owned_threads: Set::empty(), owned_endpoints: Set::empty(), owned_pages: moved,
        parent: Some(parent), depth: (pre.container_map[parent].depth + 1) as usize, scheduler: Seq::new(NUM_CPUS as nat, |i: int| Seq::<RwLockThreadPtr>::empty()),
        cpu_set: post.container_map[child].cpu_set, cpu_set_lock: LockStateU::WriteLocked,
        cpu_offline_requests: Seq::new(NUM_CPUS as nat, |i: int| false), free_pcids: Set::range(1usize, PCID_MAX).remove(1usize),
        quota_4k: (funding - process_quota) as usize, quota_2m: 0, quota_1g: 0, killed: false, cpu_set_killed: false,
    })
    &&& post == (KernelU {
        cpu_array: pre.cpu_array.update(transfer_cpu as int, CpuU { lock_state: LockStateU::WriteLocked, ..pre.cpu_array[transfer_cpu as int] }),
        container_map: post.container_map,
        process_map: pre.process_map.insert(process, ProcessU {
            lock_state: LockStateU::WriteLocked, zombie: false,
            pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, did: None, mapping_4k: Map::empty(), mapping_2m: Map::empty(), mapping_1g: Map::empty() }),
            iommu_table: None, pcid: post.process_map[process].pcid, owning_container: child, owned_pci_functions: Set::empty(), quota_4k: process_quota, quota_2m: 0, quota_1g: 0,
            parent: None, children: Seq::empty(), depth: 0, uppertree_seq: Seq::empty(), subtree_set: Set::empty(), owned_threads: Seq::empty(), killed: false,
        }),
        thread_map: pre.thread_map.insert(thread, ThreadU {
            quota_4k: (pre.thread_map[thread].quota_4k - 8 - funding) as usize, quota_2m: (pre.thread_map[thread].quota_2m - 2) as usize,
            syscall_progress: progress, ..pre.thread_map[thread]
        }),
        ..pre
    })
}

#[verifier::opaque]
pub open spec fn kernel_u_cpu_and_page_owner_changed(pre: KernelU, post: KernelU, cpu: CpuId, source: RwLockContainerPtr, target: RwLockContainerPtr, page: PagePtr) -> bool {
    post == (KernelU {
        cpu_array: pre.cpu_array.update(cpu as int, CpuU { lock_state: LockStateU::Unlocked, owning_container: target, ..pre.cpu_array[cpu as int] }),
        container_map: pre.container_map.insert(source, ContainerU {
            cpu_set_lock: LockStateU::Unlocked, owned_pages: pre.container_map[source].owned_pages.remove(page), ..pre.container_map[source]
        }).insert(target, ContainerU { cpu_set_lock: LockStateU::Unlocked, owned_pages: pre.container_map[target].owned_pages.insert(page), ..pre.container_map[target] }),
        ..pre
    })
}

#[verifier::opaque]
pub open spec fn kernel_u_container_root_created(
    pre: KernelU, post: KernelU, parent: RwLockContainerPtr, child: RwLockContainerPtr, process: RwLockProcessPtr,
    thread: RwLockThreadPtr, transfer_cpu: CpuId, funding: usize, process_quota: usize, progress: Option<SyscallProgress>,
) -> bool {
    let moved = pre.container_map[parent].owned_pages.difference(post.container_map[parent].owned_pages);
    let ancestors = pre.container_map[parent].uppertree_seq.push(parent);
    &&& pre.container_map.dom().contains(parent)
    &&& !pre.container_map.dom().contains(child)
    &&& !pre.process_map.dom().contains(process)
    &&& pre.thread_map.dom().contains(thread)
    &&& funding >= process_quota
    &&& pre.thread_map[thread].quota_4k >= 8 + funding
    &&& pre.thread_map[thread].quota_2m >= 2
    &&& pre.cpu_array[transfer_cpu as int].state is Off
    &&& pre.cpu_array[transfer_cpu as int].owning_container == parent
    &&& post.container_map.dom() == pre.container_map.dom().insert(child)
    &&& forall|c: RwLockContainerPtr| #![trigger post.container_map[c]] pre.container_map.dom().contains(c) ==> post.container_map[c] == (ContainerU {
            children: if c == parent { pre.container_map[c].children.push(child) } else { pre.container_map[c].children },
            subtree_set: if ancestors.contains(c) { pre.container_map[c].subtree_set.insert(child) } else { pre.container_map[c].subtree_set },
            owned_pages: if c == parent { post.container_map[parent].owned_pages } else { pre.container_map[c].owned_pages },
            cpu_set_lock: if c == parent { LockStateU::Unlocked } else { pre.container_map[c].cpu_set_lock },
            ..pre.container_map[c]
        })
    &&& post.container_map[parent].owned_pages.subset_of(pre.container_map[parent].owned_pages)
    &&& moved.len() == 2 * 512 + 9 + funding
    &&& moved.contains(child) && moved.contains(process) && moved.contains(post.container_map[child].cpu_set)
    &&& post.container_map[child] == (ContainerU {
        lock_state: LockStateU::WriteLocked, lock_process_owner: Some(LockOwnerId::Some(0)), zombie: false, children: Seq::empty(), uppertree_seq: ancestors, subtree_set: Set::empty(),
        root_process: process, owned_processes: set![process], owned_threads: Set::empty(), owned_endpoints: Set::empty(), owned_pages: moved,
        parent: Some(parent), depth: (pre.container_map[parent].depth + 1) as usize, scheduler: Seq::new(NUM_CPUS as nat, |i: int| Seq::<RwLockThreadPtr>::empty()),
        cpu_set: post.container_map[child].cpu_set, cpu_set_lock: LockStateU::Unlocked,
        cpu_offline_requests: Seq::new(NUM_CPUS as nat, |i: int| false), free_pcids: Set::range(1usize, PCID_MAX).remove(1usize),
        quota_4k: (funding - process_quota) as usize, quota_2m: 0, quota_1g: 0, killed: false, cpu_set_killed: false,
    })
    &&& post == (KernelU {
        cpu_array: pre.cpu_array.update(transfer_cpu as int, CpuU { lock_state: LockStateU::Unlocked, owning_container: child, ..pre.cpu_array[transfer_cpu as int] }),
        container_map: post.container_map,
        process_map: pre.process_map.insert(process, ProcessU {
            lock_state: LockStateU::WriteLocked, zombie: false,
            pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, did: None, mapping_4k: Map::empty(), mapping_2m: Map::empty(), mapping_1g: Map::empty() }),
            iommu_table: None, pcid: post.process_map[process].pcid, owning_container: child, owned_pci_functions: Set::empty(), quota_4k: process_quota, quota_2m: 0, quota_1g: 0,
            parent: None, children: Seq::empty(), depth: 0, uppertree_seq: Seq::empty(), subtree_set: Set::empty(), owned_threads: Seq::empty(), killed: false,
        }),
        thread_map: pre.thread_map.insert(thread, ThreadU {
            quota_4k: (pre.thread_map[thread].quota_4k - 8 - funding) as usize, quota_2m: (pre.thread_map[thread].quota_2m - 2) as usize,
            syscall_progress: progress, ..pre.thread_map[thread]
        }),
        ..pre
    })
}

/// The objects a share names: the thread whose process is the source, the target process, the
/// thread whose quota pays for target directory pages, the container that owns the target, and the
/// container that hands over directory pages.
pub ghost struct Share4kObjects {
    pub source_thread: RwLockThreadPtr,
    pub target: RwLockProcessPtr,
    pub quota_thread: RwLockThreadPtr,
    pub target_container: RwLockContainerPtr,
    pub transfer_source: Option<RwLockContainerPtr>,
}

/// The objects of the share recorded by the thread running on `cpu_id`: a new process shares into
/// its recorded child, a new container into its recorded child container's root process, and a
/// pages rendezvous from the sender into the receiver, which is the recorded peer exactly when the
/// peer was dequeued into transit while receiving.
pub open spec fn share_4k_objects(u: KernelU, cpu_id: CpuId) -> Share4kObjects {
    let caller = u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = u.thread_map[caller];
    match thread.syscall_progress->Some_0->Share4k_origin {
        Share4kOrigin::NewProcess(record) => Share4kObjects {
            source_thread: caller, target: record.child->Some_0, quota_thread: caller, target_container: thread.owning_container, transfer_source: None,
        },
        Share4kOrigin::NewContainer(record) => Share4kObjects {
            source_thread: caller, target: u.container_map[record.child_container->Some_0].root_process, quota_thread: caller,
            target_container: record.child_container->Some_0, transfer_source: Some(thread.owning_container),
        },
        Share4kOrigin::IpcPages { peer } => {
            let receiver = if u.thread_map[peer].state->IPC_TRANSIT_wait is Receive { peer } else { caller };
            Share4kObjects {
                source_thread: if u.thread_map[peer].state->IPC_TRANSIT_wait is Receive { caller } else { peer }, target: u.thread_map[receiver].owning_proc,
                quota_thread: receiver, target_container: u.thread_map[receiver].owning_container, transfer_source: None,
            }
        },
    }
}

/// The cpu and its running thread are write-locked while the thread records a share, and so is the peer of a
/// pages rendezvous, which is in transit with the running thread.
pub open spec fn share_4k_locked(u: KernelU, cpu_id: CpuId) -> bool {
    let caller = u.cpu_array[cpu_id as int].current_thread->Some_0;
    let origin = u.thread_map[caller].syscall_progress->Some_0->Share4k_origin;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& u.cpu_array[cpu_id as int].lock_state is WriteLocked
    &&& u.cpu_array[cpu_id as int].current_thread is Some
    &&& u.thread_map.dom().contains(caller)
    &&& u.thread_map[caller].lock_state is WriteLocked
    &&& u.thread_map[caller].syscall_progress is Some
    &&& u.thread_map[caller].syscall_progress->Some_0 is Share4k
    &&& origin is IpcPages ==> {
        let peer = origin->IpcPages_peer;
        &&& u.thread_map.dom().contains(peer)
        &&& u.thread_map[peer].lock_state is WriteLocked
        &&& u.thread_map[peer].state is IPC_TRANSIT
        &&& u.thread_map[peer].state->IPC_TRANSIT_partner == caller
    }
}

/// `container_ptr`, the running thread's container or a direct child of that live, non-zombie container, records an
/// offline request for `target`, a non-Off cpu it owns whose request bit is clear.
#[verifier::opaque]
pub open spec fn kernel_u_cpu_offline_request_changed(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, target: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let container = old_u.container_map[container_ptr];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& old_u.container_map.dom().contains(container_ptr)
    &&& cpu.owning_container == container_ptr || (container.parent == Some(cpu.owning_container) && old_u.container_map.dom().contains(cpu.owning_container)
        && !old_u.container_map[cpu.owning_container].killed && !old_u.container_map[cpu.owning_container].zombie)
    &&& index_valid(NUM_CPUS, target)
    &&& old_u.cpu_array[target as int].owning_container == container_ptr
    &&& !(old_u.cpu_array[target as int].state is Off)
    &&& container.cpu_offline_requests.len() == NUM_CPUS
    &&& !container.cpu_offline_requests[target as int]
    &&& new_u == (KernelU {
        container_map: old_u.container_map.insert(container_ptr, ContainerU { cpu_offline_requests: container.cpu_offline_requests.update(target as int, true), ..container }),
        ..old_u
    })
}

/// `target`, an Off cpu owned by `container_ptr`, the running thread's container or a direct child of that
/// live, non-zombie container, becomes Idle.
#[verifier::opaque]
pub open spec fn kernel_u_cpu_online_changed(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, target: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let target_cpu = old_u.cpu_array[target as int];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& old_u.container_map.dom().contains(container_ptr)
    &&& cpu.owning_container == container_ptr || (old_u.container_map[container_ptr].parent == Some(cpu.owning_container) && old_u.container_map.dom().contains(cpu.owning_container)
        && !old_u.container_map[cpu.owning_container].killed && !old_u.container_map[cpu.owning_container].zombie)
    &&& index_valid(NUM_CPUS, target)
    &&& old_u.cpu_array.len() == NUM_CPUS
    &&& target_cpu.owning_container == container_ptr
    &&& target_cpu.state is Off
    &&& new_u == (KernelU { cpu_array: old_u.cpu_array.update(target as int, CpuU { state: CpuState::Idle, op: CpuOpState::Idle, ..target_cpu }), ..old_u })
}

/// The running process, a live owner of `(bus, device, function)` with an IOMMU table, attaches DMA translation
/// to that function. The table keeps its DID, or adopts the function's candidate DID when it has none; nothing
/// else changes.
#[verifier::opaque]
pub open spec fn kernel_u_pci_attach_changed(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, bus: usize, device: usize, function: usize) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let process = old_u.process_map[cpu.current_process.unwrap()];
    let attached = old_u.iommu_root_table.attached;
    let table = process.iommu_table.unwrap();
    let did = match table.did { Some(did) => did, None => pci_bdf_did(bus, device, function) };
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_process is Some
    &&& old_u.process_map.dom().contains(cpu.current_process.unwrap())
    &&& !process.killed
    &&& pci_bdf_valid(bus, device, function)
    &&& process.owned_pci_functions.contains((bus, device, function))
    &&& process.iommu_table is Some
    &&& !attached[bus as int][device as int][function as int]
    &&& new_u == (KernelU {
        process_map: old_u.process_map.insert(cpu.current_process.unwrap(), ProcessU { iommu_table: Some(PageTableU { did: Some(did), ..table }), ..process }),
        iommu_root_table: IommuRootTableU { attached: seq3_update(attached, bus as int, device as int, function as int, true), ..old_u.iommu_root_table },
        ..old_u
    })
}

/// The non-Off cpu `cpu_id`, whose container `C` has a pending request for it, goes Off and unlocked: its running
/// thread, if any, is requeued at the tail of shard `cpu_id` of `C`'s scheduler with `regs`, `C`'s request bit for the cpu is
/// cleared, and the cpu's TLB entries are flushed except an unflushed default-PCID entry.
#[verifier::opaque]
pub open spec fn kernel_u_cpu_went_off_changed(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, regs: Registers, flushed_default_pcid: bool) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let container_ptr = cpu.owning_container;
    let container = old_u.container_map.spec_index(container_ptr);
    let requeued = match cpu.current_thread {
        Some(prev) => old_u.thread_map.insert(prev, ThreadU { state: ThreadState::SCHEDULED { cpu_id }, error_code: None, trap_frame: Some(regs), ..old_u.thread_map.spec_index(prev) }),
        None => old_u.thread_map,
    };
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& old_u.cpu_array.len() == NUM_CPUS
    &&& !(cpu.state is Off)
    &&& old_u.container_map.dom().contains(container_ptr)
    &&& container.cpu_offline_requests.len() == NUM_CPUS
    &&& container.cpu_offline_requests[cpu_id as int]
    &&& cpu.current_process is Some == cpu.current_thread is Some
    &&& (cpu.current_thread is Some ==> {
        let prev = old_u.thread_map.spec_index(cpu.current_thread.unwrap());
        &&& old_u.thread_map.dom().contains(cpu.current_thread.unwrap())
        &&& !prev.killed
        &&& prev.state == (ThreadState::RUNNING { cpu_id })
        &&& prev.owning_proc == cpu.current_process.unwrap()
        &&& old_u.process_map.dom().contains(cpu.current_process.unwrap())
        &&& !old_u.process_map.spec_index(cpu.current_process.unwrap()).killed
    })
    &&& new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, state: CpuState::Off, op: CpuOpState::Off, current_process: None, current_thread: None, ..cpu }),
        container_map: old_u.container_map.insert(container_ptr, ContainerU {
            scheduler: match cpu.current_thread {
                Some(prev) => container.scheduler.update(cpu_id as int, container.scheduler[cpu_id as int].push(prev)),
                None => container.scheduler,
            },
            cpu_offline_requests: container.cpu_offline_requests.update(cpu_id as int, false),
            ..container
        }),
        thread_map: requeued,
        cpu_tlb: cpu_tlb_after_cpu_went_off(old_u.cpu_tlb, cpu_id, flushed_default_pcid),
        ..old_u
    })
}

/// One quota of `thread_ptr` funds a new empty, unlocked receive endpoint `endpoint_ptr` of `container_ptr`,
/// installed at the thread's empty descriptor `endpoint_index`; the thread's progress is cleared.
#[verifier::opaque]
pub open spec fn kernel_u_new_endpoint_changed(
    old_u: KernelU, new_u: KernelU, container_ptr: RwLockContainerPtr, thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx, endpoint_ptr: RwLockEndpointPtr,
) -> bool {
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let container = old_u.container_map.spec_index(container_ptr);
    &&& old_u.container_map.dom().contains(container_ptr)
    &&& old_u.thread_map.dom().contains(thread_ptr)
    &&& !old_u.endpoint_map.dom().contains(endpoint_ptr)
    &&& edp_idx_valid(endpoint_index)
    &&& thread.quota_4k > 0
    &&& thread.endpoint_descriptors[endpoint_index as int] is None
    &&& new_u == (KernelU {
        endpoint_map: old_u.endpoint_map.insert(endpoint_ptr, EndpointU {
            lock_state: LockStateU::Unlocked, queue: Seq::empty(), queue_state: EndpointState::RECEIVE, owning_threads: set![(thread_ptr, endpoint_index)],
            owning_container: container_ptr, killed: false,
        }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU {
            quota_4k: (thread.quota_4k as int - 1) as usize, endpoint_descriptors: thread.endpoint_descriptors.update(endpoint_index as int, Some(endpoint_ptr)),
            syscall_progress: None, ..thread
        }),
        container_map: old_u.container_map.insert(container_ptr, ContainerU { owned_endpoints: container.owned_endpoints.insert(endpoint_ptr), ..container }),
        ..old_u
    })
}

/// The running thread `thread_ptr` exits from `cpu_id`, which goes idle. The thread leaves the thread map and its
/// container's thread set; its process drops it, absorbs its quota, and becomes a zombie without threads; a zombie
/// returns its PCID to its container's free set; a zombie root process makes its container a zombie; the container
/// owning the thread's page regains one 4K quota; and at most the `(cpu_id, KERNEL_DEFAULT_PCID)` TLB entry is flushed.
#[verifier::opaque]
pub open spec fn kernel_u_thread_exit_changed(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, flushed_default_pcid: bool) -> bool {
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let process_ptr = thread.owning_proc;
    let container_ptr = thread.owning_container;
    let process = old_u.process_map.spec_index(process_ptr);
    let threads = process.owned_threads.remove_value(thread_ptr);
    let zombie = threads.len() == 0;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& old_u.thread_map.dom().contains(thread_ptr)
    &&& old_u.process_map.dom().contains(process_ptr)
    &&& old_u.container_map.dom().contains(container_ptr)
    &&& new_u.container_map.dom() == old_u.container_map.dom()
    &&& forall|c: RwLockContainerPtr| #![trigger new_u.container_map.spec_index(c)]
        old_u.container_map.dom().contains(c) ==> {
            let container = old_u.container_map.spec_index(c);
            let quota_4k = if container.owned_pages.contains(thread_ptr) { (container.quota_4k + 1) as usize } else { container.quota_4k };
            new_u.container_map.spec_index(c) == if c == container_ptr {
                ContainerU {
                    zombie: container.zombie || (zombie && container.root_process == process_ptr), owned_threads: container.owned_threads.remove(thread_ptr), quota_4k,
                    free_pcids: if zombie { container.free_pcids.insert(process.pcid) } else { container.free_pcids }, ..container
                }
            } else { ContainerU { quota_4k, ..container } }
        }
    &&& new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { state: CpuState::Idle, op: CpuOpState::Idle, current_process: None, current_thread: None, ..old_u.cpu_array[cpu_id as int] }),
        container_map: new_u.container_map,
        process_map: old_u.process_map.insert(process_ptr, ProcessU {
            zombie, pagetable: if zombie { None } else { process.pagetable }, iommu_table: if zombie { None } else { process.iommu_table },
            quota_4k: (process.quota_4k + thread.quota_4k) as usize, quota_2m: (process.quota_2m + thread.quota_2m) as usize,
            quota_1g: (process.quota_1g + thread.quota_1g) as usize, owned_threads: threads, ..process
        }),
        thread_map: old_u.thread_map.remove(thread_ptr),
        cpu_tlb: if flushed_default_pcid {
            old_u.cpu_tlb.insert((cpu_id, KERNEL_DEFAULT_PCID), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
        } else { old_u.cpu_tlb },
        ..old_u
    })
}

/// One killed dangling thread, write-locked and linked to no thread, leaves the thread map and its container's thread
/// set, and the container owning its page regains one 4K quota; the kernel chooses the dangling thread (R1).
#[verifier::opaque]
pub open spec fn kernel_u_dangling_thread_reclaimed(old_u: KernelU, new_u: KernelU) -> bool {
    let removed = old_u.thread_map.dom().difference(new_u.thread_map.dom());
    &&& new_u.thread_map.dom().subset_of(old_u.thread_map.dom())
    &&& removed.len() == 1
    &&& forall|dangling_ptr: RwLockThreadPtr| #![trigger removed.contains(dangling_ptr)]
        removed.contains(dangling_ptr) ==> {
            let dangling = old_u.thread_map.spec_index(dangling_ptr);
            &&& dangling.state is KILLED
            &&& dangling.lock_state is WriteLocked
            &&& dangling.caller is None
            &&& dangling.callee is None
            &&& new_u == (KernelU {
                container_map: Map::new(old_u.container_map.dom(), |c: RwLockContainerPtr| {
                    let container = old_u.container_map[c];
                    ContainerU {
                        owned_threads: if c == dangling.owning_container { container.owned_threads.remove(dangling_ptr) } else { container.owned_threads },
                        quota_4k: if container.owned_pages.contains(dangling_ptr) { (container.quota_4k + 1) as usize } else { container.quota_4k }, ..container
                    }
                }),
                thread_map: old_u.thread_map.remove(dangling_ptr),
                ..old_u
            })
        }
}

/// Thread `thread_ptr` drops the last reference of the unlocked, unqueued endpoint at its descriptor `index`: the endpoint
/// leaves the endpoint map and its owner's endpoint set, and the container owning the endpoint's page regains one 4K quota.
/// The caller fixes the thread entry.
#[verifier::opaque]
pub open spec fn kernel_u_endpoint_released(old_u: KernelU, new_u: KernelU, thread_ptr: RwLockThreadPtr, index: int) -> bool {
    let thread = old_u.thread_map[thread_ptr];
    let endpoint_ptr = thread.endpoint_descriptors[index]->Some_0;
    let endpoint = old_u.endpoint_map[endpoint_ptr];
    &&& thread.endpoint_descriptors[index] is Some
    &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
    &&& endpoint.lock_state is Unlocked
    &&& endpoint.owning_threads == set![(thread_ptr, index as EndpointIdx)]
    &&& endpoint.queue == Seq::<RwLockThreadPtr>::empty()
    &&& new_u.endpoint_map == old_u.endpoint_map.remove(endpoint_ptr)
    &&& new_u.container_map == Map::new(old_u.container_map.dom(), |c: RwLockContainerPtr| {
        let container = old_u.container_map[c];
        ContainerU {
            owned_endpoints: if c == endpoint.owning_container { container.owned_endpoints.remove(endpoint_ptr) } else { container.owned_endpoints },
            quota_4k: if container.owned_pages.contains(endpoint_ptr) { (container.quota_4k + 1) as usize } else { container.quota_4k }, ..container
        }
    })
    &&& new_u == (KernelU { container_map: new_u.container_map, thread_map: new_u.thread_map, endpoint_map: new_u.endpoint_map, ..old_u })
}

/// One write-locked killed thread releases one descriptor: the descriptor is cleared and its unlocked endpoint, still held
/// elsewhere, drops the reference; the kernel chooses the thread and the descriptor (R1).
#[verifier::opaque]
pub open spec fn kernel_u_killed_descriptor_dropped(old_u: KernelU, new_u: KernelU) -> bool {
    let changed = old_u.thread_map.dom().filter(|t: RwLockThreadPtr| new_u.thread_map[t] != old_u.thread_map[t]);
    &&& changed.len() == 1
    &&& forall|thread_ptr: RwLockThreadPtr| #![trigger changed.contains(thread_ptr)] changed.contains(thread_ptr) ==> {
        let thread = old_u.thread_map[thread_ptr];
        let dropped = Set::<int>::range(0, MAX_NUM_ENDPOINT_DESCRIPTORS as int).filter(|j: int| new_u.thread_map[thread_ptr].endpoint_descriptors[j] != thread.endpoint_descriptors[j]);
        &&& thread.state is KILLED
        &&& thread.lock_state is WriteLocked
        &&& dropped.len() == 1
        &&& forall|index: int| #![trigger dropped.contains(index)] dropped.contains(index) ==> {
            let endpoint_ptr = thread.endpoint_descriptors[index]->Some_0;
            let endpoint = old_u.endpoint_map[endpoint_ptr];
            &&& thread.endpoint_descriptors[index] is Some
            &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
            &&& endpoint.lock_state is Unlocked
            &&& endpoint.owning_threads.len() > 1
            &&& new_u == (KernelU {
                thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { endpoint_descriptors: thread.endpoint_descriptors.update(index, None), ..thread }),
                endpoint_map: old_u.endpoint_map.insert(endpoint_ptr, EndpointU { owning_threads: endpoint.owning_threads.remove((thread_ptr, index as EndpointIdx)), ..endpoint }),
                ..old_u
            })
        }
    }
}

/// One write-locked killed thread releases the descriptor holding the last reference of its unlocked endpoint: the
/// descriptor is cleared and the endpoint is released; the kernel chooses the thread and the descriptor (R1).
#[verifier::opaque]
pub open spec fn kernel_u_killed_endpoint_released(old_u: KernelU, new_u: KernelU) -> bool {
    let changed = old_u.thread_map.dom().filter(|t: RwLockThreadPtr| new_u.thread_map[t] != old_u.thread_map[t]);
    &&& changed.len() == 1
    &&& forall|thread_ptr: RwLockThreadPtr| #![trigger changed.contains(thread_ptr)] changed.contains(thread_ptr) ==> {
        let thread = old_u.thread_map[thread_ptr];
        let dropped = Set::<int>::range(0, MAX_NUM_ENDPOINT_DESCRIPTORS as int).filter(|j: int| new_u.thread_map[thread_ptr].endpoint_descriptors[j] != thread.endpoint_descriptors[j]);
        &&& thread.state is KILLED
        &&& thread.lock_state is WriteLocked
        &&& dropped.len() == 1
        &&& forall|index: int| #![trigger dropped.contains(index)] dropped.contains(index) ==> {
            &&& kernel_u_endpoint_released(old_u, new_u, thread_ptr, index)
            &&& new_u.thread_map == old_u.thread_map.insert(thread_ptr, ThreadU { endpoint_descriptors: thread.endpoint_descriptors.update(index, None), ..thread })
        }
    }
}

/// The unlocked caller of one write-locked killed thread, waiting for its reply, is scheduled on shard `cpu_id` of its
/// container with `ErrorIpcCalleeExited`, and the killed thread drops its caller; the kernel chooses the killed thread
/// (R1).
#[verifier::opaque]
pub open spec fn kernel_u_killed_caller_woken(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let woken = old_u.thread_map.dom().filter(|t: RwLockThreadPtr| old_u.thread_map[t].state is WAITING_REPLY && new_u.thread_map[t].state is SCHEDULED);
    &&& woken.len() == 1
    &&& forall|caller_ptr: RwLockThreadPtr| #![trigger woken.contains(caller_ptr)] woken.contains(caller_ptr) ==> {
        let caller = old_u.thread_map[caller_ptr];
        let thread_ptr = caller.callee->Some_0;
        let thread = old_u.thread_map[thread_ptr];
        let container = old_u.container_map[caller.owning_container];
        &&& caller.callee is Some
        &&& old_u.thread_map.dom().contains(thread_ptr)
        &&& thread.state is KILLED
        &&& thread.lock_state is WriteLocked
        &&& thread.caller == Some(caller_ptr)
        &&& caller.lock_state is Unlocked
        &&& new_u == (KernelU {
            container_map: old_u.container_map.insert(caller.owning_container, ContainerU {
                scheduler: container.scheduler.update(cpu_id as int, container.scheduler[cpu_id as int].push(caller_ptr)), ..container
            }),
            thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { caller: None, ..thread }).insert(caller_ptr, ThreadU {
                state: ThreadState::SCHEDULED { cpu_id }, callee: None, error_code: Some(RetValueType::ErrorIpcCalleeExited), ..caller
            }),
            ..old_u
        })
    }
}

/// The unlocked dangling thread of the killed caller of one write-locked killed thread is taken over as a write-locked killed thread
/// without a callee, and the killed thread drops its caller; the kernel chooses the killed thread (R1).
#[verifier::opaque]
pub open spec fn kernel_u_killed_caller_taken_over(old_u: KernelU, new_u: KernelU) -> bool {
    let taken = old_u.thread_map.dom().filter(|t: RwLockThreadPtr| old_u.thread_map[t].state is DANGLING && new_u.thread_map[t].state is KILLED);
    &&& taken.len() == 1
    &&& forall|caller_ptr: RwLockThreadPtr| #![trigger taken.contains(caller_ptr)] taken.contains(caller_ptr) ==> {
        let caller = old_u.thread_map[caller_ptr];
        let thread_ptr = caller.callee->Some_0;
        let thread = old_u.thread_map[thread_ptr];
        &&& caller.callee is Some
        &&& old_u.thread_map.dom().contains(thread_ptr)
        &&& thread.state is KILLED
        &&& thread.lock_state is WriteLocked
        &&& thread.caller == Some(caller_ptr)
        &&& caller.lock_state is Unlocked
        &&& new_u == (KernelU {
            thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { caller: None, ..thread }) .insert(caller_ptr, ThreadU { state: ThreadState::KILLED, callee: None, lock_state: LockStateU::WriteLocked, ..caller }),
            ..old_u
        })
    }
}

/// One step of reclaiming write-locked killed threads: releasing a descriptor, waking a caller waiting for a reply,
/// taking over the dangling thread of a killed caller, reclaiming a killed dangling thread, or releasing an endpoint with
/// its last descriptor.
pub open spec fn kernel_u_killed_thread_reclaim_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    ||| kernel_u_killed_descriptor_dropped(old_u, new_u)
    ||| kernel_u_killed_caller_woken(old_u, new_u, cpu_id)
    ||| kernel_u_killed_caller_taken_over(old_u, new_u)
    ||| kernel_u_dangling_thread_reclaimed(old_u, new_u)
    ||| kernel_u_killed_endpoint_released(old_u, new_u)
}

/// Cpu `cpu_id` runs a thread in user mode, so it can enter its trap path at `syscall` or an interrupt gate.
#[verifier::opaque]
pub open spec fn kernel_u_trap_enter_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& old_u.cpu_array[cpu_id as int].state is Running
    &&& old_u.cpu_array[cpu_id as int].op is User
}

/// Cpu `cpu_id` leaves user mode for its trap path.
#[verifier::opaque]
pub open spec fn kernel_u_trap_enter_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    new_u == (KernelU { cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { op: CpuOpState::Trap, ..old_u.cpu_array[cpu_id as int] }), ..old_u })
}

/// Cpu `cpu_id` runs a thread on its trap path, so it can return to user mode at `sysretq` or `iretq`.
#[verifier::opaque]
pub open spec fn kernel_u_trap_return_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& old_u.cpu_array[cpu_id as int].state is Running
    &&& old_u.cpu_array[cpu_id as int].op is Trap
}

/// Cpu `cpu_id` returns from its trap path to user mode.
#[verifier::opaque]
pub open spec fn kernel_u_trap_return_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    new_u == (KernelU { cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { op: CpuOpState::User, ..old_u.cpu_array[cpu_id as int] }), ..old_u })
}

/// Cpu `cpu_id` runs a thread on its trap path and a killer marked it, so `restore_frame` can divert it to its idle loop.
#[verifier::opaque]
pub open spec fn kernel_u_trap_divert_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& old_u.cpu_array[cpu_id as int].state is Running
    &&& old_u.cpu_array[cpu_id as int].op is Trap
    &&& old_u.cpu_array[cpu_id as int].killed
}

/// Cpu `cpu_id` leaves its trap path for its idle loop.
#[verifier::opaque]
pub open spec fn kernel_u_trap_divert_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    new_u == (KernelU { cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { op: CpuOpState::Idle, ..old_u.cpu_array[cpu_id as int] }), ..old_u })
}
} // verus!
