use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_spec::*;

verus! {
/// The queue head of the endpoint at `endpoint_index` of the thread running on `cpu_id`.
pub open spec fn ipc_queue_head(pre: KernelK, cpu_id: CpuId, endpoint_index: EndpointIdx) -> RwLockThreadPtr {
    let thread = pre.thr_mp.spec_index(pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap()).view();
    pre.ep_mp.spec_index(thread.endpoint_descriptors.view()[endpoint_index as int].unwrap()).view().queue.view()[0]
}

/// The recorded caller of the thread running on `cpu_id`.
pub open spec fn ipc_recorded_caller(pre: KernelK, cpu_id: CpuId) -> RwLockThreadPtr {
    pre.thr_mp.spec_index(pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap()).view().caller.unwrap()
}

/// The value a call-family syscall returns for the `payload` it delivers: the carried usize, or Success.
pub open spec fn ipc_call_result(payload: IPCPayLoad) -> RetValueType {
    match payload {
        IPCPayLoad::Usize { value } => RetValueType::SuccessUsize { value },
        _ => RetValueType::Success,
    }
}

/// The value the running receive-call thread returns when it accepts the queue head's call.
pub open spec fn ipc_accept_call_result(pre: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx) -> RetValueType {
    let thread = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0];
    ipc_call_result(pre.thread_map[pre.endpoint_map[thread.endpoint_descriptors[endpoint_index as int]->Some_0].queue[0]].ipc_payload)
}

/// The rejection of a reply decided from the state at entry: a cpu no longer Running or marked by a killer, a killed caller, no recorded caller, a missing
/// descriptor, a queue of waiting senders or callers, or a killed recorded caller.
#[verifier::opaque]
pub open spec fn ipc_reply_entry_result(pre: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx) -> Option<RetValueType> {
    let cpu = pre.cpu_array[cpu_id as int];
    let thread = pre.thread_map[cpu.current_thread->Some_0];
    let endpoint = pre.endpoint_map[thread.endpoint_descriptors[endpoint_index as int]->Some_0];
    if !(cpu.state is Running) || cpu.killed { Some(RetValueType::CpuIdle) }
    else if thread.killed { Some(RetValueType::ErrorThreadKilled) }
    else if thread.caller is None { Some(RetValueType::ErrorReplyOutOfPhase) }
    else if thread.endpoint_descriptors[endpoint_index as int] is None { Some(RetValueType::ErrorInvalidEndpoint) }
    else if endpoint.queue.len() != 0 && endpoint.queue_state is SEND { Some(RetValueType::ErrorIpcSameDirection) }
    else if pre.thread_map[thread.caller->Some_0].killed { Some(RetValueType::ErrorIpcPeerKilled) }
    else { None }
}

/// The unlocked queue head of the endpoint at `endpoint_index` is a receive-call waiter of the caller's
/// container, so the caller hands it the CPU.
#[verifier::opaque]
pub open spec fn ipc_call_handoff_step_pre(old_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let caller = old_u.thread_map.spec_index(cpu.current_thread.unwrap());
    let endpoint_ptr = caller.endpoint_descriptors[endpoint_index as int].unwrap();
    let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
    let callee = old_u.thread_map.spec_index(endpoint.queue[0]);
    &&& ipc_step_pre(old_u, cpu_id, endpoint_index)
    &&& caller.callee is None
    &&& endpoint.queue.len() > 0
    &&& endpoint.queue_state is RECEIVE
    &&& endpoint.queue[0] != cpu.current_thread.unwrap()
    &&& old_u.thread_map.dom().contains(endpoint.queue[0])
    &&& callee.lock_state is Unlocked
    &&& !callee.killed
    &&& callee.state is RECEIVING_CALL
    &&& callee.caller is None
    &&& callee.callee is None
    &&& callee.blocking_endpoint_ptr == Some(endpoint_ptr)
    &&& callee.owning_container == caller.owning_container
    &&& old_u.process_map.dom().contains(callee.owning_proc)
}

/// User-visible call handoff: the queue head records the caller and runs on the caller's CPU, and the caller
/// saves `regs` and waits for the reply.
pub open spec fn ipc_call_handoff_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, regs: Registers, flushed_pcid: Option<Pcid>) -> bool {
    let caller_ptr = old_u.cpu_array[cpu_id as int].current_thread.unwrap();
    let endpoint_ptr = old_u.thread_map.spec_index(caller_ptr).endpoint_descriptors[endpoint_index as int].unwrap();
    kernel_u_ipc_call_handoff_changed(old_u, new_u, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, old_u.endpoint_map.spec_index(endpoint_ptr).queue[0], regs, flushed_pcid)
}

/// The running receive-call thread holds no caller and the unlocked queue head of the endpoint at
/// `endpoint_index` is a caller of its container, so it accepts the call.
#[verifier::opaque]
pub open spec fn ipc_accept_call_step_pre(old_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let callee = old_u.thread_map.spec_index(cpu.current_thread.unwrap());
    let endpoint_ptr = callee.endpoint_descriptors[endpoint_index as int].unwrap();
    let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
    let caller = old_u.thread_map.spec_index(endpoint.queue[0]);
    &&& ipc_step_pre(old_u, cpu_id, endpoint_index)
    &&& callee.caller is None
    &&& callee.callee is None
    &&& endpoint.queue.len() > 0
    &&& endpoint.queue_state is SEND
    &&& endpoint.queue[0] != cpu.current_thread.unwrap()
    &&& old_u.thread_map.dom().contains(endpoint.queue[0])
    &&& caller.lock_state is Unlocked
    &&& !caller.killed
    &&& caller.state is CALLING
    &&& caller.callee is None
    &&& caller.blocking_endpoint_ptr == Some(endpoint_ptr)
    &&& caller.owning_container == callee.owning_container
}

/// User-visible call acceptance: the queue head leaves the queue and waits for the reply, and the running
/// thread records it as its caller.
pub open spec fn ipc_accept_call_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx) -> bool {
    let callee_ptr = old_u.cpu_array[cpu_id as int].current_thread.unwrap();
    let endpoint_ptr = old_u.thread_map.spec_index(callee_ptr).endpoint_descriptors[endpoint_index as int].unwrap();
    kernel_u_ipc_accept_call_changed(old_u, new_u, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, old_u.endpoint_map.spec_index(endpoint_ptr).queue[0])
}

/// The running thread records an unlocked live caller of its container that waits for its reply, and the
/// endpoint at `endpoint_index` is empty or waits in the receive direction.
#[verifier::opaque]
pub open spec fn ipc_reply_handoff_step_pre(old_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let callee = old_u.thread_map.spec_index(cpu.current_thread.unwrap());
    let endpoint_ptr = callee.endpoint_descriptors[endpoint_index as int].unwrap();
    let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
    let caller = old_u.thread_map.spec_index(callee.caller.unwrap());
    &&& ipc_step_pre(old_u, cpu_id, endpoint_index)
    &&& callee.caller is Some
    &&& callee.callee is None
    &&& endpoint.queue.len() == 0 || endpoint.queue_state is RECEIVE
    &&& callee.caller.unwrap() != cpu.current_thread.unwrap()
    &&& old_u.thread_map.dom().contains(callee.caller.unwrap())
    &&& caller.lock_state is Unlocked
    &&& !caller.killed
    &&& caller.state is WAITING_REPLY
    &&& caller.callee == Some(cpu.current_thread.unwrap())
    &&& caller.owning_container == callee.owning_container
    &&& old_u.process_map.dom().contains(caller.owning_proc)
}

/// User-visible reply handoff: the recorded caller resumes on the CPU, and the running thread saves `regs`
/// and waits for the next call on the endpoint at `endpoint_index`.
pub open spec fn ipc_reply_handoff_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, regs: Registers, flushed_pcid: Option<Pcid>) -> bool {
    let callee_ptr = old_u.cpu_array[cpu_id as int].current_thread.unwrap();
    let callee = old_u.thread_map.spec_index(callee_ptr);
    kernel_u_ipc_reply_handoff_changed(old_u, new_u, cpu_id, callee_ptr, callee.endpoint_descriptors[endpoint_index as int].unwrap(), endpoint_index, callee.caller.unwrap(), regs, flushed_pcid)
}

/// A call is one block step, one rendezvous error step against a plain receiver or a foreign receive-call
/// waiter, one handoff step, or a stuttering rejection; a cpu no longer Running or marked by a killer stutters with CpuIdle.
#[verifier::opaque]
pub open spec fn ipc_call_syscall_trace(
    trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, payload: IPCPayLoad, regs: Registers,
    flushed_default_pcid: bool, flushed_pcid: Option<Pcid>, ret: RetValueType,
) -> bool {
    if ret is CpuIdle && (!(pre.cpu_array[cpu_id as int].state is Running) || pre.cpu_array[cpu_id as int].killed) {
        &&& trace.len() == 0
        &&& post == pre
    } else if ret is CpuIdle {
        &&& trace.len() == 1
        &&& trace[0].old_u == pre
        &&& trace[0].new_u == post
        &&& ipc_block_step_pre(pre, cpu_id, endpoint_index, ThreadState::CALLING)
        &&& ipc_block_step(pre, post, cpu_id, endpoint_index, ThreadState::CALLING, payload, regs, flushed_default_pcid)
    } else if ret is ErrorIpcTypeMismatch || ret is ErrorCallAcrossContainers {
        &&& trace.len() == 1
        &&& trace[0].old_u == pre
        &&& trace[0].new_u == post
        &&& ret == ipc_rendezvous_result(pre, cpu_id, endpoint_index, ThreadState::CALLING, payload)
        &&& ipc_rendezvous_step_pre(pre, cpu_id, endpoint_index, ThreadState::CALLING, payload)
        &&& ipc_rendezvous_step(pre, post, cpu_id, endpoint_index, ThreadState::CALLING, payload)
    } else if ret is Success || ret is SuccessUsize {
        &&& trace.len() == 1
        &&& trace[0].old_u == pre
        &&& trace[0].new_u == post
        &&& ret == ipc_call_result(payload)
        &&& ipc_call_handoff_step_pre(pre, cpu_id, endpoint_index)
        &&& ipc_call_handoff_step(pre, post, cpu_id, endpoint_index, regs, flushed_pcid)
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}

/// A receive_call is one block step, one rendezvous error step against a plain sender or a foreign caller,
/// one acceptance step, or a stuttering rejection; a cpu no longer Running or marked by a killer stutters with CpuIdle.
#[verifier::opaque]
pub open spec fn ipc_receive_call_syscall_trace(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, regs: Registers, flushed_default_pcid: bool, ret: RetValueType) -> bool {
    if ret is CpuIdle && (!(pre.cpu_array[cpu_id as int].state is Running) || pre.cpu_array[cpu_id as int].killed) {
        &&& trace.len() == 0
        &&& post == pre
    } else if ret is CpuIdle {
        &&& trace.len() == 1
        &&& trace[0].old_u == pre
        &&& trace[0].new_u == post
        &&& ipc_block_step_pre(pre, cpu_id, endpoint_index, ThreadState::RECEIVING_CALL)
        &&& ipc_block_step(pre, post, cpu_id, endpoint_index, ThreadState::RECEIVING_CALL, IPCPayLoad::Empty, regs, flushed_default_pcid)
    } else if ret is ErrorIpcTypeMismatch || ret is ErrorCallAcrossContainers {
        &&& trace.len() == 1
        &&& trace[0].old_u == pre
        &&& trace[0].new_u == post
        &&& ret == ipc_rendezvous_result(pre, cpu_id, endpoint_index, ThreadState::RECEIVING_CALL, IPCPayLoad::Empty)
        &&& ipc_rendezvous_step_pre(pre, cpu_id, endpoint_index, ThreadState::RECEIVING_CALL, IPCPayLoad::Empty)
        &&& ipc_rendezvous_step(pre, post, cpu_id, endpoint_index, ThreadState::RECEIVING_CALL, IPCPayLoad::Empty)
    } else if ret is Success || ret is SuccessUsize {
        &&& trace.len() == 1
        &&& trace[0].old_u == pre
        &&& trace[0].new_u == post
        &&& ret == ipc_accept_call_result(pre, cpu_id, endpoint_index)
        &&& ipc_accept_call_step_pre(pre, cpu_id, endpoint_index)
        &&& ipc_accept_call_step(pre, post, cpu_id, endpoint_index)
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}

/// The running thread records the unlocked dangling thread of a killed caller that waits for its reply, and the endpoint at
/// `endpoint_index` is empty or waits in the receive direction.
#[verifier::opaque]
pub open spec fn ipc_reply_dangling_caller_step_pre(old_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let callee = old_u.thread_map.spec_index(cpu.current_thread.unwrap());
    let endpoint = old_u.endpoint_map.spec_index(callee.endpoint_descriptors[endpoint_index as int].unwrap());
    let caller = old_u.thread_map.spec_index(callee.caller.unwrap());
    &&& ipc_step_pre(old_u, cpu_id, endpoint_index)
    &&& callee.caller is Some
    &&& endpoint.queue.len() == 0 || endpoint.queue_state is RECEIVE
    &&& callee.caller.unwrap() != cpu.current_thread.unwrap()
    &&& old_u.thread_map.dom().contains(callee.caller.unwrap())
    &&& caller.lock_state is Unlocked
    &&& !caller.killed
    &&& caller.state is DANGLING
    &&& caller.callee == Some(cpu.current_thread.unwrap())
}

/// Taking over the dangling thread write-locks the cpu, the running thread, and the dangling thread, drops the running thread's caller, and
/// leaves the dangling thread a killed thread without a callee.
pub open spec fn ipc_reply_dangling_caller_taken_over_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let callee_ptr = cpu.current_thread.unwrap();
    let dangling_ptr = old_u.thread_map.spec_index(callee_ptr).caller.unwrap();
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..cpu }),
        thread_map: old_u.thread_map.insert(callee_ptr, ThreadU { lock_state: LockStateU::WriteLocked, caller: None, ..old_u.thread_map.spec_index(callee_ptr) })
            .insert(dangling_ptr, ThreadU { state: ThreadState::KILLED, callee: None, lock_state: LockStateU::WriteLocked, ..old_u.thread_map.spec_index(dangling_ptr) }),
        ..old_u
    })
}

/// The cpu and its running thread stay write-held between the steps of a reply to a dangling thread.
pub open spec fn ipc_reply_dangling_caller_held_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is WriteLocked
    &&& cpu.state is Running
    &&& cpu.current_thread is Some
    &&& old_u.thread_map.dom().contains(cpu.current_thread->Some_0)
    &&& old_u.thread_map.spec_index(cpu.current_thread->Some_0).lock_state is WriteLocked
}

/// Releasing the cpu and the running thread after the dangling thread is reclaimed.
pub open spec fn ipc_reply_dangling_caller_released_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let callee_ptr = cpu.current_thread.unwrap();
    new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: cpu_op_after_step(cpu.state), ..cpu }),
        thread_map: old_u.thread_map.insert(callee_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..old_u.thread_map.spec_index(callee_ptr) }),
        ..old_u
    })
}

/// A reply_and_receive is one reply handoff step; a reply to the dangling thread of a killed caller takes the dangling thread over, reclaims
/// it and the killed callers it takes over one step per change, and releases the cpu and the running thread; a rejection
/// stutters.
#[verifier::opaque]
pub open spec fn ipc_reply_and_receive_syscall_trace(
    trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, payload: IPCPayLoad, regs: Registers,
    flushed_pcid: Option<Pcid>, ret: RetValueType,
) -> bool {
    if ret is Success || ret is SuccessUsize {
        &&& trace.len() == 1
        &&& trace[0].old_u == pre
        &&& trace[0].new_u == post
        &&& ret == ipc_call_result(payload)
        &&& ipc_reply_handoff_step_pre(pre, cpu_id, endpoint_index)
        &&& ipc_reply_handoff_step(pre, post, cpu_id, endpoint_index, regs, flushed_pcid)
    } else if ret is ErrorIpcCallerKilled {
        let last = trace.len() - 1;
        &&& trace.len() >= 3
        &&& trace[0].old_u == pre
        &&& ipc_reply_dangling_caller_step_pre(pre, cpu_id, endpoint_index)
        &&& ipc_reply_dangling_caller_taken_over_step(pre, trace[0].new_u, cpu_id)
        &&& forall|j: int| #![trigger trace[j]] 0 < j < last ==> ipc_reply_dangling_caller_held_step_pre(trace[j].old_u, cpu_id) && kernel_u_killed_thread_reclaim_step(trace[j].old_u, trace[j].new_u, cpu_id)
        &&& ipc_reply_dangling_caller_held_step_pre(trace[last].old_u, cpu_id)
        &&& trace[last].new_u == post
        &&& ipc_reply_dangling_caller_released_step(trace[last].old_u, post, cpu_id)
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}

/// Dequeues the receive-call callee, switches `cpu_id` to its process, records the caller on it, parks the
/// caller waiting for the reply with `entry_regs`, and updates the affected PCID publication and TLB state.
#[verifier::opaque]
pub(super) open spec fn ipc_call_handoff_eof_transition_framing(pre: KernelK, post: KernelK, cpu_id: CpuId, caller_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, callee_ptr: RwLockThreadPtr, entry_regs: Registers) -> bool {
    let cpu_before = pre.cpu_arr.spec_index(cpu_id).view();
    let cpu_after = post.cpu_arr.spec_index(cpu_id).view();
    let old_cpu = cpu_before.view().view();
    let new_cpu = cpu_after.view().view();
    let callee = pre.thr_mp.spec_index(callee_ptr).view();
    let next_process = callee.owning_proc;
    let target = pre.prc_mp.spec_index(next_process).view_rodata().view();
    let pcid = target.pcid;
    let dirty = cpu_before.view().tlb_dirty_bitmap().spec_index(pcid);
    let flush = pre.pcid_needflush.spec_index(cpu_id, pcid).view().needflush
        || (dirty is Some && (dirty.unwrap().process_ptr != next_process || dirty.unwrap().pagetable_ptr != target.pagetable));
    let callee_node = callee.endpoint_linkedlist_node.addr();
    let needflush_before = pre.pcid_needflush.spec_index(cpu_id, pcid);
    let needflush_after = post.pcid_needflush.spec_index(cpu_id, pcid);
    let endpoint_before = pre.ep_mp.spec_index(endpoint_ptr);
    let endpoint_after = post.ep_mp.spec_index(endpoint_ptr);
    &&& post == (KernelK { cpu_arr: post.cpu_arr, pcid_needflush: post.pcid_needflush, cpu_hw_cr3_pcid: post.cpu_hw_cr3_pcid, thr_mp: post.thr_mp, ep_mp: post.ep_mp, cpu_tlb: post.cpu_tlb, ..pre })
    &&& post.cpu_arr.view().len() == pre.cpu_arr.view().len()
    &&& (forall|c: CpuId| #![trigger pre.cpu_arr.spec_index(c)] #![trigger post.cpu_arr.spec_index(c)] index_valid(NUM_CPUS, c) && c != cpu_id ==> post.cpu_arr.spec_index(c) == pre.cpu_arr.spec_index(c))
    &&& cpu_after.is_init() == cpu_before.is_init()
    &&& cpu_after.view_rodata() == cpu_before.view_rodata()
    &&& cpu_after.view_ghost() == cpu_before.view_ghost()
    &&& cpu_after.view().kernel_call_perm() == cpu_before.view().kernel_call_perm()
    &&& cpu_after.being_killed() == cpu_before.being_killed()
    &&& cpu_after.killer_info() == cpu_before.killer_info()
    &&& cpu_after.locking_thread() == cpu_before.locking_thread()
    &&& new_cpu == (CpuView {
        state: CpuState::Running, current_process: Some(next_process),
        current_thread: Some(callee_ptr), current_pagetable: Some(target.pagetable),
        current_cr3: target.cr3, current_pcid: pcid, process_depth: target.depth,
        tlb_dirty_bitmap: new_cpu.tlb_dirty_bitmap, ..old_cpu
    })
    &&& cpu_after.view().wf()
    &&& cpu_after.view().tlb_dirty_bitmap() == cpu_before.view().tlb_dirty_bitmap().insert(pcid, Some(ProcessPageTablePair { process_ptr: next_process, pagetable_ptr: target.pagetable }))
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& (forall|ptr: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(ptr)] #![trigger post.thr_mp.spec_index(ptr)] pre.thr_mp.dom().contains(ptr) ==> {
        let before = pre.thr_mp.spec_index(ptr);
        let after = post.thr_mp.spec_index(ptr);
        &&& post.thr_mp.view().spec_index(ptr).is_init() == pre.thr_mp.view().spec_index(ptr).is_init()
        &&& post.thr_mp.view().spec_index(ptr).addr() == pre.thr_mp.view().spec_index(ptr).addr()
        &&& after.view().temp_alloc_cache_4k == before.view().temp_alloc_cache_4k
        &&& after.view().temp_alloc_cache_2m == before.view().temp_alloc_cache_2m
        &&& after.view().temp_alloc_cache_1g == before.view().temp_alloc_cache_1g
        &&& after.view().endpoint_descriptors == before.view().endpoint_descriptors
        &&& (ptr != caller_ptr && ptr != callee_ptr ==> after == before)
        &&& (ptr == caller_ptr || ptr == callee_ptr ==> {
            &&& after.is_init() == before.is_init()
            &&& after.view_rodata() == before.view_rodata()
            &&& after.view_ghost() == before.view_ghost()
            &&& after.being_killed() == before.being_killed()
            &&& after.locking_thread() == before.locking_thread()
            &&& after.view().inv()
        })
        &&& (ptr == caller_ptr ==> {
            &&& after.view() == (Thread { state: ThreadState::WAITING_REPLY, callee: Some(callee_ptr), trap_frame: after.view().trap_frame, ..before.view() })
            &&& after.view().trap_frame.is_some()
            &&& *after.view().trap_frame.get_some_0() == entry_regs
        })
        &&& (ptr == callee_ptr ==> {
            &&& after.view() == (Thread {
                state: ThreadState::RUNNING { cpu_id }, caller: Some(caller_ptr), call_depth: Ghost(pre.thr_mp.spec_index(caller_ptr).view().call_depth.view() + 1),
                blocking_endpoint_ptr: None, blocking_endpoint_index: None, endpoint_linkedlist_node: after.view().endpoint_linkedlist_node, last_cpu: cpu_id,
                trap_frame: after.view().trap_frame, ..before.view()
            })
            &&& after.view().endpoint_linkedlist_node.is_init()
            &&& after.view().endpoint_linkedlist_node.addr() == before.view().endpoint_linkedlist_node.addr()
            &&& after.view().trap_frame.is_none()
        })
    })
    &&& post.ep_mp.dom() == pre.ep_mp.dom()
    &&& (forall|key: RwLockEndpointPtr| #![trigger pre.ep_mp.spec_index(key)] #![trigger post.ep_mp.spec_index(key)] pre.ep_mp.dom().contains(key) ==> {
        &&& post.ep_mp.view().spec_index(key).is_init() == pre.ep_mp.view().spec_index(key).is_init()
        &&& post.ep_mp.view().spec_index(key).addr() == pre.ep_mp.view().spec_index(key).addr()
        &&& (key != endpoint_ptr ==> post.ep_mp.spec_index(key) == pre.ep_mp.spec_index(key))
    })
    &&& endpoint_after.is_init() == endpoint_before.is_init()
    &&& endpoint_after.view_rodata() == endpoint_before.view_rodata()
    &&& endpoint_after.view_ghost() == endpoint_before.view_ghost()
    &&& endpoint_after.being_killed() == endpoint_before.being_killed()
    &&& endpoint_after.locking_thread() == endpoint_before.locking_thread()
    &&& endpoint_after.view() == (Endpoint { queue: endpoint_after.view().queue, ..endpoint_before.view() })
    &&& endpoint_after.view().queue.container_depth == endpoint_before.view().queue.container_depth
    &&& endpoint_after.view().queue.lock_minor() == endpoint_before.view().queue.lock_minor()
    &&& endpoint_after.view().queue.view() == endpoint_before.view().queue.view().skip(1)
    &&& endpoint_after.view().queue.length as int == endpoint_before.view().queue.length as int - 1
    &&& endpoint_after.view().queue.map() == endpoint_before.view().queue.map().remove(callee_node)
    &&& endpoint_after.view().queue.dom() == endpoint_before.view().queue.dom().remove(callee_node)
    &&& needflush_after.view().index() == needflush_before.view().index()
    &&& needflush_after.is_init() == needflush_before.is_init()
    &&& needflush_after.view_rodata() == needflush_before.view_rodata()
    &&& needflush_after.view_ghost() == needflush_before.view_ghost()
    &&& needflush_after.being_killed() == needflush_before.being_killed()
    &&& needflush_after.locking_thread() == needflush_before.locking_thread()
    &&& needflush_after.view() == (PcidNeedFlush { needflush: false, ..needflush_before.view() })
    &&& (forall|c: CpuId, p: Pcid| #![trigger pre.pcid_needflush.spec_index(c, p)] #![trigger post.pcid_needflush.spec_index(c, p)]
        index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid) ==> post.pcid_needflush.spec_index(c, p) == pre.pcid_needflush.spec_index(c, p))
    &&& post.cpu_hw_cr3_pcid[cpu_id as int].owner_cpu() == pre.cpu_hw_cr3_pcid[cpu_id as int].owner_cpu()
    &&& post.cpu_hw_cr3_pcid[cpu_id as int].view() == (target.cr3, pcid)
    &&& (forall|c: CpuId| #![trigger pre.cpu_hw_cr3_pcid[c as int]] #![trigger post.cpu_hw_cr3_pcid[c as int]] index_valid(NUM_CPUS, c) && c != cpu_id ==> post.cpu_hw_cr3_pcid[c as int] == pre.cpu_hw_cr3_pcid[c as int])
    &&& post.cpu_tlb.view() == if flush { pre.cpu_tlb.view().insert((cpu_id, pcid), post.cpu_tlb.spec_index((cpu_id, pcid))) } else { pre.cpu_tlb.view() }
    &&& (forall|c: CpuId, p: Pcid| #![trigger pre.cpu_tlb.spec_index((c, p))] #![trigger post.cpu_tlb.spec_index((c, p))]
        index_valid(NUM_CPUS, c) && pcid_valid(p) && !(flush && c == cpu_id && p == pcid) ==> post.cpu_tlb.spec_index((c, p)) == pre.cpu_tlb.spec_index((c, p)))
    &&& flush ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(post.cpu_tlb.spec_index((cpu_id, pcid)), pagetable_c(pre.pt_mp, pre.pt_lower.view(), target.pagetable))
}

/// Dequeues the caller at the queue head, parks it waiting for the reply of the running callee, and records
/// it as that callee's caller.
#[verifier::opaque]
pub(super) open spec fn ipc_accept_call_eof_transition_framing(pre: KernelK, post: KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, caller_ptr: RwLockThreadPtr) -> bool {
    let caller = pre.thr_mp.spec_index(caller_ptr).view();
    let caller_node = caller.endpoint_linkedlist_node.addr();
    let endpoint_before = pre.ep_mp.spec_index(endpoint_ptr);
    let endpoint_after = post.ep_mp.spec_index(endpoint_ptr);
    &&& post == (KernelK { thr_mp: post.thr_mp, ep_mp: post.ep_mp, ..pre })
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& (forall|ptr: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(ptr)] #![trigger post.thr_mp.spec_index(ptr)] pre.thr_mp.dom().contains(ptr) ==> {
        let before = pre.thr_mp.spec_index(ptr);
        let after = post.thr_mp.spec_index(ptr);
        &&& post.thr_mp.view().spec_index(ptr).is_init() == pre.thr_mp.view().spec_index(ptr).is_init()
        &&& post.thr_mp.view().spec_index(ptr).addr() == pre.thr_mp.view().spec_index(ptr).addr()
        &&& after.view().temp_alloc_cache_4k == before.view().temp_alloc_cache_4k
        &&& after.view().temp_alloc_cache_2m == before.view().temp_alloc_cache_2m
        &&& after.view().temp_alloc_cache_1g == before.view().temp_alloc_cache_1g
        &&& after.view().endpoint_descriptors == before.view().endpoint_descriptors
        &&& (ptr != caller_ptr && ptr != callee_ptr ==> after == before)
        &&& (ptr == caller_ptr || ptr == callee_ptr ==> {
            &&& after.is_init() == before.is_init()
            &&& after.view_rodata() == before.view_rodata()
            &&& after.view_ghost() == before.view_ghost()
            &&& after.being_killed() == before.being_killed()
            &&& after.locking_thread() == before.locking_thread()
            &&& after.view().inv()
        })
        &&& (ptr == callee_ptr ==> after.view() == (Thread { caller: Some(caller_ptr), call_depth: Ghost(pre.thr_mp.spec_index(caller_ptr).view().call_depth.view() + 1), ..before.view() }))
        &&& (ptr == caller_ptr ==> {
            &&& after.view() == (Thread {
                state: ThreadState::WAITING_REPLY, callee: Some(callee_ptr), blocking_endpoint_ptr: None, blocking_endpoint_index: None,
                endpoint_linkedlist_node: after.view().endpoint_linkedlist_node, ..before.view()
            })
            &&& after.view().endpoint_linkedlist_node.is_init()
            &&& after.view().endpoint_linkedlist_node.addr() == before.view().endpoint_linkedlist_node.addr()
        })
    })
    &&& post.ep_mp.dom() == pre.ep_mp.dom()
    &&& (forall|key: RwLockEndpointPtr| #![trigger pre.ep_mp.spec_index(key)] #![trigger post.ep_mp.spec_index(key)] pre.ep_mp.dom().contains(key) ==> {
        &&& post.ep_mp.view().spec_index(key).is_init() == pre.ep_mp.view().spec_index(key).is_init()
        &&& post.ep_mp.view().spec_index(key).addr() == pre.ep_mp.view().spec_index(key).addr()
        &&& (key != endpoint_ptr ==> post.ep_mp.spec_index(key) == pre.ep_mp.spec_index(key))
    })
    &&& endpoint_after.is_init() == endpoint_before.is_init()
    &&& endpoint_after.view_rodata() == endpoint_before.view_rodata()
    &&& endpoint_after.view_ghost() == endpoint_before.view_ghost()
    &&& endpoint_after.being_killed() == endpoint_before.being_killed()
    &&& endpoint_after.locking_thread() == endpoint_before.locking_thread()
    &&& endpoint_after.view() == (Endpoint { queue: endpoint_after.view().queue, ..endpoint_before.view() })
    &&& endpoint_after.view().queue.container_depth == endpoint_before.view().queue.container_depth
    &&& endpoint_after.view().queue.lock_minor() == endpoint_before.view().queue.lock_minor()
    &&& endpoint_after.view().queue.view() == endpoint_before.view().queue.view().skip(1)
    &&& endpoint_after.view().queue.length as int == endpoint_before.view().queue.length as int - 1
    &&& endpoint_after.view().queue.map() == endpoint_before.view().queue.map().remove(caller_node)
    &&& endpoint_after.view().queue.dom() == endpoint_before.view().queue.dom().remove(caller_node)
}

/// Switches `cpu_id` to the recorded caller's process and resumes it, parks the replying callee with
/// `entry_regs` at the endpoint tail as a receive-call waiter, and updates the affected PCID publication and
/// TLB state.
#[verifier::opaque]
pub(super) open spec fn ipc_reply_handoff_eof_transition_framing(pre: KernelK, post: KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, caller_ptr: RwLockThreadPtr, entry_regs: Registers) -> bool {
    let cpu_before = pre.cpu_arr.spec_index(cpu_id).view();
    let cpu_after = post.cpu_arr.spec_index(cpu_id).view();
    let old_cpu = cpu_before.view().view();
    let new_cpu = cpu_after.view().view();
    let callee = pre.thr_mp.spec_index(callee_ptr).view();
    let caller = pre.thr_mp.spec_index(caller_ptr).view();
    let next_process = caller.owning_proc;
    let target = pre.prc_mp.spec_index(next_process).view_rodata().view();
    let pcid = target.pcid;
    let dirty = cpu_before.view().tlb_dirty_bitmap().spec_index(pcid);
    let flush = pre.pcid_needflush.spec_index(cpu_id, pcid).view().needflush
        || (dirty is Some && (dirty.unwrap().process_ptr != next_process || dirty.unwrap().pagetable_ptr != target.pagetable));
    let callee_node = callee.endpoint_linkedlist_node.addr();
    let needflush_before = pre.pcid_needflush.spec_index(cpu_id, pcid);
    let needflush_after = post.pcid_needflush.spec_index(cpu_id, pcid);
    let endpoint_before = pre.ep_mp.spec_index(endpoint_ptr);
    let endpoint_after = post.ep_mp.spec_index(endpoint_ptr);
    &&& post == (KernelK { cpu_arr: post.cpu_arr, pcid_needflush: post.pcid_needflush, cpu_hw_cr3_pcid: post.cpu_hw_cr3_pcid, thr_mp: post.thr_mp, ep_mp: post.ep_mp, cpu_tlb: post.cpu_tlb, ..pre })
    &&& post.cpu_arr.view().len() == pre.cpu_arr.view().len()
    &&& (forall|c: CpuId| #![trigger pre.cpu_arr.spec_index(c)] #![trigger post.cpu_arr.spec_index(c)] index_valid(NUM_CPUS, c) && c != cpu_id ==> post.cpu_arr.spec_index(c) == pre.cpu_arr.spec_index(c))
    &&& cpu_after.is_init() == cpu_before.is_init()
    &&& cpu_after.view_rodata() == cpu_before.view_rodata()
    &&& cpu_after.view_ghost() == cpu_before.view_ghost()
    &&& cpu_after.view().kernel_call_perm() == cpu_before.view().kernel_call_perm()
    &&& cpu_after.being_killed() == cpu_before.being_killed()
    &&& cpu_after.killer_info() == cpu_before.killer_info()
    &&& cpu_after.locking_thread() == cpu_before.locking_thread()
    &&& new_cpu == (CpuView {
        state: CpuState::Running, current_process: Some(next_process),
        current_thread: Some(caller_ptr), current_pagetable: Some(target.pagetable),
        current_cr3: target.cr3, current_pcid: pcid, process_depth: target.depth,
        tlb_dirty_bitmap: new_cpu.tlb_dirty_bitmap, ..old_cpu
    })
    &&& cpu_after.view().wf()
    &&& cpu_after.view().tlb_dirty_bitmap() == cpu_before.view().tlb_dirty_bitmap().insert(pcid, Some(ProcessPageTablePair { process_ptr: next_process, pagetable_ptr: target.pagetable }))
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& (forall|ptr: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(ptr)] #![trigger post.thr_mp.spec_index(ptr)] pre.thr_mp.dom().contains(ptr) ==> {
        let before = pre.thr_mp.spec_index(ptr);
        let after = post.thr_mp.spec_index(ptr);
        &&& post.thr_mp.view().spec_index(ptr).is_init() == pre.thr_mp.view().spec_index(ptr).is_init()
        &&& post.thr_mp.view().spec_index(ptr).addr() == pre.thr_mp.view().spec_index(ptr).addr()
        &&& after.view().temp_alloc_cache_4k == before.view().temp_alloc_cache_4k
        &&& after.view().temp_alloc_cache_2m == before.view().temp_alloc_cache_2m
        &&& after.view().temp_alloc_cache_1g == before.view().temp_alloc_cache_1g
        &&& after.view().endpoint_descriptors == before.view().endpoint_descriptors
        &&& (ptr != caller_ptr && ptr != callee_ptr ==> after == before)
        &&& (ptr == caller_ptr || ptr == callee_ptr ==> {
            &&& after.is_init() == before.is_init()
            &&& after.view_rodata() == before.view_rodata()
            &&& after.view_ghost() == before.view_ghost()
            &&& after.being_killed() == before.being_killed()
            &&& after.locking_thread() == before.locking_thread()
            &&& after.view().inv()
        })
        &&& (ptr == callee_ptr ==> {
            &&& after.view() == (Thread {
                state: ThreadState::RECEIVING_CALL, caller: None, blocking_endpoint_ptr: Some(endpoint_ptr), blocking_endpoint_index: Some(endpoint_index),
                ipc_payload: IPCPayLoad::Empty, trap_frame: after.view().trap_frame, endpoint_linkedlist_node: after.view().endpoint_linkedlist_node, ..before.view()
            })
            &&& !after.view().endpoint_linkedlist_node.is_init()
            &&& after.view().endpoint_linkedlist_node.addr() == before.view().endpoint_linkedlist_node.addr()
            &&& after.view().trap_frame.is_some()
            &&& *after.view().trap_frame.get_some_0() == entry_regs
        })
        &&& (ptr == caller_ptr ==> {
            &&& after.view() == (Thread { state: ThreadState::RUNNING { cpu_id }, callee: None, last_cpu: cpu_id, trap_frame: after.view().trap_frame, ..before.view() })
            &&& after.view().trap_frame.is_none()
        })
    })
    &&& post.ep_mp.dom() == pre.ep_mp.dom()
    &&& (forall|key: RwLockEndpointPtr| #![trigger pre.ep_mp.spec_index(key)] #![trigger post.ep_mp.spec_index(key)] pre.ep_mp.dom().contains(key) ==> {
        &&& post.ep_mp.view().spec_index(key).is_init() == pre.ep_mp.view().spec_index(key).is_init()
        &&& post.ep_mp.view().spec_index(key).addr() == pre.ep_mp.view().spec_index(key).addr()
        &&& (key != endpoint_ptr ==> post.ep_mp.spec_index(key) == pre.ep_mp.spec_index(key))
    })
    &&& endpoint_after.is_init() == endpoint_before.is_init()
    &&& endpoint_after.view_rodata() == endpoint_before.view_rodata()
    &&& endpoint_after.view_ghost() == endpoint_before.view_ghost()
    &&& endpoint_after.being_killed() == endpoint_before.being_killed()
    &&& endpoint_after.locking_thread() == endpoint_before.locking_thread()
    &&& endpoint_after.view() == (Endpoint { queue: endpoint_after.view().queue, queue_state: endpoint_after.view().queue_state, ..endpoint_before.view() })
    &&& endpoint_after.view().queue.wf()
    &&& endpoint_after.view().queue.container_depth == endpoint_before.view().queue.container_depth
    &&& endpoint_after.view().queue.lock_minor() == endpoint_before.view().queue.lock_minor()
    &&& endpoint_after.view().queue.view() == endpoint_before.view().queue.view().push(callee_ptr)
    &&& endpoint_after.view().queue.length as int == endpoint_before.view().queue.length as int + 1
    &&& endpoint_after.view().queue.map() == endpoint_before.view().queue.map().insert(callee_node, callee_ptr)
    &&& endpoint_after.view().queue.dom() == endpoint_before.view().queue.dom().insert(callee_node)
    &&& endpoint_after.view().queue_state == if endpoint_before.view().queue.length == 0 { EndpointState::RECEIVE } else { endpoint_before.view().queue_state }
    &&& needflush_after.view().index() == needflush_before.view().index()
    &&& needflush_after.is_init() == needflush_before.is_init()
    &&& needflush_after.view_rodata() == needflush_before.view_rodata()
    &&& needflush_after.view_ghost() == needflush_before.view_ghost()
    &&& needflush_after.being_killed() == needflush_before.being_killed()
    &&& needflush_after.locking_thread() == needflush_before.locking_thread()
    &&& needflush_after.view() == (PcidNeedFlush { needflush: false, ..needflush_before.view() })
    &&& (forall|c: CpuId, p: Pcid| #![trigger pre.pcid_needflush.spec_index(c, p)] #![trigger post.pcid_needflush.spec_index(c, p)]
        index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid) ==> post.pcid_needflush.spec_index(c, p) == pre.pcid_needflush.spec_index(c, p))
    &&& post.cpu_hw_cr3_pcid[cpu_id as int].owner_cpu() == pre.cpu_hw_cr3_pcid[cpu_id as int].owner_cpu()
    &&& post.cpu_hw_cr3_pcid[cpu_id as int].view() == (target.cr3, pcid)
    &&& (forall|c: CpuId| #![trigger pre.cpu_hw_cr3_pcid[c as int]] #![trigger post.cpu_hw_cr3_pcid[c as int]] index_valid(NUM_CPUS, c) && c != cpu_id ==> post.cpu_hw_cr3_pcid[c as int] == pre.cpu_hw_cr3_pcid[c as int])
    &&& post.cpu_tlb.view() == if flush { pre.cpu_tlb.view().insert((cpu_id, pcid), post.cpu_tlb.spec_index((cpu_id, pcid))) } else { pre.cpu_tlb.view() }
    &&& (forall|c: CpuId, p: Pcid| #![trigger pre.cpu_tlb.spec_index((c, p))] #![trigger post.cpu_tlb.spec_index((c, p))]
        index_valid(NUM_CPUS, c) && pcid_valid(p) && !(flush && c == cpu_id && p == pcid) ==> post.cpu_tlb.spec_index((c, p)) == pre.cpu_tlb.spec_index((c, p)))
    &&& flush ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(post.cpu_tlb.spec_index((cpu_id, pcid)), pagetable_c(pre.pt_mp, pre.pt_lower.view(), target.pagetable))
}
}
