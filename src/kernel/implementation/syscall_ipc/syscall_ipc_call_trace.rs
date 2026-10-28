use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_spec::*;
use super::syscall_ipc_call_spec::*;

verus! {
/// The reply rejection on the user projection of `krnl` is `ret` when `ret` follows the same checks on `krnl`.
pub(super) proof fn ipc_reply_entry_result_from_k(krnl: &KernelK, cpu_id: CpuId, endpoint_index: EndpointIdx, ret: Option<RetValueType>)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        ({
            let cpu = krnl.cpu_arr.spec_index(cpu_id).value;
            let thread = krnl.thr_mp.spec_index(cpu.view().view().current_thread->Some_0);
            let endpoint_ptr = thread.view().endpoint_descriptors.view()[endpoint_index as int];
            let endpoint = krnl.ep_mp.spec_index(endpoint_ptr->Some_0).view();
            if !(cpu.view().view().state is Running) || cpu.being_killed() { ret == Some(RetValueType::CpuIdle) }
            else if !krnl.thr_mp.dom().contains(cpu.view().view().current_thread->Some_0) { false }
            else if thread.being_killed() { ret == Some(RetValueType::ErrorThreadKilled) }
            else if thread.view().caller is None { ret == Some(RetValueType::ErrorReplyOutOfPhase) }
            else if endpoint_ptr is None { ret == Some(RetValueType::ErrorInvalidEndpoint) }
            else if !krnl.ep_mp.dom().contains(endpoint_ptr->Some_0) { false }
            else if endpoint.queue.view().len() != 0 && endpoint.queue_state is SEND { ret == Some(RetValueType::ErrorIpcSameDirection) }
            else { ret == if krnl.thr_mp.spec_index(thread.view().caller->Some_0).being_killed() { Some(RetValueType::ErrorIpcPeerKilled) } else { None } }
        }),
    ensures ipc_reply_entry_result(kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index) == ret,
{
    reveal(ipc_reply_entry_result); kernel_cpu_projection_at(krnl, cpu_id);
    let thread_ptr = krnl.cpu_arr.spec_index(cpu_id).value.view().view().current_thread->Some_0;
    let endpoint_ptr = krnl.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int];
    if krnl.thr_mp.dom().contains(thread_ptr) {
        kernel_thread_projection_at(krnl, thread_ptr); thread_caller_callee_wf_at(krnl.thr_mp, thread_ptr);
        if krnl.thr_mp.spec_index(thread_ptr).view().caller is Some { kernel_thread_projection_at(krnl, krnl.thr_mp.spec_index(thread_ptr).view().caller->Some_0); }
    }
    if endpoint_ptr is Some && krnl.ep_mp.dom().contains(endpoint_ptr->Some_0) { kernel_endpoint_projection_at(krnl, endpoint_ptr->Some_0); }
}

/// The accepted call's result on the user projection of `krnl` is `ret` when `ret` is the call result of the queue head `caller_ptr` on `krnl`.
pub(super) proof fn ipc_accept_call_result_from_k(
    krnl: &KernelK, cpu_id: CpuId, endpoint_index: EndpointIdx, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, caller_ptr: RwLockThreadPtr, ret: RetValueType,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        krnl.thr_mp.dom().contains(callee_ptr),
        krnl.thr_mp.dom().contains(caller_ptr),
        krnl.ep_mp.dom().contains(endpoint_ptr),
        krnl.cpu_arr.spec_index(cpu_id).value.view().view().current_thread == Some(callee_ptr),
        krnl.thr_mp.spec_index(callee_ptr).view().endpoint_descriptors.view()[endpoint_index as int] == Some(endpoint_ptr),
        krnl.ep_mp.spec_index(endpoint_ptr).view().queue.view()[0] == caller_ptr,
        ret == ipc_call_result(krnl.thr_mp.spec_index(caller_ptr).view().ipc_payload),
    ensures ipc_accept_call_result(kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index) == ret,
{ kernel_cpu_projection_at(krnl, cpu_id); kernel_thread_projection_at(krnl, callee_ptr); kernel_thread_projection_at(krnl, caller_ptr); kernel_endpoint_queue_projection_at(krnl, endpoint_ptr); }

/// The unlocked cpu, running callee, endpoint, and dangling caller on `krnl` give the pre of a reply to the dangling caller.
pub(super) proof fn ipc_reply_dangling_caller_step_pre_from_k(
    krnl: &KernelK, cpu_id: CpuId, endpoint_index: EndpointIdx, process_ptr: RwLockProcessPtr, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    caller_ptr: RwLockThreadPtr,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        edp_idx_valid(endpoint_index),
        krnl.prc_mp.dom().contains(process_ptr),
        krnl.thr_mp.dom().contains(callee_ptr),
        krnl.thr_mp.dom().contains(caller_ptr),
        krnl.ep_mp.dom().contains(endpoint_ptr),
        caller_ptr != callee_ptr,
        krnl.cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        krnl.thr_mp.spec_index(callee_ptr).locking_thread() is None,
        krnl.thr_mp.spec_index(caller_ptr).locking_thread() is None,
        krnl.ep_mp.spec_index(endpoint_ptr).locking_thread() is None,
        ({
            let cpu = krnl.cpu_arr.spec_index(cpu_id).value.view().view();
            &&& cpu.state is Running
            &&& cpu.current_process == Some(process_ptr)
            &&& cpu.current_thread == Some(callee_ptr)
        }),
        ({
            let callee = krnl.thr_mp.spec_index(callee_ptr);
            &&& !callee.being_killed()
            &&& callee.view().state == (ThreadState::RUNNING { cpu_id })
            &&& callee.view().owning_proc == process_ptr
            &&& krnl.ctn_mp.dom().contains(callee.view().owning_container)
            &&& callee.view().syscall_progress.view() is None
            &&& callee.view().caller == Some(caller_ptr)
            &&& callee.view().endpoint_descriptors.view()[endpoint_index as int] == Some(endpoint_ptr)
        }),
        !krnl.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(callee_ptr),
        krnl.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() == 0 || krnl.ep_mp.spec_index(endpoint_ptr).view().queue_state is RECEIVE,
        !krnl.thr_mp.spec_index(caller_ptr).being_killed(),
        krnl.thr_mp.spec_index(caller_ptr).view().state is DANGLING,
        krnl.thr_mp.spec_index(caller_ptr).view().callee == Some(callee_ptr),
    ensures
        ({
            let pre = kernel_k_to_kernel_u(*krnl);
            &&& ipc_reply_dangling_caller_step_pre(pre, cpu_id, endpoint_index)
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(callee_ptr)
            &&& pre.thread_map[callee_ptr].caller == Some(caller_ptr)
            &&& pre.thread_map[caller_ptr].state is DANGLING
            &&& pre.endpoint_map.dom().contains(endpoint_ptr)
            &&& pre.endpoint_map[endpoint_ptr].lock_state is Unlocked
        }),
{ reveal(ipc_reply_dangling_caller_step_pre); reveal(ipc_step_pre); kernel_cpu_thread_projection_at(krnl, cpu_id, process_ptr, callee_ptr, Some(endpoint_ptr)); kernel_thread_projection_at(krnl, caller_ptr); }

/// Locking the cpu, the callee, the dangling caller, and the endpoint, then taking the dangling caller over and releasing the endpoint, is the
/// taken-over step of a reply to the dangling caller.
pub(super) proof fn ipc_reply_dangling_caller_taken_over_step_from_u(
    pre_u: KernelU, locked_u: KernelU, post_u: KernelU, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, caller_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
)
    requires
        locked_u == (KernelU {
            cpu_array: pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..pre_u.cpu_array[cpu_id as int] }),
            thread_map: pre_u.thread_map.insert(callee_ptr, ThreadU { lock_state: LockStateU::WriteLocked, ..pre_u.thread_map[callee_ptr] })
                .insert(caller_ptr, ThreadU { lock_state: LockStateU::WriteLocked, ..pre_u.thread_map[caller_ptr] }),
            endpoint_map: pre_u.endpoint_map.insert(endpoint_ptr, EndpointU { lock_state: LockStateU::WriteLocked, ..pre_u.endpoint_map[endpoint_ptr] }),
            ..pre_u
        }),
        post_u == (KernelU {
            thread_map: locked_u.thread_map.insert(callee_ptr, ThreadU { caller: None, ..locked_u.thread_map[callee_ptr] })
                .insert(caller_ptr, ThreadU { state: ThreadState::KILLED, callee: None, lock_state: LockStateU::WriteLocked, ..locked_u.thread_map[caller_ptr] }),
            endpoint_map: locked_u.endpoint_map.insert(endpoint_ptr, EndpointU { lock_state: LockStateU::Unlocked, ..locked_u.endpoint_map[endpoint_ptr] }),
            ..locked_u
        }),
        callee_ptr != caller_ptr,
        pre_u.cpu_array[cpu_id as int].current_thread == Some(callee_ptr),
        pre_u.thread_map[callee_ptr].caller == Some(caller_ptr),
        pre_u.thread_map[caller_ptr].state is DANGLING,
        pre_u.endpoint_map.dom().contains(endpoint_ptr),
        pre_u.endpoint_map[endpoint_ptr].lock_state is Unlocked,
    ensures
        pre_u != post_u,
        ipc_reply_dangling_caller_taken_over_step(pre_u, post_u, cpu_id),
{
    assert(post_u.thread_map =~= pre_u.thread_map.insert(callee_ptr, ThreadU { lock_state: LockStateU::WriteLocked, caller: None, ..pre_u.thread_map[callee_ptr] })
        .insert(caller_ptr, ThreadU { state: ThreadState::KILLED, callee: None, lock_state: LockStateU::WriteLocked, ..pre_u.thread_map[caller_ptr] }));
    assert(post_u.endpoint_map =~= pre_u.endpoint_map);
    assert(post_u.thread_map[caller_ptr].state is KILLED);
}

/// The cpu and its running thread `thread_ptr` write-held on `krnl` give the held pre of a reply to a dangling caller.
pub(super) proof fn ipc_reply_dangling_caller_held_step_pre_from_k(krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        krnl.prc_mp.dom().contains(process_ptr),
        krnl.cpu_arr.spec_index(cpu_id).value.view().view().state is Running,
        krnl.cpu_arr.spec_index(cpu_id).value.view().view().current_thread == Some(thread_ptr),
    ensures
        ipc_reply_dangling_caller_held_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
{ kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, None); kernel_cpu_projection_at(krnl, cpu_id); }

/// The ensures of a reply to a dangling caller recorded since `before` are the ErrorIpcCallerKilled reply_and_receive trace.
pub(super) proof fn ipc_reply_and_receive_trace_from_dangling(
    steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, payload: IPCPayLoad, regs: Registers,
    flushed_pcid: Option<Pcid>,
)
    requires
        ({
            let n = before.len() as int;
            let trace = steps.view();
            let last = trace.len() - 1;
            &&& trace.len() >= n + 3
            &&& trace[n].old_u == pre
            &&& ipc_reply_dangling_caller_step_pre(trace[n].old_u, cpu_id, endpoint_index)
            &&& ipc_reply_dangling_caller_taken_over_step(trace[n].old_u, trace[n].new_u, cpu_id)
            &&& forall|j: int| #![trigger trace[j]] n < j < last ==> ipc_reply_dangling_caller_held_step_pre(trace[j].old_u, cpu_id) && kernel_u_killed_thread_reclaim_step(trace[j].old_u, trace[j].new_u, cpu_id)
            &&& ipc_reply_dangling_caller_held_step_pre(trace[last].old_u, cpu_id)
            &&& ipc_reply_dangling_caller_released_step(trace[last].old_u, trace[last].new_u, cpu_id)
            &&& trace[last].new_u == post
        }),
    ensures
        ipc_reply_and_receive_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index, payload, regs, flushed_pcid,
            RetValueType::ErrorIpcCallerKilled),
{ reveal(ipc_reply_and_receive_syscall_trace); }

/// The call-handoff wrapper's user-view facts are exactly the call handoff step on `pre`/`post`.
pub(super) proof fn ipc_call_handoff_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, caller_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, callee_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>)
    requires
        kernel_u_ipc_call_handoff_changed(pre, post, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let caller = pre.thread_map.spec_index(caller_ptr);
            let callee = pre.thread_map.spec_index(callee_ptr);
            let endpoint = pre.endpoint_map.spec_index(endpoint_ptr);
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& cpu.current_thread == Some(caller_ptr)
            &&& cpu.current_process == Some(caller.owning_proc)
            &&& pre.process_map.dom().contains(caller.owning_proc)
            &&& pre.container_map.dom().contains(caller.owning_container)
            &&& pre.thread_map.dom().contains(caller_ptr)
            &&& caller.lock_state is Unlocked
            &&& caller.syscall_progress is None
            &&& !caller.killed
            &&& caller.state == (ThreadState::RUNNING { cpu_id })
            &&& caller.callee is None
            &&& edp_idx_valid(endpoint_index)
            &&& caller.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
            &&& pre.endpoint_map.dom().contains(endpoint_ptr)
            &&& endpoint.lock_state is Unlocked
            &&& !endpoint.queue.contains(caller_ptr)
            &&& endpoint.queue.len() > 0
            &&& endpoint.queue[0] == callee_ptr
            &&& endpoint.queue_state is RECEIVE
            &&& callee_ptr != caller_ptr
            &&& pre.thread_map.dom().contains(callee_ptr)
            &&& callee.lock_state is Unlocked
            &&& !callee.killed
            &&& callee.state is RECEIVING_CALL
            &&& callee.caller is None
            &&& callee.callee is None
            &&& callee.blocking_endpoint_ptr == Some(endpoint_ptr)
            &&& callee.owning_container == caller.owning_container
            &&& pre.process_map.dom().contains(callee.owning_proc)
        },
    ensures
        ipc_call_handoff_step_pre(pre, cpu_id, endpoint_index),
        ipc_call_handoff_step(pre, post, cpu_id, endpoint_index, regs, flushed_pcid),
{ reveal(ipc_call_handoff_step_pre); reveal(ipc_step_pre); }

/// The accept-call wrapper's user-view facts are exactly the accept step on `pre`/`post`.
pub(super) proof fn ipc_accept_call_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, caller_ptr: RwLockThreadPtr)
    requires
        kernel_u_ipc_accept_call_changed(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let callee = pre.thread_map.spec_index(callee_ptr);
            let caller = pre.thread_map.spec_index(caller_ptr);
            let endpoint = pre.endpoint_map.spec_index(endpoint_ptr);
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& cpu.current_thread == Some(callee_ptr)
            &&& cpu.current_process == Some(callee.owning_proc)
            &&& pre.process_map.dom().contains(callee.owning_proc)
            &&& pre.container_map.dom().contains(callee.owning_container)
            &&& pre.thread_map.dom().contains(callee_ptr)
            &&& callee.lock_state is Unlocked
            &&& callee.syscall_progress is None
            &&& !callee.killed
            &&& callee.state == (ThreadState::RUNNING { cpu_id })
            &&& callee.caller is None
            &&& callee.callee is None
            &&& edp_idx_valid(endpoint_index)
            &&& callee.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
            &&& pre.endpoint_map.dom().contains(endpoint_ptr)
            &&& endpoint.lock_state is Unlocked
            &&& !endpoint.queue.contains(callee_ptr)
            &&& endpoint.queue.len() > 0
            &&& endpoint.queue[0] == caller_ptr
            &&& endpoint.queue_state is SEND
            &&& caller_ptr != callee_ptr
            &&& pre.thread_map.dom().contains(caller_ptr)
            &&& caller.lock_state is Unlocked
            &&& !caller.killed
            &&& caller.state is CALLING
            &&& caller.callee is None
            &&& caller.blocking_endpoint_ptr == Some(endpoint_ptr)
            &&& caller.owning_container == callee.owning_container
        },
    ensures
        ipc_accept_call_step_pre(pre, cpu_id, endpoint_index),
        ipc_accept_call_step(pre, post, cpu_id, endpoint_index),
{ reveal(ipc_accept_call_step_pre); reveal(ipc_step_pre); }

/// The reply-handoff wrapper's user-view facts are exactly the reply handoff step on `pre`/`post`.
pub(super) proof fn ipc_reply_handoff_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, caller_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>)
    requires
        kernel_u_ipc_reply_handoff_changed(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let callee = pre.thread_map.spec_index(callee_ptr);
            let caller = pre.thread_map.spec_index(caller_ptr);
            let endpoint = pre.endpoint_map.spec_index(endpoint_ptr);
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& cpu.current_thread == Some(callee_ptr)
            &&& cpu.current_process == Some(callee.owning_proc)
            &&& pre.process_map.dom().contains(callee.owning_proc)
            &&& pre.container_map.dom().contains(callee.owning_container)
            &&& pre.thread_map.dom().contains(callee_ptr)
            &&& callee.lock_state is Unlocked
            &&& callee.syscall_progress is None
            &&& !callee.killed
            &&& callee.state == (ThreadState::RUNNING { cpu_id })
            &&& callee.caller == Some(caller_ptr)
            &&& callee.callee is None
            &&& edp_idx_valid(endpoint_index)
            &&& callee.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
            &&& pre.endpoint_map.dom().contains(endpoint_ptr)
            &&& endpoint.lock_state is Unlocked
            &&& !endpoint.queue.contains(callee_ptr)
            &&& endpoint.queue.len() == 0 || endpoint.queue_state is RECEIVE
            &&& caller_ptr != callee_ptr
            &&& pre.thread_map.dom().contains(caller_ptr)
            &&& caller.lock_state is Unlocked
            &&& !caller.killed
            &&& caller.state is WAITING_REPLY
            &&& caller.callee == Some(callee_ptr)
            &&& caller.owning_container == callee.owning_container
            &&& pre.process_map.dom().contains(caller.owning_proc)
        },
    ensures
        ipc_reply_handoff_step_pre(pre, cpu_id, endpoint_index),
        ipc_reply_handoff_step(pre, post, cpu_id, endpoint_index, regs, flushed_pcid),
{ reveal(ipc_reply_handoff_step_pre); reveal(ipc_step_pre); }

/// A rejected ordinary call records no step and leaves the user view unchanged.
pub(super) proof fn ipc_rejection_trace_stutters(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool, ret: RetValueType)
    requires
        ipc_ordinary_syscall_trace(trace, pre, post, cpu_id, endpoint_index, waiting_state, payload, regs, flushed_default_pcid, ret),
        !(ret is CpuIdle) || ipc_entry_result(pre, cpu_id, endpoint_index, waiting_state, false) == Some(RetValueType::CpuIdle),
        !ipc_rendezvous_ret(ret),
    ensures
        trace.len() == 0,
        post == pre,
{ reveal(ipc_ordinary_syscall_trace); reveal(ipc_entry_result); }

/// The one block step pushed since `before` is the blocking call trace.
pub(super) proof fn ipc_call_trace_block_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool, flushed_pcid: Option<Pcid>)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        ipc_ordinary_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index, ThreadState::CALLING, payload, regs,
            flushed_default_pcid, RetValueType::CpuIdle),
    ensures
        ipc_call_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index, payload, regs, flushed_default_pcid, flushed_pcid, RetValueType::CpuIdle),
{ reveal(ipc_call_syscall_trace); reveal(ipc_ordinary_syscall_trace); }

/// The one block step pushed since `before` is the blocking receive-call trace.
pub(super) proof fn ipc_receive_call_trace_block_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, regs: Registers, flushed_default_pcid: bool)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        ipc_ordinary_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index, ThreadState::RECEIVING_CALL,
            IPCPayLoad::Empty, regs, flushed_default_pcid, RetValueType::CpuIdle),
    ensures
        ipc_receive_call_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index, regs, flushed_default_pcid, RetValueType::CpuIdle),
{ reveal(ipc_receive_call_syscall_trace); reveal(ipc_ordinary_syscall_trace); }

/// The one rendezvous error step pushed since `before` is the rejected call trace.
pub(super) proof fn ipc_call_trace_error_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool, flushed_pcid: Option<Pcid>, ret: RetValueType)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        ret is ErrorIpcTypeMismatch || ret is ErrorCallAcrossContainers,
        ret == ipc_rendezvous_result(pre, cpu_id, endpoint_index, ThreadState::CALLING, payload),
        ipc_rendezvous_step_pre(pre, cpu_id, endpoint_index, ThreadState::CALLING, payload),
        ipc_rendezvous_step(pre, post, cpu_id, endpoint_index, ThreadState::CALLING, payload),
    ensures
        ipc_call_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index, payload, regs, flushed_default_pcid, flushed_pcid, ret),
{ reveal(ipc_call_syscall_trace); }

/// The one rendezvous error step pushed since `before` is the rejected receive-call trace.
pub(super) proof fn ipc_receive_call_trace_error_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, regs: Registers, flushed_default_pcid: bool, ret: RetValueType)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        ret is ErrorIpcTypeMismatch || ret is ErrorCallAcrossContainers,
        ret == ipc_rendezvous_result(pre, cpu_id, endpoint_index, ThreadState::RECEIVING_CALL, IPCPayLoad::Empty),
        ipc_rendezvous_step_pre(pre, cpu_id, endpoint_index, ThreadState::RECEIVING_CALL, IPCPayLoad::Empty),
        ipc_rendezvous_step(pre, post, cpu_id, endpoint_index, ThreadState::RECEIVING_CALL, IPCPayLoad::Empty),
    ensures
        ipc_receive_call_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index, regs, flushed_default_pcid, ret),
{ reveal(ipc_receive_call_syscall_trace); }

/// The one handoff step pushed since `before` is the successful call trace.
pub(super) proof fn ipc_call_trace_handoff_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool, flushed_pcid: Option<Pcid>, ret: RetValueType)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        ret == ipc_call_result(payload),
        ipc_call_handoff_step_pre(pre, cpu_id, endpoint_index),
        ipc_call_handoff_step(pre, post, cpu_id, endpoint_index, regs, flushed_pcid),
    ensures
        ipc_call_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index, payload, regs, flushed_default_pcid, flushed_pcid, ret),
{ reveal(ipc_call_syscall_trace); }

/// The one acceptance step pushed since `before` is the successful receive-call trace.
pub(super) proof fn ipc_receive_call_trace_accept_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, regs: Registers, flushed_default_pcid: bool, ret: RetValueType)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        ret == ipc_accept_call_result(pre, cpu_id, endpoint_index),
        ipc_accept_call_step_pre(pre, cpu_id, endpoint_index),
        ipc_accept_call_step(pre, post, cpu_id, endpoint_index),
    ensures
        ipc_receive_call_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index, regs, flushed_default_pcid, ret),
{ reveal(ipc_receive_call_syscall_trace); }

/// The one reply handoff step pushed since `before` is the successful reply_and_receive trace.
pub(super) proof fn ipc_reply_and_receive_trace_handoff_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, payload: IPCPayLoad, regs: Registers, flushed_pcid: Option<Pcid>, ret: RetValueType)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        ret == ipc_call_result(payload),
        ipc_reply_handoff_step_pre(pre, cpu_id, endpoint_index),
        ipc_reply_handoff_step(pre, post, cpu_id, endpoint_index, regs, flushed_pcid),
    ensures
        ipc_reply_and_receive_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index, payload, regs, flushed_pcid, ret),
{ reveal(ipc_reply_and_receive_syscall_trace); }

/// A call rejected before any visible change records no step.
pub(super) proof fn ipc_call_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool, flushed_pcid: Option<Pcid>, ret: RetValueType)
    requires
        trace.len() == 0,
        !(ret is CpuIdle) || ipc_entry_result(pre, cpu_id, endpoint_index, ThreadState::CALLING, false) == Some(RetValueType::CpuIdle),
        !(ret is Success) && !(ret is SuccessUsize) && !(ret is ErrorIpcTypeMismatch) && !(ret is ErrorCallAcrossContainers),
    ensures
        ipc_call_syscall_trace(trace, pre, pre, cpu_id, endpoint_index, payload, regs, flushed_default_pcid, flushed_pcid, ret),
{ reveal(ipc_call_syscall_trace); reveal(ipc_entry_result); }

/// A receive_call rejected before any visible change records no step.
pub(super) proof fn ipc_receive_call_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, regs: Registers, flushed_default_pcid: bool, ret: RetValueType)
    requires
        trace.len() == 0,
        !(ret is CpuIdle) || ipc_entry_result(pre, cpu_id, endpoint_index, ThreadState::RECEIVING_CALL, false) == Some(RetValueType::CpuIdle),
        !(ret is Success) && !(ret is SuccessUsize) && !(ret is ErrorIpcTypeMismatch) && !(ret is ErrorCallAcrossContainers),
    ensures
        ipc_receive_call_syscall_trace(trace, pre, pre, cpu_id, endpoint_index, regs, flushed_default_pcid, ret),
{ reveal(ipc_receive_call_syscall_trace); reveal(ipc_entry_result); }

/// A reply_and_receive rejected before any visible change records no step.
pub(super) proof fn ipc_reply_and_receive_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, payload: IPCPayLoad, regs: Registers, flushed_pcid: Option<Pcid>, ret: RetValueType)
    requires
        trace.len() == 0,
        !(ret is Success) && !(ret is SuccessUsize) && !(ret is ErrorIpcCallerKilled),
    ensures
        ipc_reply_and_receive_syscall_trace(trace, pre, pre, cpu_id, endpoint_index, payload, regs, flushed_pcid, ret),
{ reveal(ipc_reply_and_receive_syscall_trace); }
}
