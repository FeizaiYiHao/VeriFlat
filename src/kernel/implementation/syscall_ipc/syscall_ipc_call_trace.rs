use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_spec::*;
use super::syscall_ipc_call_spec::*;

verus! {
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
        !(ret is CpuIdle) || !(pre.cpu_array[cpu_id as int].state is Running),
        !ipc_rendezvous_ret(ret),
    ensures
        trace.len() == 0,
        post == pre,
{ reveal(ipc_ordinary_syscall_trace); }

/// The one block step pushed since `before` is the blocking call trace.
pub(super) proof fn ipc_call_trace_block_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool, flushed_pcid: Option<Pcid>)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        ipc_block_step_pre(pre, cpu_id, endpoint_index, ThreadState::CALLING),
        ipc_block_step(pre, post, cpu_id, endpoint_index, ThreadState::CALLING, payload, regs, flushed_default_pcid),
    ensures
        ipc_call_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index, payload, regs, flushed_default_pcid, flushed_pcid, RetValueType::CpuIdle),
{ reveal(ipc_call_syscall_trace); reveal(ipc_block_step_pre); reveal(ipc_step_pre); }

/// The one block step pushed since `before` is the blocking receive-call trace.
pub(super) proof fn ipc_receive_call_trace_block_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, regs: Registers, flushed_default_pcid: bool)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        ipc_block_step_pre(pre, cpu_id, endpoint_index, ThreadState::RECEIVING_CALL),
        ipc_block_step(pre, post, cpu_id, endpoint_index, ThreadState::RECEIVING_CALL, IPCPayLoad::Empty, regs, flushed_default_pcid),
    ensures
        ipc_receive_call_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, endpoint_index, regs, flushed_default_pcid, RetValueType::CpuIdle),
{ reveal(ipc_receive_call_syscall_trace); reveal(ipc_block_step_pre); reveal(ipc_step_pre); }

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
        !(ret is CpuIdle) || !(pre.cpu_array[cpu_id as int].state is Running),
        !(ret is Success) && !(ret is SuccessUsize) && !(ret is ErrorIpcTypeMismatch) && !(ret is ErrorCallAcrossContainers),
    ensures
        ipc_call_syscall_trace(trace, pre, pre, cpu_id, endpoint_index, payload, regs, flushed_default_pcid, flushed_pcid, ret),
{ reveal(ipc_call_syscall_trace); }

/// A receive_call rejected before any visible change records no step.
pub(super) proof fn ipc_receive_call_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, regs: Registers, flushed_default_pcid: bool, ret: RetValueType)
    requires
        trace.len() == 0,
        !(ret is CpuIdle) || !(pre.cpu_array[cpu_id as int].state is Running),
        !(ret is Success) && !(ret is SuccessUsize) && !(ret is ErrorIpcTypeMismatch) && !(ret is ErrorCallAcrossContainers),
    ensures
        ipc_receive_call_syscall_trace(trace, pre, pre, cpu_id, endpoint_index, regs, flushed_default_pcid, ret),
{ reveal(ipc_receive_call_syscall_trace); }

/// A reply_and_receive rejected before any visible change records no step.
pub(super) proof fn ipc_reply_and_receive_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, payload: IPCPayLoad, regs: Registers, flushed_pcid: Option<Pcid>, ret: RetValueType)
    requires
        trace.len() == 0,
        !(ret is Success) && !(ret is SuccessUsize) && !(ret is ErrorIpcCallerKilled),
    ensures
        ipc_reply_and_receive_syscall_trace(trace, pre, pre, cpu_id, endpoint_index, payload, regs, flushed_pcid, ret),
{ reveal(ipc_reply_and_receive_syscall_trace); }
}
