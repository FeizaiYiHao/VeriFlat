use vstd::prelude::*;
use crate::*;
use super::syscall_new_endpoint_spec::*;
verus! {
/// Acquiring the caller's context locks and recording the progress is the enter step on `pre`/`post`.
pub proof fn new_endpoint_enter_step_from_u(
    pre: KernelU, locked: KernelU, post: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        edp_idx_valid(endpoint_index),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thread_ptr);
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& cpu.current_process == Some(process_ptr)
            &&& cpu.current_thread == Some(thread_ptr)
            &&& cpu.owning_container == container_ptr
            &&& pre.container_map.dom().contains(container_ptr)
            &&& pre.container_map.spec_index(container_ptr).lock_state is Unlocked
            &&& !pre.container_map.spec_index(container_ptr).killed
            &&& pre.process_map.dom().contains(process_ptr)
            &&& pre.process_map.spec_index(process_ptr).lock_state is Unlocked
            &&& !pre.process_map.spec_index(process_ptr).killed
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is Unlocked
            &&& thread.syscall_progress is None
            &&& !thread.killed
            &&& thread.state == (ThreadState::RUNNING { cpu_id })
            &&& thread.owning_proc == process_ptr
            &&& thread.owning_container == container_ptr
            &&& thread.endpoint_descriptors[endpoint_index as int] is None
            &&& thread.quota_4k >= 1
        },
        locked == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, ..pre.cpu_array[cpu_id as int] }),
            container_map: pre.container_map.insert(container_ptr, ContainerU { lock_state: LockStateU::WriteLocked, ..pre.container_map[container_ptr] }),
            process_map: pre.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::WriteLocked, ..pre.process_map[process_ptr] }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, ..pre.thread_map.spec_index(thread_ptr) }),
            ..pre
        }),
        post == (KernelU { thread_map: locked.thread_map.insert(thread_ptr, ThreadU { syscall_progress: Some(SyscallProgress::NewEndpoint { slot: endpoint_index }), ..locked.thread_map[thread_ptr] }), ..locked }),
    ensures
        new_endpoint_enter_step_pre(pre, cpu_id, endpoint_index),
        new_endpoint_enter_step(pre, post, cpu_id, endpoint_index),
{ reveal(new_endpoint_enter_step_pre); reveal(new_endpoint_enter_step); }

/// Publishing the new endpoint while releasing the caller's context locks is the finish step on `pre`/`post`.
pub proof fn new_endpoint_finish_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    endpoint_index: EndpointIdx, new_endpoint_ptr: RwLockEndpointPtr,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        edp_idx_valid(endpoint_index),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thread_ptr);
            &&& cpu.lock_state is WriteLocked
            &&& cpu.current_process == Some(process_ptr)
            &&& cpu.current_thread == Some(thread_ptr)
            &&& cpu.owning_container == container_ptr
            &&& pre.container_map.dom().contains(container_ptr)
            &&& pre.container_map.spec_index(container_ptr).lock_state is WriteLocked
            &&& pre.process_map.dom().contains(process_ptr)
            &&& pre.process_map.spec_index(process_ptr).lock_state is WriteLocked
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is WriteLocked
            &&& thread.syscall_progress == Some(SyscallProgress::NewEndpoint { slot: endpoint_index })
        },
        post.thread_map.spec_index(thread_ptr).endpoint_descriptors[endpoint_index as int] == Some(new_endpoint_ptr),
        kernel_u_new_endpoint_changed(KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..pre.cpu_array[cpu_id as int] }),
            container_map: pre.container_map.insert(container_ptr, ContainerU { lock_state: LockStateU::Unlocked, ..pre.container_map[container_ptr] }),
            process_map: pre.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::Unlocked, ..pre.process_map[process_ptr] }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..pre.thread_map.spec_index(thread_ptr) }),
            ..pre
        }, post, container_ptr, thread_ptr, endpoint_index, new_endpoint_ptr),
    ensures
        new_endpoint_finish_step_pre(pre, cpu_id),
        new_endpoint_finish_step(pre, post, cpu_id),
{ reveal(new_endpoint_finish_step_pre); reveal(new_endpoint_finish_step); }

/// The one step pushed since `before` is the partial trace after entering.
pub proof fn new_endpoint_trace_enter_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        new_endpoint_enter_step_pre(pre, cpu_id, endpoint_index),
        new_endpoint_enter_step(pre, post, cpu_id, endpoint_index),
    ensures
        new_endpoint_trace_after_enter(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, cpu_id, endpoint_index),
{ reveal(new_endpoint_trace_after_enter); }

/// The finish step pushed after the partial trace that starts at `start` completes the successful trace.
pub proof fn new_endpoint_trace_finish_step(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, finish_pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx,
)
    requires
        0 <= start <= before.len(),
        new_endpoint_trace_after_enter(before.subrange(start, before.len() as int), pre, cpu_id, endpoint_index),
        steps.view() == before.push(KernelStep { old_u: finish_pre, new_u: post }),
        new_endpoint_finish_step_pre(finish_pre, cpu_id),
        new_endpoint_finish_step(finish_pre, post, cpu_id),
    ensures
        new_endpoint_syscall_trace(steps.view().subrange(start, steps.view().len() as int), pre, post, cpu_id, endpoint_index, true),
{ reveal(new_endpoint_syscall_trace); reveal(new_endpoint_trace_after_enter); }

/// A rejected call records no step.
pub proof fn new_endpoint_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx)
    requires
        trace.len() == 0,
    ensures
        new_endpoint_syscall_trace(trace, pre, pre, cpu_id, endpoint_index, false),
{ reveal(new_endpoint_syscall_trace); }
} // verus!
