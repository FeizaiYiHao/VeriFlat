use vstd::prelude::*;
use crate::*;
use super::syscall_new_thread_spec::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::kernel_u_new_thread_changed;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;
verus! {
/// Acquiring the caller's context locks and recording the progress is the enter step on `pre`/`post`.
pub proof fn new_thread_enter_step_from_u(
    pre: KernelU, locked: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, endpoint_ptr: Option<RwLockEndpointPtr>, regs: Registers, endpoint_index: Option<EndpointIdx>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thread_ptr);
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& cpu.current_process == Some(process_ptr)
            &&& cpu.current_thread == Some(thread_ptr)
            &&& cpu.owning_container == container_ptr
            &&& pre.container_map.dom().contains(container_ptr)
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
            &&& thread.quota_4k >= 1
            &&& (endpoint_index is Some ==> edp_idx_valid(endpoint_index->Some_0) && endpoint_ptr is Some && thread.endpoint_descriptors[endpoint_index->Some_0 as int] == endpoint_ptr)
            &&& (endpoint_index is None ==> endpoint_ptr is None)
            &&& (endpoint_ptr is Some ==> pre.endpoint_map.dom().contains(endpoint_ptr->Some_0) && pre.endpoint_map.spec_index(endpoint_ptr->Some_0).lock_state is Unlocked)
        },
        locked == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, ..pre.cpu_array[cpu_id as int] }),
            process_map: pre.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::WriteLocked, ..pre.process_map[process_ptr] }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, ..pre.thread_map.spec_index(thread_ptr) }),
            endpoint_map: match endpoint_ptr {
                Some(e) => pre.endpoint_map.insert(e, EndpointU { lock_state: LockStateU::WriteLocked, ..pre.endpoint_map.spec_index(e) }),
                None => pre.endpoint_map,
            },
            ..pre
        }),
        post == (KernelU {
            thread_map: locked.thread_map.insert(thread_ptr, ThreadU { syscall_progress: Some(SyscallProgress::NewThread { regs, endpoint_index }), ..locked.thread_map[thread_ptr] }),
            ..locked
        }),
    ensures
        new_thread_enter_step_pre(pre, cpu_id, endpoint_index),
        new_thread_enter_step(pre, post, cpu_id, regs, endpoint_index),
{ reveal(new_thread_enter_step_pre); reveal(new_thread_enter_step); }

/// Publishing the new thread while releasing the caller's context locks is the finish step on `pre`/`post`.
pub proof fn new_thread_finish_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    new_thread_ptr: RwLockThreadPtr, endpoint_ptr: Option<RwLockEndpointPtr>, regs: Registers, endpoint_index: Option<EndpointIdx>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let thread = pre.thread_map.spec_index(thread_ptr);
            &&& cpu.lock_state is WriteLocked
            &&& cpu.current_process == Some(process_ptr)
            &&& cpu.current_thread == Some(thread_ptr)
            &&& cpu.owning_container == container_ptr
            &&& pre.process_map.dom().contains(process_ptr)
            &&& pre.process_map.spec_index(process_ptr).lock_state is WriteLocked
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& thread.lock_state is WriteLocked
            &&& thread.syscall_progress == Some(SyscallProgress::NewThread { regs, endpoint_index })
            &&& (endpoint_index is Some ==> edp_idx_valid(endpoint_index->Some_0) && endpoint_ptr is Some && thread.endpoint_descriptors[endpoint_index->Some_0 as int] == endpoint_ptr)
            &&& (endpoint_index is None ==> endpoint_ptr is None)
            &&& (endpoint_ptr is Some ==> pre.endpoint_map.dom().contains(endpoint_ptr->Some_0) && pre.endpoint_map.spec_index(endpoint_ptr->Some_0).lock_state is WriteLocked)
        },
        post.process_map.spec_index(process_ptr).owned_threads.last() == new_thread_ptr,
        kernel_u_new_thread_changed(KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..pre.cpu_array[cpu_id as int] }),
            process_map: pre.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::Unlocked, ..pre.process_map[process_ptr] }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..pre.thread_map.spec_index(thread_ptr) }),
            endpoint_map: match endpoint_ptr {
                Some(e) => pre.endpoint_map.insert(e, EndpointU { lock_state: LockStateU::Unlocked, ..pre.endpoint_map.spec_index(e) }),
                None => pre.endpoint_map,
            },
            ..pre
        }, post, process_ptr, thread_ptr, container_ptr, new_thread_ptr, regs, endpoint_ptr, None),
    ensures
        new_thread_finish_step_pre(pre, cpu_id),
        new_thread_finish_step(pre, post, cpu_id),
{ reveal(new_thread_finish_step_pre); reveal(new_thread_finish_step); }

/// The one step pushed since `before` is the partial trace after entering.
pub proof fn new_thread_trace_enter_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, regs: Registers, endpoint_index: Option<EndpointIdx>)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        new_thread_enter_step_pre(pre, cpu_id, endpoint_index),
        new_thread_enter_step(pre, post, cpu_id, regs, endpoint_index),
    ensures
        new_thread_trace_after_enter(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, cpu_id, regs, endpoint_index),
{ reveal(new_thread_trace_after_enter); }

/// The finish step pushed after the partial trace that starts at `start` completes the successful trace.
pub proof fn new_thread_trace_finish_step(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, finish_pre: KernelU, post: KernelU, cpu_id: CpuId, regs: Registers, endpoint_index: Option<EndpointIdx>,
)
    requires
        0 <= start <= before.len(),
        new_thread_trace_after_enter(before.subrange(start, before.len() as int), pre, cpu_id, regs, endpoint_index),
        steps.view() == before.push(KernelStep { old_u: finish_pre, new_u: post }),
        new_thread_finish_step_pre(finish_pre, cpu_id),
        new_thread_finish_step(finish_pre, post, cpu_id),
    ensures
        new_thread_syscall_trace(steps.view().subrange(start, steps.view().len() as int), pre, post, cpu_id, regs, endpoint_index, true),
{ reveal(new_thread_syscall_trace); reveal(new_thread_trace_after_enter); }

/// A rejected call records no step.
pub proof fn new_thread_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, regs: Registers, endpoint_index: Option<EndpointIdx>)
    requires
        trace.len() == 0,
    ensures
        new_thread_syscall_trace(trace, pre, pre, cpu_id, regs, endpoint_index, false),
{ reveal(new_thread_syscall_trace); }
} // verus!
