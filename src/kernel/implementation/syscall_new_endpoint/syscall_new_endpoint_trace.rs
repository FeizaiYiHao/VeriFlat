use vstd::prelude::*;
use crate::*;
use super::syscall_new_endpoint_spec::*;
verus! {
/// Acquiring the caller's context locks, the container under the owner `locked_k` records for it, and recording the
/// progress is the enter step on `pre`/`post`.
pub proof fn new_endpoint_enter_step_from_u(
    pre: KernelU, locked: KernelU, post: KernelU, locked_k: &KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        edp_idx_valid(endpoint_index),
        locked == kernel_k_to_kernel_u(*locked_k),
        locked_k.prc_mp.dom().contains(process_ptr),
        locked_k.ctn_mp.spec_index(container_ptr).lock_process_owner_u() == Some(LockOwnerId::Some(locked_k.prc_mp.spec_index(process_ptr).view_rodata().view().depth)),
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
            &&& !pre.container_map.spec_index(container_ptr).zombie
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
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..pre.cpu_array[cpu_id as int] }),
            container_map: pre.container_map.insert(container_ptr, ContainerU {
                lock_state: LockStateU::WriteLocked, lock_process_owner: locked_k.ctn_mp.spec_index(container_ptr).lock_process_owner_u(), ..pre.container_map[container_ptr]
            }),
            process_map: pre.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::WriteLocked, ..pre.process_map[process_ptr] }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, ..pre.thread_map.spec_index(thread_ptr) }),
            ..pre
        }),
        post == (KernelU { thread_map: locked.thread_map.insert(thread_ptr, ThreadU { syscall_progress: Some(SyscallProgress::NewEndpoint { slot: endpoint_index }), ..locked.thread_map[thread_ptr] }), ..locked }),
    ensures
        new_endpoint_enter_step_pre(pre, cpu_id, endpoint_index),
        new_endpoint_enter_step(pre, post, cpu_id, endpoint_index),
{ kernel_process_projection_at(locked_k, process_ptr); reveal(new_endpoint_enter_step_pre); reveal(new_endpoint_enter_step); }

/// Each return path's entry-state K facts give its value as the user-view result.
pub(super) proof fn new_endpoint_result_from_k(krnl: &KernelK, cpu_id: CpuId, endpoint_index: EndpointIdx, ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let c = cpu.view().view();
            let container = krnl.ctn_mp.spec_index(c.owning_container);
            let process = krnl.prc_mp.spec_index(c.current_process->Some_0);
            let thread = krnl.thr_mp.spec_index(c.current_thread->Some_0);
            let owner = container.lock_process_owner_u();
            &&& c.state is Running && !cpu.being_killed() ==> {
                &&& krnl.ctn_mp.dom().contains(c.owning_container)
                &&& krnl.prc_mp.dom().contains(c.current_process->Some_0)
                &&& krnl.thr_mp.dom().contains(c.current_thread->Some_0)
            }
            &&& ret == if !(c.state is Running) || cpu.being_killed() { RetValueType::CpuIdle }
                else if container.being_killed() { RetValueType::ErrorContainerKilled }
                else if owner is Some && owner->Some_0 < LockOwnerId::Some(process.view_rodata().view().depth) { RetValueType::ErrorContainerLockOrderConflict }
                else if container.view().zombie { RetValueType::ErrorContainerZombie }
                else if process.being_killed() { RetValueType::ErrorProcessKilled }
                else if thread.being_killed() { RetValueType::ErrorThreadKilled }
                else if thread.view().endpoint_descriptors.spec_index(endpoint_index) is Some { RetValueType::ErrorIpcEndpointTargetInUse }
                else if thread.view().quota_4k == 0 { RetValueType::ErrorNoQuota }
                else { RetValueType::Success }
        },
    ensures
        new_endpoint_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
    kernel_cpu_projection_at(krnl, cpu_id);
    if krnl.ctn_mp.dom().contains(c.owning_container) { kernel_container_projection_at(krnl, c.owning_container); }
    if krnl.prc_mp.dom().contains(c.current_process->Some_0) { kernel_process_projection_at(krnl, c.current_process->Some_0); }
    if krnl.prc_mp.dom().contains(c.current_process->Some_0) && krnl.thr_mp.dom().contains(c.current_thread->Some_0) {
        kernel_cpu_thread_projection_at(krnl, cpu_id, c.current_process->Some_0, c.current_thread->Some_0, None);
    }
}

/// The caller's write-held context and recorded progress at `krnl` give the finish step's precondition on its user view,
/// together with the objects that step binds.
pub(super) proof fn new_endpoint_finish_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    endpoint_index: EndpointIdx,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        edp_idx_valid(endpoint_index),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        krnl.prc_mp.dom().contains(process_ptr),
        krnl.thr_mp.dom().contains(thread_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::NewEndpoint { slot: endpoint_index }),
    ensures
        new_endpoint_finish_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            &&& u.cpu_array[cpu_id as int].current_process == Some(process_ptr)
            &&& u.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& u.cpu_array[cpu_id as int].owning_container == container_ptr
            &&& u.cpu_array[cpu_id as int].state == krnl.cpu_arr.spec_index(cpu_id).view().view().view().state
            &&& u.thread_map.spec_index(thread_ptr).syscall_progress == Some(SyscallProgress::NewEndpoint { slot: endpoint_index })
        }),
{ kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, None); kernel_cpu_thread_projection_at(krnl, cpu_id, process_ptr, thread_ptr, None); reveal(new_endpoint_finish_step_pre); }

/// Publishing the new endpoint while releasing the caller's context locks is the finish step on `pre`/`post`.
pub(super) proof fn new_endpoint_finish_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    endpoint_index: EndpointIdx, new_endpoint_ptr: RwLockEndpointPtr,
)
    requires
        pre.cpu_array[cpu_id as int].current_process == Some(process_ptr),
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.cpu_array[cpu_id as int].owning_container == container_ptr,
        pre.thread_map.spec_index(thread_ptr).syscall_progress == Some(SyscallProgress::NewEndpoint { slot: endpoint_index }),
        post.thread_map.spec_index(thread_ptr).endpoint_descriptors[endpoint_index as int] == Some(new_endpoint_ptr),
        kernel_u_new_endpoint_changed(KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: cpu_op_after_step(pre.cpu_array[cpu_id as int].state), ..pre.cpu_array[cpu_id as int] }),
            container_map: pre.container_map.insert(container_ptr, ContainerU { lock_state: LockStateU::Unlocked, lock_process_owner: None, ..pre.container_map[container_ptr] }),
            process_map: pre.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::Unlocked, ..pre.process_map[process_ptr] }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..pre.thread_map.spec_index(thread_ptr) }),
            ..pre
        }, post, container_ptr, thread_ptr, endpoint_index, new_endpoint_ptr),
    ensures
        new_endpoint_finish_step(pre, post, cpu_id),
{ reveal(new_endpoint_finish_step); }

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
