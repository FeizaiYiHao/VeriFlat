use vstd::prelude::*;
use crate::*;
use super::syscall_cpu_hotplug_spec::*;
verus! {
/// The request wrapper's user-view facts are exactly the request step on `pre`/`post`.
pub(super) proof fn cpu_offline_request_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, target: CpuId)
    requires
        kernel_u_cpu_offline_request_changed(pre, post, cpu_id, container_ptr, target),
        pre.cpu_array[cpu_id as int].lock_state is Unlocked,
        pre.container_map[container_ptr].cpu_set_lock is Unlocked,
    ensures
        cpu_offline_request_step_pre(pre, cpu_id, target),
        cpu_offline_request_step(pre, post, cpu_id, target),
{ reveal(cpu_offline_request_step_pre); reveal(kernel_u_cpu_offline_request_changed); }

/// The one step pushed since `before` is the complete successful request trace.
pub(super) proof fn cpu_offline_request_trace_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, target: CpuId)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        !cpu_offline_request_pending(pre, cpu_id, target),
        cpu_offline_request_step_pre(pre, cpu_id, target),
        cpu_offline_request_step(pre, post, cpu_id, target),
    ensures
        cpu_offline_request_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, target, RetValueType::Success),
{ reveal(cpu_offline_request_syscall_trace); }

/// A rejected or already pending request records no step.
pub(super) proof fn cpu_offline_request_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, target: CpuId, ret: RetValueType)
    requires
        trace.len() == 0,
        !(ret is Success && !cpu_offline_request_pending(pre, cpu_id, target)),
    ensures
        cpu_offline_request_syscall_trace(trace, pre, pre, cpu_id, target, ret),
{ reveal(cpu_offline_request_syscall_trace); }

/// The online wrapper's user-view facts are exactly the online step on `pre`/`post`.
pub(super) proof fn cpu_online_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, target: CpuId)
    requires
        kernel_u_cpu_online_changed(pre, post, cpu_id, container_ptr, target),
        pre.cpu_array[cpu_id as int].lock_state is Unlocked,
        pre.cpu_array[target as int].lock_state is Unlocked,
        pre.container_map[container_ptr].cpu_set_lock is Unlocked,
    ensures
        cpu_online_step_pre(pre, cpu_id, target),
        cpu_online_step(pre, post, cpu_id, target),
{ reveal(cpu_online_step_pre); reveal(kernel_u_cpu_online_changed); }

/// The one step pushed since `before` is the complete successful online trace.
pub(super) proof fn cpu_online_trace_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, target: CpuId)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        cpu_online_step_pre(pre, cpu_id, target),
        cpu_online_step(pre, post, cpu_id, target),
    ensures
        cpu_online_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, target, RetValueType::Success),
{ reveal(cpu_online_syscall_trace); }

/// A rejected online call records no step.
pub(super) proof fn cpu_online_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, target: CpuId, ret: RetValueType)
    requires
        trace.len() == 0,
        !(ret is Success),
    ensures
        cpu_online_syscall_trace(trace, pre, pre, cpu_id, target, ret),
{ reveal(cpu_online_syscall_trace); }
} // verus!
