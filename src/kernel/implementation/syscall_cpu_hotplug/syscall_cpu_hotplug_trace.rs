use vstd::prelude::*;
use crate::*;
use super::syscall_cpu_hotplug_spec::*;
verus! {
/// Each return path's entry-state K facts give its value as the user-view result, and a successful call's read request bit as its pending flag.
pub(super) proof fn cpu_offline_request_result_from_k(krnl: &KernelK, cpu_id: CpuId, target: CpuId, ret: RetValueType, pending: bool)
    requires
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, target),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let container_ptr = cpu.view().view().owning_container;
            let t = krnl.cpu_arr.spec_index(target).view().view().view();
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed()
            &&& ret is ErrorCpuOwnerMismatch ==> t.owning_container != container_ptr
            &&& ret is ErrorCpuAlreadyOff ==> t.owning_container == container_ptr && t.state is Off
            &&& ret is Success ==> t.owning_container == container_ptr && !(t.state is Off)
            &&& ret is Success ==> krnl.ctn_mp.dom().contains(container_ptr) && pending == krnl.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(container_ptr)).flags.spec_index(target).view().view().requested
            &&& ret is CpuIdle || ret is ErrorCpuOwnerMismatch || ret is ErrorCpuAlreadyOff || ret is Success
        },
    ensures
        cpu_offline_request_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, target) == ret,
        ret is Success ==> cpu_offline_request_pending(kernel_k_to_kernel_u(*krnl), cpu_id, target) == pending,
{
    let container_ptr = krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container;
    kernel_cpu_projection_at(krnl, cpu_id); kernel_cpu_projection_at(krnl, target);
    if krnl.ctn_mp.dom().contains(container_ptr) { kernel_container_projection_at(krnl, container_ptr); }
    reveal(cpu_offline_requests_of);
}

/// The request wrapper's user-view facts are exactly the request step on `pre`/`post`.
pub(super) proof fn cpu_offline_request_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, target: CpuId)
    requires
        kernel_u_cpu_offline_request_changed(pre, post, cpu_id, container_ptr, target),
        pre.cpu_array[cpu_id as int].lock_state is Unlocked,
        pre.container_map[container_ptr].cpu_set_lock is Unlocked,
        pre.cpu_array[cpu_id as int].owning_container == container_ptr,
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

/// Each return path's entry-state K facts give its value as the user-view result.
pub(super) proof fn cpu_online_result_from_k(krnl: &KernelK, cpu_id: CpuId, target: CpuId, ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, target),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let container_ptr = cpu.view().view().owning_container;
            let t = krnl.cpu_arr.spec_index(target).view().view().view();
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed()
            &&& ret is ErrorCpuOwnerMismatch ==> t.owning_container != container_ptr
            &&& ret is ErrorCpuNotOff ==> t.owning_container == container_ptr && !(t.state is Off)
            &&& ret is Success ==> t.owning_container == container_ptr && t.state is Off
            &&& ret is CpuIdle || ret is ErrorCpuOwnerMismatch || ret is ErrorCpuNotOff || ret is Success
        },
    ensures
        cpu_online_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, target) == ret,
{ kernel_cpu_projection_at(krnl, cpu_id); kernel_cpu_projection_at(krnl, target); }

/// The online wrapper's user-view facts are exactly the online step on `pre`/`post`.
pub(super) proof fn cpu_online_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, target: CpuId)
    requires
        kernel_u_cpu_online_changed(pre, post, cpu_id, container_ptr, target),
        pre.cpu_array[cpu_id as int].lock_state is Unlocked,
        pre.cpu_array[target as int].lock_state is Unlocked,
        pre.container_map[container_ptr].cpu_set_lock is Unlocked,
        pre.cpu_array[cpu_id as int].owning_container == container_ptr,
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

/// Each return path's entry-state K facts give its value as the user-view result, and a successful call's read request bit as its pending flag.
pub(super) proof fn cpu_offline_request_child_result_from_k(krnl: &KernelK, cpu_id: CpuId, child: usize, target: CpuId, ret: RetValueType, pending: bool)
    requires
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, target),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let caller = krnl.ctn_mp.spec_index(cpu.view().view().owning_container);
            let children = caller.view().children.view();
            let t = krnl.cpu_arr.spec_index(target).view().view().view();
            let live = !caller.being_killed() && !caller.view().zombie;
            let owned = child < children.len() && t.owning_container == children[child as int];
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed() && krnl.ctn_mp.dom().contains(cpu.view().view().owning_container)
            &&& ret is ErrorContainerKilled ==> caller.being_killed()
            &&& ret is ErrorContainerZombie ==> !caller.being_killed() && caller.view().zombie
            &&& ret is ErrorCpuOwnerMismatch ==> live && !owned
            &&& ret is ErrorCpuAlreadyOff ==> live && owned && t.state is Off
            &&& ret is Success ==> live && owned && !(t.state is Off)
            &&& ret is Success ==> krnl.ctn_mp.dom().contains(t.owning_container) && pending == krnl.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(t.owning_container)).flags.spec_index(target).view().view().requested
            &&& ret is CpuIdle || ret is ErrorContainerKilled || ret is ErrorContainerZombie || ret is ErrorCpuOwnerMismatch || ret is ErrorCpuAlreadyOff || ret is Success
        },
    ensures
        cpu_offline_request_child_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, child, target) == ret,
        ret is Success ==> cpu_offline_request_child_pending(kernel_k_to_kernel_u(*krnl), target) == pending,
{
    let container_ptr = krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container;
    kernel_cpu_projection_at(krnl, cpu_id); kernel_cpu_projection_at(krnl, target);
    if krnl.ctn_mp.dom().contains(container_ptr) { kernel_container_projection_at(krnl, container_ptr); }
    let t = krnl.cpu_arr.spec_index(target).view().view().view();
    if krnl.ctn_mp.dom().contains(t.owning_container) { kernel_container_projection_at(krnl, t.owning_container); }
    reveal(cpu_offline_requests_of);
}

/// The request wrapper's user-view facts on the child path are exactly the child request step on `pre`/`post`.
pub(super) proof fn cpu_offline_request_child_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, target: CpuId)
    requires
        kernel_u_cpu_offline_request_changed(pre, post, cpu_id, container_ptr, target),
        pre.cpu_array[cpu_id as int].lock_state is Unlocked,
        pre.container_map[container_ptr].cpu_set_lock is Unlocked,
        pre.cpu_array[cpu_id as int].owning_container != container_ptr,
        pre.container_map[pre.cpu_array[cpu_id as int].owning_container].lock_state is Unlocked,
    ensures
        cpu_offline_request_child_step_pre(pre, cpu_id, target),
        cpu_offline_request_child_step(pre, post, cpu_id, target),
{ reveal(cpu_offline_request_child_step_pre); reveal(kernel_u_cpu_offline_request_changed); }

/// The one step pushed since `before` is the complete successful child request trace.
pub(super) proof fn cpu_offline_request_child_trace_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, target: CpuId)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        !cpu_offline_request_child_pending(pre, target),
        cpu_offline_request_child_step_pre(pre, cpu_id, target),
        cpu_offline_request_child_step(pre, post, cpu_id, target),
    ensures
        cpu_offline_request_child_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, target, RetValueType::Success),
{ reveal(cpu_offline_request_child_syscall_trace); }

/// A rejected or already pending child request records no step.
pub(super) proof fn cpu_offline_request_child_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, target: CpuId, ret: RetValueType)
    requires
        trace.len() == 0,
        !(ret is Success && !cpu_offline_request_child_pending(pre, target)),
    ensures
        cpu_offline_request_child_syscall_trace(trace, pre, pre, cpu_id, target, ret),
{ reveal(cpu_offline_request_child_syscall_trace); }

/// Each return path's entry-state K facts give its value as the user-view result.
pub(super) proof fn cpu_online_child_result_from_k(krnl: &KernelK, cpu_id: CpuId, child: usize, target: CpuId, ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, target),
        container_cpu_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let caller = krnl.ctn_mp.spec_index(cpu.view().view().owning_container);
            let children = caller.view().children.view();
            let child_set = krnl.cpu_set_mp.spec_index(krnl.ctn_mp.spec_index(children[child as int]).view_rodata().view().cpu_set).view().owned_cpus;
            let live = !caller.being_killed() && !caller.view().zombie;
            let owned = child < children.len() && krnl.ctn_mp.dom().contains(children[child as int]) && child_set.view().contains(target);
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed() && krnl.ctn_mp.dom().contains(cpu.view().view().owning_container)
            &&& ret is ErrorContainerKilled ==> caller.being_killed()
            &&& ret is ErrorContainerZombie ==> !caller.being_killed() && caller.view().zombie
            &&& ret is ErrorCpuOwnerMismatch ==> live && !owned
            &&& ret is ErrorCpuNotOff ==> live && owned && !child_set.closed_view().contains(target)
            &&& ret is Success ==> live && owned && child_set.closed_view().contains(target)
            &&& ret is CpuIdle || ret is ErrorContainerKilled || ret is ErrorContainerZombie || ret is ErrorCpuOwnerMismatch || ret is ErrorCpuNotOff || ret is Success
        },
    ensures
        cpu_online_child_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, child, target) == ret,
{
    let container_ptr = krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container;
    reveal(container_cpu_wf); kernel_cpu_projection_at(krnl, cpu_id); kernel_cpu_projection_at(krnl, target);
    if krnl.ctn_mp.dom().contains(container_ptr) { kernel_container_projection_at(krnl, container_ptr); }
}

/// The online wrapper's user-view facts on the child path are exactly the child online step on `pre`/`post`.
pub(super) proof fn cpu_online_child_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, target: CpuId)
    requires
        kernel_u_cpu_online_changed(pre, post, cpu_id, container_ptr, target),
        pre.cpu_array[cpu_id as int].lock_state is Unlocked,
        pre.cpu_array[target as int].lock_state is Unlocked,
        pre.container_map[container_ptr].cpu_set_lock is Unlocked,
        pre.cpu_array[cpu_id as int].owning_container != container_ptr,
        pre.container_map[pre.cpu_array[cpu_id as int].owning_container].lock_state is Unlocked,
    ensures
        cpu_online_child_step_pre(pre, cpu_id, target),
        cpu_online_child_step(pre, post, cpu_id, target),
{ reveal(cpu_online_child_step_pre); reveal(kernel_u_cpu_online_changed); }

/// The one step pushed since `before` is the complete successful child online trace.
pub(super) proof fn cpu_online_child_trace_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, target: CpuId)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        cpu_online_child_step_pre(pre, cpu_id, target),
        cpu_online_child_step(pre, post, cpu_id, target),
    ensures
        cpu_online_child_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, target, RetValueType::Success),
{ reveal(cpu_online_child_syscall_trace); }

/// A rejected child online call records no step.
pub(super) proof fn cpu_online_child_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, target: CpuId, ret: RetValueType)
    requires
        trace.len() == 0,
        !(ret is Success),
    ensures
        cpu_online_child_syscall_trace(trace, pre, pre, cpu_id, target, ret),
{ reveal(cpu_online_child_syscall_trace); }
} // verus!
