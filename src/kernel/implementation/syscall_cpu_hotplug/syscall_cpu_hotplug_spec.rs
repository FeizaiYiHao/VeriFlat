use vstd::prelude::*;
use crate::*;

verus! {
/// The result of `syscall_cpu_offline_request` from the state at entry: `target` must be a cpu of the
/// caller's container that is not Off. A request already pending succeeds without a step.
/// A cpu no longer Running or marked by a killer returns CpuIdle after the argument checks.
pub open spec fn cpu_offline_request_syscall_result(pre: KernelU, cpu_id: CpuId, target: CpuId) -> RetValueType {
    let cpu = pre.cpu_array[cpu_id as int];
    if !index_valid(NUM_CPUS, target) { RetValueType::ErrorCpuOwnerMismatch }
    else if !(cpu.state is Running) || cpu.killed { RetValueType::CpuIdle }
    else if pre.cpu_array[target as int].owning_container != cpu.owning_container { RetValueType::ErrorCpuOwnerMismatch }
    else if pre.cpu_array[target as int].state is Off { RetValueType::ErrorCpuAlreadyOff }
    else { RetValueType::Success }
}

/// The request bit of `target` in the caller's container is clear at entry, so the call records a step.
pub open spec fn cpu_offline_request_pending(pre: KernelU, cpu_id: CpuId, target: CpuId) -> bool {
    pre.container_map[pre.cpu_array[cpu_id as int].owning_container].cpu_offline_requests[target as int]
}

/// The cpu and its container's cpu-set lock are unlocked; `target` is a non-Off cpu of that container
/// with no pending request.
#[verifier::opaque]
pub open spec fn cpu_offline_request_step_pre(old_u: KernelU, cpu_id: CpuId, target: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let container_ptr = cpu.owning_container;
    let container = old_u.container_map[container_ptr];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& cpu.state is Running
    &&& old_u.container_map.dom().contains(container_ptr)
    &&& container.cpu_set_lock is Unlocked
    &&& index_valid(NUM_CPUS, target)
    &&& old_u.cpu_array[target as int].owning_container == container_ptr
    &&& !(old_u.cpu_array[target as int].state is Off)
    &&& !container.cpu_offline_requests[target as int]
}

/// The caller container's request bit for `target` is set.
pub open spec fn cpu_offline_request_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, target: CpuId) -> bool {
    kernel_u_cpu_offline_request_changed(old_u, new_u, cpu_id, old_u.cpu_array[cpu_id as int].owning_container, target)
}

/// Complete trace of the call; rejections and an already pending request stutter.
#[verifier::opaque]
pub open spec fn cpu_offline_request_syscall_trace(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, target: CpuId, ret: RetValueType) -> bool {
    if ret is Success && !cpu_offline_request_pending(pre, cpu_id, target) {
        &&& trace.len() == 1
        &&& trace[0].old_u == pre
        &&& trace[0].new_u == post
        &&& cpu_offline_request_step_pre(pre, cpu_id, target)
        &&& cpu_offline_request_step(pre, post, cpu_id, target)
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}

/// The result of `syscall_cpu_online` from the state at entry: `target` must be an Off cpu of the
/// caller's container.
/// A cpu no longer Running or marked by a killer returns CpuIdle after the argument checks.
pub open spec fn cpu_online_syscall_result(pre: KernelU, cpu_id: CpuId, target: CpuId) -> RetValueType {
    let cpu = pre.cpu_array[cpu_id as int];
    if !index_valid(NUM_CPUS, target) { RetValueType::ErrorCpuOwnerMismatch }
    else if !(cpu.state is Running) || cpu.killed { RetValueType::CpuIdle }
    else if pre.cpu_array[target as int].owning_container != cpu.owning_container { RetValueType::ErrorCpuOwnerMismatch }
    else if !(pre.cpu_array[target as int].state is Off) { RetValueType::ErrorCpuNotOff }
    else { RetValueType::Success }
}

/// The cpu, its container's cpu-set lock, and `target` are unlocked; `target` is an Off cpu of that container.
#[verifier::opaque]
pub open spec fn cpu_online_step_pre(old_u: KernelU, cpu_id: CpuId, target: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let container_ptr = cpu.owning_container;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& cpu.state is Running
    &&& old_u.container_map.dom().contains(container_ptr)
    &&& old_u.container_map[container_ptr].cpu_set_lock is Unlocked
    &&& index_valid(NUM_CPUS, target)
    &&& old_u.cpu_array[target as int].lock_state is Unlocked
    &&& old_u.cpu_array[target as int].owning_container == container_ptr
    &&& old_u.cpu_array[target as int].state is Off
}

/// `target` becomes Idle.
pub open spec fn cpu_online_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, target: CpuId) -> bool {
    kernel_u_cpu_online_changed(old_u, new_u, cpu_id, old_u.cpu_array[cpu_id as int].owning_container, target)
}

/// Complete trace of the call; rejections stutter.
#[verifier::opaque]
pub open spec fn cpu_online_syscall_trace(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, target: CpuId, ret: RetValueType) -> bool {
    if ret is Success {
        &&& trace.len() == 1
        &&& trace[0].old_u == pre
        &&& trace[0].new_u == post
        &&& cpu_online_step_pre(pre, cpu_id, target)
        &&& cpu_online_step(pre, post, cpu_id, target)
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}

/// The result of `syscall_cpu_offline_request_child` from the state at entry: the caller's container must be
/// live and not a zombie, and `target` a cpu, not Off, of its `child`-th child. A request already pending succeeds without a step.
/// A cpu no longer Running or marked by a killer returns CpuIdle after the argument checks.
pub open spec fn cpu_offline_request_child_syscall_result(pre: KernelU, cpu_id: CpuId, child: usize, target: CpuId) -> RetValueType {
    let caller = pre.container_map[pre.cpu_array[cpu_id as int].owning_container];
    if !index_valid(NUM_CPUS, target) { RetValueType::ErrorCpuOwnerMismatch }
    else if !(pre.cpu_array[cpu_id as int].state is Running) || pre.cpu_array[cpu_id as int].killed { RetValueType::CpuIdle }
    else if caller.killed { RetValueType::ErrorContainerKilled }
    else if caller.zombie { RetValueType::ErrorContainerZombie }
    else if child >= caller.children.len() || pre.cpu_array[target as int].owning_container != caller.children[child as int] { RetValueType::ErrorCpuOwnerMismatch }
    else if pre.cpu_array[target as int].state is Off { RetValueType::ErrorCpuAlreadyOff }
    else { RetValueType::Success }
}

/// The request bit of `target` in its owning container is set at entry, so the child call records no step.
pub open spec fn cpu_offline_request_child_pending(pre: KernelU, target: CpuId) -> bool {
    pre.container_map[pre.cpu_array[target as int].owning_container].cpu_offline_requests[target as int]
}

/// The cpu, the caller's live, non-zombie container, and the cpu-set lock of `target`'s container, a direct child of the
/// caller's, are unlocked; `target` is a non-Off cpu with no pending request.
#[verifier::opaque]
pub open spec fn cpu_offline_request_child_step_pre(old_u: KernelU, cpu_id: CpuId, target: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let container_ptr = old_u.cpu_array[target as int].owning_container;
    let container = old_u.container_map[container_ptr];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& cpu.state is Running
    &&& old_u.container_map.dom().contains(cpu.owning_container)
    &&& old_u.container_map[cpu.owning_container].lock_state is Unlocked
    &&& !old_u.container_map[cpu.owning_container].killed
    &&& !old_u.container_map[cpu.owning_container].zombie
    &&& index_valid(NUM_CPUS, target)
    &&& old_u.container_map.dom().contains(container_ptr)
    &&& container.parent == Some(cpu.owning_container)
    &&& container.cpu_set_lock is Unlocked
    &&& !(old_u.cpu_array[target as int].state is Off)
    &&& !container.cpu_offline_requests[target as int]
}

/// The request bit of `target` in its owning container, a direct child of the caller's, is set.
pub open spec fn cpu_offline_request_child_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, target: CpuId) -> bool {
    kernel_u_cpu_offline_request_changed(old_u, new_u, cpu_id, old_u.cpu_array[target as int].owning_container, target)
}

/// Complete trace of the child call; rejections and an already pending request stutter.
#[verifier::opaque]
pub open spec fn cpu_offline_request_child_syscall_trace(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, target: CpuId, ret: RetValueType) -> bool {
    if ret is Success && !cpu_offline_request_child_pending(pre, target) {
        &&& trace.len() == 1
        &&& trace[0].old_u == pre
        &&& trace[0].new_u == post
        &&& cpu_offline_request_child_step_pre(pre, cpu_id, target)
        &&& cpu_offline_request_child_step(pre, post, cpu_id, target)
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}

/// The result of `syscall_cpu_online_child` from the state at entry: the caller's container must be live and
/// not a zombie, and `target` an Off cpu of its `child`-th child.
/// A cpu no longer Running or marked by a killer returns CpuIdle after the argument checks.
pub open spec fn cpu_online_child_syscall_result(pre: KernelU, cpu_id: CpuId, child: usize, target: CpuId) -> RetValueType {
    let caller = pre.container_map[pre.cpu_array[cpu_id as int].owning_container];
    if !index_valid(NUM_CPUS, target) { RetValueType::ErrorCpuOwnerMismatch }
    else if !(pre.cpu_array[cpu_id as int].state is Running) || pre.cpu_array[cpu_id as int].killed { RetValueType::CpuIdle }
    else if caller.killed { RetValueType::ErrorContainerKilled }
    else if caller.zombie { RetValueType::ErrorContainerZombie }
    else if child >= caller.children.len() || pre.cpu_array[target as int].owning_container != caller.children[child as int] { RetValueType::ErrorCpuOwnerMismatch }
    else if !(pre.cpu_array[target as int].state is Off) { RetValueType::ErrorCpuNotOff }
    else { RetValueType::Success }
}

/// The cpu, the caller's live, non-zombie container, the cpu-set lock of `target`'s container, a direct child of the
/// caller's, and `target` are unlocked; `target` is Off.
#[verifier::opaque]
pub open spec fn cpu_online_child_step_pre(old_u: KernelU, cpu_id: CpuId, target: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let container_ptr = old_u.cpu_array[target as int].owning_container;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& cpu.state is Running
    &&& old_u.container_map.dom().contains(cpu.owning_container)
    &&& old_u.container_map[cpu.owning_container].lock_state is Unlocked
    &&& !old_u.container_map[cpu.owning_container].killed
    &&& !old_u.container_map[cpu.owning_container].zombie
    &&& index_valid(NUM_CPUS, target)
    &&& old_u.container_map.dom().contains(container_ptr)
    &&& old_u.container_map[container_ptr].parent == Some(cpu.owning_container)
    &&& old_u.container_map[container_ptr].cpu_set_lock is Unlocked
    &&& old_u.cpu_array[target as int].lock_state is Unlocked
    &&& old_u.cpu_array[target as int].state is Off
}

/// `target`, an Off cpu of a direct child of the caller's container, becomes Idle.
pub open spec fn cpu_online_child_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, target: CpuId) -> bool {
    kernel_u_cpu_online_changed(old_u, new_u, cpu_id, old_u.cpu_array[target as int].owning_container, target)
}

/// Complete trace of the child call; rejections stutter.
#[verifier::opaque]
pub open spec fn cpu_online_child_syscall_trace(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, target: CpuId, ret: RetValueType) -> bool {
    if ret is Success {
        &&& trace.len() == 1
        &&& trace[0].old_u == pre
        &&& trace[0].new_u == post
        &&& cpu_online_child_step_pre(pre, cpu_id, target)
        &&& cpu_online_child_step(pre, post, cpu_id, target)
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}
} // verus!
