use vstd::prelude::*;
use crate::*;

verus! {
/// The result of `syscall_alloc_quota_4k` from the state at entry, in the implementation's check order:
/// a killed container or process, too little container 4K quota, and process 4K quota overflow.
pub open spec fn alloc_quota_4k_syscall_result(pre: KernelU, cpu_id: CpuId, alloc_amount: usize) -> RetValueType {
    let cpu = pre.cpu_array[cpu_id as int];
    let container = pre.container_map[cpu.owning_container];
    let process = pre.process_map[cpu.current_process->Some_0];
    if container.killed { RetValueType::ErrorContainerKilled }
    else if process.killed { RetValueType::ErrorProcessKilled }
    else if container.quota_4k < alloc_amount { RetValueType::ErrorContainerQuotaInsufficient }
    else if alloc_amount > usize::MAX - process.quota_4k { RetValueType::ErrorProcessQuotaOverflow }
    else { RetValueType::Success }
}

/// The cpu, the running process, and its container are unlocked, exist, are alive, and can move
/// `alloc_amount` 4K quota from the container to the process without overflow.
#[verifier::opaque]
pub open spec fn alloc_quota_4k_step_pre(old_u: KernelU, cpu_id: CpuId, alloc_amount: usize) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let process_ptr = cpu.current_process->Some_0;
    let container_ptr = cpu.owning_container;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& cpu.state is Running
    &&& cpu.current_process is Some
    &&& old_u.container_map.dom().contains(container_ptr)
    &&& old_u.container_map.spec_index(container_ptr).lock_state is Unlocked
    &&& !old_u.container_map.spec_index(container_ptr).killed
    &&& old_u.container_map.spec_index(container_ptr).quota_4k >= alloc_amount
    &&& old_u.process_map.dom().contains(process_ptr)
    &&& old_u.process_map.spec_index(process_ptr).lock_state is Unlocked
    &&& !old_u.process_map.spec_index(process_ptr).killed
    &&& old_u.process_map.spec_index(process_ptr).quota_4k + alloc_amount <= usize::MAX
    &&& alloc_amount > 0
}

/// The container's 4K quota decreases by `alloc_amount` and the running process's increases by it.
pub open spec fn alloc_quota_4k_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, alloc_amount: usize) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    kernel_u_only_process_quota_4k_changed(old_u, new_u, cpu_id, cpu.current_process->Some_0, cpu.owning_container, alloc_amount as int)
}
/// Complete trace of the call; acquiring and releasing its locks inside one section stutters.
#[verifier::opaque]
pub open spec fn alloc_quota_4k_syscall_trace(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, alloc_amount: usize, ret: RetValueType) -> bool {
    if ret is Success && alloc_amount > 0 {
        &&& trace.len() == 1
        &&& trace[0].old_u == pre
        &&& trace[0].new_u == post
        &&& alloc_quota_4k_step_pre(pre, cpu_id, alloc_amount)
        &&& alloc_quota_4k_step(pre, post, cpu_id, alloc_amount)
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}
} // verus!
