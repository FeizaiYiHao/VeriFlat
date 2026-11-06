use vstd::prelude::*;
use crate::*;

verus! {
/// The entry-state result of `syscall_alloc_quota_1g` in check order: cpu not Running or killer-marked, killed container, container write-held by a live owner below the caller depth, zombie container, killed process, short container 1G quota, process 1G quota overflow.
pub open spec fn alloc_quota_1g_syscall_result(pre: KernelU, cpu_id: CpuId, alloc_amount: usize) -> RetValueType {
    let cpu = pre.cpu_array[cpu_id as int];
    let container = pre.container_map[cpu.owning_container];
    let process = pre.process_map[cpu.current_process->Some_0];
    if !(cpu.state is Running) || cpu.killed { RetValueType::CpuIdle }
    else if container.killed { RetValueType::ErrorContainerKilled }
    else if container.lock_process_owner is Some && container.lock_process_owner->Some_0 < LockOwnerId::Some(process.depth) { RetValueType::ErrorContainerLockOrderConflict }
    else if container.zombie { RetValueType::ErrorContainerZombie }
    else if process.killed { RetValueType::ErrorProcessKilled }
    else if container.quota_1g < alloc_amount { RetValueType::ErrorContainerQuotaInsufficient }
    else if alloc_amount > usize::MAX - process.quota_1g { RetValueType::ErrorProcessQuotaOverflow }
    else { RetValueType::Success }
}

/// The cpu, the running process, and its container are unlocked, exist, are alive, and can move `alloc_amount` 1G quota from the container to the process without overflow.
#[verifier::opaque]
pub open spec fn alloc_quota_1g_step_pre(old_u: KernelU, cpu_id: CpuId, alloc_amount: usize) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let prc_ptr = cpu.current_process->Some_0;
    let ctn_ptr = cpu.owning_container;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& cpu.state is Running
    &&& cpu.current_process is Some
    &&& old_u.container_map.dom().contains(ctn_ptr)
    &&& old_u.container_map.spec_index(ctn_ptr).lock_state is Unlocked
    &&& !old_u.container_map.spec_index(ctn_ptr).killed
    &&& !old_u.container_map.spec_index(ctn_ptr).zombie
    &&& old_u.container_map.spec_index(ctn_ptr).quota_1g >= alloc_amount
    &&& old_u.process_map.dom().contains(prc_ptr)
    &&& old_u.process_map.spec_index(prc_ptr).lock_state is Unlocked
    &&& !old_u.process_map.spec_index(prc_ptr).killed
    &&& old_u.process_map.spec_index(prc_ptr).quota_1g + alloc_amount <= usize::MAX
    &&& alloc_amount > 0
}

/// The container's 1G quota decreases by `alloc_amount` and the running process's increases by it.
pub open spec fn alloc_quota_1g_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, alloc_amount: usize) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    kernel_u_only_process_quota_1g_changed(old_u, new_u, cpu_id, cpu.current_process->Some_0, cpu.owning_container, alloc_amount as int)
}
/// Complete trace of the call; acquiring and releasing its locks inside one section stutters.
#[verifier::opaque]
pub open spec fn alloc_quota_1g_syscall_trace(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, alloc_amount: usize, ret: RetValueType) -> bool {
    if ret is Success && alloc_amount > 0 {
        &&& trace.len() == 1
        &&& trace[0].old_u == pre
        &&& trace[0].new_u == post
        &&& alloc_quota_1g_step_pre(pre, cpu_id, alloc_amount)
        &&& alloc_quota_1g_step(pre, post, cpu_id, alloc_amount)
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}

/// The result of `syscall_alloc_thread_quota_1g` from the state at entry, in the implementation's check order: a cpu no longer Running or marked by a killer, a killed process or thread, too little process 1G quota, and thread 1G quota overflow.
pub open spec fn alloc_thread_quota_1g_syscall_result(pre: KernelU, cpu_id: CpuId, alloc_amount: usize) -> RetValueType {
    let cpu = pre.cpu_array[cpu_id as int];
    let process = pre.process_map[cpu.current_process->Some_0];
    let thread = pre.thread_map[cpu.current_thread->Some_0];
    if !(cpu.state is Running) || cpu.killed { RetValueType::CpuIdle }
    else if process.killed { RetValueType::ErrorProcessKilled }
    else if thread.killed { RetValueType::ErrorThreadKilled }
    else if process.quota_1g < alloc_amount { RetValueType::ErrorNoQuota }
    else if alloc_amount > usize::MAX - thread.quota_1g { RetValueType::ErrorThreadQuotaOverflow }
    else { RetValueType::Success }
}

/// The cpu, its running process, and its running thread are unlocked, exist, are alive, and can move `alloc_amount` 1G quota from the process to the thread without overflow.
#[verifier::opaque]
pub open spec fn alloc_thread_quota_1g_step_pre(old_u: KernelU, cpu_id: CpuId, alloc_amount: usize) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let prc_ptr = cpu.current_process->Some_0;
    let thrd_ptr = cpu.current_thread->Some_0;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& cpu.state is Running
    &&& cpu.current_process is Some
    &&& cpu.current_thread is Some
    &&& old_u.process_map.dom().contains(prc_ptr)
    &&& old_u.process_map.spec_index(prc_ptr).lock_state is Unlocked
    &&& !old_u.process_map.spec_index(prc_ptr).killed
    &&& old_u.process_map.spec_index(prc_ptr).quota_1g >= alloc_amount
    &&& old_u.thread_map.dom().contains(thrd_ptr)
    &&& old_u.thread_map.spec_index(thrd_ptr).lock_state is Unlocked
    &&& !old_u.thread_map.spec_index(thrd_ptr).killed
    &&& old_u.thread_map.spec_index(thrd_ptr).quota_1g + alloc_amount <= usize::MAX
    &&& alloc_amount > 0
}

/// The running process's 1G quota decreases by `alloc_amount` and its running thread's increases by it.
pub open spec fn alloc_thread_quota_1g_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, alloc_amount: usize) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    kernel_u_only_process2thread_quota_1g_changed(old_u, new_u, cpu_id, cpu.current_process->Some_0, cpu.current_thread->Some_0, alloc_amount as int)
}
/// Complete trace of the call; acquiring and releasing its locks inside one section stutters.
#[verifier::opaque]
pub open spec fn alloc_thread_quota_1g_syscall_trace(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, alloc_amount: usize, ret: RetValueType) -> bool {
    if ret is Success && alloc_amount > 0 {
        &&& trace.len() == 1
        &&& trace[0].old_u == pre
        &&& trace[0].new_u == post
        &&& alloc_thread_quota_1g_step_pre(pre, cpu_id, alloc_amount)
        &&& alloc_thread_quota_1g_step(pre, post, cpu_id, alloc_amount)
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}
} // verus!
