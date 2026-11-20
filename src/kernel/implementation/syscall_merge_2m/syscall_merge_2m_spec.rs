#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;

verus! {
/// Result relation: physical fragmentation is deliberately absent from U.
pub open spec fn merge_2m_syscall_result(pre: KernelU, cpu_id: CpuId, n: usize, ret: RetValueType) -> bool {
    let cpu = pre.cpu_array[cpu_id as int];
    if n > usize::MAX / 512 { ret == RetValueType::Error }
    else if !(cpu.state is Running) || cpu.killed { ret == RetValueType::CpuIdle }
    else {
        let thread = pre.thread_map[cpu.current_thread->Some_0];
        if thread.killed { ret == RetValueType::ErrorThreadKilled }
        else if thread.quota_4k < 512 * n { ret == RetValueType::ErrorNoQuota }
        else { ret is SuccessUsize && ret->SuccessUsize_value <= n }
    }
}

/// A concrete quota exchange on the running thread, which records no progress: the first section starts from the trap
/// path with the cpu and thread unlocked, a later one with both write-held by the cpu.
pub open spec fn merge_2m_step_pre(pre: KernelU, cpu_id: CpuId) -> bool {
    let cpu = pre.cpu_array[cpu_id as int];
    let thread = pre.thread_map[cpu.current_thread->Some_0];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& !cpu.killed
    &&& cpu.current_thread is Some
    &&& pre.thread_map.dom().contains(cpu.current_thread->Some_0)
    &&& !thread.killed
    &&& thread.syscall_progress is None
    &&& if cpu.lock_state is Unlocked { cpu.op is Trap && thread.lock_state is Unlocked }
        else { cpu.lock_state == (LockStateU::WriteLocked { writer: cpu_id }) && cpu.op is InStep && thread.lock_state == (LockStateU::WriteLocked { writer: cpu_id }) }
    &&& thread.quota_4k >= 512
    &&& thread.quota_2m < usize::MAX
}

/// Each section keeps the cpu and thread write-held inside the kernel step, or releases both and returns the cpu to its
/// trap path.
pub open spec fn merge_2m_step(pre: KernelU, post: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = pre.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = pre.thread_map[thrd_ptr];
    let cpu = pre.cpu_array[cpu_id as int];
    let held = post.cpu_array[cpu_id as int].lock_state is WriteLocked;
    let lock = if held { LockStateU::WriteLocked { writer: cpu_id } } else { LockStateU::Unlocked };
    post == (KernelU {
        cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: lock, op: if held { CpuOpState::InStep } else { CpuOpState::Trap }, ..cpu }),
        thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { lock_state: lock, quota_4k: (thread.quota_4k - 512) as usize, quota_2m: (thread.quota_2m + 1) as usize, ..thread }), ..pre
    })
}

/// Every recorded section converts one block; the final section also releases the sources, CPU, and thread.
#[verifier::opaque]
pub open spec fn merge_2m_syscall_trace(trace: Seq<KernelStep>, cpu_id: CpuId, n: usize, ret: RetValueType) -> bool {
    if ret is SuccessUsize {
        &&& ret->SuccessUsize_value <= n
        &&& trace.len() == ret->SuccessUsize_value
        &&& forall|i: int| #![trigger trace[i]] 0 <= i < trace.len() ==> {
            &&& merge_2m_step_pre(trace[i].old_u, cpu_id)
            &&& merge_2m_step(trace[i].old_u, trace[i].new_u, cpu_id)
        }
    } else { trace.len() == 0 }
}

}
