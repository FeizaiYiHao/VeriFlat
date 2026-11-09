#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;

verus! {
/// A valid request splits its full count of free 2M blocks.
pub open spec fn split_2m_syscall_result(pre: KernelU, cpu_id: CpuId, n: usize, ret: RetValueType) -> bool {
    let cpu = pre.cpu_array[cpu_id as int];
    if n > usize::MAX / 512 { ret == RetValueType::Error }
    else if !(cpu.state is Running) || cpu.killed { ret == RetValueType::CpuIdle }
    else {
        let thread = pre.thread_map[cpu.current_thread->Some_0];
        if thread.killed { ret == RetValueType::ErrorThreadKilled }
        else if thread.quota_2m < n { ret == RetValueType::ErrorNoQuota }
        else { ret == RetValueType::SuccessUsize { value: n } }
    }
}

/// A concrete quota exchange on the running thread. The label supplies the actual count.
pub open spec fn split_2m_step_pre(pre: KernelU, cpu_id: CpuId, m: usize) -> bool {
    let cpu = pre.cpu_array[cpu_id as int];
    let thread = pre.thread_map[cpu.current_thread->Some_0];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& !cpu.killed
    &&& cpu.current_thread is Some
    &&& pre.thread_map.dom().contains(cpu.current_thread->Some_0)
    &&& !thread.killed
    &&& m <= usize::MAX / 512
    &&& thread.quota_2m >= m
    &&& thread.quota_4k + 512 * m <= usize::MAX
}

pub open spec fn split_2m_step(pre: KernelU, post: KernelU, cpu_id: CpuId, m: usize) -> bool {
    let thrd_ptr = pre.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = pre.thread_map[thrd_ptr];
    let cpu = pre.cpu_array[cpu_id as int];
    post == (KernelU {
        cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: post.cpu_array[cpu_id as int].lock_state, op: post.cpu_array[cpu_id as int].op, ..cpu }),
        thread_map: pre.thread_map.insert(thrd_ptr, ThreadU {
            lock_state: post.thread_map[thrd_ptr].lock_state, quota_4k: (thread.quota_4k + 512 * m) as usize, quota_2m: (thread.quota_2m - m) as usize, ..thread
        }), ..pre
    })
}

/// Every recorded section converts one block; the final section also releases the sources, CPU, and thread.
#[verifier::opaque]
pub open spec fn split_2m_syscall_trace(trace: Seq<KernelStep>, cpu_id: CpuId, n: usize, ret: RetValueType) -> bool {
    if ret is SuccessUsize {
        &&& ret->SuccessUsize_value <= n
        &&& trace.len() == ret->SuccessUsize_value
        &&& forall|i: int| #![trigger trace[i]] 0 <= i < trace.len() ==> {
            &&& split_2m_step_pre(trace[i].old_u, cpu_id, 1)
            &&& split_2m_step(trace[i].old_u, trace[i].new_u, cpu_id, 1)
        }
    } else { trace.len() == 0 }
}

}
