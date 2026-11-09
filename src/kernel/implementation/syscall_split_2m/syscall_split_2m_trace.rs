#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::{assert_seqs_equal, assert_seqs_equal_internal};
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_split_2m_spec::*;

verus! {
/// The K transition that exchanges `m` blocks of the running thread's quota and changes only lock and op state is the U split_2m step.
pub proof fn split_2m_step_from_k(pre: &KernelK, post: &KernelK, cpu_id: CpuId, thread: RwLockThreadPtr, m: usize)
    requires
        index_valid(NUM_CPUS, cpu_id),
        pre.inv(),
        post.inv(),
        post.allc_2m_mp.dom() == pre.allc_2m_mp.dom(),
        post.allc_4k_mp.dom() == pre.allc_4k_mp.dom(),
        forall|allocator: RwLockPageAllocatorPtr| #![trigger post.allc_2m_mp.spec_index(allocator)] pre.allc_2m_mp.dom().contains(allocator) ==>
            post.allc_2m_mp.spec_index(allocator).quota == pre.allc_2m_mp.spec_index(allocator).quota,
        forall|allocator: RwLockPageAllocatorPtr| #![trigger post.allc_4k_mp.spec_index(allocator)] pre.allc_4k_mp.dom().contains(allocator) ==>
            post.allc_4k_mp.spec_index(allocator).quota == pre.allc_4k_mp.spec_index(allocator).quota,
        pre.thrd_mp.dom().contains(thread),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread),
        post.thrd_mp.dom().contains(thread),
        *post == (KernelK { pg_arr: post.pg_arr, allc_2m_mp: post.allc_2m_mp, allc_4k_mp: post.allc_4k_mp,
            cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, thrd_mp: post.thrd_mp, ..*pre }),
        post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, cpu_id),
        post.cpu_arr.spec_index(cpu_id).view().view().view() == pre.cpu_arr.spec_index(cpu_id).view().view().view(),
        post.cpu_arr.spec_index(cpu_id).view().being_killed() == pre.cpu_arr.spec_index(cpu_id).view().being_killed(),
        post.cpu_arr.spec_index(cpu_id).view().killer_info() == pre.cpu_arr.spec_index(cpu_id).view().killer_info(),
        forall|other: CpuId| #![trigger post.cpu_op.view().view().spec_index(other as int)] index_valid(NUM_CPUS, other) && other != cpu_id ==>
            post.cpu_op.view().view().spec_index(other as int) == pre.cpu_op.view().view().spec_index(other as int),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thread),
        post.thrd_mp.spec_index(thread).being_killed() == pre.thrd_mp.spec_index(thread).being_killed(),
        m <= usize::MAX / 512,
        pre.thrd_mp.spec_index(thread).view().quota_2m >= m,
        pre.thrd_mp.spec_index(thread).view().quota_4k + 512 * m <= usize::MAX,
        post.thrd_mp.spec_index(thread).view() == (Thread {
            quota_2m: (pre.thrd_mp.spec_index(thread).view().quota_2m - m) as usize,
            quota_4k: (pre.thrd_mp.spec_index(thread).view().quota_4k + 512 * m) as usize, ..pre.thrd_mp.spec_index(thread).view()
        }),
    ensures split_2m_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id, m),
{
    kernel_cpu_projection_at(pre, cpu_id); kernel_thread_projection_at(pre, thread);
    kernel_thread_quotas_exchanged_implies_u_step(pre, post, cpu_id, thread, (pre.thrd_mp.spec_index(thread).view().quota_4k + 512 * m) as usize, (pre.thrd_mp.spec_index(thread).view().quota_2m - m) as usize);
}
pub proof fn split_2m_step_pre_from_k(krnl: &KernelK, cpu_id: CpuId, thread: RwLockThreadPtr)
    requires
        index_valid(NUM_CPUS, cpu_id),
        krnl.inv(),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        !krnl.cpu_arr.spec_index(cpu_id).view().being_killed(),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread),
        krnl.thrd_mp.dom().contains(thread),
        !krnl.thrd_mp.spec_index(thread).being_killed(),
        krnl.thrd_mp.spec_index(thread).view().quota_2m >= 1,
        krnl.thrd_mp.spec_index(thread).view().quota_4k <= usize::MAX - 512,
    ensures
        split_2m_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, 1),
{ kernel_cpu_projection_at(krnl, cpu_id); kernel_thread_projection_at(krnl, thread); }

pub proof fn split_2m_empty_trace_implies_syscall_trace(trace: Seq<KernelStep>, cpu_id: CpuId, n: usize, ret: RetValueType)
    requires
        trace.len() == 0,
        ret is SuccessUsize ==> ret->SuccessUsize_value == 0,
    ensures
        split_2m_syscall_trace(trace, cpu_id, n, ret),
{ reveal(split_2m_syscall_trace); }

pub proof fn split_2m_recorded_step_implies_extended_trace(before: Seq<KernelStep>, after: Seq<KernelStep>, start: int,
    pre: KernelK, post: KernelK, cpu_id: CpuId, n: usize, count: usize)
    requires
        0 <= start <= before.len(),
        count < n,
        split_2m_syscall_trace(before.subrange(start, before.len() as int), cpu_id, n, RetValueType::SuccessUsize { value: count }),
        after == before.push(KernelStep { old_u: kernel_k_to_kernel_u(pre), new_u: kernel_k_to_kernel_u(post) }),
        split_2m_step_pre(kernel_k_to_kernel_u(pre), cpu_id, 1),
        split_2m_step(kernel_k_to_kernel_u(pre), kernel_k_to_kernel_u(post), cpu_id, 1),
    ensures
        split_2m_syscall_trace(after.subrange(start, after.len() as int), cpu_id, n, RetValueType::SuccessUsize { value: (count + 1) as usize }),
{
    reveal(split_2m_syscall_trace);
    assert_seqs_equal!(after.subrange(start, after.len() as int),
        before.subrange(start, before.len() as int).push(KernelStep { old_u: kernel_k_to_kernel_u(pre), new_u: kernel_k_to_kernel_u(post) }));
}

pub proof fn split_2m_result_from_k(krnl: &KernelK, cpu_id: CpuId, n: usize, ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        krnl.inv(),
        krnl.cpu_op.view().view()[cpu_id as int] is Trap,
        n <= usize::MAX / 512 && krnl.cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !krnl.cpu_arr.spec_index(cpu_id).view().being_killed() ==> {
            &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread is Some
            &&& krnl.thrd_mp.dom().contains(krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0)
        },
        ({
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            if n > usize::MAX / 512 { ret == RetValueType::Error }
            else if !(cpu.view().view().state is Running) || cpu.being_killed() { ret == RetValueType::CpuIdle }
            else {
                let thread = krnl.thrd_mp.spec_index(cpu.view().view().current_thread->Some_0);
                if thread.being_killed() { ret == RetValueType::ErrorThreadKilled }
                else if thread.view().quota_2m < n { ret == RetValueType::ErrorNoQuota }
                else { ret == RetValueType::SuccessUsize { value: n } }
            }
        }),
    ensures
        split_2m_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, n, ret),
{
    kernel_cpu_projection_at(krnl, cpu_id);
    if n <= usize::MAX / 512 && krnl.cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !krnl.cpu_arr.spec_index(cpu_id).view().being_killed() {
        thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id);
        kernel_thread_projection_at(krnl, krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0);
    }
}

}
