#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal, assert_seqs_equal_internal};
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_merge_2m_spec::*;

verus! {
/// The K transition that exchanges `m` blocks of the running thread's quota and changes only lock and op state is the U merge_2m step.
pub proof fn merge_2m_step_from_k(pre: &KernelK, post: &KernelK, cpu_id: CpuId, thread: RwLockThreadPtr, m: usize)
    requires
        index_valid(NUM_CPUS, cpu_id),
        pre.inv(),
        post.inv(),
        post.allc_4k_mp.dom() == pre.allc_4k_mp.dom(),
        post.allc_2m_mp.dom() == pre.allc_2m_mp.dom(),
        forall|allocator: RwLockPageAllocatorPtr| #![trigger post.allc_4k_mp.spec_index(allocator)] pre.allc_4k_mp.dom().contains(allocator) ==>
            post.allc_4k_mp.spec_index(allocator).quota == pre.allc_4k_mp.spec_index(allocator).quota,
        forall|allocator: RwLockPageAllocatorPtr| #![trigger post.allc_2m_mp.spec_index(allocator)] pre.allc_2m_mp.dom().contains(allocator) ==>
            post.allc_2m_mp.spec_index(allocator).quota == pre.allc_2m_mp.spec_index(allocator).quota,
        pre.thrd_mp.dom().contains(thread),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread),
        post.thrd_mp.dom().contains(thread),
        *post == (KernelK { pg_arr: post.pg_arr, allc_4k_mp: post.allc_4k_mp, allc_2m_mp: post.allc_2m_mp,
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
        pre.thrd_mp.spec_index(thread).view().quota_4k >= 512 * m,
        pre.thrd_mp.spec_index(thread).view().quota_2m + m <= usize::MAX,
        post.thrd_mp.spec_index(thread).view() == (Thread {
            quota_4k: (pre.thrd_mp.spec_index(thread).view().quota_4k - 512 * m) as usize,
            quota_2m: (pre.thrd_mp.spec_index(thread).view().quota_2m + m) as usize, ..pre.thrd_mp.spec_index(thread).view()
        }),
    ensures merge_2m_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id, m),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    kernel_cpu_projection_at(pre, cpu_id); kernel_cpu_projection_at(post, cpu_id);
    kernel_thread_projection_at(pre, thread); kernel_thread_projection_at(post, thread);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let cpu = pre_u.cpu_array[cpu_id as int];
    let t = pre_u.thread_map[thread];
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU {
        lock_state: post_u.cpu_array[cpu_id as int].lock_state, op: post_u.cpu_array[cpu_id as int].op, ..cpu
    }), i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread, ThreadU {
        lock_state: post_u.thread_map[thread].lock_state, quota_4k: (t.quota_4k - 512 * m) as usize, quota_2m: (t.quota_2m + m) as usize, ..t
    }), ptr => { if pre.thrd_mp.dom().contains(ptr) { kernel_thread_projection_at(pre, ptr); } if post.thrd_mp.dom().contains(ptr) { kernel_thread_projection_at(post, ptr); } });
    assert_maps_equal!(post_u.container_map, pre_u.container_map, ptr => {
        if pre.ctn_mp.dom().contains(ptr) {
            kernel_container_projection_at(pre, ptr); kernel_container_projection_at(post, ptr);
            container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, ptr);
        }
    });
    assert_maps_equal!(post_u.process_map, pre_u.process_map, ptr => {
        if pre.prc_mp.dom().contains(ptr) { kernel_process_projection_at(pre, ptr); kernel_process_projection_at(post, ptr); }
    });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, ptr => {
        if pre.ep_mp.dom().contains(ptr) { kernel_endpoint_projection_at(pre, ptr); kernel_endpoint_projection_at(post, ptr); }
    });
}
pub proof fn merge_2m_step_pre_from_k(krnl: &KernelK, cpu_id: CpuId, thread: RwLockThreadPtr)
    requires
        index_valid(NUM_CPUS, cpu_id),
        krnl.inv(),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        !krnl.cpu_arr.spec_index(cpu_id).view().being_killed(),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread),
        krnl.thrd_mp.dom().contains(thread),
        !krnl.thrd_mp.spec_index(thread).being_killed(),
        krnl.thrd_mp.spec_index(thread).view().quota_4k >= 512,
        krnl.thrd_mp.spec_index(thread).view().quota_2m < usize::MAX,
    ensures
        merge_2m_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, 1),
{ kernel_cpu_projection_at(krnl, cpu_id); kernel_thread_projection_at(krnl, thread); }

pub proof fn merge_2m_empty_trace_implies_syscall_trace(trace: Seq<KernelStep>, cpu_id: CpuId, n: usize, ret: RetValueType)
    requires
        trace.len() == 0,
        ret is SuccessUsize ==> ret->SuccessUsize_value == 0,
    ensures
        merge_2m_syscall_trace(trace, cpu_id, n, ret),
{ reveal(merge_2m_syscall_trace); }

pub proof fn merge_2m_recorded_step_implies_extended_trace(before: Seq<KernelStep>, after: Seq<KernelStep>, start: int,
    pre: KernelK, post: KernelK, cpu_id: CpuId, n: usize, count: usize)
    requires
        0 <= start <= before.len(),
        count < n,
        merge_2m_syscall_trace(before.subrange(start, before.len() as int), cpu_id, n, RetValueType::SuccessUsize { value: count }),
        after == before.push(KernelStep { old_u: kernel_k_to_kernel_u(pre), new_u: kernel_k_to_kernel_u(post) }),
        merge_2m_step_pre(kernel_k_to_kernel_u(pre), cpu_id, 1),
        merge_2m_step(kernel_k_to_kernel_u(pre), kernel_k_to_kernel_u(post), cpu_id, 1),
    ensures
        merge_2m_syscall_trace(after.subrange(start, after.len() as int), cpu_id, n, RetValueType::SuccessUsize { value: (count + 1) as usize }),
{
    reveal(merge_2m_syscall_trace);
    assert_seqs_equal!(after.subrange(start, after.len() as int),
        before.subrange(start, before.len() as int).push(KernelStep { old_u: kernel_k_to_kernel_u(pre), new_u: kernel_k_to_kernel_u(post) }));
}

pub proof fn merge_2m_result_from_k(krnl: &KernelK, cpu_id: CpuId, n: usize, ret: RetValueType)
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
                else if thread.view().quota_4k < 512 * n { ret == RetValueType::ErrorNoQuota }
                else { ret is SuccessUsize && ret->SuccessUsize_value <= n }
            }
        }),
    ensures
        merge_2m_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, n, ret),
{
    kernel_cpu_projection_at(krnl, cpu_id);
    if n <= usize::MAX / 512 && krnl.cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !krnl.cpu_arr.spec_index(cpu_id).view().being_killed() {
        thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id);
        kernel_thread_projection_at(krnl, krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0);
    }
}

}
