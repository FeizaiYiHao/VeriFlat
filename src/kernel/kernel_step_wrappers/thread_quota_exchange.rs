#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal, assert_seqs_equal_internal};
use crate::*;

verus! {
/// A transition that changes only page, allocator, and lock state besides one thread's 4K and 2M quotas projects to the U state with that thread's quotas set and the cpu's and thread's lock state and the cpu's op taken from `post`.
pub proof fn kernel_thread_quotas_exchanged_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, thread: RwLockThreadPtr, quota_4k: usize, quota_2m: usize)
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
        *post == (KernelK { pg_arr: post.pg_arr, allc_4k_mp: post.allc_4k_mp, allc_2m_mp: post.allc_2m_mp,
            cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, thrd_mp: post.thrd_mp, ..*pre }),
        post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, cpu_id),
        post.cpu_arr.spec_index(cpu_id).view().view().view() == pre.cpu_arr.spec_index(cpu_id).view().view().view(),
        post.cpu_arr.spec_index(cpu_id).view().being_killed() == pre.cpu_arr.spec_index(cpu_id).view().being_killed(),
        post.cpu_arr.spec_index(cpu_id).view().killer_info() == pre.cpu_arr.spec_index(cpu_id).view().killer_info(),
        forall|other: CpuId| #![trigger post.cpu_op.view().view().spec_index(other as int)] index_valid(NUM_CPUS, other) && other != cpu_id ==>
            post.cpu_op.view().view().spec_index(other as int) == pre.cpu_op.view().view().spec_index(other as int),
        (post.cpu_op.view().view()[cpu_id as int] is User) == (pre.cpu_op.view().view()[cpu_id as int] is User),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thread),
        post.thrd_mp.spec_index(thread).being_killed() == pre.thrd_mp.spec_index(thread).being_killed(),
        post.thrd_mp.spec_index(thread).view() == (Thread { quota_4k, quota_2m, ..pre.thrd_mp.spec_index(thread).view() }),
    ensures
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let post_u = kernel_k_to_kernel_u(*post);
            post_u == (KernelU {
                cpu_array: pre_u.cpu_array.update(cpu_id as int, CpuU {
                    lock_state: post_u.cpu_array[cpu_id as int].lock_state, op: post_u.cpu_array[cpu_id as int].op, ..pre_u.cpu_array[cpu_id as int]
                }),
                thread_map: pre_u.thread_map.insert(thread, ThreadU { lock_state: post_u.thread_map[thread].lock_state, quota_4k, quota_2m, ..pre_u.thread_map[thread] }),
                ..pre_u
            })
        }),
{
    kernel_k_to_kernel_u_implies_domains_and_scalars_from_k(pre); kernel_k_to_kernel_u_implies_domains_and_scalars_from_k(post);
    kernel_cpu_projection_at(pre, cpu_id); kernel_cpu_projection_at(post, cpu_id);
    kernel_thread_projection_at(pre, thread); kernel_thread_projection_at(post, thread);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let cpu = pre_u.cpu_array[cpu_id as int];
    let t = pre_u.thread_map[thread];
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU {
        lock_state: post_u.cpu_array[cpu_id as int].lock_state, op: post_u.cpu_array[cpu_id as int].op, ..cpu
    }), i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread, ThreadU { lock_state: post_u.thread_map[thread].lock_state, quota_4k, quota_2m, ..t }),
        ptr => { if pre.thrd_mp.dom().contains(ptr) { kernel_thread_projection_at(pre, ptr); } if post.thrd_mp.dom().contains(ptr) { kernel_thread_projection_at(post, ptr); } thread_cpu_wf_thread_at(pre.thrd_mp, pre.cpu_arr, ptr); });
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
}
