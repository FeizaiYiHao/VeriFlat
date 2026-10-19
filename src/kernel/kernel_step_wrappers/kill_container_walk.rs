use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;

verus! {
/// Write-locking and marking the unmarked container `container_ptr` changes only its lock mode and kill mark in the
/// projection.
pub proof fn kernel_container_locked_and_marked_implies_u_step(before: &KernelK, after: &KernelK, container_ptr: RwLockContainerPtr)
    requires
        *after == (KernelK { ctn_mp: after.ctn_mp, ..*before }),
        before.ctn_mp.dom().contains(container_ptr),
        after.ctn_mp.unchanged_except(&before.ctn_mp, container_ptr),
        after.ctn_mp.spec_index(container_ptr).view() == before.ctn_mp.spec_index(container_ptr).view(),
        after.ctn_mp.spec_index(container_ptr).view_rodata() == before.ctn_mp.spec_index(container_ptr).view_rodata(),
        after.ctn_mp.spec_index(container_ptr).view_ghost() == before.ctn_mp.spec_index(container_ptr).view_ghost(),
        after.ctn_mp.spec_index(container_ptr).locking_thread() is Write,
        after.ctn_mp.spec_index(container_ptr).being_killed(),
    ensures
        kernel_k_to_kernel_u(*before).container_map.dom().contains(container_ptr),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after) == (KernelU {
                container_map: pre.container_map.insert(container_ptr, ContainerU { lock_state: LockStateU::WriteLocked, killed: true, ..pre.container_map[container_ptr] }), ..pre
            })
        }),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    assert_maps_equal!(post.container_map, pre.container_map.insert(container_ptr, ContainerU { lock_state: LockStateU::WriteLocked, killed: true, ..pre.container_map[container_ptr] }), c => {
        if before.ctn_mp.dom().contains(c) { kernel_container_projection_at(before, c); kernel_container_projection_at(after, c); }
    });
    assert_seqs_equal!(post.cpu_array == pre.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(before, i as usize); kernel_cpu_projection_at(after, i as usize); } });
    assert_maps_equal!(post.process_map, pre.process_map, p => {
        if before.prc_mp.dom().contains(p) { kernel_process_projection_at(before, p); kernel_process_projection_at(after, p); }
    });
    assert_maps_equal!(post.thread_map, pre.thread_map, t => {
        if before.thr_mp.dom().contains(t) { kernel_thread_projection_at(before, t); kernel_thread_projection_at(after, t); }
    });
    assert_maps_equal!(post.endpoint_map, pre.endpoint_map, e => {
        if before.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(before, e); kernel_endpoint_projection_at(after, e); }
    });
    reveal(kernel_k_to_kernel_u);
}
}
