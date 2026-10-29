use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;

verus! {
/// Write-locking and marking the cpu set of the container `container_ptr` changes only that container's cpu-set lock
/// mode and mark in the projection.
pub proof fn kernel_cpu_set_locked_and_marked_implies_u_step(before: &KernelK, after: &KernelK, container_ptr: RwLockContainerPtr)
    requires
        container_cpu_set_wf(before.ctn_mp, before.cpu_set_mp),
        *after == (KernelK { cpu_set_mp: after.cpu_set_mp, ..*before }),
        before.ctn_mp.dom().contains(container_ptr),
        after.cpu_set_mp.unchanged_except(&before.cpu_set_mp, before.ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set),
        after.cpu_set_mp.spec_index(before.ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set).locking_thread() is Write,
        after.cpu_set_mp.spec_index(before.ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set).being_killed(),
    ensures
        kernel_k_to_kernel_u(*before).container_map.dom().contains(container_ptr),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after) == (KernelU {
                container_map: pre.container_map.insert(container_ptr, ContainerU { cpu_set_lock: LockStateU::WriteLocked, cpu_set_killed: true, ..pre.container_map[container_ptr] }), ..pre
            })
        }),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    container_cpu_set_wf_container_at(before.ctn_mp, before.cpu_set_mp, container_ptr);
    assert_maps_equal!(post.container_map, pre.container_map.insert(container_ptr, ContainerU { cpu_set_lock: LockStateU::WriteLocked, cpu_set_killed: true, ..pre.container_map[container_ptr] }), c => {
        if before.ctn_mp.dom().contains(c) {
            kernel_container_projection_at(before, c); kernel_container_projection_at(after, c); container_cpu_set_wf_container_at(before.ctn_mp, before.cpu_set_mp, c);
        }
    });
    assert_seqs_equal!(post.cpu_array == pre.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(before, i as usize); kernel_cpu_projection_at(after, i as usize); } });
    assert_maps_equal!(post.process_map, pre.process_map, p => { if before.prc_mp.dom().contains(p) { kernel_process_projection_at(before, p); kernel_process_projection_at(after, p); } });
    assert_maps_equal!(post.thread_map, pre.thread_map, t => { if before.thr_mp.dom().contains(t) { kernel_thread_projection_at(before, t); kernel_thread_projection_at(after, t); } });
    assert_maps_equal!(post.endpoint_map, pre.endpoint_map, e => { if before.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(before, e); kernel_endpoint_projection_at(after, e); } });
}

/// Moving the cpu `cpu_id` from the container `source` to `target`, with every cpu-set lock mode and mark kept and the
/// offline request of `source` for that cpu cleared, changes only that cpu's owner and that request, so both
/// projections change.
pub proof fn kernel_cpu_moved_to_container_implies_u_step(before: &KernelK, after: &KernelK, cpu_id: CpuId, source: RwLockContainerPtr, target: RwLockContainerPtr)
    requires
        container_cpu_set_wf(before.ctn_mp, before.cpu_set_mp),
        container_cpu_offline_flags_wf(before.ctn_mp, before.cpu_offline_mp),
        *after == (KernelK { cpu_arr: after.cpu_arr, cpu_set_mp: after.cpu_set_mp, cpu_offline_mp: after.cpu_offline_mp, ..*before }),
        index_valid(NUM_CPUS, cpu_id),
        before.ctn_mp.dom().contains(source),
        source != target,
        forall|i: CpuId| #![trigger after.cpu_arr.spec_index(i)] index_valid(NUM_CPUS, i) && i != cpu_id ==> after.cpu_arr.spec_index(i) == before.cpu_arr.spec_index(i),
        before.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == source,
        after.cpu_arr.spec_index(cpu_id).view().view().view()
            == (CpuView { owning_container: target, container_depth: after.cpu_arr.spec_index(cpu_id).view().view().view().container_depth, ..before.cpu_arr.spec_index(cpu_id).view().view().view() }),
        after.cpu_arr.spec_index(cpu_id).view().lock_state_u() == before.cpu_arr.spec_index(cpu_id).view().lock_state_u(),
        after.cpu_arr.spec_index(cpu_id).view().being_killed() == before.cpu_arr.spec_index(cpu_id).view().being_killed(),
        after.cpu_set_mp.dom() == before.cpu_set_mp.dom(),
        forall|s: RwLockCpuSetPtr| #![trigger after.cpu_set_mp.spec_index(s)] before.cpu_set_mp.dom().contains(s)
            ==> after.cpu_set_mp.spec_index(s).lock_state_u() == before.cpu_set_mp.spec_index(s).lock_state_u() && after.cpu_set_mp.spec_index(s).being_killed() == before.cpu_set_mp.spec_index(s).being_killed(),
        after.cpu_offline_mp.unchanged_except(&before.cpu_offline_mp, cpu_offline_flags_ptr(source)),
        cpu_offline_requests_of(after.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(source)))
            == cpu_offline_requests_of(before.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(source))).update(cpu_id as int, false),
    ensures
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let container = pre.container_map[source];
            &&& pre.container_map.dom().contains(source)
            &&& container.cpu_offline_requests.len() == NUM_CPUS
            &&& kernel_k_to_kernel_u(*after) == (KernelU {
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { owning_container: target, ..pre.cpu_array[cpu_id as int] }),
                container_map: pre.container_map.insert(source, ContainerU { cpu_offline_requests: container.cpu_offline_requests.update(cpu_id as int, false), ..container }),
                ..pre
            })
        }),
        kernel_k_to_kernel_u(*before) != kernel_k_to_kernel_u(*after),
        kernel_k_to_nonlock_kernel_u(*before) != kernel_k_to_nonlock_kernel_u(*after),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    kernel_container_projection_at(before, source);
    container_cpu_offline_flags_wf_container_at(before.ctn_mp, before.cpu_offline_mp, source);
    let container = pre.container_map[source];
    assert(container.cpu_offline_requests.len() == NUM_CPUS) by { reveal(cpu_offline_requests_of); };
    assert_seqs_equal!(post.cpu_array == pre.cpu_array.update(cpu_id as int, CpuU { owning_container: target, ..pre.cpu_array[cpu_id as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(before, i as usize); kernel_cpu_projection_at(after, i as usize); }
    });
    assert_maps_equal!(post.container_map, pre.container_map.insert(source, ContainerU { cpu_offline_requests: container.cpu_offline_requests.update(cpu_id as int, false), ..container }), c => {
        if before.ctn_mp.dom().contains(c) {
            kernel_container_projection_at(before, c); kernel_container_projection_at(after, c); container_cpu_set_wf_container_at(before.ctn_mp, before.cpu_set_mp, c);
            container_cpu_offline_flags_wf_container_at(before.ctn_mp, before.cpu_offline_mp, c);
        }
    });
    assert_maps_equal!(post.process_map, pre.process_map, p => { if before.prc_mp.dom().contains(p) { kernel_process_projection_at(before, p); kernel_process_projection_at(after, p); } });
    assert_maps_equal!(post.thread_map, pre.thread_map, t => { if before.thr_mp.dom().contains(t) { kernel_thread_projection_at(before, t); kernel_thread_projection_at(after, t); } });
    assert_maps_equal!(post.endpoint_map, pre.endpoint_map, e => { if before.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(before, e); kernel_endpoint_projection_at(after, e); } });
    assert(post.cpu_array[cpu_id as int].owning_container != pre.cpu_array[cpu_id as int].owning_container) by { kernel_cpu_projection_at(before, cpu_id); kernel_cpu_projection_at(after, cpu_id); };
    kernel_nonlock_projection_is_u_nonlock_fields(*before); kernel_nonlock_projection_is_u_nonlock_fields(*after);
    assert(kernel_u_nonlock_fields(post).cpu_array[cpu_id as int].owning_container != kernel_u_nonlock_fields(pre).cpu_array[cpu_id as int].owning_container) by { reveal(kernel_u_nonlock_fields); };
}

/// With no cpu in the cpu set of the container `container_ptr`, no cpu of the projection belongs to that container.
pub proof fn kernel_container_without_cpus_implies_u(krnl: &KernelK, container_ptr: RwLockContainerPtr)
    requires
        container_cpu_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr),
        forall|i: CpuId| #![trigger krnl.cpu_set_mp.spec_index(krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set).view().owned_cpus.view().contains(i)]
            index_valid(NUM_CPUS, i) ==> !krnl.cpu_set_mp.spec_index(krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set).view().owned_cpus.view().contains(i),
    ensures
        forall|i: int| #![trigger kernel_k_to_kernel_u(*krnl).cpu_array[i]] 0 <= i < NUM_CPUS ==> kernel_k_to_kernel_u(*krnl).cpu_array[i].owning_container != container_ptr,
{
    let u = kernel_k_to_kernel_u(*krnl);
    let other: RwLockContainerPtr = if container_ptr == 0usize { 1usize } else { 0usize };
    kernel_u_domains_projection(krnl);
    assert_seqs_equal!(u.cpu_array == Seq::new(NUM_CPUS as nat, |i: int| if u.cpu_array[i].owning_container == container_ptr { CpuU { owning_container: other, ..u.cpu_array[i] } } else { u.cpu_array[i] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(krnl, i as usize); container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, i as usize); }
    });
}
}
