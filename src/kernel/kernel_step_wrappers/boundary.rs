use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;
#[cfg(verus_keep_ghost)]
use crate::kernel::kernel_step_spec::kernel_u_new_thread_changed;

verus! {
pub(super) proof fn kernel_thread_quota_4k_changed_implies_u_neq(pre: &KernelK, post: &KernelK, thrd_ptr: RwLockThreadPtr, delta: int)
    requires
        delta != 0,
        kernel_thread_quota_4k_changed(pre, post, thrd_ptr, delta),
    ensures kernel_k_to_kernel_u(*pre) != kernel_k_to_kernel_u(*post),
{
    assert(kernel_k_to_kernel_u(*pre).thread_map.spec_index(thrd_ptr).quota_4k != kernel_k_to_kernel_u(*post).thread_map.spec_index(thrd_ptr).quota_4k) by {
        reveal(kernel_thread_quota_4k_changed); kernel_thread_projection_at(pre, thrd_ptr); kernel_thread_projection_at(post, thrd_ptr);
    };
}

pub(super) proof fn kernel_process_quota_4k_changed_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, delta: int)
    requires
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        process_iommu_table_wf(post.prc_mp, post.it_mp),
        kernel_process_quota_4k_changed(pre, post, cpu_id, prc_ptr, ctn_ptr, delta),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        kernel_u_only_process_quota_4k_changed(kernel_k_user_projection(*pre), kernel_k_user_projection(*post), cpu_id, prc_ptr, ctn_ptr, delta),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_only_process_quota_4k_changed); reveal(kernel_process_quota_4k_changed); reveal(kernel_endpoint_nonlock_fields_unchanged);
    kernel_u_user_domains_projection(pre); kernel_u_user_domains_projection(post);
    kernel_cpu_user_projection_at(pre, cpu_id); kernel_container_user_projection_at(pre, ctn_ptr); kernel_process_user_projection_at(pre, prc_ptr);
    let pre_u = kernel_k_user_projection(*pre);
    let post_u = kernel_k_user_projection(*post);
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(IommuRootTable::user_view); };
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, i as usize); kernel_cpu_user_projection_at(post, i as usize); } });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map, t => { if pre.thrd_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_user_projection_at(post, t); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, e); } });
    kernel_process_quota_4k_changed_implies_u_container_map(pre, post, cpu_id, prc_ptr, ctn_ptr, delta);
    kernel_process_quota_4k_changed_implies_u_process_map(pre, post, cpu_id, prc_ptr, ctn_ptr, delta);
}

/// Moving `delta` 4K quota from a container to its running process lowers only that container's quota in the
/// container projection.
proof fn kernel_process_quota_4k_changed_implies_u_container_map(pre: &KernelK, post: &KernelK, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, delta: int)
    requires
        kernel_process_quota_4k_changed(pre, post, cpu_id, prc_ptr, ctn_ptr, delta),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre);
            let container = pre_u.container_map.spec_index(ctn_ptr);
            kernel_k_user_projection(*post).container_map == pre_u.container_map.insert(ctn_ptr, ContainerU { quota_4k: (container.quota_4k as int - delta) as usize, ..container })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_process_quota_4k_changed);
    kernel_u_user_domains_projection(pre); kernel_u_user_domains_projection(post);
    let pre_u = kernel_k_user_projection(*pre);
    let post_u = kernel_k_user_projection(*post);
    let container = pre_u.container_map.spec_index(ctn_ptr);
    assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(ctn_ptr, ContainerU {
        quota_4k: (container.quota_4k as int - delta) as usize, ..container
    }), c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, c); } });
}

/// Moving `delta` 4K quota from a container to its running process raises only that process's quota in the
/// process projection.
proof fn kernel_process_quota_4k_changed_implies_u_process_map(pre: &KernelK, post: &KernelK, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, delta: int)
    requires
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        process_iommu_table_wf(post.prc_mp, post.it_mp),
        kernel_process_quota_4k_changed(pre, post, cpu_id, prc_ptr, ctn_ptr, delta),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre);
            let process = pre_u.process_map.spec_index(prc_ptr);
            kernel_k_user_projection(*post).process_map == pre_u.process_map.insert(prc_ptr, ProcessU { quota_4k: (process.quota_4k as int + delta) as usize, ..process })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_process_quota_4k_changed);
    kernel_u_user_domains_projection(pre); kernel_u_user_domains_projection(post);
    let pre_u = kernel_k_user_projection(*pre);
    let post_u = kernel_k_user_projection(*post);
    let process = pre_u.process_map.spec_index(prc_ptr);
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(prc_ptr, ProcessU {
        quota_4k: (process.quota_4k as int + delta) as usize, ..process
    }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_user_projection_at(post, p); }
        reveal(process_pagetable_wf); reveal(process_iommu_table_wf);
    });
}

pub(super) proof fn kernel_process2thread_quota_4k_changed_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, delta: int)
    requires kernel_process2thread_quota_4k_changed(pre, post, cpu_id, prc_ptr, thrd_ptr, delta),
    ensures
        kernel_u_only_process2thread_quota_4k_changed(kernel_k_user_projection(*pre), kernel_k_user_projection(*post), cpu_id, prc_ptr, thrd_ptr, delta),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_only_process2thread_quota_4k_changed); reveal(kernel_process2thread_quota_4k_changed);
    kernel_u_user_domains_projection(pre); kernel_u_user_domains_projection(post);
    kernel_cpu_user_projection_at(pre, cpu_id); kernel_process_user_projection_at(pre, prc_ptr); kernel_thread_user_projection_at(pre, thrd_ptr);
    let pre_u = kernel_k_user_projection(*pre);
    let post_u = kernel_k_user_projection(*post);
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, i as usize); kernel_cpu_user_projection_at(post, i as usize); } });
    let process = pre_u.process_map.spec_index(prc_ptr);
    let thread = pre_u.thread_map.spec_index(thrd_ptr);
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thrd_ptr, ThreadU {
        quota_4k: (thread.quota_4k as int + delta) as usize, ..thread
    }), t => { if pre.thrd_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_user_projection_at(post, t); } });
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(prc_ptr, ProcessU {
        quota_4k: (process.quota_4k as int - delta) as usize, ..process
    }), p => { if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_user_projection_at(post, p); } });
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, c); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, e); } });
}

pub(super) proof fn kernel_process_quota_2m_changed_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, delta: int)
    requires
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        process_iommu_table_wf(post.prc_mp, post.it_mp),
        kernel_process_quota_2m_changed(pre, post, cpu_id, prc_ptr, ctn_ptr, delta),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        kernel_u_only_process_quota_2m_changed(kernel_k_user_projection(*pre), kernel_k_user_projection(*post), cpu_id, prc_ptr, ctn_ptr, delta),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_only_process_quota_2m_changed); reveal(kernel_process_quota_2m_changed); reveal(kernel_endpoint_nonlock_fields_unchanged);
    kernel_u_user_domains_projection(pre); kernel_u_user_domains_projection(post);
    kernel_cpu_user_projection_at(pre, cpu_id); kernel_container_user_projection_at(pre, ctn_ptr); kernel_process_user_projection_at(pre, prc_ptr);
    let pre_u = kernel_k_user_projection(*pre);
    let post_u = kernel_k_user_projection(*post);
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(IommuRootTable::user_view); };
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, i as usize); kernel_cpu_user_projection_at(post, i as usize); } });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map, t => { if pre.thrd_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_user_projection_at(post, t); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, e); } });
    kernel_process_quota_2m_changed_implies_u_container_map(pre, post, cpu_id, prc_ptr, ctn_ptr, delta);
    kernel_process_quota_2m_changed_implies_u_process_map(pre, post, cpu_id, prc_ptr, ctn_ptr, delta);
}

/// Moving `delta` 2M quota from a container to its running process lowers only that container's quota in the
/// container projection.
proof fn kernel_process_quota_2m_changed_implies_u_container_map(pre: &KernelK, post: &KernelK, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, delta: int)
    requires
        kernel_process_quota_2m_changed(pre, post, cpu_id, prc_ptr, ctn_ptr, delta),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre);
            let container = pre_u.container_map.spec_index(ctn_ptr);
            kernel_k_user_projection(*post).container_map == pre_u.container_map.insert(ctn_ptr, ContainerU { quota_2m: (container.quota_2m as int - delta) as usize, ..container })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_process_quota_2m_changed);
    kernel_u_user_domains_projection(pre); kernel_u_user_domains_projection(post);
    let pre_u = kernel_k_user_projection(*pre);
    let post_u = kernel_k_user_projection(*post);
    let container = pre_u.container_map.spec_index(ctn_ptr);
    assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(ctn_ptr, ContainerU {
        quota_2m: (container.quota_2m as int - delta) as usize, ..container
    }), c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, c); } });
}

/// Moving `delta` 2M quota from a container to its running process raises only that process's quota in the
/// process projection.
proof fn kernel_process_quota_2m_changed_implies_u_process_map(pre: &KernelK, post: &KernelK, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, delta: int)
    requires
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        process_iommu_table_wf(post.prc_mp, post.it_mp),
        kernel_process_quota_2m_changed(pre, post, cpu_id, prc_ptr, ctn_ptr, delta),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre);
            let process = pre_u.process_map.spec_index(prc_ptr);
            kernel_k_user_projection(*post).process_map == pre_u.process_map.insert(prc_ptr, ProcessU { quota_2m: (process.quota_2m as int + delta) as usize, ..process })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_process_quota_2m_changed);
    kernel_u_user_domains_projection(pre); kernel_u_user_domains_projection(post);
    let pre_u = kernel_k_user_projection(*pre);
    let post_u = kernel_k_user_projection(*post);
    let process = pre_u.process_map.spec_index(prc_ptr);
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(prc_ptr, ProcessU {
        quota_2m: (process.quota_2m as int + delta) as usize, ..process
    }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_user_projection_at(post, p); }
        reveal(process_pagetable_wf); reveal(process_iommu_table_wf);
    });
}

pub(super) proof fn kernel_process2thread_quota_2m_changed_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, delta: int)
    requires kernel_process2thread_quota_2m_changed(pre, post, cpu_id, prc_ptr, thrd_ptr, delta),
    ensures
        kernel_u_only_process2thread_quota_2m_changed(kernel_k_user_projection(*pre), kernel_k_user_projection(*post), cpu_id, prc_ptr, thrd_ptr, delta),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_only_process2thread_quota_2m_changed); reveal(kernel_process2thread_quota_2m_changed);
    kernel_u_user_domains_projection(pre); kernel_u_user_domains_projection(post);
    kernel_cpu_user_projection_at(pre, cpu_id); kernel_process_user_projection_at(pre, prc_ptr); kernel_thread_user_projection_at(pre, thrd_ptr);
    let pre_u = kernel_k_user_projection(*pre);
    let post_u = kernel_k_user_projection(*post);
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, i as usize); kernel_cpu_user_projection_at(post, i as usize); } });
    let process = pre_u.process_map.spec_index(prc_ptr);
    let thread = pre_u.thread_map.spec_index(thrd_ptr);
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thrd_ptr, ThreadU {
        quota_2m: (thread.quota_2m as int + delta) as usize, ..thread
    }), t => { if pre.thrd_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_user_projection_at(post, t); } });
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(prc_ptr, ProcessU {
        quota_2m: (process.quota_2m as int - delta) as usize, ..process
    }), p => { if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_user_projection_at(post, p); } });
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, c); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, e); } });
}

/// K→U: setting one request bit of the caller container's table changes only that
/// `ContainerU.cpu_offline_requests` entry.
pub(super) proof fn kernel_cpu_offline_request_changed_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, target: CpuId)
    requires
        kernel_cpu_offline_request_changed(pre, post, cpu_id, ctn_ptr, target),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        kernel_u_cpu_offline_request_changed(kernel_k_user_projection(*pre), kernel_k_user_projection(*post), cpu_id, ctn_ptr, target),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_cpu_offline_request_changed); reveal(kernel_cpu_offline_request_changed);
    reveal(container_cpu_set_wf); reveal(container_cpu_offline_flags_wf);
    kernel_u_user_domains_projection(pre); kernel_u_user_domains_projection(post);
    kernel_cpu_user_projection_at(pre, cpu_id); kernel_cpu_user_projection_at(pre, target);
    kernel_container_user_projection_at(pre, ctn_ptr); kernel_container_user_projection_at(pre, pre.cpu_arr.spec_index(cpu_id).value.view().view().owning_container);
    let pre_u = kernel_k_user_projection(*pre);
    let post_u = kernel_k_user_projection(*post);
    let container = pre_u.container_map.spec_index(ctn_ptr);
    assert(container.cpu_offline_requests.len() == NUM_CPUS && !container.cpu_offline_requests[target as int]) by { reveal(cpu_offline_requests_of); };
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, i as usize); kernel_cpu_user_projection_at(post, i as usize); } });
    kernel_cpu_offline_request_changed_implies_u_container_map(pre, post, cpu_id, ctn_ptr, target);
    assert(post_u.thread_map == pre_u.thread_map && post_u.endpoint_map == pre_u.endpoint_map && post_u.process_map == pre_u.process_map) by {
        reveal(kernel_k_to_kernel_u); kernel_thread_map_unchanged_implies_u_thread_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post); kernel_process_maps_unchanged_implies_u_process_map(pre, post);
    };
}

/// K→U: setting one request bit of the caller container's table changes only that container's `cpu_offline_requests`
/// in the container projection.
proof fn kernel_cpu_offline_request_changed_implies_u_container_map(pre: &KernelK, post: &KernelK, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, target: CpuId)
    requires
        kernel_cpu_offline_request_changed(pre, post, cpu_id, ctn_ptr, target),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre);
            let container = pre_u.container_map.spec_index(ctn_ptr);
            kernel_k_user_projection(*post).container_map == pre_u.container_map.insert(ctn_ptr, ContainerU {
                cpu_offline_requests: container.cpu_offline_requests.update(target as int, true), ..container
            })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_cpu_offline_request_changed); reveal(container_cpu_set_wf); reveal(container_cpu_offline_flags_wf);
    kernel_u_user_domains_projection(pre); kernel_u_user_domains_projection(post);
    let pre_u = kernel_k_user_projection(*pre);
    let post_u = kernel_k_user_projection(*post);
    let container = pre_u.container_map.spec_index(ctn_ptr);
    assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(ctn_ptr, ContainerU {
        cpu_offline_requests: container.cpu_offline_requests.update(target as int, true), ..container
    }), c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, c); } });
}

/// K→U: publishing Idle on an Off cpu changes only that `CpuU.state`.
pub(super) proof fn kernel_cpu_online_changed_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, target: CpuId)
    requires
        kernel_cpu_online_changed(pre, post, cpu_id, ctn_ptr, target),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        kernel_u_cpu_online_changed(kernel_k_user_projection(*pre), kernel_k_user_projection(*post), cpu_id, ctn_ptr, target),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_cpu_online_changed); reveal(kernel_cpu_online_changed); reveal(container_cpu_set_wf);
    kernel_u_user_domains_projection(pre); kernel_u_user_domains_projection(post);
    kernel_cpu_user_projection_at(pre, cpu_id); kernel_cpu_user_projection_at(pre, target);
    kernel_container_user_projection_at(pre, ctn_ptr); kernel_container_user_projection_at(pre, pre.cpu_arr.spec_index(cpu_id).value.view().view().owning_container);
    let pre_u = kernel_k_user_projection(*pre);
    let post_u = kernel_k_user_projection(*post);
    let target_cpu = pre_u.cpu_array[target as int];
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(target as int, CpuU { state: CpuState::Idle, op: CpuOpState::Idle, ..target_cpu }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, i as usize); kernel_cpu_user_projection_at(post, i as usize); }
    });
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, c); } });
    assert(post_u.thread_map == pre_u.thread_map && post_u.endpoint_map == pre_u.endpoint_map && post_u.process_map == pre_u.process_map) by {
        reveal(kernel_k_to_kernel_u); kernel_thread_map_unchanged_implies_u_thread_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post); kernel_process_maps_unchanged_implies_u_process_map(pre, post);
    };
}

pub(super) proof fn kernel_cpu_went_off_fields_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, regs: Registers, flushed_default_pcid: bool)
    requires
        post.inv(),
        kernel_cpu_went_off_fields(pre, post, cpu_id, regs, flushed_default_pcid),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        kernel_u_cpu_went_off_changed(kernel_k_user_projection(*pre), kernel_k_user_projection(*post), cpu_id, regs, flushed_default_pcid),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_cpu_went_off_changed); reveal(kernel_cpu_went_off_fields);
    kernel_u_user_domains_projection(pre); kernel_u_user_domains_projection(post); kernel_cpu_user_projection_at(pre, cpu_id);
    let pre_u = kernel_k_user_projection(*pre);
    let post_u = kernel_k_user_projection(*post);
    let cpu = pre_u.cpu_array[cpu_id as int];
    let container = pre_u.container_map.spec_index(cpu.owning_container);
    let k_cpu = pre.cpu_arr.spec_index(cpu_id).value.view().view();
    kernel_container_user_projection_at(pre, k_cpu.owning_container);
    if let Some(t) = k_cpu.current_thread { kernel_thread_user_projection_at(pre, t); kernel_process_user_projection_at(pre, k_cpu.current_process.unwrap()); }
    assert(container.cpu_offline_requests.len() == NUM_CPUS) by { reveal(cpu_offline_requests_of); };
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(IommuRootTable::user_view); };
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, state: CpuState::Off, op: CpuOpState::Off, current_process: None, current_thread: None, ..cpu }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, i as usize); kernel_cpu_user_projection_at(post, i as usize); }
    });
    kernel_endpoint_nonlock_fields_and_locks_unchanged_implies_u_endpoint_map(pre, post);
    kernel_process_nonlock_fields_and_locks_unchanged_implies_u_process_map(pre, post);
    kernel_cpu_went_off_fields_implies_u_container_map(pre, post, cpu_id, regs, flushed_default_pcid);
    kernel_cpu_went_off_fields_implies_u_thread_map(pre, post, cpu_id, regs, flushed_default_pcid);
}

pub(super) proof fn kernel_process_added_implies_u_neq(pre: &KernelK, post: &KernelK, prc_ptr: RwLockProcessPtr)
    requires kernel_process_added(pre, post, prc_ptr),
    ensures
        kernel_k_to_kernel_u(*pre) != kernel_k_to_kernel_u(*post),
{ reveal(kernel_process_added); reveal(kernel_k_to_kernel_u); }

pub proof fn kernel_process_4k_mapping_changed_implies_u_neq(pre: &KernelK, post: &KernelK, prc_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires kernel_process_4k_mapping_changed(pre, post, prc_ptr, pagetable_ptr, va),
    ensures kernel_k_to_kernel_u(*pre) != kernel_k_to_kernel_u(*post),
{
    assert(kernel_k_to_kernel_u(*pre).process_map.spec_index(prc_ptr).pagetable.unwrap().mapping_4k.dom().contains(va) != kernel_k_to_kernel_u(*post).process_map.spec_index(prc_ptr).pagetable.unwrap().mapping_4k.dom().contains(va)) by {
        reveal(kernel_process_4k_mapping_changed); reveal(kernel_k_to_kernel_u);
    };
}

/// A section that changes only cpu state, TLBs, needflush flags, and page-table ghost state that keeps every table's lock
/// mode and mappings changes only the TLB projection.
pub proof fn kernel_cpu_tlb_updated_implies_u_step(pre: &KernelK, post: &KernelK)
    requires
        *post == (KernelK { cpu_arr: post.cpu_arr, cpu_tlb: post.cpu_tlb, pcid_needflush: post.pcid_needflush, pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..*pre }),
        kernel_cpu_nonlock_fields_unchanged(pre.cpu_arr, post.cpu_arr),
        forall|cpu: CpuId| #![trigger post.cpu_arr.spec_index(cpu)] index_valid(NUM_CPUS, cpu) ==>
            post.cpu_arr.spec_index(cpu).value.locking_thread() == pre.cpu_arr.spec_index(cpu).value.locking_thread(),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        post.pt_mp.dom() == pre.pt_mp.dom(),
        forall|pt: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(pt)] pre.pt_mp.dom().contains(pt) ==> {
            &&& post.pt_mp.spec_index(pt).locking_thread() == pre.pt_mp.spec_index(pt).locking_thread()
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pt).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt).mapping_4k()
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pt).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt).mapping_2m()
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pt).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt).mapping_1g()
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pt).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt).lower.pagetable_window_locks
        },
    ensures
        kernel_k_to_kernel_u(*post) == (KernelU { cpu_tlb: post.cpu_tlb.view(), ..kernel_k_to_kernel_u(*pre) }),
{
    reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_k_to_kernel_u);
    assert_seqs_equal!(kernel_k_to_kernel_u(*post).cpu_array == kernel_k_to_kernel_u(*pre).cpu_array);
    assert_maps_equal!(kernel_k_to_kernel_u(*post).process_map, kernel_k_to_kernel_u(*pre).process_map, p => { reveal(process_pagetable_wf); });
}

pub proof fn kernel_container_quota_4k_changed_implies_u_step(pre: &KernelK, post: &KernelK, container: RwLockContainerPtr, delta: int)
    requires
        kernel_container_quota_4k_changed(pre, post, container, delta),
        delta > 0,
    ensures
        kernel_k_to_kernel_u(*pre).container_map.dom().contains(container),
        kernel_k_to_kernel_u(*post).container_map[container].quota_4k as int == kernel_k_to_kernel_u(*pre).container_map[container].quota_4k as int + delta,
        kernel_k_to_kernel_u(*post) == (KernelU {
            container_map: kernel_k_to_kernel_u(*pre).container_map.insert(container, ContainerU {
                quota_4k: (kernel_k_to_kernel_u(*pre).container_map[container].quota_4k as int + delta) as usize,
                ..kernel_k_to_kernel_u(*pre).container_map[container]
            }), ..kernel_k_to_kernel_u(*pre)
        }),
{
    reveal(kernel_container_quota_4k_changed); kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(kernel_thread_nonlock_fields_unchanged);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    if pre.ctn_mp.dom().contains(container) { kernel_container_projection_at(pre, container); } if post.ctn_mp.dom().contains(container) { kernel_container_projection_at(post, container); }
    assert_maps_equal!(after.container_map, before.container_map.insert(container, ContainerU {
        quota_4k: (before.container_map[container].quota_4k as int + delta) as usize, ..before.container_map[container]
    }), c => { if pre.ctn_mp.dom().contains(c) { kernel_container_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_projection_at(post, c); } });
    assert_maps_equal!(after.thread_map, before.thread_map, t => {
        if pre.thrd_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_projection_at(post, t); }
    });
    assert_seqs_equal!(after.cpu_array == before.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(after.process_map, before.process_map, p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
    });
    assert_maps_equal!(after.endpoint_map, before.endpoint_map, p => {
        if pre.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(pre, p); } if post.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(post, p); }
    });
}

/// Clearing one present 4K entry and replacing one thread's progress removes that VA from the
/// owning process's user mapping and changes only that thread's progress.
pub proof fn kernel_pagetable_4k_present_cleared_and_progress_changed_implies_u_step(pre: &KernelK, post: &KernelK, pagetable: RwLockPageTableRoot, va: VAddr, thrd_ptr: RwLockThreadPtr)
    requires
        process_pagetable_wf(pre.prc_mp, pre.pt_mp),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        pre.pt_mp.dom().contains(pagetable),
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, thrd_mp: post.thrd_mp, ..*pre }),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable)),
        post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread(),
        post.pt_mp.spec_index(pagetable).view().proc_ptr == pre.pt_mp.spec_index(pagetable).view().proc_ptr,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k()[va].present,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().insert(va, MapEntry { present: false, ..whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k()[va] }),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks,
        pre.thrd_mp.dom().contains(thrd_ptr),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..pre.thrd_mp.spec_index(thrd_ptr).view() }),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() == pre.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        !pre.prc_mp.spec_index(pre.pt_mp.spec_index(pagetable).view().proc_ptr).view().zombie,
    ensures
        {
            let before = kernel_k_to_kernel_u(*pre);
            let process = pre.pt_mp.spec_index(pagetable).view().proc_ptr;
            &&& before.process_map.dom().contains(process)
            &&& before.process_map[process].pagetable is Some
            &&& before.process_map[process].pagetable->Some_0.mapping_4k.dom().contains(va)
            &&& before.thread_map.dom().contains(thrd_ptr)
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                process_map: before.process_map.insert(process, ProcessU {
                    pagetable: Some(PageTableU { mapping_4k: before.process_map[process].pagetable->Some_0.mapping_4k.remove(va), ..before.process_map[process].pagetable->Some_0 }),
                    ..before.process_map[process]
                }),
                thread_map: before.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), ..before.thread_map[thrd_ptr] }),
                ..before
            })
        },
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(process_pagetable_wf);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    let process = pre.pt_mp.spec_index(pagetable).view().proc_ptr;
    if pre.prc_mp.dom().contains(process) { kernel_process_projection_at(pre, process); } if post.prc_mp.dom().contains(process) { kernel_process_projection_at(post, process); }
    if pre.thrd_mp.dom().contains(thrd_ptr) { kernel_thread_projection_at(pre, thrd_ptr); }
    assert_maps_equal!(after.process_map[process].pagetable->Some_0.mapping_4k, before.process_map[process].pagetable->Some_0.mapping_4k.remove(va), a => {});
    assert_maps_equal!(after.process_map, before.process_map.insert(process, ProcessU {
        pagetable: Some(PageTableU { mapping_4k: before.process_map[process].pagetable->Some_0.mapping_4k.remove(va), ..before.process_map[process].pagetable->Some_0 }),
        ..before.process_map[process]
    }), p => { if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } });
    assert_maps_equal!(after.thread_map, before.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), ..before.thread_map[thrd_ptr] }), t => {
        if pre.thrd_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_projection_at(post, t); }
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_container_maps_unchanged_implies_u_container_map(pre, post);
    kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

/// Clearing one present 4K entry of an IOMMU table removes that IOVA from the owning process's user IOMMU mapping and
/// changes nothing else in the complete projection.
pub proof fn kernel_iommu_table_4k_present_cleared_implies_u_step(pre: &KernelK, post: &KernelK, iommu_table: RwLockPageTableRoot, iova: VAddr)
    requires
        process_iommu_table_wf(pre.prc_mp, pre.it_mp),
        pre.it_mp.dom().contains(iommu_table),
        *post == (KernelK { it_mp: post.it_mp, ..*pre }),
        post.it_mp.unchanged_except(&pre.it_mp, iommu_table),
        post.it_mp.spec_index(iommu_table).locking_thread() == pre.it_mp.spec_index(iommu_table).locking_thread(),
        post.it_mp.spec_index(iommu_table).view().proc_ptr == pre.it_mp.spec_index(iommu_table).view().proc_ptr,
        pre.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(iova),
        pre.it_mp.spec_index(iommu_table).view().mapping_4k()[iova].present,
        post.it_mp.spec_index(iommu_table).view().mapping_4k() == pre.it_mp.spec_index(iommu_table).view().mapping_4k().insert(iova, MapEntry { present: false, ..pre.it_mp.spec_index(iommu_table).view().mapping_4k()[iova] }),
        post.it_mp.spec_index(iommu_table).view().mapping_2m() == pre.it_mp.spec_index(iommu_table).view().mapping_2m(),
        post.it_mp.spec_index(iommu_table).view().mapping_1g() == pre.it_mp.spec_index(iommu_table).view().mapping_1g(),
        post.it_mp.spec_index(iommu_table).view().did == pre.it_mp.spec_index(iommu_table).view().did,
        !pre.prc_mp.spec_index(pre.it_mp.spec_index(iommu_table).view().proc_ptr).view().zombie,
    ensures
        ({
            let before = kernel_k_to_kernel_u(*pre);
            let process = pre.it_mp.spec_index(iommu_table).view().proc_ptr;
            &&& before.process_map.dom().contains(process)
            &&& before.process_map[process].iommu_table is Some
            &&& before.process_map[process].iommu_table->Some_0.mapping_4k.dom().contains(iova)
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                process_map: before.process_map.insert(process, ProcessU {
                    iommu_table: Some(PageTableU { mapping_4k: before.process_map[process].iommu_table->Some_0.mapping_4k.remove(iova), ..before.process_map[process].iommu_table->Some_0 }),
                    ..before.process_map[process]
                }),
                ..before
            })
        }),
        kernel_k_to_kernel_u(*pre) != kernel_k_to_kernel_u(*post),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(process_iommu_table_wf);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    let process = pre.it_mp.spec_index(iommu_table).view().proc_ptr;
    kernel_process_projection_at(pre, process); kernel_process_projection_at(post, process);
    assert_maps_equal!(after.process_map[process].iommu_table->Some_0.mapping_4k, before.process_map[process].iommu_table->Some_0.mapping_4k.remove(iova), a => {});
    assert_maps_equal!(after.process_map, before.process_map.insert(process, ProcessU {
        iommu_table: Some(PageTableU { mapping_4k: before.process_map[process].iommu_table->Some_0.mapping_4k.remove(iova), ..before.process_map[process].iommu_table->Some_0 }),
        ..before.process_map[process]
    }), p => { if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } });
    kernel_thread_map_unchanged_implies_u_thread_map(pre, post); kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post);
    kernel_container_maps_unchanged_implies_u_container_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
    assert(!after.process_map[process].iommu_table->Some_0.mapping_4k.dom().contains(iova));
}

/// Replacing one thread's progress changes only that thread's progress in the complete projection.
pub proof fn kernel_thread_syscall_progress_changed_implies_u_step(pre: &KernelK, post: &KernelK, thrd_ptr: RwLockThreadPtr)
    requires
        *post == (KernelK { thrd_mp: post.thrd_mp, ..*pre }),
        pre.thrd_mp.dom().contains(thrd_ptr),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..pre.thrd_mp.spec_index(thrd_ptr).view() }),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() == pre.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
    ensures
        kernel_k_to_kernel_u(*pre).thread_map.dom().contains(thrd_ptr),
        kernel_k_to_kernel_u(*post) == (KernelU {
            thread_map: kernel_k_to_kernel_u(*pre).thread_map.insert(thrd_ptr, ThreadU {
                syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), ..kernel_k_to_kernel_u(*pre).thread_map[thrd_ptr]
            }),
            ..kernel_k_to_kernel_u(*pre)
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    assert_maps_equal!(after.thread_map, before.thread_map.insert(thrd_ptr, ThreadU {
        syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), ..before.thread_map[thrd_ptr]
    }), t => { if pre.thrd_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_projection_at(post, t); } });
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_container_maps_unchanged_implies_u_container_map(pre, post);
    kernel_process_maps_unchanged_implies_u_process_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

/// A section that changes only one thread's quota, temporary cache, and progress plus the
/// kernel-only structure of one pagetable changes only that thread's quota and progress and,
/// for a visible process, that pagetable's window locks in the complete projection. `lctx` is
/// aligned with `post` and write-holds the cpu, thread, and pagetable across the section.
#[verifier::spinoff_prover]
pub proof fn kernel_thread_quota_4k_and_progress_changed_implies_u_step(pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot)
    requires
        process_cpu_wf(pre.prc_mp, pre.cpu_arr),
        process_pagetable_wf(pre.prc_mp, pre.pt_mp),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(post, lctx),
        pre.thrd_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        pre.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, pg_arr: post.pg_arr, thrd_mp: post.thrd_mp, ..*pre }),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread {
            quota_4k: post.thrd_mp.spec_index(thrd_ptr).view().quota_4k,
            temp_alloc_cache_4k: post.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k,
            syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress,
            ..pre.thrd_mp.spec_index(thrd_ptr).view()
        }),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        pre.prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, post.pt_lower.view().spec_index(pagetable_ptr)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g(),
    ensures
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let thread = pre.thrd_mp.spec_index(thrd_ptr).view();
            let process = pre_u.process_map.spec_index(prc_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& pre_u.cpu_array[cpu_id as int].current_thread == pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread
            &&& pre_u.thread_map.dom().contains(thrd_ptr)
            &&& pre_u.thread_map.spec_index(thrd_ptr).lock_state is WriteLocked
            &&& pre_u.thread_map.spec_index(thrd_ptr).owning_proc == thread.owning_proc
            &&& pre_u.thread_map.spec_index(thrd_ptr).quota_4k == thread.quota_4k
            &&& pre_u.thread_map.spec_index(thrd_ptr).syscall_progress == thread.syscall_progress.view()
            &&& pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr) ==> {
                &&& pre_u.process_map.dom().contains(prc_ptr)
                &&& process.pagetable is Some
                &&& process.pagetable->Some_0.lock_state is WriteLocked
            }
        }),
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let owner = pre.pt_mp.spec_index(pagetable_ptr).view().proc_ptr;
            kernel_k_to_kernel_u(*post) == (KernelU {
                thread_map: pre_u.thread_map.insert(thrd_ptr, ThreadU {
                    quota_4k: post.thrd_mp.spec_index(thrd_ptr).view().quota_4k,
                    syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(),
                    ..pre_u.thread_map.spec_index(thrd_ptr)
                }),
                process_map: if pre_u.process_map.dom().contains(owner) && pre_u.process_map[owner].pagetable is Some {
                    pre_u.process_map.insert(owner, ProcessU {
                        pagetable: Some(PageTableU {
                            pagetable_window_locks: whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, ..pre_u.process_map[owner].pagetable->Some_0
                        }),
                        ..pre_u.process_map[owner]
                    })
                } else { pre_u.process_map },
                ..pre_u
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    pre.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr);
    post.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr);
    pre.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
    post.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
    kernel_cpu_projection_at(pre, cpu_id); kernel_cpu_projection_at(post, cpu_id);
    if pre.prc_mp.dom().contains(prc_ptr) { kernel_process_projection_at(pre, prc_ptr); }
    if pre.thrd_mp.dom().contains(thrd_ptr) { kernel_thread_projection_at(pre, thrd_ptr); }
    assert(pre.cpu_arr.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    assert(pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr)
        ==> pre.prc_mp.dom().contains(prc_ptr) && !pre.prc_mp.spec_index(prc_ptr).view().zombie && pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr) by {
        reveal(process_cpu_wf); reveal(process_pagetable_wf);
    };
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_container_maps_unchanged_implies_u_container_map(pre, post);
    let owner = pre.pt_mp.spec_index(pagetable_ptr).view().proc_ptr;
    if pre_u.process_map.dom().contains(owner) && pre_u.process_map[owner].pagetable is Some {
        assert(pre.prc_mp.spec_index(owner).view().pagetable == pagetable_ptr) by { reveal(process_pagetable_wf); };
        assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(owner, ProcessU {
            pagetable: Some(PageTableU { pagetable_window_locks: whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, ..pre_u.process_map[owner].pagetable->Some_0 }),
            ..pre_u.process_map[owner]
        }), p => {
            if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } reveal(process_pagetable_wf);
        });
    } else {
        assert_maps_equal!(post_u.process_map, pre_u.process_map, p => {
            if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } reveal(process_pagetable_wf);
        });
    }
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thrd_ptr, ThreadU {
        quota_4k: post.thrd_mp.spec_index(thrd_ptr).view().quota_4k,
        syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(),
        ..pre_u.thread_map.spec_index(thrd_ptr)
    }), t => { if pre.thrd_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_projection_at(post, t); } });
    kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

/// Setting the cpu, thread, and pagetable lock modes to the thread's mode and replacing the
/// thread's progress changes only those three projections. `lctx` is aligned with `pre`; the
/// objects it write-holds project as write-locked before the section.
#[verifier::spinoff_prover]
pub proof fn kernel_cpu_thread_pagetable_lock_states_and_progress_changed_implies_u_step(pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot)
    requires
        process_cpu_wf(pre.prc_mp, pre.cpu_arr),
        process_pagetable_wf(pre.prc_mp, pre.pt_mp),
        typed_lock_maps_aligned(pre, lctx),
        index_valid(NUM_CPUS, cpu_id),
        *post == (KernelK { cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, thrd_mp: post.thrd_mp, pt_mp: post.pt_mp, ..*pre }),
        post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, cpu_id),
        post.cpu_arr.spec_index(cpu_id).view().view().view() == pre.cpu_arr.spec_index(cpu_id).view().view().view(),
        forall|i: CpuId| #![trigger post.cpu_op.view().view()[i as int]] index_valid(NUM_CPUS, i) && i != cpu_id ==> post.cpu_op.view().view()[i as int] == pre.cpu_op.view().view()[i as int],
        post.cpu_arr.spec_index(cpu_id).value.being_killed() == pre.cpu_arr.spec_index(cpu_id).value.being_killed(),
        (post.cpu_arr.spec_index(cpu_id).value.locking_thread() is Write) == (post.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write),
        (post.cpu_arr.spec_index(cpu_id).value.locking_thread() is Read) == (post.thrd_mp.spec_index(thrd_ptr).locking_thread() is Read),
        pre.thrd_mp.dom().contains(thrd_ptr),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..pre.thrd_mp.spec_index(thrd_ptr).view() }),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        pre.prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        post.pt_mp.spec_index(pagetable_ptr).view() == pre.pt_mp.spec_index(pagetable_ptr).view(),
        (post.pt_mp.spec_index(pagetable_ptr).locking_thread() is Write) == (post.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write),
        (post.pt_mp.spec_index(pagetable_ptr).locking_thread() is Read) == (post.thrd_mp.spec_index(thrd_ptr).locking_thread() is Read),
    ensures
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let thread = pre.thrd_mp.spec_index(thrd_ptr).view();
            let process = pre_u.process_map.spec_index(prc_ptr);
            &&& pre_u.thread_map.dom().contains(thrd_ptr)
            &&& pre_u.thread_map.spec_index(thrd_ptr).owning_proc == thread.owning_proc
            &&& pre_u.thread_map.spec_index(thrd_ptr).syscall_progress == thread.syscall_progress.view()
            &&& pre_u.process_map.dom().contains(prc_ptr)
            &&& process.pagetable is Some
            &&& typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) ==> pre_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write) ==> pre_u.thread_map.spec_index(thrd_ptr).lock_state is WriteLocked
            &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) ==> process.pagetable->Some_0.lock_state is WriteLocked
            &&& pre_u.cpu_array[cpu_id as int].lock_state == pre.cpu_arr.spec_index(cpu_id).value.lock_state_u()
            &&& pre_u.cpu_array[cpu_id as int].state == pre.cpu_arr.spec_index(cpu_id).view().view().view().state
            &&& pre_u.cpu_array[cpu_id as int].current_thread == pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread
            &&& pre_u.thread_map.spec_index(thrd_ptr).lock_state == pre.thrd_mp.spec_index(thrd_ptr).lock_state_u()
            &&& pre_u.thread_map.spec_index(thrd_ptr).killed == pre.thrd_mp.spec_index(thrd_ptr).being_killed()
            &&& pre_u.thread_map.spec_index(thrd_ptr).quota_4k == thread.quota_4k
            &&& process.pagetable->Some_0.lock_state == pre.pt_mp.spec_index(pagetable_ptr).lock_state_u()
            &&& process.pagetable->Some_0.mapping_4k.dom().subset_of(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k().dom())
            &&& process.pagetable->Some_0.mapping_2m.dom().subset_of(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m().dom())
            &&& process.pagetable->Some_0.mapping_1g.dom().subset_of(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g().dom())
        }),
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let lock_state = post.thrd_mp.spec_index(thrd_ptr).lock_state_u();
            let process = pre_u.process_map.spec_index(prc_ptr);
            kernel_k_to_kernel_u(*post) == (KernelU {
                cpu_array: pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state, op: post.cpu_op.view().view()[cpu_id as int], ..pre_u.cpu_array[cpu_id as int] }),
                thread_map: pre_u.thread_map.insert(thrd_ptr, ThreadU {
                    lock_state, syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), ..pre_u.thread_map.spec_index(thrd_ptr)
                }),
                process_map: pre_u.process_map.insert(prc_ptr, ProcessU { pagetable: Some(PageTableU { lock_state, ..process.pagetable->Some_0 }), ..process }),
                ..pre_u
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let lock_state = post.thrd_mp.spec_index(thrd_ptr).lock_state_u();
    let process = pre_u.process_map.spec_index(prc_ptr);
    kernel_cpu_projection_at(pre, cpu_id);
    if pre.prc_mp.dom().contains(prc_ptr) { kernel_process_projection_at(pre, prc_ptr); } if post.prc_mp.dom().contains(prc_ptr) { kernel_process_projection_at(post, prc_ptr); }
    if pre.thrd_mp.dom().contains(thrd_ptr) { kernel_thread_projection_at(pre, thrd_ptr); }
    assert(pre.prc_mp.dom().contains(prc_ptr) && !pre.prc_mp.spec_index(prc_ptr).view().zombie && pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr) by { reveal(process_cpu_wf); reveal(process_pagetable_wf); };
    assert(typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) ==> pre.cpu_arr.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    if typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write) { pre.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr); }
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) { pre.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); }
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state, op: post.cpu_op.view().view()[cpu_id as int], ..pre_u.cpu_array[cpu_id as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); }
    });
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(prc_ptr, ProcessU { pagetable: Some(PageTableU { lock_state, ..process.pagetable->Some_0 }), ..process }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } reveal(process_pagetable_wf);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thrd_ptr, ThreadU {
        lock_state, syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), ..pre_u.thread_map.spec_index(thrd_ptr)
    }), t => { if pre.thrd_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_projection_at(post, t); } });
    kernel_container_maps_unchanged_implies_u_container_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

/// Setting the lock modes of cpu `cpu_id` and its thread `thrd_ptr` to the thread's mode, with at most one pagetable
/// `table` whose payload and lock mode the section restored, changes only those two lock projections. `lctx` is aligned
/// with `pre`; the objects it write-holds project as write-locked before the section. The cpu's running state is `post`'s.
pub proof fn kernel_cpu_thread_lock_states_changed_implies_u_step(pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, table: Option<RwLockPageTableRoot>)
    requires
        typed_lock_maps_aligned(pre, lctx),
        index_valid(NUM_CPUS, cpu_id),
        *post == (KernelK { cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, thrd_mp: post.thrd_mp, pt_mp: post.pt_mp, ..*pre }),
        post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, cpu_id),
        post.cpu_arr.spec_index(cpu_id).view().view().view() == pre.cpu_arr.spec_index(cpu_id).view().view().view(),
        forall|i: CpuId| #![trigger post.cpu_op.view().view()[i as int]] index_valid(NUM_CPUS, i) && i != cpu_id ==> post.cpu_op.view().view()[i as int] == pre.cpu_op.view().view()[i as int],
        post.cpu_arr.spec_index(cpu_id).value.being_killed() == pre.cpu_arr.spec_index(cpu_id).value.being_killed(),
        (post.cpu_arr.spec_index(cpu_id).value.locking_thread() is Write) == (post.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write),
        (post.cpu_arr.spec_index(cpu_id).value.locking_thread() is Read) == (post.thrd_mp.spec_index(thrd_ptr).locking_thread() is Read),
        pre.thrd_mp.dom().contains(thrd_ptr),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view() == pre.thrd_mp.spec_index(thrd_ptr).view(),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        match table {
            Some(p) => {
                &&& post.pt_mp.unchanged_except(&pre.pt_mp, p)
                &&& post.pt_mp.spec_index(p).view() == pre.pt_mp.spec_index(p).view()
                &&& (post.pt_mp.spec_index(p).locking_thread() is Write) == (pre.pt_mp.spec_index(p).locking_thread() is Write)
                &&& (post.pt_mp.spec_index(p).locking_thread() is Read) == (pre.pt_mp.spec_index(p).locking_thread() is Read)
            },
            None => post.pt_mp == pre.pt_mp,
        },
    ensures
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            &&& pre_u.thread_map.dom().contains(thrd_ptr)
            &&& pre_u.thread_map.spec_index(thrd_ptr).syscall_progress == pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()
            &&& typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) ==> pre_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write) ==> pre_u.thread_map.spec_index(thrd_ptr).lock_state is WriteLocked
            &&& pre_u.cpu_array[cpu_id as int].current_thread == pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread
        }),
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let lock_state = post.thrd_mp.spec_index(thrd_ptr).lock_state_u();
            kernel_k_to_kernel_u(*post) == (KernelU {
                cpu_array: pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state, op: post.cpu_op.view().view()[cpu_id as int], ..pre_u.cpu_array[cpu_id as int] }),
                thread_map: pre_u.thread_map.insert(thrd_ptr, ThreadU { lock_state, ..pre_u.thread_map.spec_index(thrd_ptr) }),
                ..pre_u
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let lock_state = post.thrd_mp.spec_index(thrd_ptr).lock_state_u();
    kernel_cpu_projection_at(pre, cpu_id); kernel_thread_projection_at(pre, thrd_ptr);
    assert(typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) ==> pre.cpu_arr.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    if typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write) { pre.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr); }
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state, op: post.cpu_op.view().view()[cpu_id as int], ..pre_u.cpu_array[cpu_id as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); }
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thrd_ptr, ThreadU { lock_state, ..pre_u.thread_map.spec_index(thrd_ptr) }), t => {
        if pre.thrd_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_projection_at(post, t); }
    });
    assert_maps_equal!(pagetable_map_user_view(post.pt_mp, post.pt_lower.view()), pagetable_map_user_view(pre.pt_mp, pre.pt_lower.view()));
    assert_maps_equal!(post_u.process_map, pre_u.process_map, p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
    });
    kernel_container_maps_unchanged_implies_u_container_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

/// Changing only the lock mode and running state of cpu `cpu_id`, with every non-lock field and every other user-visible
/// lock mode unchanged, changes only that cpu's lock and running-state projection.
pub proof fn kernel_cpu_lock_mode_changed_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId)
    requires
        index_valid(NUM_CPUS, cpu_id),
        post.inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        post.irt.view().owners() == pre.irt.view().owners(),
        post.irt.view().iommu_roots() == pre.irt.view().iommu_roots(),
        post.cpu_tlb.view() == pre.cpu_tlb.view(),
        post.iommu_tlb.view() == pre.iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
        post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, cpu_id),
        forall|i: CpuId| #![trigger post.cpu_op.view().view()[i as int]] index_valid(NUM_CPUS, i) && i != cpu_id ==> post.cpu_op.view().view()[i as int] == pre.cpu_op.view().view()[i as int],
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> {
            &&& (post.ctn_mp.spec_index(p).locking_thread() is Write) == (pre.ctn_mp.spec_index(p).locking_thread() is Write)
            &&& (post.ctn_mp.spec_index(p).locking_thread() is Read) == (pre.ctn_mp.spec_index(p).locking_thread() is Read)
            &&& post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u()
        },
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)] pre.prc_mp.dom().contains(p) ==> {
            &&& (post.prc_mp.spec_index(p).locking_thread() is Write) == (pre.prc_mp.spec_index(p).locking_thread() is Write)
            &&& (post.prc_mp.spec_index(p).locking_thread() is Read) == (pre.prc_mp.spec_index(p).locking_thread() is Read)
        },
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)] pre.pt_mp.dom().contains(p) ==> {
            &&& (post.pt_mp.spec_index(p).locking_thread() is Write) == (pre.pt_mp.spec_index(p).locking_thread() is Write)
            &&& (post.pt_mp.spec_index(p).locking_thread() is Read) == (pre.pt_mp.spec_index(p).locking_thread() is Read)
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), p).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p).lower.pagetable_window_locks
        },
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)] pre.it_mp.dom().contains(p) ==> {
            &&& (post.it_mp.spec_index(p).locking_thread() is Write) == (pre.it_mp.spec_index(p).locking_thread() is Write)
            &&& (post.it_mp.spec_index(p).locking_thread() is Read) == (pre.it_mp.spec_index(p).locking_thread() is Read)
        },
        forall|p: RwLockThreadPtr| #![trigger post.thrd_mp.spec_index(p)] pre.thrd_mp.dom().contains(p) ==> {
            &&& (post.thrd_mp.spec_index(p).locking_thread() is Write) == (pre.thrd_mp.spec_index(p).locking_thread() is Write)
            &&& (post.thrd_mp.spec_index(p).locking_thread() is Read) == (pre.thrd_mp.spec_index(p).locking_thread() is Read)
        },
        forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)] pre.ep_mp.dom().contains(p) ==> {
            &&& (post.ep_mp.spec_index(p).locking_thread() is Write) == (pre.ep_mp.spec_index(p).locking_thread() is Write)
            &&& (post.ep_mp.spec_index(p).locking_thread() is Read) == (pre.ep_mp.spec_index(p).locking_thread() is Read)
        },
    ensures
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            kernel_k_to_kernel_u(*post) == (KernelU {
                cpu_array: pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state: post.cpu_arr.spec_index(cpu_id).value.lock_state_u(), op: post.cpu_op.view().view()[cpu_id as int], ..pre_u.cpu_array[cpu_id as int] }),
                ..pre_u
            })
        }),
{
    let mid = KernelK { cpu_arr: pre.cpu_arr, cpu_op: pre.cpu_op, ..*post };
    assert({
        &&& kernel_cpu_process_thread_nonlock_fields_unchanged(pre, &mid)
        &&& kernel_container_nonlock_fields_and_quotas_unchanged(pre, &mid)
        &&& kernel_cpu_nonlock_fields_unchanged(mid.cpu_arr, post.cpu_arr)
    }) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(pre, &mid);
    kernel_cpu_lock_mode_changed_implies_u_cpu_array(&mid, post, cpu_id, post.cpu_arr.spec_index(cpu_id).value.lock_state_u());
    kernel_container_maps_unchanged_implies_u_container_map(&mid, post); kernel_process_maps_unchanged_implies_u_process_map(&mid, post);
    kernel_thread_map_unchanged_implies_u_thread_map(&mid, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(&mid, post);
    kernel_u_domains_projection(&mid); kernel_u_domains_projection(post);
}

} // verus!
