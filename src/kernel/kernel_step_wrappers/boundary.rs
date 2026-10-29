use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;
#[cfg(verus_keep_ghost)]
use crate::kernel::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;

verus! {
#[verifier::spinoff_prover]
pub(super) proof fn kernel_new_thread_fields_implies_u_step(
    pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    cpu_id: CpuId, new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, initial_endpoint: Option<RwLockEndpointPtr>, staging_progress: Option<SyscallProgress>,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        container_scheduler_wf(post.ctn_mp, post.sched_mp),
        kernel_new_thread_fields(pre, post, process_ptr, staging_thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, initial_endpoint, staging_progress),
    ensures
        kernel_u_new_thread_changed(kernel_k_to_nonlock_kernel_u(*pre), kernel_k_to_nonlock_kernel_u(*post),
            process_ptr, staging_thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, initial_endpoint, staging_progress),
{
    reveal(kernel_new_thread_fields); reveal(kernel_u_new_thread_changed); kernel_u_nonlock_domains_projection(pre); kernel_u_nonlock_domains_projection(post);
    let pre_u = kernel_k_to_nonlock_kernel_u(*pre);
    let post_u = kernel_k_to_nonlock_kernel_u(*post);
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(IommuRootTable::user_view); };
    match initial_endpoint {
        Some(e) => {
            assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map.insert(e, EndpointU {
                owning_threads: pre_u.endpoint_map.spec_index(e).owning_threads.insert((new_thread_ptr, 0usize)),
                ..pre_u.endpoint_map.spec_index(e)
            }), ptr => {
                if pre.ep_mp.dom().contains(ptr) { kernel_endpoint_nonlock_projection_at(pre, ptr); } if post.ep_mp.dom().contains(ptr) { kernel_endpoint_nonlock_projection_at(post, ptr); }
                kernel_endpoint_nonlock_projection_at(pre, e);
            });
        },
        None => { assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, ptr => {
            if pre.ep_mp.dom().contains(ptr) { kernel_endpoint_nonlock_projection_at(pre, ptr); } if post.ep_mp.dom().contains(ptr) { kernel_endpoint_nonlock_projection_at(post, ptr); }
        }); },
    }
    kernel_thread_nonlock_projection_at(pre, staging_thread_ptr); kernel_thread_nonlock_projection_at(post, new_thread_ptr);
    let staging = pre_u.thread_map.spec_index(staging_thread_ptr);
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_nonlock_projection_at(pre, i as usize); kernel_cpu_nonlock_projection_at(post, i as usize); } });
    assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(container_ptr, ContainerU {
        owned_threads: pre_u.container_map.spec_index(container_ptr).owned_threads.insert(new_thread_ptr),
        scheduler: pre_u.container_map.spec_index(container_ptr).scheduler.update(cpu_id as int, pre_u.container_map.spec_index(container_ptr).scheduler[cpu_id as int].push(new_thread_ptr)),
        ..pre_u.container_map.spec_index(container_ptr)
    }), c => {
        if pre.ctn_mp.dom().contains(c) { kernel_container_nonlock_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_nonlock_projection_at(post, c); }
        reveal(container_scheduler_wf);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(staging_thread_ptr, ThreadU {
        quota_4k: (staging.quota_4k as int - 1) as usize, syscall_progress: staging_progress, ..staging
    }).insert(new_thread_ptr, post_u.thread_map.spec_index(new_thread_ptr)), t => {
        if pre.thr_mp.dom().contains(t) { kernel_thread_nonlock_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_nonlock_projection_at(post, t); }
    });
    assert_seqs_equal!(post_u.thread_map.spec_index(new_thread_ptr).endpoint_descriptors == Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| if i == 0 { initial_endpoint } else { None }));
    kernel_process_nonlock_projection_at(pre, process_ptr);
    let process = pre_u.process_map.spec_index(process_ptr);
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(process_ptr, ProcessU {
        owned_threads: process.owned_threads.push(new_thread_ptr), ..process
    }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_nonlock_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_nonlock_projection_at(post, p); }
        reveal(process_pagetable_match); reveal(process_iommu_table_match); reveal(kernel_pagetable_nonlock_fields_unchanged);
    });
}

pub proof fn kernel_thread_state_changed_implies_u_neq(pre: &KernelK, post: &KernelK, thread_ptr: RwLockThreadPtr)
    requires kernel_thread_state_changed(pre, post, thread_ptr),
    ensures kernel_k_to_nonlock_kernel_u(*pre) != kernel_k_to_nonlock_kernel_u(*post),
{
    assert(kernel_k_to_nonlock_kernel_u(*pre).thread_map.spec_index(thread_ptr).state != kernel_k_to_nonlock_kernel_u(*post).thread_map.spec_index(thread_ptr).state) by {
        reveal(kernel_thread_state_changed); kernel_thread_nonlock_projection_at(pre, thread_ptr); kernel_thread_nonlock_projection_at(post, thread_ptr);
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn kernel_thread_quota_4k_changed_implies_u_step(pre: &KernelK, post: &KernelK, thread_ptr: RwLockThreadPtr, delta: int)
    requires
        delta != 0,
        kernel_thread_quota_4k_changed(pre, post, thread_ptr, delta),
    ensures
        kernel_k_to_nonlock_kernel_u(*post).thread_map.spec_index(thread_ptr) == (ThreadU {
            quota_4k: (kernel_k_to_nonlock_kernel_u(*pre).thread_map.spec_index(thread_ptr).quota_4k as int + delta) as usize,
            syscall_progress: kernel_k_to_nonlock_kernel_u(*post).thread_map.spec_index(thread_ptr).syscall_progress,
            ..kernel_k_to_nonlock_kernel_u(*pre).thread_map.spec_index(thread_ptr)
        }),
        kernel_k_to_nonlock_kernel_u(*pre) != kernel_k_to_nonlock_kernel_u(*post),
{
    assert(kernel_k_to_nonlock_kernel_u(*post).thread_map.spec_index(thread_ptr) == (ThreadU {
        quota_4k: (kernel_k_to_nonlock_kernel_u(*pre).thread_map.spec_index(thread_ptr).quota_4k as int + delta) as usize,
        syscall_progress: kernel_k_to_nonlock_kernel_u(*post).thread_map.spec_index(thread_ptr).syscall_progress,
        ..kernel_k_to_nonlock_kernel_u(*pre).thread_map.spec_index(thread_ptr)
    })) by { reveal(kernel_thread_quota_4k_changed); kernel_thread_nonlock_projection_at(pre, thread_ptr); kernel_thread_nonlock_projection_at(post, thread_ptr); };
    assert(kernel_k_to_nonlock_kernel_u(*pre).thread_map.spec_index(thread_ptr).quota_4k != kernel_k_to_nonlock_kernel_u(*post).thread_map.spec_index(thread_ptr).quota_4k) by {
        reveal(kernel_thread_quota_4k_changed); kernel_thread_nonlock_projection_at(pre, thread_ptr); kernel_thread_nonlock_projection_at(post, thread_ptr);
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn kernel_process_quota_4k_changed_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, delta: int, include_lock_state: bool)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_process_quota_4k_changed(pre, post, cpu_id, process_ptr, container_ptr, delta),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        kernel_u_only_process_quota_4k_changed(kernel_k_user_projection(*pre, include_lock_state), kernel_k_user_projection(*post, include_lock_state), cpu_id, process_ptr, container_ptr, delta),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_only_process_quota_4k_changed); reveal(kernel_process_quota_4k_changed); reveal(kernel_endpoint_nonlock_fields_unchanged);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id); kernel_container_user_projection_at(pre, include_lock_state, container_ptr); kernel_process_user_projection_at(pre, include_lock_state, process_ptr);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(IommuRootTable::user_view); };
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, include_lock_state, i as usize); kernel_cpu_user_projection_at(post, include_lock_state, i as usize); } });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map, t => { if pre.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, include_lock_state, t); } if post.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(post, include_lock_state, t); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, include_lock_state, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, include_lock_state, e); } });
    kernel_process_quota_4k_changed_implies_u_container_map(pre, post, cpu_id, process_ptr, container_ptr, delta, include_lock_state);
    kernel_process_quota_4k_changed_implies_u_process_map(pre, post, cpu_id, process_ptr, container_ptr, delta, include_lock_state);
}

/// Moving `delta` 4K quota from a container to its running process lowers only that container's quota in the
/// container projection.
proof fn kernel_process_quota_4k_changed_implies_u_container_map(pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, delta: int, include_lock_state: bool)
    requires
        kernel_process_quota_4k_changed(pre, post, cpu_id, process_ptr, container_ptr, delta),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let container = pre_u.container_map.spec_index(container_ptr);
            kernel_k_user_projection(*post, include_lock_state).container_map == pre_u.container_map.insert(container_ptr, ContainerU { quota_4k: (container.quota_4k as int - delta) as usize, ..container })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_process_quota_4k_changed);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let container = pre_u.container_map.spec_index(container_ptr);
    assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(container_ptr, ContainerU {
        quota_4k: (container.quota_4k as int - delta) as usize, ..container
    }), c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, include_lock_state, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, include_lock_state, c); } });
}

/// Moving `delta` 4K quota from a container to its running process raises only that process's quota in the
/// process projection.
proof fn kernel_process_quota_4k_changed_implies_u_process_map(pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, delta: int, include_lock_state: bool)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_process_quota_4k_changed(pre, post, cpu_id, process_ptr, container_ptr, delta),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let process = pre_u.process_map.spec_index(process_ptr);
            kernel_k_user_projection(*post, include_lock_state).process_map == pre_u.process_map.insert(process_ptr, ProcessU { quota_4k: (process.quota_4k as int + delta) as usize, ..process })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_process_quota_4k_changed);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let process = pre_u.process_map.spec_index(process_ptr);
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(process_ptr, ProcessU {
        quota_4k: (process.quota_4k as int + delta) as usize, ..process
    }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, include_lock_state, p); } if post.prc_mp.dom().contains(p) { kernel_process_user_projection_at(post, include_lock_state, p); }
        reveal(process_pagetable_match); reveal(process_iommu_table_match);
    });
}

pub(super) proof fn kernel_process2thread_quota_4k_changed_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, delta: int, include_lock_state: bool)
    requires kernel_process2thread_quota_4k_changed(pre, post, cpu_id, process_ptr, thread_ptr, delta),
    ensures
        kernel_u_only_process2thread_quota_4k_changed(kernel_k_user_projection(*pre, include_lock_state), kernel_k_user_projection(*post, include_lock_state), cpu_id, process_ptr, thread_ptr, delta),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_only_process2thread_quota_4k_changed); reveal(kernel_process2thread_quota_4k_changed);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id); kernel_process_user_projection_at(pre, include_lock_state, process_ptr); kernel_thread_user_projection_at(pre, include_lock_state, thread_ptr);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, include_lock_state, i as usize); kernel_cpu_user_projection_at(post, include_lock_state, i as usize); } });
    let process = pre_u.process_map.spec_index(process_ptr);
    let thread = pre_u.thread_map.spec_index(thread_ptr);
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread_ptr, ThreadU {
        quota_4k: (thread.quota_4k as int + delta) as usize, ..thread
    }), t => { if pre.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, include_lock_state, t); } if post.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(post, include_lock_state, t); } });
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(process_ptr, ProcessU {
        quota_4k: (process.quota_4k as int - delta) as usize, ..process
    }), p => { if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, include_lock_state, p); } if post.prc_mp.dom().contains(p) { kernel_process_user_projection_at(post, include_lock_state, p); } });
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, include_lock_state, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, include_lock_state, c); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, include_lock_state, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, include_lock_state, e); } });
}

#[verifier::spinoff_prover]
pub(super) proof fn kernel_process_quota_2m_changed_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, delta: int, include_lock_state: bool)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_process_quota_2m_changed(pre, post, cpu_id, process_ptr, container_ptr, delta),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        kernel_u_only_process_quota_2m_changed(kernel_k_user_projection(*pre, include_lock_state), kernel_k_user_projection(*post, include_lock_state), cpu_id, process_ptr, container_ptr, delta),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_only_process_quota_2m_changed); reveal(kernel_process_quota_2m_changed); reveal(kernel_endpoint_nonlock_fields_unchanged);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id); kernel_container_user_projection_at(pre, include_lock_state, container_ptr); kernel_process_user_projection_at(pre, include_lock_state, process_ptr);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(IommuRootTable::user_view); };
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, include_lock_state, i as usize); kernel_cpu_user_projection_at(post, include_lock_state, i as usize); } });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map, t => { if pre.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, include_lock_state, t); } if post.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(post, include_lock_state, t); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, include_lock_state, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, include_lock_state, e); } });
    kernel_process_quota_2m_changed_implies_u_container_map(pre, post, cpu_id, process_ptr, container_ptr, delta, include_lock_state);
    kernel_process_quota_2m_changed_implies_u_process_map(pre, post, cpu_id, process_ptr, container_ptr, delta, include_lock_state);
}

/// Moving `delta` 2M quota from a container to its running process lowers only that container's quota in the
/// container projection.
proof fn kernel_process_quota_2m_changed_implies_u_container_map(pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, delta: int, include_lock_state: bool)
    requires
        kernel_process_quota_2m_changed(pre, post, cpu_id, process_ptr, container_ptr, delta),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let container = pre_u.container_map.spec_index(container_ptr);
            kernel_k_user_projection(*post, include_lock_state).container_map == pre_u.container_map.insert(container_ptr, ContainerU { quota_2m: (container.quota_2m as int - delta) as usize, ..container })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_process_quota_2m_changed);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let container = pre_u.container_map.spec_index(container_ptr);
    assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(container_ptr, ContainerU {
        quota_2m: (container.quota_2m as int - delta) as usize, ..container
    }), c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, include_lock_state, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, include_lock_state, c); } });
}

/// Moving `delta` 2M quota from a container to its running process raises only that process's quota in the
/// process projection.
proof fn kernel_process_quota_2m_changed_implies_u_process_map(pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, delta: int, include_lock_state: bool)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_process_quota_2m_changed(pre, post, cpu_id, process_ptr, container_ptr, delta),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let process = pre_u.process_map.spec_index(process_ptr);
            kernel_k_user_projection(*post, include_lock_state).process_map == pre_u.process_map.insert(process_ptr, ProcessU { quota_2m: (process.quota_2m as int + delta) as usize, ..process })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_process_quota_2m_changed);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let process = pre_u.process_map.spec_index(process_ptr);
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(process_ptr, ProcessU {
        quota_2m: (process.quota_2m as int + delta) as usize, ..process
    }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, include_lock_state, p); } if post.prc_mp.dom().contains(p) { kernel_process_user_projection_at(post, include_lock_state, p); }
        reveal(process_pagetable_match); reveal(process_iommu_table_match);
    });
}

pub(super) proof fn kernel_process2thread_quota_2m_changed_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, delta: int, include_lock_state: bool)
    requires kernel_process2thread_quota_2m_changed(pre, post, cpu_id, process_ptr, thread_ptr, delta),
    ensures
        kernel_u_only_process2thread_quota_2m_changed(kernel_k_user_projection(*pre, include_lock_state), kernel_k_user_projection(*post, include_lock_state), cpu_id, process_ptr, thread_ptr, delta),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_only_process2thread_quota_2m_changed); reveal(kernel_process2thread_quota_2m_changed);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id); kernel_process_user_projection_at(pre, include_lock_state, process_ptr); kernel_thread_user_projection_at(pre, include_lock_state, thread_ptr);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, include_lock_state, i as usize); kernel_cpu_user_projection_at(post, include_lock_state, i as usize); } });
    let process = pre_u.process_map.spec_index(process_ptr);
    let thread = pre_u.thread_map.spec_index(thread_ptr);
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread_ptr, ThreadU {
        quota_2m: (thread.quota_2m as int + delta) as usize, ..thread
    }), t => { if pre.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, include_lock_state, t); } if post.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(post, include_lock_state, t); } });
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(process_ptr, ProcessU {
        quota_2m: (process.quota_2m as int - delta) as usize, ..process
    }), p => { if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, include_lock_state, p); } if post.prc_mp.dom().contains(p) { kernel_process_user_projection_at(post, include_lock_state, p); } });
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, include_lock_state, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, include_lock_state, c); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, include_lock_state, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, include_lock_state, e); } });
}

/// K→U: setting one request bit of the caller container's table changes only that
/// `ContainerU.cpu_offline_requests` entry.
pub(super) proof fn kernel_cpu_offline_request_changed_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, target: CpuId, include_lock_state: bool)
    requires
        kernel_cpu_offline_request_changed(pre, post, cpu_id, container_ptr, target),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        kernel_u_cpu_offline_request_changed(kernel_k_user_projection(*pre, include_lock_state), kernel_k_user_projection(*post, include_lock_state), cpu_id, container_ptr, target),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_cpu_offline_request_changed); reveal(kernel_cpu_offline_request_changed);
    reveal(container_cpu_set_wf); reveal(container_cpu_offline_flags_wf);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id); kernel_cpu_user_projection_at(pre, include_lock_state, target);
    kernel_container_user_projection_at(pre, include_lock_state, container_ptr); kernel_container_user_projection_at(pre, include_lock_state, pre.cpu_arr.spec_index(cpu_id).value.view().view().owning_container);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let container = pre_u.container_map.spec_index(container_ptr);
    assert(container.cpu_offline_requests.len() == NUM_CPUS && !container.cpu_offline_requests[target as int]) by { reveal(cpu_offline_requests_of); };
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, include_lock_state, i as usize); kernel_cpu_user_projection_at(post, include_lock_state, i as usize); } });
    kernel_cpu_offline_request_changed_implies_u_container_map(pre, post, cpu_id, container_ptr, target, include_lock_state);
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map, t => { if pre.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, include_lock_state, t); } if post.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(post, include_lock_state, t); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, include_lock_state, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, include_lock_state, e); } });
    assert_maps_equal!(post_u.process_map, pre_u.process_map, p => { if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, include_lock_state, p); } if post.prc_mp.dom().contains(p) { kernel_process_user_projection_at(post, include_lock_state, p); } });
}

/// K→U: setting one request bit of the caller container's table changes only that container's `cpu_offline_requests`
/// in the container projection.
proof fn kernel_cpu_offline_request_changed_implies_u_container_map(pre: &KernelK, post: &KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, target: CpuId, include_lock_state: bool)
    requires
        kernel_cpu_offline_request_changed(pre, post, cpu_id, container_ptr, target),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let container = pre_u.container_map.spec_index(container_ptr);
            kernel_k_user_projection(*post, include_lock_state).container_map == pre_u.container_map.insert(container_ptr, ContainerU {
                cpu_offline_requests: container.cpu_offline_requests.update(target as int, true), ..container
            })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_cpu_offline_request_changed); reveal(container_cpu_set_wf); reveal(container_cpu_offline_flags_wf);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let container = pre_u.container_map.spec_index(container_ptr);
    assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(container_ptr, ContainerU {
        cpu_offline_requests: container.cpu_offline_requests.update(target as int, true), ..container
    }), c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, include_lock_state, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, include_lock_state, c); } });
}

/// K→U: publishing Idle on an Off cpu changes only that `CpuU.state`.
pub(super) proof fn kernel_cpu_online_changed_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, target: CpuId, include_lock_state: bool)
    requires
        kernel_cpu_online_changed(pre, post, cpu_id, container_ptr, target),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        kernel_u_cpu_online_changed(kernel_k_user_projection(*pre, include_lock_state), kernel_k_user_projection(*post, include_lock_state), cpu_id, container_ptr, target),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_cpu_online_changed); reveal(kernel_cpu_online_changed); reveal(container_cpu_set_wf);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id); kernel_cpu_user_projection_at(pre, include_lock_state, target);
    kernel_container_user_projection_at(pre, include_lock_state, container_ptr); kernel_container_user_projection_at(pre, include_lock_state, pre.cpu_arr.spec_index(cpu_id).value.view().view().owning_container);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let target_cpu = pre_u.cpu_array[target as int];
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(target as int, CpuU { state: CpuState::Idle, op: CpuOpState::Idle, ..target_cpu }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, include_lock_state, i as usize); kernel_cpu_user_projection_at(post, include_lock_state, i as usize); }
    });
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, include_lock_state, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, include_lock_state, c); } });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map, t => { if pre.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, include_lock_state, t); } if post.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(post, include_lock_state, t); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, include_lock_state, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, include_lock_state, e); } });
    assert_maps_equal!(post_u.process_map, pre_u.process_map, p => { if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, include_lock_state, p); } if post.prc_mp.dom().contains(p) { kernel_process_user_projection_at(post, include_lock_state, p); } });
}

#[verifier::spinoff_prover]
pub(super) proof fn kernel_cpu_went_off_fields_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, regs: Registers, flushed_default_pcid: bool, include_lock_state: bool)
    requires
        post.inv(),
        kernel_cpu_went_off_fields(pre, post, cpu_id, regs, flushed_default_pcid),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        kernel_u_cpu_went_off_changed(kernel_k_user_projection(*pre, include_lock_state), kernel_k_user_projection(*post, include_lock_state), cpu_id, regs, flushed_default_pcid),
{
    hide(kernel_k_user_projection);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let cpu = pre_u.cpu_array[cpu_id as int];
    let container = pre_u.container_map.spec_index(cpu.owning_container);
    assert({
        &&& index_valid(NUM_CPUS, cpu_id)
        &&& pre_u.cpu_array.len() == NUM_CPUS
        &&& post_u.cpu_array.len() == NUM_CPUS
        &&& !(cpu.state is Off)
        &&& pre_u.container_map.dom().contains(cpu.owning_container)
        &&& container.cpu_offline_requests.len() == NUM_CPUS
        &&& container.cpu_offline_requests[cpu_id as int]
        &&& cpu.current_process is Some == cpu.current_thread is Some
        &&& (cpu.current_thread is Some ==> {
            let prev = pre_u.thread_map.spec_index(cpu.current_thread.unwrap());
            &&& pre_u.thread_map.dom().contains(cpu.current_thread.unwrap())
            &&& !prev.killed
            &&& prev.state == (ThreadState::RUNNING { cpu_id })
            &&& prev.owning_proc == cpu.current_process.unwrap()
            &&& pre_u.process_map.dom().contains(cpu.current_process.unwrap())
            &&& !pre_u.process_map.spec_index(cpu.current_process.unwrap()).killed
        })
        &&& post_u.iommu_root_table == pre_u.iommu_root_table
        &&& post_u.cpu_tlb == cpu_tlb_after_cpu_went_off(pre_u.cpu_tlb, cpu_id, flushed_default_pcid)
        &&& post_u.iommu_tlb == pre_u.iommu_tlb
        &&& post_u.kernel_l4_end == pre_u.kernel_l4_end
    }) by { reveal(kernel_k_user_projection); reveal(kernel_cpu_went_off_fields); reveal(cpu_offline_requests_of); reveal(IommuRootTable::user_view); };
    reveal(kernel_u_cpu_went_off_changed); reveal(kernel_cpu_went_off_fields);
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, state: CpuState::Off, op: CpuOpState::Off, current_process: None, current_thread: None, ..cpu }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, include_lock_state, i as usize); kernel_cpu_user_projection_at(post, include_lock_state, i as usize); }
    });
    kernel_endpoint_nonlock_fields_and_locks_unchanged_implies_u_endpoint_map(pre, post, include_lock_state);
    kernel_process_nonlock_fields_and_locks_unchanged_implies_u_process_map(pre, post, include_lock_state);
    kernel_cpu_went_off_fields_implies_u_container_map(pre, post, cpu_id, regs, flushed_default_pcid, include_lock_state);
    kernel_cpu_went_off_fields_implies_u_thread_map(pre, post, cpu_id, regs, flushed_default_pcid, include_lock_state);
}

#[verifier::spinoff_prover]
pub(super) proof fn kernel_process_added_implies_u_neq(pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr)
    requires kernel_process_added(pre, post, process_ptr),
    ensures
        kernel_k_to_nonlock_kernel_u(*pre) != kernel_k_to_nonlock_kernel_u(*post),
        kernel_k_to_kernel_u(*pre) != kernel_k_to_kernel_u(*post),
{ reveal(kernel_process_added); reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_k_to_kernel_u); }

#[verifier::spinoff_prover]
pub proof fn kernel_process_4k_mapping_changed_implies_u_neq(pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires kernel_process_4k_mapping_changed(pre, post, process_ptr, pagetable_ptr, va),
    ensures
        kernel_k_to_nonlock_kernel_u(*pre) != kernel_k_to_nonlock_kernel_u(*post),
{
    assert(kernel_k_to_nonlock_kernel_u(*pre).process_map.spec_index(process_ptr).pagetable.unwrap().mapping_4k.dom().contains(va) != kernel_k_to_nonlock_kernel_u(*post).process_map.spec_index(process_ptr).pagetable.unwrap().mapping_4k.dom().contains(va)) by {
        reveal(kernel_process_4k_mapping_changed); reveal(kernel_k_to_nonlock_kernel_u);
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
        process_pagetable_match(post.prc_mp, post.pt_mp),
        post.pt_mp.dom() == pre.pt_mp.dom(),
        forall|pt: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(pt)] pre.pt_mp.dom().contains(pt) ==> {
            &&& post.pt_mp.spec_index(pt).locking_thread() == pre.pt_mp.spec_index(pt).locking_thread()
            &&& pagetable_c(post.pt_mp, post.pt_lower.view(), pt).mapping_4k() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pt).mapping_4k()
            &&& pagetable_c(post.pt_mp, post.pt_lower.view(), pt).mapping_2m() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pt).mapping_2m()
            &&& pagetable_c(post.pt_mp, post.pt_lower.view(), pt).mapping_1g() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pt).mapping_1g()
        },
    ensures
        kernel_k_to_kernel_u(*post) == (KernelU { cpu_tlb: post.cpu_tlb.view(), ..kernel_k_to_kernel_u(*pre) }),
{
    reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_k_to_kernel_u);
    assert_seqs_equal!(kernel_k_to_kernel_u(*post).cpu_array == kernel_k_to_kernel_u(*pre).cpu_array);
    assert_maps_equal!(kernel_k_to_kernel_u(*post).process_map, kernel_k_to_kernel_u(*pre).process_map, p => { reveal(process_pagetable_match); });
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
        if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_projection_at(post, t); }
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
pub proof fn kernel_pagetable_4k_present_cleared_and_progress_changed_implies_u_step(pre: &KernelK, post: &KernelK, pagetable: RwLockPageTableRoot, va: VAddr, thread_ptr: RwLockThreadPtr)
    requires
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        pre.pt_mp.dom().contains(pagetable),
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, thr_mp: post.thr_mp, ..*pre }),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable)),
        post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread(),
        post.pt_mp.spec_index(pagetable).view().proc_ptr == pre.pt_mp.spec_index(pagetable).view().proc_ptr,
        pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k()[va].present,
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().insert(va, MapEntry { present: false, ..pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k()[va] }),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable).mapping_1g() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g(),
        pre.thr_mp.dom().contains(thread_ptr),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).locking_thread() == pre.thr_mp.spec_index(thread_ptr).locking_thread(),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        !pre.prc_mp.spec_index(pre.pt_mp.spec_index(pagetable).view().proc_ptr).view().zombie,
    ensures
        {
            let before = kernel_k_to_kernel_u(*pre);
            let process = pre.pt_mp.spec_index(pagetable).view().proc_ptr;
            &&& before.process_map.dom().contains(process)
            &&& before.process_map[process].pagetable is Some
            &&& before.process_map[process].pagetable->Some_0.mapping_4k.dom().contains(va)
            &&& before.thread_map.dom().contains(thread_ptr)
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                process_map: before.process_map.insert(process, ProcessU {
                    pagetable: Some(PageTableU { mapping_4k: before.process_map[process].pagetable->Some_0.mapping_4k.remove(va), ..before.process_map[process].pagetable->Some_0 }),
                    ..before.process_map[process]
                }),
                thread_map: before.thread_map.insert(thread_ptr, ThreadU { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..before.thread_map[thread_ptr] }),
                ..before
            })
        },
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(process_pagetable_match);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    let process = pre.pt_mp.spec_index(pagetable).view().proc_ptr;
    if pre.prc_mp.dom().contains(process) { kernel_process_projection_at(pre, process); } if post.prc_mp.dom().contains(process) { kernel_process_projection_at(post, process); }
    if pre.thr_mp.dom().contains(thread_ptr) { kernel_thread_projection_at(pre, thread_ptr); }
    assert_maps_equal!(after.process_map[process].pagetable->Some_0.mapping_4k, before.process_map[process].pagetable->Some_0.mapping_4k.remove(va), a => {});
    assert_maps_equal!(after.process_map, before.process_map.insert(process, ProcessU {
        pagetable: Some(PageTableU { mapping_4k: before.process_map[process].pagetable->Some_0.mapping_4k.remove(va), ..before.process_map[process].pagetable->Some_0 }),
        ..before.process_map[process]
    }), p => { if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } });
    assert_maps_equal!(after.thread_map, before.thread_map.insert(thread_ptr, ThreadU { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..before.thread_map[thread_ptr] }), t => {
        if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_projection_at(post, t); }
    });
    assert_seqs_equal!(after.cpu_array == before.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(after.container_map, before.container_map, p => {
        if pre.ctn_mp.dom().contains(p) { kernel_container_projection_at(pre, p); } if post.ctn_mp.dom().contains(p) { kernel_container_projection_at(post, p); }
    });
    assert_maps_equal!(after.endpoint_map, before.endpoint_map, p => {
        if pre.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(pre, p); } if post.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(post, p); }
    });
}

/// Clearing one present 4K entry of an IOMMU table removes that IOVA from the owning process's user IOMMU mapping and
/// changes nothing else in the complete projection.
pub proof fn kernel_iommu_table_4k_present_cleared_implies_u_step(pre: &KernelK, post: &KernelK, iommu_table: RwLockPageTableRoot, iova: VAddr)
    requires
        process_iommu_table_match(pre.prc_mp, pre.it_mp),
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
        kernel_k_to_nonlock_kernel_u(*pre) != kernel_k_to_nonlock_kernel_u(*post),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(process_iommu_table_match);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    let process = pre.it_mp.spec_index(iommu_table).view().proc_ptr;
    kernel_process_projection_at(pre, process); kernel_process_projection_at(post, process);
    assert_maps_equal!(after.process_map[process].iommu_table->Some_0.mapping_4k, before.process_map[process].iommu_table->Some_0.mapping_4k.remove(iova), a => {});
    assert_maps_equal!(after.process_map, before.process_map.insert(process, ProcessU {
        iommu_table: Some(PageTableU { mapping_4k: before.process_map[process].iommu_table->Some_0.mapping_4k.remove(iova), ..before.process_map[process].iommu_table->Some_0 }),
        ..before.process_map[process]
    }), p => { if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } });
    assert_maps_equal!(after.thread_map, before.thread_map, t => {
        if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_projection_at(post, t); }
    });
    assert_seqs_equal!(after.cpu_array == before.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(after.container_map, before.container_map, p => {
        if pre.ctn_mp.dom().contains(p) { kernel_container_projection_at(pre, p); } if post.ctn_mp.dom().contains(p) { kernel_container_projection_at(post, p); }
    });
    assert_maps_equal!(after.endpoint_map, before.endpoint_map, p => {
        if pre.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(pre, p); } if post.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(post, p); }
    });
    assert(!after.process_map[process].iommu_table->Some_0.mapping_4k.dom().contains(iova));
    assert(kernel_k_to_nonlock_kernel_u(*pre).process_map[process].iommu_table->Some_0.mapping_4k.dom().contains(iova)
        != kernel_k_to_nonlock_kernel_u(*post).process_map[process].iommu_table->Some_0.mapping_4k.dom().contains(iova)) by { kernel_process_nonlock_projection_at(pre, process); kernel_process_nonlock_projection_at(post, process); };
}

/// Replacing one thread's progress changes only that thread's progress in the complete projection.
pub proof fn kernel_thread_syscall_progress_changed_implies_u_step(pre: &KernelK, post: &KernelK, thread_ptr: RwLockThreadPtr)
    requires
        *post == (KernelK { thr_mp: post.thr_mp, ..*pre }),
        pre.thr_mp.dom().contains(thread_ptr),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).locking_thread() == pre.thr_mp.spec_index(thread_ptr).locking_thread(),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
    ensures
        kernel_k_to_kernel_u(*pre).thread_map.dom().contains(thread_ptr),
        kernel_k_to_kernel_u(*post) == (KernelU {
            thread_map: kernel_k_to_kernel_u(*pre).thread_map.insert(thread_ptr, ThreadU {
                syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..kernel_k_to_kernel_u(*pre).thread_map[thread_ptr]
            }),
            ..kernel_k_to_kernel_u(*pre)
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    assert_maps_equal!(after.thread_map, before.thread_map.insert(thread_ptr, ThreadU {
        syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..before.thread_map[thread_ptr]
    }), t => { if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_projection_at(post, t); } });
    assert_seqs_equal!(after.cpu_array == before.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(after.container_map, before.container_map, p => {
        if pre.ctn_mp.dom().contains(p) { kernel_container_projection_at(pre, p); } if post.ctn_mp.dom().contains(p) { kernel_container_projection_at(post, p); }
    });
    assert_maps_equal!(after.process_map, before.process_map, p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
    });
    assert_maps_equal!(after.endpoint_map, before.endpoint_map, p => {
        if pre.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(pre, p); } if post.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(post, p); }
    });
}

/// A section that changes only one thread's quota, temporary cache, and progress plus the
/// kernel-only structure of one pagetable changes only that thread's quota and progress in
/// the complete projection. `lctx` is aligned with `post` and write-holds the cpu, thread,
/// and pagetable across the section.
#[verifier::spinoff_prover]
pub proof fn kernel_thread_quota_4k_and_progress_changed_implies_u_step(pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot)
    requires
        process_cpu_wf(pre.prc_mp, pre.cpu_arr),
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(post, lctx),
        pre.thr_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        pre.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, pg_arr: post.pg_arr, thr_mp: post.thr_mp, ..*pre }),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread {
            quota_4k: post.thr_mp.spec_index(thread_ptr).view().quota_4k,
            temp_alloc_cache_4k: post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k,
            syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress,
            ..pre.thr_mp.spec_index(thread_ptr).view()
        }),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, post.pt_lower.view().spec_index(pagetable_ptr)),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_2m() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g(),
    ensures
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let thread = pre.thr_mp.spec_index(thread_ptr).view();
            let process = pre_u.process_map.spec_index(process_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& pre_u.cpu_array[cpu_id as int].current_thread == pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread
            &&& pre_u.thread_map.dom().contains(thread_ptr)
            &&& pre_u.thread_map.spec_index(thread_ptr).lock_state is WriteLocked
            &&& pre_u.thread_map.spec_index(thread_ptr).owning_proc == thread.owning_proc
            &&& pre_u.thread_map.spec_index(thread_ptr).quota_4k == thread.quota_4k
            &&& pre_u.thread_map.spec_index(thread_ptr).syscall_progress == thread.syscall_progress.view()
            &&& pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr) ==> {
                &&& pre_u.process_map.dom().contains(process_ptr)
                &&& process.pagetable is Some
                &&& process.pagetable->Some_0.lock_state is WriteLocked
            }
        }),
        kernel_k_to_kernel_u(*post) == (KernelU {
            thread_map: kernel_k_to_kernel_u(*pre).thread_map.insert(thread_ptr, ThreadU {
                quota_4k: post.thr_mp.spec_index(thread_ptr).view().quota_4k,
                syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(),
                ..kernel_k_to_kernel_u(*pre).thread_map.spec_index(thread_ptr)
            }),
            ..kernel_k_to_kernel_u(*pre)
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    pre.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr);
    post.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr);
    pre.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
    post.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
    kernel_cpu_projection_at(pre, cpu_id); kernel_cpu_projection_at(post, cpu_id);
    if pre.prc_mp.dom().contains(process_ptr) { kernel_process_projection_at(pre, process_ptr); }
    if pre.thr_mp.dom().contains(thread_ptr) { kernel_thread_projection_at(pre, thread_ptr); }
    assert(pre.cpu_arr.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    assert(pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr)
        ==> pre.prc_mp.dom().contains(process_ptr) && !pre.prc_mp.spec_index(process_ptr).view().zombie && pre.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr) by {
        reveal(process_cpu_wf); reveal(process_pagetable_match);
    };
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => {
        if pre.ctn_mp.dom().contains(c) { kernel_container_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_projection_at(post, c); }
    });
    assert_maps_equal!(post_u.process_map, pre_u.process_map, p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } reveal(process_pagetable_match);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread_ptr, ThreadU {
        quota_4k: post.thr_mp.spec_index(thread_ptr).view().quota_4k,
        syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(),
        ..pre_u.thread_map.spec_index(thread_ptr)
    }), t => { if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_projection_at(post, t); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => {
        if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(post, e); }
    });
}

/// A section that changes one thread's quota, temporary cache, and progress and publishes one
/// present 4K entry of the running process's pagetable changes only that thread and that
/// process's pagetable mapping in the complete projection. `lctx` is aligned with `post` and
/// write-holds the cpu, thread, and pagetable across the section.
#[verifier::spinoff_prover]
pub proof fn kernel_thread_quota_4k_progress_and_4k_mapping_added_implies_u_step(pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(post, lctx),
        pre.thr_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        pre.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, pg_arr: post.pg_arr, thr_mp: post.thr_mp, ..*pre }),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread {
            quota_4k: post.thr_mp.spec_index(thread_ptr).view().quota_4k,
            temp_alloc_cache_4k: post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k,
            syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress,
            ..pre.thr_mp.spec_index(thread_ptr).view()
        }),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, post.pt_lower.view().spec_index(pagetable_ptr)),
        !pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(va),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k().insert(va, pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(va)),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(va).present,
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_2m() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g(),
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(va).addr)).view().view().state is Owned4k,
    ensures
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let thread = pre.thr_mp.spec_index(thread_ptr).view();
            let process = pre_u.process_map.spec_index(process_ptr);
            let addr = pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(va).addr;
            &&& pre_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& pre_u.cpu_array[cpu_id as int].current_thread == pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread
            &&& pre_u.thread_map.dom().contains(thread_ptr)
            &&& pre_u.thread_map.spec_index(thread_ptr).lock_state is WriteLocked
            &&& pre_u.thread_map.spec_index(thread_ptr).owning_container == thread.owning_container
            &&& pre_u.thread_map.spec_index(thread_ptr).owning_proc == thread.owning_proc
            &&& pre_u.thread_map.spec_index(thread_ptr).quota_4k == thread.quota_4k
            &&& pre_u.thread_map.spec_index(thread_ptr).syscall_progress == thread.syscall_progress.view()
            &&& pre_u.process_map.dom().contains(process_ptr)
            &&& process.pagetable is Some
            &&& process.pagetable->Some_0.lock_state is WriteLocked
            &&& !process.pagetable->Some_0.mapping_4k.dom().contains(va)
            &&& forall|p: RwLockProcessPtr, v: VAddr| #![trigger pre_u.process_map[p].pagetable->Some_0.mapping_4k[v]]
                pre_u.process_map.dom().contains(p) && pre_u.process_map[p].pagetable is Some && pre_u.process_map[p].pagetable->Some_0.mapping_4k.dom().contains(v)
                ==> pre_u.process_map[p].pagetable->Some_0.mapping_4k[v].addr != addr
        }),
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let process = pre_u.process_map.spec_index(process_ptr);
            let pagetable = process.pagetable->Some_0;
            let entry = pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(va);
            kernel_k_to_kernel_u(*post) == (KernelU {
                thread_map: pre_u.thread_map.insert(thread_ptr, ThreadU {
                    quota_4k: post.thr_mp.spec_index(thread_ptr).view().quota_4k,
                    syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(),
                    ..pre_u.thread_map.spec_index(thread_ptr)
                }),
                process_map: pre_u.process_map.insert(process_ptr, ProcessU {
                    pagetable: Some(PageTableU { mapping_4k: pagetable.mapping_4k.insert(va, entry), ..pagetable }),
                    ..process
                }),
                ..pre_u
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let process = pre_u.process_map.spec_index(process_ptr);
    let pagetable = process.pagetable->Some_0;
    let entry = pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(va);
    let new_pagetable = PageTableU { mapping_4k: pagetable.mapping_4k.insert(va, entry), ..pagetable };
    pre.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr);
    post.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr);
    pre.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
    post.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
    kernel_cpu_projection_at(post, cpu_id);
    if pre.prc_mp.dom().contains(process_ptr) { kernel_process_projection_at(pre, process_ptr); } if post.prc_mp.dom().contains(process_ptr) { kernel_process_projection_at(post, process_ptr); }
    if pre.thr_mp.dom().contains(thread_ptr) { kernel_thread_projection_at(pre, thread_ptr); } if post.thr_mp.dom().contains(thread_ptr) { kernel_thread_projection_at(post, thread_ptr); }
    assert(pre.cpu_arr.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    assert(pre.prc_mp.dom().contains(process_ptr) && !pre.prc_mp.spec_index(process_ptr).view().zombie && pre.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr) by { reveal(process_cpu_wf); reveal(process_pagetable_match); };
    assert(pagetable == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).user_view(pre.pt_mp.spec_index(pagetable_ptr).lock_state_u()));
    assert(post_u.process_map.spec_index(process_ptr).pagetable == Some(new_pagetable)) by {
        assert_maps_equal!(pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).user_view(post.pt_mp.spec_index(pagetable_ptr).lock_state_u()).mapping_4k, new_pagetable.mapping_4k);
    };
    assert(forall|p: RwLockProcessPtr, v: VAddr| #![trigger pre_u.process_map[p].pagetable->Some_0.mapping_4k[v]]
        pre_u.process_map.dom().contains(p) && pre_u.process_map[p].pagetable is Some && pre_u.process_map[p].pagetable->Some_0.mapping_4k.dom().contains(v)
        ==> pre_u.process_map[p].pagetable->Some_0.mapping_4k[v].addr != entry.addr) by { reveal(kernel_k_to_kernel_u); reveal(process_pagetable_match); reveal(mapped_4k_page_pagetable_wf); };
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => {
        if pre.ctn_mp.dom().contains(c) { kernel_container_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_projection_at(post, c); }
    });
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(process_ptr, ProcessU { pagetable: Some(new_pagetable), ..process }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } reveal(process_pagetable_match);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread_ptr, ThreadU {
        quota_4k: post.thr_mp.spec_index(thread_ptr).view().quota_4k,
        syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(),
        ..pre_u.thread_map.spec_index(thread_ptr)
    }), t => { if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_projection_at(post, t); } });
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, p => {
        if pre.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(pre, p); } if post.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(post, p); }
    });
}

/// Setting the cpu, thread, and pagetable lock modes to the thread's mode and replacing the
/// thread's progress changes only those three projections. `lctx` is aligned with `pre`; the
/// objects it write-holds project as write-locked before the section.
#[verifier::spinoff_prover]
pub proof fn kernel_cpu_thread_pagetable_lock_states_and_progress_changed_implies_u_step(pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot)
    requires
        process_cpu_wf(pre.prc_mp, pre.cpu_arr),
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        typed_lock_maps_aligned(pre, lctx),
        index_valid(NUM_CPUS, cpu_id),
        *post == (KernelK { cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, thr_mp: post.thr_mp, pt_mp: post.pt_mp, ..*pre }),
        post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, cpu_id),
        post.cpu_arr.spec_index(cpu_id).view().view().view() == pre.cpu_arr.spec_index(cpu_id).view().view().view(),
        forall|i: CpuId| #![trigger post.cpu_op.view().view()[i as int]] index_valid(NUM_CPUS, i) && i != cpu_id ==> post.cpu_op.view().view()[i as int] == pre.cpu_op.view().view()[i as int],
        post.cpu_arr.spec_index(cpu_id).value.being_killed() == pre.cpu_arr.spec_index(cpu_id).value.being_killed(),
        (post.cpu_arr.spec_index(cpu_id).value.locking_thread() is Write) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Write),
        (post.cpu_arr.spec_index(cpu_id).value.locking_thread() is Read) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Read),
        pre.thr_mp.dom().contains(thread_ptr),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        post.pt_mp.spec_index(pagetable_ptr).view() == pre.pt_mp.spec_index(pagetable_ptr).view(),
        (post.pt_mp.spec_index(pagetable_ptr).locking_thread() is Write) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Write),
        (post.pt_mp.spec_index(pagetable_ptr).locking_thread() is Read) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Read),
    ensures
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let thread = pre.thr_mp.spec_index(thread_ptr).view();
            let process = pre_u.process_map.spec_index(process_ptr);
            &&& pre_u.thread_map.dom().contains(thread_ptr)
            &&& pre_u.thread_map.spec_index(thread_ptr).owning_proc == thread.owning_proc
            &&& pre_u.thread_map.spec_index(thread_ptr).syscall_progress == thread.syscall_progress.view()
            &&& pre_u.process_map.dom().contains(process_ptr)
            &&& process.pagetable is Some
            &&& typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) ==> pre_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write) ==> pre_u.thread_map.spec_index(thread_ptr).lock_state is WriteLocked
            &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) ==> process.pagetable->Some_0.lock_state is WriteLocked
            &&& pre_u.cpu_array[cpu_id as int].lock_state == pre.cpu_arr.spec_index(cpu_id).value.lock_state_u()
            &&& pre_u.cpu_array[cpu_id as int].state == pre.cpu_arr.spec_index(cpu_id).view().view().view().state
            &&& pre_u.cpu_array[cpu_id as int].current_thread == pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread
            &&& pre_u.thread_map.spec_index(thread_ptr).lock_state == pre.thr_mp.spec_index(thread_ptr).lock_state_u()
            &&& pre_u.thread_map.spec_index(thread_ptr).killed == pre.thr_mp.spec_index(thread_ptr).being_killed()
            &&& pre_u.thread_map.spec_index(thread_ptr).quota_4k == thread.quota_4k
            &&& process.pagetable->Some_0.lock_state == pre.pt_mp.spec_index(pagetable_ptr).lock_state_u()
            &&& process.pagetable->Some_0.mapping_4k.dom().subset_of(pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k().dom())
            &&& process.pagetable->Some_0.mapping_2m.dom().subset_of(pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m().dom())
            &&& process.pagetable->Some_0.mapping_1g.dom().subset_of(pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g().dom())
        }),
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let lock_state = post.thr_mp.spec_index(thread_ptr).lock_state_u();
            let process = pre_u.process_map.spec_index(process_ptr);
            kernel_k_to_kernel_u(*post) == (KernelU {
                cpu_array: pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state, op: post.cpu_op.view().view()[cpu_id as int], ..pre_u.cpu_array[cpu_id as int] }),
                thread_map: pre_u.thread_map.insert(thread_ptr, ThreadU {
                    lock_state, syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..pre_u.thread_map.spec_index(thread_ptr)
                }),
                process_map: pre_u.process_map.insert(process_ptr, ProcessU { pagetable: Some(PageTableU { lock_state, ..process.pagetable->Some_0 }), ..process }),
                ..pre_u
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let lock_state = post.thr_mp.spec_index(thread_ptr).lock_state_u();
    let process = pre_u.process_map.spec_index(process_ptr);
    kernel_cpu_projection_at(pre, cpu_id);
    if pre.prc_mp.dom().contains(process_ptr) { kernel_process_projection_at(pre, process_ptr); } if post.prc_mp.dom().contains(process_ptr) { kernel_process_projection_at(post, process_ptr); }
    if pre.thr_mp.dom().contains(thread_ptr) { kernel_thread_projection_at(pre, thread_ptr); }
    assert(pre.prc_mp.dom().contains(process_ptr) && !pre.prc_mp.spec_index(process_ptr).view().zombie && pre.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr) by { reveal(process_cpu_wf); reveal(process_pagetable_match); };
    assert(typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) ==> pre.cpu_arr.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    if typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write) { pre.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr); }
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) { pre.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); }
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state, op: post.cpu_op.view().view()[cpu_id as int], ..pre_u.cpu_array[cpu_id as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); }
    });
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(process_ptr, ProcessU { pagetable: Some(PageTableU { lock_state, ..process.pagetable->Some_0 }), ..process }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } reveal(process_pagetable_match);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread_ptr, ThreadU {
        lock_state, syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..pre_u.thread_map.spec_index(thread_ptr)
    }), t => { if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_projection_at(post, t); } });
    assert_maps_equal!(post_u.container_map, pre_u.container_map, p => {
        if pre.ctn_mp.dom().contains(p) { kernel_container_projection_at(pre, p); } if post.ctn_mp.dom().contains(p) { kernel_container_projection_at(post, p); }
    });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, p => {
        if pre.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(pre, p); } if post.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(post, p); }
    });
}

/// Setting the lock modes of cpu `cpu_id` and its thread `thread_ptr` to the thread's mode, with at most one pagetable
/// `table` whose payload and lock mode the section restored, changes only those two lock projections. `lctx` is aligned
/// with `pre`; the objects it write-holds project as write-locked before the section. The cpu's running state is `post`'s.
pub proof fn kernel_cpu_thread_lock_states_changed_implies_u_step(pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, table: Option<RwLockPageTableRoot>)
    requires
        typed_lock_maps_aligned(pre, lctx),
        index_valid(NUM_CPUS, cpu_id),
        *post == (KernelK { cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, thr_mp: post.thr_mp, pt_mp: post.pt_mp, ..*pre }),
        post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, cpu_id),
        post.cpu_arr.spec_index(cpu_id).view().view().view() == pre.cpu_arr.spec_index(cpu_id).view().view().view(),
        forall|i: CpuId| #![trigger post.cpu_op.view().view()[i as int]] index_valid(NUM_CPUS, i) && i != cpu_id ==> post.cpu_op.view().view()[i as int] == pre.cpu_op.view().view()[i as int],
        post.cpu_arr.spec_index(cpu_id).value.being_killed() == pre.cpu_arr.spec_index(cpu_id).value.being_killed(),
        (post.cpu_arr.spec_index(cpu_id).value.locking_thread() is Write) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Write),
        (post.cpu_arr.spec_index(cpu_id).value.locking_thread() is Read) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Read),
        pre.thr_mp.dom().contains(thread_ptr),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == pre.thr_mp.spec_index(thread_ptr).view(),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
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
            &&& pre_u.thread_map.dom().contains(thread_ptr)
            &&& pre_u.thread_map.spec_index(thread_ptr).syscall_progress == pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()
            &&& typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) ==> pre_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write) ==> pre_u.thread_map.spec_index(thread_ptr).lock_state is WriteLocked
            &&& pre_u.cpu_array[cpu_id as int].current_thread == pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread
        }),
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let lock_state = post.thr_mp.spec_index(thread_ptr).lock_state_u();
            kernel_k_to_kernel_u(*post) == (KernelU {
                cpu_array: pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state, op: post.cpu_op.view().view()[cpu_id as int], ..pre_u.cpu_array[cpu_id as int] }),
                thread_map: pre_u.thread_map.insert(thread_ptr, ThreadU { lock_state, ..pre_u.thread_map.spec_index(thread_ptr) }),
                ..pre_u
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let lock_state = post.thr_mp.spec_index(thread_ptr).lock_state_u();
    kernel_cpu_projection_at(pre, cpu_id); kernel_thread_projection_at(pre, thread_ptr);
    assert(typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) ==> pre.cpu_arr.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    if typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write) { pre.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr); }
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state, op: post.cpu_op.view().view()[cpu_id as int], ..pre_u.cpu_array[cpu_id as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); }
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread_ptr, ThreadU { lock_state, ..pre_u.thread_map.spec_index(thread_ptr) }), t => {
        if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_projection_at(post, t); }
    });
    assert_maps_equal!(pagetable_map_user_view(post.pt_mp, post.pt_lower.view()), pagetable_map_user_view(pre.pt_mp, pre.pt_lower.view()));
    assert_maps_equal!(post_u.process_map, pre_u.process_map, p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
    });
    assert_maps_equal!(post_u.container_map, pre_u.container_map, p => {
        if pre.ctn_mp.dom().contains(p) { kernel_container_projection_at(pre, p); } if post.ctn_mp.dom().contains(p) { kernel_container_projection_at(post, p); }
    });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, p => {
        if pre.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(pre, p); } if post.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(post, p); }
    });
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
        },
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)] pre.it_mp.dom().contains(p) ==> {
            &&& (post.it_mp.spec_index(p).locking_thread() is Write) == (pre.it_mp.spec_index(p).locking_thread() is Write)
            &&& (post.it_mp.spec_index(p).locking_thread() is Read) == (pre.it_mp.spec_index(p).locking_thread() is Read)
        },
        forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)] pre.thr_mp.dom().contains(p) ==> {
            &&& (post.thr_mp.spec_index(p).locking_thread() is Write) == (pre.thr_mp.spec_index(p).locking_thread() is Write)
            &&& (post.thr_mp.spec_index(p).locking_thread() is Read) == (pre.thr_mp.spec_index(p).locking_thread() is Read)
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

/// Setting the cpu, container, process, pagetable, and thread lock modes to the thread's mode and
/// replacing the thread's progress changes only those five projections. `lctx` is aligned with
/// `pre`; the objects it write-holds project as write-locked before the section.
#[verifier::spinoff_prover]
pub proof fn kernel_thread_context_lock_states_and_progress_changed_implies_u_step(pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot)
    requires
        process_cpu_wf(pre.prc_mp, pre.cpu_arr),
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        typed_lock_maps_aligned(pre, lctx),
        index_valid(NUM_CPUS, cpu_id),
        *post == (KernelK { cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, ctn_mp: post.ctn_mp, prc_mp: post.prc_mp, thr_mp: post.thr_mp, pt_mp: post.pt_mp, ..*pre }),
        post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, cpu_id),
        post.cpu_arr.spec_index(cpu_id).view().view().view() == pre.cpu_arr.spec_index(cpu_id).view().view().view(),
        forall|i: CpuId| #![trigger post.cpu_op.view().view()[i as int]] index_valid(NUM_CPUS, i) && i != cpu_id ==> post.cpu_op.view().view()[i as int] == pre.cpu_op.view().view()[i as int],
        post.cpu_arr.spec_index(cpu_id).value.being_killed() == pre.cpu_arr.spec_index(cpu_id).value.being_killed(),
        (post.cpu_arr.spec_index(cpu_id).value.locking_thread() is Write) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Write),
        (post.cpu_arr.spec_index(cpu_id).value.locking_thread() is Read) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Read),
        post.ctn_mp.unchanged_except(&pre.ctn_mp, container_ptr),
        post.ctn_mp.spec_index(container_ptr).view() == pre.ctn_mp.spec_index(container_ptr).view(),
        post.ctn_mp.spec_index(container_ptr).view_rodata() == pre.ctn_mp.spec_index(container_ptr).view_rodata(),
        post.ctn_mp.spec_index(container_ptr).view_ghost() == pre.ctn_mp.spec_index(container_ptr).view_ghost(),
        post.ctn_mp.spec_index(container_ptr).being_killed() == pre.ctn_mp.spec_index(container_ptr).being_killed(),
        (post.ctn_mp.spec_index(container_ptr).locking_thread() is Write) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Write),
        (post.ctn_mp.spec_index(container_ptr).locking_thread() is Read) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Read),
        post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr),
        post.prc_mp.spec_index(process_ptr).view() == pre.prc_mp.spec_index(process_ptr).view(),
        post.prc_mp.spec_index(process_ptr).view_rodata() == pre.prc_mp.spec_index(process_ptr).view_rodata(),
        post.prc_mp.spec_index(process_ptr).view_ghost() == pre.prc_mp.spec_index(process_ptr).view_ghost(),
        post.prc_mp.spec_index(process_ptr).being_killed() == pre.prc_mp.spec_index(process_ptr).being_killed(),
        (post.prc_mp.spec_index(process_ptr).locking_thread() is Write) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Write),
        (post.prc_mp.spec_index(process_ptr).locking_thread() is Read) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Read),
        pre.thr_mp.dom().contains(thread_ptr),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        post.pt_mp.spec_index(pagetable_ptr).view() == pre.pt_mp.spec_index(pagetable_ptr).view(),
        (post.pt_mp.spec_index(pagetable_ptr).locking_thread() is Write) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Write),
        (post.pt_mp.spec_index(pagetable_ptr).locking_thread() is Read) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Read),
    ensures
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let thread = pre.thr_mp.spec_index(thread_ptr).view();
            let process = pre_u.process_map.spec_index(process_ptr);
            &&& pre_u.container_map.dom().contains(container_ptr)
            &&& pre_u.thread_map.dom().contains(thread_ptr)
            &&& pre_u.thread_map.spec_index(thread_ptr).owning_container == thread.owning_container
            &&& pre_u.thread_map.spec_index(thread_ptr).owning_proc == thread.owning_proc
            &&& pre_u.thread_map.spec_index(thread_ptr).syscall_progress == thread.syscall_progress.view()
            &&& pre_u.process_map.dom().contains(process_ptr)
            &&& process.pagetable is Some
            &&& typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) ==> pre_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write) ==> pre_u.container_map.spec_index(container_ptr).lock_state is WriteLocked
            &&& typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write) ==> process.lock_state is WriteLocked
            &&& typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write) ==> pre_u.thread_map.spec_index(thread_ptr).lock_state is WriteLocked
            &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) ==> process.pagetable->Some_0.lock_state is WriteLocked
            &&& pre_u.cpu_array[cpu_id as int].lock_state == pre.cpu_arr.spec_index(cpu_id).value.lock_state_u()
            &&& pre_u.container_map.spec_index(container_ptr).lock_state == pre.ctn_mp.spec_index(container_ptr).lock_state_u()
            &&& process.lock_state == pre.prc_mp.spec_index(process_ptr).lock_state_u()
            &&& pre_u.thread_map.spec_index(thread_ptr).lock_state == pre.thr_mp.spec_index(thread_ptr).lock_state_u()
            &&& process.pagetable->Some_0.lock_state == pre.pt_mp.spec_index(pagetable_ptr).lock_state_u()
            &&& pre_u.cpu_array[cpu_id as int].state == pre.cpu_arr.spec_index(cpu_id).view().view().view().state
            &&& pre_u.cpu_array[cpu_id as int].current_thread == pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread
            &&& pre_u.container_map.spec_index(container_ptr).killed == pre.ctn_mp.spec_index(container_ptr).being_killed()
            &&& pre_u.container_map.spec_index(container_ptr).zombie == pre.ctn_mp.spec_index(container_ptr).view().zombie
            &&& process.killed == pre.prc_mp.spec_index(process_ptr).being_killed()
            &&& pre_u.thread_map.spec_index(thread_ptr).killed == pre.thr_mp.spec_index(thread_ptr).being_killed()
            &&& forall|va: VAddr| #![trigger process.pagetable->Some_0.mapping_4k.dom().contains(va)]
                pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(va) && pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k()[va].present
                ==> process.pagetable->Some_0.mapping_4k.dom().contains(va)
        }),
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let lock_state = post.thr_mp.spec_index(thread_ptr).lock_state_u();
            let process = pre_u.process_map.spec_index(process_ptr);
            kernel_k_to_kernel_u(*post) == (KernelU {
                cpu_array: pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state, op: post.cpu_op.view().view()[cpu_id as int], ..pre_u.cpu_array[cpu_id as int] }),
                container_map: pre_u.container_map.insert(container_ptr, ContainerU {
                    lock_state, lock_process_owner: if lock_state is WriteLocked { post.ctn_mp.spec_index(container_ptr).lock_process_owner_u() } else { None }, ..pre_u.container_map.spec_index(container_ptr)
                }),
                process_map: pre_u.process_map.insert(process_ptr, ProcessU { lock_state, pagetable: Some(PageTableU { lock_state, ..process.pagetable->Some_0 }), ..process }),
                thread_map: pre_u.thread_map.insert(thread_ptr, ThreadU {
                    lock_state, syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..pre_u.thread_map.spec_index(thread_ptr)
                }),
                ..pre_u
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let lock_state = post.thr_mp.spec_index(thread_ptr).lock_state_u();
    let process = pre_u.process_map.spec_index(process_ptr);
    kernel_cpu_projection_at(pre, cpu_id);
    if pre.prc_mp.dom().contains(process_ptr) { kernel_process_projection_at(pre, process_ptr); }
    if pre.thr_mp.dom().contains(thread_ptr) { kernel_thread_projection_at(pre, thread_ptr); } if post.thr_mp.dom().contains(thread_ptr) { kernel_thread_projection_at(post, thread_ptr); }
    if pre.ctn_mp.dom().contains(container_ptr) { kernel_container_projection_at(pre, container_ptr); }
    assert(pre.prc_mp.dom().contains(process_ptr) && !pre.prc_mp.spec_index(process_ptr).view().zombie && pre.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr) by { reveal(process_cpu_wf); reveal(process_pagetable_match); };
    assert(typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) ==> pre.cpu_arr.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    if typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write) { pre.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), container_ptr); }
    if typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write) { pre.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), process_ptr); }
    if typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write) { pre.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr); }
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) { pre.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); }
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state, op: post.cpu_op.view().view()[cpu_id as int], ..pre_u.cpu_array[cpu_id as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); }
    });
    assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(container_ptr, ContainerU {
        lock_state, lock_process_owner: if lock_state is WriteLocked { post.ctn_mp.spec_index(container_ptr).lock_process_owner_u() } else { None }, ..pre_u.container_map.spec_index(container_ptr)
    }), c => {
        if pre.ctn_mp.dom().contains(c) { kernel_container_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_projection_at(post, c); }
    });
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(process_ptr, ProcessU {
        lock_state, pagetable: Some(PageTableU { lock_state, ..process.pagetable->Some_0 }), ..process
    }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } reveal(process_pagetable_match);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread_ptr, ThreadU {
        lock_state, syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..pre_u.thread_map.spec_index(thread_ptr)
    }), t => { if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_projection_at(post, t); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, p => {
        if pre.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(pre, p); } if post.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(post, p); }
    });
}

/// Equal per-element business fields imply equal nonlock projections.
/// Complete U equality additionally requires equal observable lock modes.
pub proof fn kernel_no_change_to_nonlock_fields_imply_kernel_u_nonlock_eq(pre: &KernelK, post: &KernelK)
    requires
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        post.irt.view().owners() == pre.irt.view().owners(),
        post.irt.view().iommu_roots() == pre.irt.view().iommu_roots(),
        post.cpu_tlb.view() == pre.cpu_tlb.view(),
        post.iommu_tlb.view() == pre.iommu_tlb.view(),
        post.dflt_pt == pre.dflt_pt,
        kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
        // This connects each process's projected pagetable pointer to the
        // domain on which the per-entry framing premise below applies.
        // Domain equality alone does not constrain `Map::spec_index` at a
        // process-referenced key unless that key is known to be present.
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        process_iommu_table_match(pre.prc_mp, pre.it_mp),
        kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view()),
        kernel_iommu_table_nonlock_fields_unchanged(pre.it_mp, post.it_mp),
        // process_map: same domain, and per process only the fields
        // `ProcessU` projects are read — quota/children fields off `view()`,
        // tree closure fields off `view_ghost()`, `parent`/`depth` off
        // `view_rodata()`, and `being_killed()`. NOT
        // the whole `view()`: other kernel-only fields are unprojected.
        post.prc_mp.dom() =~= pre.prc_mp.dom(),
        forall|ptr: RwLockProcessPtr|
            #![trigger post.prc_mp.spec_index(ptr)]
            pre.prc_mp.dom().contains(ptr) ==>
                post.prc_mp.spec_index(ptr).view().zombie == pre.prc_mp.spec_index(ptr).view().zombie
                && post.prc_mp.spec_index(ptr).view().quota_4k == pre.prc_mp.spec_index(ptr).view().quota_4k
                && post.prc_mp.spec_index(ptr).view().quota_2m == pre.prc_mp.spec_index(ptr).view().quota_2m
                && post.prc_mp.spec_index(ptr).view().quota_1g == pre.prc_mp.spec_index(ptr).view().quota_1g
                && post.prc_mp.spec_index(ptr).view().children.view() == pre.prc_mp.spec_index(ptr).view().children.view()
                && post.prc_mp.spec_index(ptr).view_ghost().uppertree_seq.view() == pre.prc_mp.spec_index(ptr).view_ghost().uppertree_seq.view()
                && post.prc_mp.spec_index(ptr).view_ghost().subtree_set.view() == pre.prc_mp.spec_index(ptr).view_ghost().subtree_set.view()
                && post.prc_mp.spec_index(ptr).view().owned_threads.view() == pre.prc_mp.spec_index(ptr).view().owned_threads.view()
                && post.prc_mp.spec_index(ptr).view().pagetable == pre.prc_mp.spec_index(ptr).view().pagetable
                && post.prc_mp.spec_index(ptr).view().iommu_table == pre.prc_mp.spec_index(ptr).view().iommu_table
                && post.prc_mp.spec_index(ptr).view_ghost().owned_pci_functions.view() == pre.prc_mp.spec_index(ptr).view_ghost().owned_pci_functions.view()
                && post.prc_mp.spec_index(ptr).view_rodata() == pre.prc_mp.spec_index(ptr).view_rodata()
                && post.prc_mp.spec_index(ptr).being_killed() == pre.prc_mp.spec_index(ptr).being_killed(),
        post.thr_mp.dom() =~= pre.thr_mp.dom(),
        forall|ptr: RwLockThreadPtr|
            #![trigger post.thr_mp.spec_index(ptr)]
            pre.thr_mp.dom().contains(ptr) ==>
                post.thr_mp.spec_index(ptr).view().state == pre.thr_mp.spec_index(ptr).view().state
                && post.thr_mp.spec_index(ptr).view().caller == pre.thr_mp.spec_index(ptr).view().caller
                && post.thr_mp.spec_index(ptr).view().callee == pre.thr_mp.spec_index(ptr).view().callee
                && post.thr_mp.spec_index(ptr).view().owning_container == pre.thr_mp.spec_index(ptr).view().owning_container
                && post.thr_mp.spec_index(ptr).view().owning_proc == pre.thr_mp.spec_index(ptr).view().owning_proc
                && post.thr_mp.spec_index(ptr).view().last_cpu == pre.thr_mp.spec_index(ptr).view().last_cpu
                && post.thr_mp.spec_index(ptr).view().quota_4k == pre.thr_mp.spec_index(ptr).view().quota_4k
                && post.thr_mp.spec_index(ptr).view().quota_2m == pre.thr_mp.spec_index(ptr).view().quota_2m
                && post.thr_mp.spec_index(ptr).view().quota_1g == pre.thr_mp.spec_index(ptr).view().quota_1g
                && post.thr_mp.spec_index(ptr).view().endpoint_descriptors.view() == pre.thr_mp.spec_index(ptr).view().endpoint_descriptors.view()
                && post.thr_mp.spec_index(ptr).view().blocking_endpoint_ptr == pre.thr_mp.spec_index(ptr).view().blocking_endpoint_ptr
                && post.thr_mp.spec_index(ptr).view().ipc_payload == pre.thr_mp.spec_index(ptr).view().ipc_payload
                && post.thr_mp.spec_index(ptr).view().error_code == pre.thr_mp.spec_index(ptr).view().error_code
                && post.thr_mp.spec_index(ptr).view().trap_frame == pre.thr_mp.spec_index(ptr).view().trap_frame
                && post.thr_mp.spec_index(ptr).view().syscall_progress == pre.thr_mp.spec_index(ptr).view().syscall_progress
                && post.thr_mp.spec_index(ptr).being_killed() == pre.thr_mp.spec_index(ptr).being_killed(),
        // cpu_array: per-slot payload `view()`.
        forall|i: usize|
            #![trigger post.cpu_arr.spec_index(i).value.view()]
            index_valid(NUM_CPUS, i) ==> post.cpu_arr.spec_index(i).value.view() == pre.cpu_arr.spec_index(i).value.view() && post.cpu_arr.spec_index(i).value.being_killed() == pre.cpu_arr.spec_index(i).value.being_killed(),
    ensures
        kernel_k_to_nonlock_kernel_u(*pre) == kernel_k_to_nonlock_kernel_u(*post),
{
    kernel_u_nonlock_domains_projection(pre); kernel_u_nonlock_domains_projection(post);
    reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
    reveal(kernel_endpoint_nonlock_fields_unchanged);
    let pre_u = kernel_k_to_nonlock_kernel_u(*pre);
    let post_u = kernel_k_to_nonlock_kernel_u(*post);
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(IommuRootTable::user_view); };
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_nonlock_projection_at(pre, i as usize); kernel_cpu_nonlock_projection_at(post, i as usize); } });
    assert_maps_equal!(post_u.container_map, pre_u.container_map, ptr => { if pre.ctn_mp.dom().contains(ptr) { kernel_container_nonlock_projection_at(pre, ptr); } if post.ctn_mp.dom().contains(ptr) { kernel_container_nonlock_projection_at(post, ptr); } });
    assert_maps_equal!(post_u.process_map, pre_u.process_map, ptr => {
        if pre.prc_mp.dom().contains(ptr) { kernel_process_nonlock_projection_at(pre, ptr); } if post.prc_mp.dom().contains(ptr) { kernel_process_nonlock_projection_at(post, ptr); }
        reveal(process_pagetable_match); reveal(process_iommu_table_match); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map, ptr => { if pre.thr_mp.dom().contains(ptr) { kernel_thread_nonlock_projection_at(pre, ptr); } if post.thr_mp.dom().contains(ptr) { kernel_thread_nonlock_projection_at(post, ptr); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, ptr => { if pre.ep_mp.dom().contains(ptr) { kernel_endpoint_nonlock_projection_at(pre, ptr); } if post.ep_mp.dom().contains(ptr) { kernel_endpoint_nonlock_projection_at(post, ptr); } });
}
} // verus!
