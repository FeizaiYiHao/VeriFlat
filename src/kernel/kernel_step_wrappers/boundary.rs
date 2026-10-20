use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal, assert_sets_equal};
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
        reveal(process_pagetable_match); reveal(process_iommu_table_match);
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
proof fn kernel_thread_quota_4k_changed_implies_u_step(pre: &KernelK, post: &KernelK, thread_ptr: RwLockThreadPtr, delta: int)
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
    let container = pre_u.container_map.spec_index(container_ptr);
    let process = pre_u.process_map.spec_index(process_ptr);
    assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(container_ptr, ContainerU {
        quota_4k: (container.quota_4k as int - delta) as usize, ..container
    }), c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, include_lock_state, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, include_lock_state, c); } });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map, t => { if pre.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, include_lock_state, t); } if post.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(post, include_lock_state, t); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, include_lock_state, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, include_lock_state, e); } });
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
    let container = pre_u.container_map.spec_index(container_ptr);
    let process = pre_u.process_map.spec_index(process_ptr);
    assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(container_ptr, ContainerU {
        quota_2m: (container.quota_2m as int - delta) as usize, ..container
    }), c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, include_lock_state, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, include_lock_state, c); } });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map, t => { if pre.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, include_lock_state, t); } if post.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(post, include_lock_state, t); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, include_lock_state, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, include_lock_state, e); } });
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
    requires kernel_cpu_offline_request_changed(pre, post, cpu_id, container_ptr, target),
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
    assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(container_ptr, ContainerU {
        cpu_offline_requests: container.cpu_offline_requests.update(target as int, true), ..container
    }), c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, include_lock_state, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, include_lock_state, c); } });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map, t => { if pre.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, include_lock_state, t); } if post.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(post, include_lock_state, t); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, include_lock_state, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, include_lock_state, e); } });
    assert_maps_equal!(post_u.process_map, pre_u.process_map, p => { if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, include_lock_state, p); } if post.prc_mp.dom().contains(p) { kernel_process_user_projection_at(post, include_lock_state, p); } });
}

/// K→U: publishing Idle on an Off cpu changes only that `CpuU.state`.
pub(super) proof fn kernel_cpu_online_changed_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, target: CpuId, include_lock_state: bool)
    requires kernel_cpu_online_changed(pre, post, cpu_id, container_ptr, target),
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
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(target as int, CpuU { state: CpuState::Idle, ..target_cpu }), i => {
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
    kernel_cpu_state_set_and_current_cleared_implies_u_cpu_array(pre, post, cpu_id, CpuState::Off, include_lock_state);
    kernel_endpoint_nonlock_fields_and_locks_unchanged_implies_u_endpoint_map(pre, post, include_lock_state);
    kernel_process_nonlock_fields_and_locks_unchanged_implies_u_process_map(pre, post, include_lock_state);
    kernel_cpu_went_off_fields_implies_u_container_map(pre, post, cpu_id, regs, flushed_default_pcid, include_lock_state);
    kernel_cpu_went_off_fields_implies_u_thread_map(pre, post, cpu_id, regs, flushed_default_pcid, include_lock_state);
}

#[verifier::spinoff_prover]
proof fn kernel_process_added_implies_u_neq(pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr)
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

pub proof fn kernel_cpu_tlb_updated_implies_u_step(pre: &KernelK, post: &KernelK)
    requires
        *post == (KernelK { cpu_arr: post.cpu_arr, cpu_tlb: post.cpu_tlb, pcid_needflush: post.pcid_needflush, ..*pre }),
        kernel_cpu_nonlock_fields_unchanged(pre.cpu_arr, post.cpu_arr),
        forall|cpu: CpuId| #![trigger post.cpu_arr.spec_index(cpu)] index_valid(NUM_CPUS, cpu) ==>
            post.cpu_arr.spec_index(cpu).value.locking_thread() == pre.cpu_arr.spec_index(cpu).value.locking_thread(),
    ensures
        kernel_k_to_kernel_u(*post) == (KernelU { cpu_tlb: post.cpu_tlb.view(), ..kernel_k_to_kernel_u(*pre) }),
{ reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_k_to_kernel_u); assert_seqs_equal!(kernel_k_to_kernel_u(*post).cpu_array == kernel_k_to_kernel_u(*pre).cpu_array); }

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
    if index_valid(NUM_CPUS, cpu_id) { kernel_cpu_projection_at(pre, cpu_id); } if index_valid(NUM_CPUS, cpu_id) { kernel_cpu_projection_at(post, cpu_id); }
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
    if index_valid(NUM_CPUS, cpu_id) { kernel_cpu_projection_at(post, cpu_id); }
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
        *post == (KernelK { cpu_arr: post.cpu_arr, thr_mp: post.thr_mp, pt_mp: post.pt_mp, ..*pre }),
        post.cpu_arr.unchanged_except(&pre.cpu_arr, cpu_id),
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
                cpu_array: pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state, ..pre_u.cpu_array[cpu_id as int] }),
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
    if index_valid(NUM_CPUS, cpu_id) { kernel_cpu_projection_at(pre, cpu_id); }
    if pre.prc_mp.dom().contains(process_ptr) { kernel_process_projection_at(pre, process_ptr); } if post.prc_mp.dom().contains(process_ptr) { kernel_process_projection_at(post, process_ptr); }
    if pre.thr_mp.dom().contains(thread_ptr) { kernel_thread_projection_at(pre, thread_ptr); }
    assert(pre.prc_mp.dom().contains(process_ptr) && !pre.prc_mp.spec_index(process_ptr).view().zombie && pre.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr) by { reveal(process_cpu_wf); reveal(process_pagetable_match); };
    assert(typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) ==> pre.cpu_arr.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    if typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write) { pre.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr); }
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) { pre.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); }
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state, ..pre_u.cpu_array[cpu_id as int] }), i => {
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
        *post == (KernelK { cpu_arr: post.cpu_arr, ctn_mp: post.ctn_mp, prc_mp: post.prc_mp, thr_mp: post.thr_mp, pt_mp: post.pt_mp, ..*pre }),
        post.cpu_arr.unchanged_except(&pre.cpu_arr, cpu_id),
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
                cpu_array: pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state, ..pre_u.cpu_array[cpu_id as int] }),
                container_map: pre_u.container_map.insert(container_ptr, ContainerU { lock_state, ..pre_u.container_map.spec_index(container_ptr) }),
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
    if index_valid(NUM_CPUS, cpu_id) { kernel_cpu_projection_at(pre, cpu_id); }
    if pre.prc_mp.dom().contains(process_ptr) { kernel_process_projection_at(pre, process_ptr); }
    if pre.thr_mp.dom().contains(thread_ptr) { kernel_thread_projection_at(pre, thread_ptr); } if post.thr_mp.dom().contains(thread_ptr) { kernel_thread_projection_at(post, thread_ptr); }
    if pre.ctn_mp.dom().contains(container_ptr) { kernel_container_projection_at(pre, container_ptr); }
    assert(pre.prc_mp.dom().contains(process_ptr) && !pre.prc_mp.spec_index(process_ptr).view().zombie && pre.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr) by { reveal(process_cpu_wf); reveal(process_pagetable_match); };
    assert(typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) ==> pre.cpu_arr.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    if typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write) { pre.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), container_ptr); }
    if typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write) { pre.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), process_ptr); }
    if typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write) { pre.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr); }
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) { pre.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); }
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state, ..pre_u.cpu_array[cpu_id as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); }
    });
    assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(container_ptr, ContainerU { lock_state, ..pre_u.container_map.spec_index(container_ptr) }), c => {
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

impl KernelK {
    pub proof fn kernel_step_boundary_nonlock_fields_unchanged(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps)
        requires
            old(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(self).ep_mp),
            old(self).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
            old(self).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
            old(self).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(self).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(self)),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> {
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3 == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid
                &&& final(self).cpu_published[old(lctx).cpu_id() as int].view() == old(self).cpu_published[old(lctx).cpu_id() as int].view()
            },
            final(self).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|pt: RwLockPageTableRoot|
                #![trigger pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pt))]
                old(lctx).pagetable_lock_map().dom().contains(pt) && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt))
                    ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pt)),
            forall|pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr), final(self).cpu_tlb.spec_index((cpu_id, pcid))]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) && index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID ==> {
                    let before = old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    let after = final(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    after is Some && after.unwrap().pagetable_ptr == pagetable_ptr && (before is None || before.unwrap().pagetable_ptr != pagetable_ptr
                        || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(self).cpu_tlb.spec_index((cpu_id, pcid)), pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pagetable_ptr))
                        || (old(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush && old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                            && (!final(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush || final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)))
                    ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).cpu_tlb.spec_index((cpu_id, pcid)), pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pagetable_ptr))
                },
            forall|cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))]
                old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))
                ==> final(self).pcid_needflush.spec_index(cpu_id, pcid) == old(self).pcid_needflush.spec_index(cpu_id, pcid),
            forall|cpu_id: CpuId|
                #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)]
                old(lctx).cpu_lock_map().dom().contains(cpu_id) ==> final(self).cpu_arr.spec_index(cpu_id).view() == old(self).cpu_arr.spec_index(cpu_id).view(),
            forall|container_ptr: RwLockContainerPtr|
                #![trigger old(lctx).container_lock_map().dom().contains(container_ptr)]
                old(lctx).container_lock_map().dom().contains(container_ptr) ==> {
                    &&& final(self).ctn_mp.dom().contains(container_ptr)
                    &&& final(self).ctn_mp.lock_id_by_key(container_ptr) == old(self).ctn_mp.lock_id_by_key(container_ptr)
                    &&& final(self).ctn_mp.spec_index(container_ptr) == old(self).ctn_mp.spec_index(container_ptr)
                },
            forall|process_ptr: RwLockProcessPtr|
                #![trigger old(lctx).process_lock_map().dom().contains(process_ptr)]
                old(lctx).process_lock_map().dom().contains(process_ptr) ==> {
                    &&& final(self).prc_mp.dom().contains(process_ptr)
                    &&& final(self).prc_mp.lock_id_by_key(process_ptr) == old(self).prc_mp.lock_id_by_key(process_ptr)
                    &&& final(self).prc_mp.spec_index(process_ptr) == old(self).prc_mp.spec_index(process_ptr)
                },
            forall|thread_ptr: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(thread_ptr)]
                old(lctx).thread_lock_map().dom().contains(thread_ptr) ==> {
                    &&& final(self).thr_mp.dom().contains(thread_ptr)
                    &&& final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr)
                    &&& final(self).thr_mp.spec_index(thread_ptr) == old(self).thr_mp.spec_index(thread_ptr)
                },
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) ==> {
                    &&& final(self).pt_mp.dom().contains(pagetable_ptr)
                    &&& final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr)
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) ==> {
                        &&& final(self).pt_mp.spec_index(pagetable_ptr) == old(self).pt_mp.spec_index(pagetable_ptr)
                        &&& pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pagetable_ptr) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pagetable_ptr)
                    }
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read) ==> {
                        &&& final(self).pt_mp.spec_index(pagetable_ptr).view() == old(self).pt_mp.spec_index(pagetable_ptr).view()
                        &&& final(self).pt_mp.spec_index(pagetable_ptr).rlocked_by_thread(old(lctx).thread_id())
                        &&& final(self).pt_mp.spec_index(pagetable_ptr).being_killed() == old(self).pt_mp.spec_index(pagetable_ptr).being_killed()
                    }
                },
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self))),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view(),
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            final(self).dflt_pt == old(self).dflt_pt,
            containers_rodata_unchanged(old(self).ctn_mp, final(self).ctn_mp),
            processes_rodata_unchanged(old(self).prc_mp, final(self).prc_mp),
            held_containers_unchanged(old(self).ctn_mp, final(self).ctn_mp, old(lctx)),
            held_processes_unchanged(old(self).prc_mp, final(self).prc_mp, old(lctx)),
            held_threads_unchanged(old(self).thr_mp, final(self).thr_mp, old(lctx)),
            held_endpoints_unchanged(old(self).ep_mp, final(self).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(self).sched_mp, final(self).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(self).pcid_allc_mp, final(self).pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(self).cpu_set_mp, final(self).cpu_set_mp, old(lctx)),
            held_pagetables_unchanged(old(self).pt_mp, final(self).pt_mp, old(lctx)),
            held_pagetable_windows_unchanged(old(self).pt_mp, old(self).pt_lower.view(), final(self).pt_mp, final(self).pt_lower.view(), old(lctx)),
            held_iommu_tables_unchanged(old(self).it_mp, final(self).it_mp, old(lctx)),
            held_pages_unchanged(old(self).pg_arr, final(self).pg_arr, old(lctx)),
            held_cpus_unchanged(old(self).cpu_arr, final(self).cpu_arr, old(lctx)),
            held_allocator_objects_unchanged(old(self).allc_4k_mp, final(self).allc_4k_mp, old(lctx), PageSize::SZ4k),
            held_allocator_objects_unchanged(old(self).allc_2m_mp, final(self).allc_2m_mp, old(lctx), PageSize::SZ2m),
            held_allocator_objects_unchanged(old(self).allc_1g_mp, final(self).allc_1g_mp, old(lctx), PageSize::SZ1g),
            forall|p: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(p)] old(lctx).page_lock_map().dom().contains(p) ==> {
                let owner = old(self).pg_arr.spec_index(p).view().view().owning_container;
                &&& final(self).ctn_mp.dom().contains(owner)
                &&& final(self).ctn_mp.spec_index(owner).view_rodata() == old(self).ctn_mp.spec_index(owner).view_rodata()
            },
            forall|t: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(t)] old(lctx).thread_lock_map().dom().contains(t) ==> {
                let owner = old(self).thr_mp.spec_index(t).view().owning_container;
                &&& old(self).ctn_mp.dom().contains(owner)
                &&& final(self).ctn_mp.dom().contains(owner)
                &&& final(self).ctn_mp.spec_index(owner).view_rodata() == old(self).ctn_mp.spec_index(owner).view_rodata()
                &&& final(self).ctn_mp.spec_index(owner).view_ghost().uppertree_seq == old(self).ctn_mp.spec_index(owner).view_ghost().uppertree_seq
            },
            forall|pt: RwLockPageTableRoot, window_va: VAddr, va: VAddr|
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pt, window_va)), pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_4k().spec_index(va)]
                old(lctx).pagetable_lock_map().dom().contains(pt) && old(lctx).pagetable_window_lock_map().dom().contains((pt, window_va))
                    && spec_v2l4index(va) == spec_v2l4index(window_va) && spec_v2l3index(va) == spec_v2l3index(window_va) && spec_v2l2index(va) == spec_v2l2index(window_va)
                    && pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_4k().dom().contains(va) && page_ptr_valid(pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_4k().spec_index(va).addr) ==> {
                    let entry = pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_4k().spec_index(va);
                    let page_index = page_ptr2page_index(entry.addr);
                    &&& old(self).pg_arr.spec_index(page_index).view().view().owning_container == entry.owning_container.view()
                    &&& old(self).ctn_mp.dom().contains(entry.owning_container.view())
                    &&& final(self).ctn_mp.dom().contains(entry.owning_container.view())
                    &&& final(self).pg_arr.spec_index(page_index).view().view().state == PageState::Mapped4k
                    &&& final(self).pg_arr.spec_index(page_index).view().view().mappings().contains((pt, va))
                },
            forall|pt: RwLockPageTableRoot, va: VAddr|
                #![trigger typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pt, TypedLockMode::Write), pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_4k().spec_index(va)]
                typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pt, TypedLockMode::Write) && pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_4k().dom().contains(va)
                    && page_ptr_valid(pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_4k().spec_index(va).addr) ==> {
                    let entry = pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_4k().spec_index(va);
                    let page_index = page_ptr2page_index(entry.addr);
                    &&& old(self).pg_arr.spec_index(page_index).view().view().owning_container == entry.owning_container.view()
                    &&& old(self).ctn_mp.dom().contains(entry.owning_container.view())
                    &&& final(self).ctn_mp.dom().contains(entry.owning_container.view())
                    &&& final(self).pg_arr.spec_index(page_index).view().view().state == PageState::Mapped4k
                    &&& final(self).pg_arr.spec_index(page_index).view().view().mappings().contains((pt, va))
                },
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        assert(steps.nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*self)) by { kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(&steps.snapshot_k(), &*self); };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*self);
        old(self).thr_mp.typed_lock_map_aligned_held_in_dom(old(lctx).thread_lock_map(), old(lctx).thread_id()); old(self).pt_mp.typed_lock_map_aligned_held_in_dom(old(lctx).pagetable_lock_map(), old(lctx).thread_id());
        reveal(container_page_owner_wf); reveal(container_thread_wf); reveal(mapped_4k_page_pagetable_wf);
    }

    pub proof fn kernel_step_boundary_cpu_tlb_updated(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, cpu_id: CpuId, pcid: Pcid, flushed: bool)
        requires
            *old(self) == (KernelK { cpu_arr: old(self).cpu_arr, cpu_tlb: old(self).cpu_tlb, pcid_needflush: old(self).pcid_needflush, ..old(steps).snapshot_k() }),
            forall|cpu: CpuId| #![trigger old(self).cpu_arr.spec_index(cpu)] index_valid(NUM_CPUS, cpu) ==>
                old(self).cpu_arr.spec_index(cpu).value.locking_thread() == old(steps).snapshot_k().cpu_arr.spec_index(cpu).value.locking_thread(),
            old(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(self).ep_mp),
            old(self).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
            old(self).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
            index_valid(NUM_CPUS, cpu_id),
            pcid_valid(pcid),
            old(self).cpu_tlb.view() == if flushed {
                old(steps).snapshot_k().cpu_tlb.view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
            } else { old(steps).snapshot_k().cpu_tlb.view() },
            old(self).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(self)),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==>
                kernel_u_cpu_tlb_cleared(final(steps).view()[j].old_u, final(steps).view()[j].new_u, pcid),
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> {
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3 == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid
                &&& final(self).cpu_published[old(lctx).cpu_id() as int].view() == old(self).cpu_published[old(lctx).cpu_id() as int].view()
            },
            final(self).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|pt: RwLockPageTableRoot|
                #![trigger pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pt))]
                old(lctx).pagetable_lock_map().dom().contains(pt) && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt))
                    ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pt)),
            forall|pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr), final(self).cpu_tlb.spec_index((cpu_id, pcid))]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) && index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID ==> {
                    let before = old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    let after = final(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    after is Some && after.unwrap().pagetable_ptr == pagetable_ptr && (before is None || before.unwrap().pagetable_ptr != pagetable_ptr
                        || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(self).cpu_tlb.spec_index((cpu_id, pcid)), pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pagetable_ptr))
                        || (old(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush && old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                            && (!final(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush || final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)))
                    ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).cpu_tlb.spec_index((cpu_id, pcid)), pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pagetable_ptr))
                },
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self))),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == if old(self).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view() {
                old(steps).nonlock_view()
            } else {
                old(steps).nonlock_view().push(KernelStep { old_u: old(steps).nonlock_snapshot_u(),
                    new_u: KernelU { cpu_tlb: old(self).cpu_tlb.view(), ..old(steps).nonlock_snapshot_u() } })
            },
            old(steps).nonlock_view().len() <= final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + 1,
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
            held_containers_unchanged(old(self).ctn_mp, final(self).ctn_mp, old(lctx)),
            held_processes_unchanged(old(self).prc_mp, final(self).prc_mp, old(lctx)),
            held_threads_unchanged(old(self).thr_mp, final(self).thr_mp, old(lctx)),
            held_pagetables_unchanged(old(self).pt_mp, final(self).pt_mp, old(lctx)),
            forall|p: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), p, TypedLockMode::Write)
                ==> pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), p) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), p),
            held_pagetable_windows_unchanged(old(self).pt_mp, old(self).pt_lower.view(), final(self).pt_mp, final(self).pt_lower.view(), old(lctx)),
            held_iommu_tables_unchanged(old(self).it_mp, final(self).it_mp, old(lctx)),
            held_pages_unchanged(old(self).pg_arr, final(self).pg_arr, old(lctx)),
            held_cpus_unchanged(old(self).cpu_arr, final(self).cpu_arr, old(lctx)),
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        assert(kernel_k_to_kernel_u(*self) == (KernelU { cpu_tlb: self.cpu_tlb.view(), ..steps.snapshot_u() })) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
            kernel_cpu_tlb_updated_implies_u_step(&steps.snapshot_k(), &*self);
        };
        let pre_u = steps.nonlock_snapshot_u();
        let post_u = kernel_k_to_nonlock_kernel_u(*self);
        assert(post_u == (KernelU { cpu_tlb: self.cpu_tlb.view(), ..pre_u }) && pre_u.cpu_tlb == steps.snapshot_k().cpu_tlb.view()) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
            kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(&KernelK { cpu_tlb: self.cpu_tlb, ..steps.snapshot_k() }, self);
            reveal(kernel_k_to_nonlock_kernel_u);
        };
        assert(steps.snapshot_u() != kernel_k_to_kernel_u(*self) ==> kernel_u_cpu_tlb_cleared(steps.snapshot_u(), kernel_k_to_kernel_u(*self), pcid)) by {
            reveal(kernel_u_cpu_tlb_cleared); reveal(kernel_k_to_kernel_u);
            if steps.snapshot_u() != kernel_k_to_kernel_u(*self) {
                assert(!steps.snapshot_u().cpu_tlb.dom().contains((cpu_id, pcid)) || steps.snapshot_u().cpu_tlb[(cpu_id, pcid)] != (SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })) by {
                    if steps.snapshot_u().cpu_tlb.dom().contains((cpu_id, pcid)) && steps.snapshot_u().cpu_tlb[(cpu_id, pcid)] == (SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }) {
                        assert_maps_equal!(steps.snapshot_u().cpu_tlb, self.cpu_tlb.view(), key => {});
                    }
                };
                assert_sets_equal!(self.cpu_tlb.view().dom().filter(|key: (CpuId, Pcid)| !steps.snapshot_u().cpu_tlb.dom().contains(key) || steps.snapshot_u().cpu_tlb[key] != self.cpu_tlb.view()[key]), set![(cpu_id, pcid)]);
            }
        };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*self);
    }

    #[verifier::spinoff_prover]
    pub proof fn kernel_step_boundary_container_quota_4k_changed(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, container_ptr: RwLockContainerPtr, delta: int, origin: RwLockContainerPtr)
        requires
            old(self).inv(),
            delta > 0,
            kernel_container_quota_4k_changed(&old(steps).snapshot_k(), old(self), container_ptr, delta),
            old(steps).snapshot_k().ctn_mp.dom().contains(origin),
            container_ptr == origin || old(steps).snapshot_k().ctn_mp.spec_index(origin).view_ghost().uppertree_seq.view().contains(container_ptr),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            kernel_u_container_quota_4k_increased(old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self)), origin),
            old(steps).snapshot_u().container_map.dom().contains(container_ptr),
            kernel_k_to_kernel_u(*old(self)).container_map[container_ptr].quota_4k as int == old(steps).snapshot_u().container_map[container_ptr].quota_4k as int + delta,
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            kernel_k_to_kernel_u(*old(self)) == (KernelU { container_map: old(steps).snapshot_u().container_map.insert(container_ptr, ContainerU {
                quota_4k: (old(steps).snapshot_u().container_map[container_ptr].quota_4k as int + delta) as usize,
                ..old(steps).snapshot_u().container_map[container_ptr]
            }), ..old(steps).snapshot_u() }),
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(self).inv(),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(self).cpu_published[old(lctx).cpu_id() as int].view() == old(self).cpu_published[old(lctx).cpu_id() as int].view(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|pt: RwLockPageTableRoot|
                #![trigger pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pt))]
                old(lctx).pagetable_lock_map().dom().contains(pt) && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt))
                    ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pt)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep { old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*old(self)) }),
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
            final(steps).nonlock_view().last().new_u == (KernelU {
                container_map: final(steps).nonlock_view().last().old_u.container_map.insert(container_ptr, ContainerU {
                    quota_4k: (final(steps).nonlock_view().last().old_u.container_map.spec_index(container_ptr).quota_4k as int + delta) as usize,
                    ..final(steps).nonlock_view().last().old_u.container_map.spec_index(container_ptr)
                }),
                ..final(steps).nonlock_view().last().old_u
            }),
            containers_rodata_unchanged(old(self).ctn_mp, final(self).ctn_mp),
            held_containers_unchanged(old(self).ctn_mp, final(self).ctn_mp, old(lctx)),
            held_processes_unchanged(old(self).prc_mp, final(self).prc_mp, old(lctx)),
            held_threads_unchanged(old(self).thr_mp, final(self).thr_mp, old(lctx)),
            held_pagetables_unchanged(old(self).pt_mp, final(self).pt_mp, old(lctx)),
            forall|p: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), p, TypedLockMode::Write)
                ==> pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), p) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), p),
            held_pagetable_windows_unchanged(old(self).pt_mp, old(self).pt_lower.view(), final(self).pt_mp, final(self).pt_lower.view(), old(lctx)),
            held_iommu_tables_unchanged(old(self).it_mp, final(self).it_mp, old(lctx)),
            held_pages_unchanged(old(self).pg_arr, final(self).pg_arr, old(lctx)),
            held_cpus_unchanged(old(self).cpu_arr, final(self).cpu_arr, old(lctx)),
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        assert(steps.snapshot_u().container_map.dom().contains(container_ptr)
            && kernel_k_to_kernel_u(*self).container_map[container_ptr].quota_4k as int == steps.snapshot_u().container_map[container_ptr].quota_4k as int + delta
            && kernel_k_to_kernel_u(*self) != steps.snapshot_u() && kernel_k_to_kernel_u(*self) == (KernelU {
                container_map: steps.snapshot_u().container_map.insert(container_ptr, ContainerU {
                    quota_4k: (steps.snapshot_u().container_map[container_ptr].quota_4k as int + delta) as usize, ..steps.snapshot_u().container_map[container_ptr]
                }), ..steps.snapshot_u()
            })) by { kernel_container_quota_4k_changed_implies_u_step(&steps.snapshot_k(), &*self, container_ptr, delta); };
        assert(kernel_u_container_quota_4k_increased(steps.snapshot_u(), kernel_k_to_kernel_u(*self), origin)) by {
            reveal(kernel_u_container_quota_4k_increased);
            kernel_container_ancestry_projection_at(&steps.snapshot_k(), origin);
            let pre = steps.snapshot_u();
            let post = kernel_k_to_kernel_u(*self);
            assert_sets_equal!(pre.container_map.dom().filter(|c: RwLockContainerPtr| pre.container_map[c] != post.container_map[c]), set![container_ptr]);
            assert_sets_equal!(post.container_map.dom(), pre.container_map.dom());
        };
        let pre_u = steps.nonlock_snapshot_u();
        let post_u = kernel_k_to_nonlock_kernel_u(*self);
        assert(post_u != pre_u && post_u == (KernelU {
            container_map: pre_u.container_map.insert(container_ptr, ContainerU {
                quota_4k: (pre_u.container_map.spec_index(container_ptr).quota_4k as int + delta) as usize,
                ..pre_u.container_map.spec_index(container_ptr)
            }),
            ..pre_u
        })) by {
            reveal(kernel_container_quota_4k_changed); reveal(kernel_thread_nonlock_fields_unchanged); reveal(kernel_k_to_nonlock_kernel_u);
            assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array);
            assert_maps_equal!(post_u.thread_map, pre_u.thread_map, t => {});
            assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => {});
            reveal(process_pagetable_match);
            assert_maps_equal!(post_u.process_map, pre_u.process_map);
            assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(container_ptr, post_u.container_map.spec_index(container_ptr)), c => {});
        };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*self);
    }

    pub proof fn kernel_step_boundary_thread_quota_4k_changed(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, thread_ptr: RwLockThreadPtr, delta: int)
        requires
            old(self).inv(),
            delta != 0,
            kernel_thread_quota_4k_changed(&old(steps).snapshot_k(), old(self), thread_ptr, delta),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(self).cpu_published[old(lctx).cpu_id() as int].view() == old(self).cpu_published[old(lctx).cpu_id() as int].view(),
            final(self).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|pt: RwLockPageTableRoot|
                #![trigger pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pt))]
                old(lctx).pagetable_lock_map().dom().contains(pt) && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt))
                    ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pt)),
            forall|cpu_id: CpuId|
                #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)]
                old(lctx).cpu_lock_map().dom().contains(cpu_id) ==> final(self).cpu_arr.spec_index(cpu_id).view() == old(self).cpu_arr.spec_index(cpu_id).view(),
            forall|container_ptr: RwLockContainerPtr|
                #![trigger old(lctx).container_lock_map().dom().contains(container_ptr)]
                old(lctx).container_lock_map().dom().contains(container_ptr) ==> {
                    &&& final(self).ctn_mp.dom().contains(container_ptr)
                    &&& final(self).ctn_mp.lock_id_by_key(container_ptr) == old(self).ctn_mp.lock_id_by_key(container_ptr)
                    &&& final(self).ctn_mp.spec_index(container_ptr) == old(self).ctn_mp.spec_index(container_ptr)
                },
            forall|process_ptr: RwLockProcessPtr|
                #![trigger old(lctx).process_lock_map().dom().contains(process_ptr)]
                old(lctx).process_lock_map().dom().contains(process_ptr) ==> {
                    &&& final(self).prc_mp.dom().contains(process_ptr)
                    &&& final(self).prc_mp.lock_id_by_key(process_ptr) == old(self).prc_mp.lock_id_by_key(process_ptr)
                    &&& final(self).prc_mp.spec_index(process_ptr) == old(self).prc_mp.spec_index(process_ptr)
                },
            forall|thread_ptr: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(thread_ptr)]
                old(lctx).thread_lock_map().dom().contains(thread_ptr) ==> {
                    &&& final(self).thr_mp.dom().contains(thread_ptr)
                    &&& final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr)
                    &&& final(self).thr_mp.spec_index(thread_ptr) == old(self).thr_mp.spec_index(thread_ptr)
                },
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) ==> {
                    &&& final(self).pt_mp.dom().contains(pagetable_ptr)
                    &&& final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr)
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) ==> {
                        &&& final(self).pt_mp.spec_index(pagetable_ptr) == old(self).pt_mp.spec_index(pagetable_ptr)
                        &&& pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pagetable_ptr) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pagetable_ptr)
                    }
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read) ==> {
                        &&& final(self).pt_mp.spec_index(pagetable_ptr).view() == old(self).pt_mp.spec_index(pagetable_ptr).view()
                        &&& final(self).pt_mp.spec_index(pagetable_ptr).rlocked_by_thread(old(lctx).thread_id())
                        &&& final(self).pt_mp.spec_index(pagetable_ptr).being_killed() == old(self).pt_mp.spec_index(pagetable_ptr).being_killed()
                    }
                },
            held_pagetable_windows_unchanged(old(self).pt_mp, old(self).pt_lower.view(), final(self).pt_mp, final(self).pt_lower.view(), old(lctx)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep {
                old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*old(self)),
            }),
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
            containers_rodata_unchanged(old(self).ctn_mp, final(self).ctn_mp),
            processes_rodata_unchanged(old(self).prc_mp, final(self).prc_mp),
            held_endpoints_unchanged(old(self).ep_mp, final(self).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(self).sched_mp, final(self).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(self).pcid_allc_mp, final(self).pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(self).cpu_set_mp, final(self).cpu_set_mp, old(lctx)),
            held_iommu_tables_unchanged(old(self).it_mp, final(self).it_mp, old(lctx)),
            held_pages_unchanged(old(self).pg_arr, final(self).pg_arr, old(lctx)),
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        kernel_thread_quota_4k_changed_implies_u_step(&steps.snapshot_k(), &*self, thread_ptr, delta);
        assert(steps.snapshot_u() != kernel_k_to_kernel_u(*self)) by { kernel_nonlock_projection_is_u_nonlock_fields(steps.snapshot_k()); kernel_nonlock_projection_is_u_nonlock_fields(*self); };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*self);
    }

    #[verifier::spinoff_prover]
    pub proof fn kernel_step_boundary_thread_syscall_progress_changed(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, thread_ptr: RwLockThreadPtr)
        requires
            old(self).inv(),
            old(steps).snapshot_k().thr_mp.dom().contains(thread_ptr),
            old(self).thr_mp.dom().contains(thread_ptr),
            old(steps).snapshot_k().thr_mp.spec_index(thread_ptr).view().syscall_progress.view() != old(self).thr_mp.spec_index(thread_ptr).view().syscall_progress.view(),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> {
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3 == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid
                &&& final(self).cpu_published[old(lctx).cpu_id() as int].view() == old(self).cpu_published[old(lctx).cpu_id() as int].view()
            },
            final(self).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|pt: RwLockPageTableRoot|
                #![trigger pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pt))]
                old(lctx).pagetable_lock_map().dom().contains(pt) && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt))
                    ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pt)),
            forall|pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr), final(self).cpu_tlb.spec_index((cpu_id, pcid))]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) && index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID ==> {
                    let before = old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    let after = final(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    after is Some && after.unwrap().pagetable_ptr == pagetable_ptr && (before is None || before.unwrap().pagetable_ptr != pagetable_ptr
                        || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(self).cpu_tlb.spec_index((cpu_id, pcid)), pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pagetable_ptr))
                        || (old(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush && old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                            && (!final(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush || final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)))
                    ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).cpu_tlb.spec_index((cpu_id, pcid)), pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pagetable_ptr))
                },
            forall|cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))]
                old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))
                ==> final(self).pcid_needflush.spec_index(cpu_id, pcid) == old(self).pcid_needflush.spec_index(cpu_id, pcid),
            forall|cpu_id: CpuId|
                #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)]
                old(lctx).cpu_lock_map().dom().contains(cpu_id) ==> final(self).cpu_arr.spec_index(cpu_id).view() == old(self).cpu_arr.spec_index(cpu_id).view(),
            forall|container_ptr: RwLockContainerPtr|
                #![trigger old(lctx).container_lock_map().dom().contains(container_ptr)]
                old(lctx).container_lock_map().dom().contains(container_ptr) ==> {
                    &&& final(self).ctn_mp.dom().contains(container_ptr)
                    &&& final(self).ctn_mp.lock_id_by_key(container_ptr) == old(self).ctn_mp.lock_id_by_key(container_ptr)
                    &&& final(self).ctn_mp.spec_index(container_ptr) == old(self).ctn_mp.spec_index(container_ptr)
                },
            forall|process_ptr: RwLockProcessPtr|
                #![trigger old(lctx).process_lock_map().dom().contains(process_ptr)]
                old(lctx).process_lock_map().dom().contains(process_ptr) ==> {
                    &&& final(self).prc_mp.dom().contains(process_ptr)
                    &&& final(self).prc_mp.lock_id_by_key(process_ptr) == old(self).prc_mp.lock_id_by_key(process_ptr)
                    &&& final(self).prc_mp.spec_index(process_ptr) == old(self).prc_mp.spec_index(process_ptr)
                },
            forall|thread_ptr: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(thread_ptr)]
                old(lctx).thread_lock_map().dom().contains(thread_ptr) ==> {
                    &&& final(self).thr_mp.dom().contains(thread_ptr)
                    &&& final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr)
                    &&& final(self).thr_mp.spec_index(thread_ptr) == old(self).thr_mp.spec_index(thread_ptr)
                },
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) ==> {
                    &&& final(self).pt_mp.dom().contains(pagetable_ptr)
                    &&& final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr)
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) ==> {
                        &&& final(self).pt_mp.spec_index(pagetable_ptr) == old(self).pt_mp.spec_index(pagetable_ptr)
                        &&& pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pagetable_ptr) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pagetable_ptr)
                    }
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read) ==> {
                        &&& final(self).pt_mp.spec_index(pagetable_ptr).view() == old(self).pt_mp.spec_index(pagetable_ptr).view()
                        &&& final(self).pt_mp.spec_index(pagetable_ptr).rlocked_by_thread(old(lctx).thread_id())
                        &&& final(self).pt_mp.spec_index(pagetable_ptr).being_killed() == old(self).pt_mp.spec_index(pagetable_ptr).being_killed()
                    }
                },
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep {
                old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*old(self)),
            }),
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
            final(self).dflt_pt == old(self).dflt_pt,
            containers_rodata_unchanged(old(self).ctn_mp, final(self).ctn_mp),
            processes_rodata_unchanged(old(self).prc_mp, final(self).prc_mp),
            held_containers_unchanged(old(self).ctn_mp, final(self).ctn_mp, old(lctx)),
            held_processes_unchanged(old(self).prc_mp, final(self).prc_mp, old(lctx)),
            held_threads_unchanged(old(self).thr_mp, final(self).thr_mp, old(lctx)),
            held_endpoints_unchanged(old(self).ep_mp, final(self).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(self).sched_mp, final(self).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(self).pcid_allc_mp, final(self).pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(self).cpu_set_mp, final(self).cpu_set_mp, old(lctx)),
            held_pagetables_unchanged(old(self).pt_mp, final(self).pt_mp, old(lctx)),
            held_pagetable_windows_unchanged(old(self).pt_mp, old(self).pt_lower.view(), final(self).pt_mp, final(self).pt_lower.view(), old(lctx)),
            held_iommu_tables_unchanged(old(self).it_mp, final(self).it_mp, old(lctx)),
            held_pages_unchanged(old(self).pg_arr, final(self).pg_arr, old(lctx)),
            held_cpus_unchanged(old(self).cpu_arr, final(self).cpu_arr, old(lctx)),
            held_allocator_objects_unchanged(old(self).allc_4k_mp, final(self).allc_4k_mp, old(lctx), PageSize::SZ4k),
            held_allocator_objects_unchanged(old(self).allc_2m_mp, final(self).allc_2m_mp, old(lctx), PageSize::SZ2m),
            held_allocator_objects_unchanged(old(self).allc_1g_mp, final(self).allc_1g_mp, old(lctx), PageSize::SZ1g),
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        steps.end_kernel_step_thread_syscall_progress_changed(&*self, &*lctx, thread_ptr);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*self);
    }

    /// Records the section that changed both the complete and the business projection.
    pub proof fn kernel_step_boundary_user_view_changed(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps)
        requires
            old(self).inv(),
            kernel_k_to_kernel_u(old(steps).snapshot_k()) != kernel_k_to_kernel_u(*old(self)),
            kernel_k_to_nonlock_kernel_u(old(steps).snapshot_k()) != kernel_k_to_nonlock_kernel_u(*old(self)),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> {
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3 == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid
                &&& final(self).cpu_published[old(lctx).cpu_id() as int].view() == old(self).cpu_published[old(lctx).cpu_id() as int].view()
            },
            final(self).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|pt: RwLockPageTableRoot|
                #![trigger pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pt))]
                old(lctx).pagetable_lock_map().dom().contains(pt) && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt))
                    ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pt)),
            forall|pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr), final(self).cpu_tlb.spec_index((cpu_id, pcid))]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) && index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID ==> {
                    let before = old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    let after = final(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    after is Some && after.unwrap().pagetable_ptr == pagetable_ptr && (before is None || before.unwrap().pagetable_ptr != pagetable_ptr
                        || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(self).cpu_tlb.spec_index((cpu_id, pcid)), pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pagetable_ptr))
                        || (old(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush && old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                            && (!final(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush || final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)))
                    ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).cpu_tlb.spec_index((cpu_id, pcid)), pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pagetable_ptr))
                },
            forall|cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))]
                old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))
                ==> final(self).pcid_needflush.spec_index(cpu_id, pcid) == old(self).pcid_needflush.spec_index(cpu_id, pcid),
            forall|cpu_id: CpuId|
                #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)]
                old(lctx).cpu_lock_map().dom().contains(cpu_id) ==> final(self).cpu_arr.spec_index(cpu_id).view() == old(self).cpu_arr.spec_index(cpu_id).view(),
            forall|container_ptr: RwLockContainerPtr|
                #![trigger old(lctx).container_lock_map().dom().contains(container_ptr)]
                old(lctx).container_lock_map().dom().contains(container_ptr) ==> {
                    &&& final(self).ctn_mp.dom().contains(container_ptr)
                    &&& final(self).ctn_mp.lock_id_by_key(container_ptr) == old(self).ctn_mp.lock_id_by_key(container_ptr)
                    &&& final(self).ctn_mp.spec_index(container_ptr) == old(self).ctn_mp.spec_index(container_ptr)
                },
            forall|process_ptr: RwLockProcessPtr|
                #![trigger old(lctx).process_lock_map().dom().contains(process_ptr)]
                old(lctx).process_lock_map().dom().contains(process_ptr) ==> {
                    &&& final(self).prc_mp.dom().contains(process_ptr)
                    &&& final(self).prc_mp.lock_id_by_key(process_ptr) == old(self).prc_mp.lock_id_by_key(process_ptr)
                    &&& final(self).prc_mp.spec_index(process_ptr) == old(self).prc_mp.spec_index(process_ptr)
                },
            forall|thread_ptr: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(thread_ptr)]
                #![trigger final(self).thr_mp.dom().contains(thread_ptr)]
                old(lctx).thread_lock_map().dom().contains(thread_ptr) ==> {
                    &&& final(self).thr_mp.dom().contains(thread_ptr)
                    &&& final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr)
                    &&& final(self).thr_mp.spec_index(thread_ptr) == old(self).thr_mp.spec_index(thread_ptr)
                },
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) ==> {
                    &&& final(self).pt_mp.dom().contains(pagetable_ptr)
                    &&& final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr)
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) ==> {
                        &&& final(self).pt_mp.spec_index(pagetable_ptr) == old(self).pt_mp.spec_index(pagetable_ptr)
                        &&& pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pagetable_ptr) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pagetable_ptr)
                    }
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read) ==> {
                        &&& final(self).pt_mp.spec_index(pagetable_ptr).view() == old(self).pt_mp.spec_index(pagetable_ptr).view()
                        &&& final(self).pt_mp.spec_index(pagetable_ptr).rlocked_by_thread(old(lctx).thread_id())
                        &&& final(self).pt_mp.spec_index(pagetable_ptr).being_killed() == old(self).pt_mp.spec_index(pagetable_ptr).being_killed()
                    }
                },
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep {
                old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*old(self)),
            }),
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
            final(self).dflt_pt == old(self).dflt_pt,
            containers_rodata_unchanged(old(self).ctn_mp, final(self).ctn_mp),
            processes_rodata_unchanged(old(self).prc_mp, final(self).prc_mp),
            held_containers_unchanged(old(self).ctn_mp, final(self).ctn_mp, old(lctx)),
            held_processes_unchanged(old(self).prc_mp, final(self).prc_mp, old(lctx)),
            held_threads_unchanged(old(self).thr_mp, final(self).thr_mp, old(lctx)),
            held_endpoints_unchanged(old(self).ep_mp, final(self).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(self).sched_mp, final(self).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(self).pcid_allc_mp, final(self).pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(self).cpu_set_mp, final(self).cpu_set_mp, old(lctx)),
            held_pagetables_unchanged(old(self).pt_mp, final(self).pt_mp, old(lctx)),
            held_pagetable_windows_unchanged(old(self).pt_mp, old(self).pt_lower.view(), final(self).pt_mp, final(self).pt_lower.view(), old(lctx)),
            held_iommu_tables_unchanged(old(self).it_mp, final(self).it_mp, old(lctx)),
            held_pages_unchanged(old(self).pg_arr, final(self).pg_arr, old(lctx)),
            held_cpus_unchanged(old(self).cpu_arr, final(self).cpu_arr, old(lctx)),
            held_allocator_objects_unchanged(old(self).allc_4k_mp, final(self).allc_4k_mp, old(lctx), PageSize::SZ4k),
            held_allocator_objects_unchanged(old(self).allc_2m_mp, final(self).allc_2m_mp, old(lctx), PageSize::SZ2m),
            held_allocator_objects_unchanged(old(self).allc_1g_mp, final(self).allc_1g_mp, old(lctx), PageSize::SZ1g),
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*self);
    }

    #[verifier::spinoff_prover]
    pub proof fn kernel_step_boundary_thread_state_changed(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, thread_ptr: RwLockThreadPtr, old_state: ThreadState, new_state: ThreadState)
        requires
            old(self).inv(),
            kernel_thread_state_changed(&old(steps).snapshot_k(), old(self), thread_ptr),
            old(steps).snapshot_k().thr_mp.spec_index(thread_ptr).view().state == old_state,
            old(self).thr_mp.spec_index(thread_ptr).view().state == new_state,
            old(lctx).kernel_view_locking_state() is Release,
            old(lctx).thread_lock_map().dom().contains(thread_ptr),
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> {
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3 == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid
                &&& final(self).cpu_published[old(lctx).cpu_id() as int].view() == old(self).cpu_published[old(lctx).cpu_id() as int].view()
            },
            final(self).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|pt: RwLockPageTableRoot|
                #![trigger pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pt))]
                old(lctx).pagetable_lock_map().dom().contains(pt) && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt))
                    ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pt)),
            forall|pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr), final(self).cpu_tlb.spec_index((cpu_id, pcid))]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) && index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID ==> {
                    let before = old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    let after = final(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    after is Some && after.unwrap().pagetable_ptr == pagetable_ptr && (before is None || before.unwrap().pagetable_ptr != pagetable_ptr
                        || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(self).cpu_tlb.spec_index((cpu_id, pcid)), pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pagetable_ptr))
                        || (old(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush && old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                            && (!final(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush || final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)))
                    ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).cpu_tlb.spec_index((cpu_id, pcid)), pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pagetable_ptr))
                },
            forall|cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))]
                old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))
                ==> final(self).pcid_needflush.spec_index(cpu_id, pcid) == old(self).pcid_needflush.spec_index(cpu_id, pcid),
            forall|cpu_id: CpuId|
                #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)]
                old(lctx).cpu_lock_map().dom().contains(cpu_id) ==> final(self).cpu_arr.spec_index(cpu_id).view() == old(self).cpu_arr.spec_index(cpu_id).view(),
            forall|container_ptr: RwLockContainerPtr|
                #![trigger old(lctx).container_lock_map().dom().contains(container_ptr)]
                old(lctx).container_lock_map().dom().contains(container_ptr) ==> {
                    &&& final(self).ctn_mp.dom().contains(container_ptr)
                    &&& final(self).ctn_mp.lock_id_by_key(container_ptr) == old(self).ctn_mp.lock_id_by_key(container_ptr)
                    &&& final(self).ctn_mp.spec_index(container_ptr) == old(self).ctn_mp.spec_index(container_ptr)
                },
            forall|process_ptr: RwLockProcessPtr|
                #![trigger old(lctx).process_lock_map().dom().contains(process_ptr)]
                old(lctx).process_lock_map().dom().contains(process_ptr) ==> {
                    &&& final(self).prc_mp.dom().contains(process_ptr)
                    &&& final(self).prc_mp.lock_id_by_key(process_ptr) == old(self).prc_mp.lock_id_by_key(process_ptr)
                    &&& final(self).prc_mp.spec_index(process_ptr) == old(self).prc_mp.spec_index(process_ptr)
                },
            forall|thread_ptr: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(thread_ptr)]
                old(lctx).thread_lock_map().dom().contains(thread_ptr) ==> {
                    &&& final(self).thr_mp.dom().contains(thread_ptr)
                    &&& final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr)
                    &&& final(self).thr_mp.spec_index(thread_ptr) == old(self).thr_mp.spec_index(thread_ptr)
                },
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) ==> {
                    &&& final(self).pt_mp.dom().contains(pagetable_ptr)
                    &&& final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr)
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) ==> {
                        &&& final(self).pt_mp.spec_index(pagetable_ptr) == old(self).pt_mp.spec_index(pagetable_ptr)
                        &&& pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pagetable_ptr) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pagetable_ptr)
                    }
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read) ==> {
                        &&& final(self).pt_mp.spec_index(pagetable_ptr).view() == old(self).pt_mp.spec_index(pagetable_ptr).view()
                        &&& final(self).pt_mp.spec_index(pagetable_ptr).rlocked_by_thread(old(lctx).thread_id())
                        &&& final(self).pt_mp.spec_index(pagetable_ptr).being_killed() == old(self).pt_mp.spec_index(pagetable_ptr).being_killed()
                    }
                },
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self))),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep {
                old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*old(self)),
            }),
            final(steps).snapshot_k() == *final(self),
            final(steps).nonlock_view().last().old_u.thread_map.dom().contains(thread_ptr),
            final(steps).nonlock_view().last().old_u.thread_map.spec_index(thread_ptr).state == old_state,
            final(steps).nonlock_view().last().new_u.thread_map.dom().contains(thread_ptr),
            final(steps).nonlock_view().last().new_u.thread_map.spec_index(thread_ptr).state == new_state,
            final(steps).nonlock_snapshot_u().thread_map.dom().contains(thread_ptr),
            final(steps).nonlock_snapshot_u().thread_map.spec_index(thread_ptr).state == new_state,
            final(self).dflt_pt == old(self).dflt_pt,
            containers_rodata_unchanged(old(self).ctn_mp, final(self).ctn_mp),
            processes_rodata_unchanged(old(self).prc_mp, final(self).prc_mp),
            held_containers_unchanged(old(self).ctn_mp, final(self).ctn_mp, old(lctx)),
            held_processes_unchanged(old(self).prc_mp, final(self).prc_mp, old(lctx)),
            held_threads_unchanged(old(self).thr_mp, final(self).thr_mp, old(lctx)),
            held_endpoints_unchanged(old(self).ep_mp, final(self).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(self).sched_mp, final(self).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(self).pcid_allc_mp, final(self).pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(self).cpu_set_mp, final(self).cpu_set_mp, old(lctx)),
            held_pagetables_unchanged(old(self).pt_mp, final(self).pt_mp, old(lctx)),
            held_pagetable_windows_unchanged(old(self).pt_mp, old(self).pt_lower.view(), final(self).pt_mp, final(self).pt_lower.view(), old(lctx)),
            held_iommu_tables_unchanged(old(self).it_mp, final(self).it_mp, old(lctx)),
            held_pages_unchanged(old(self).pg_arr, final(self).pg_arr, old(lctx)),
            held_cpus_unchanged(old(self).cpu_arr, final(self).cpu_arr, old(lctx)),
            held_allocator_objects_unchanged(old(self).allc_4k_mp, final(self).allc_4k_mp, old(lctx), PageSize::SZ4k),
            held_allocator_objects_unchanged(old(self).allc_2m_mp, final(self).allc_2m_mp, old(lctx), PageSize::SZ2m),
            held_allocator_objects_unchanged(old(self).allc_1g_mp, final(self).allc_1g_mp, old(lctx), PageSize::SZ1g),
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        assert(steps.snapshot_k().thr_mp.dom().contains(thread_ptr) && old(self).thr_mp.dom().contains(thread_ptr)) by { reveal(kernel_thread_state_changed); };
        kernel_thread_state_changed_implies_u_neq(&steps.snapshot_k(), &*self, thread_ptr);
        assert(steps.nonlock_snapshot_u().thread_map.dom().contains(thread_ptr)
            && steps.nonlock_snapshot_u().thread_map.spec_index(thread_ptr).state == old_state) by { kernel_thread_nonlock_projection_at(&steps.snapshot_k(), thread_ptr); };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        kernel_thread_nonlock_projection_at(old(self), thread_ptr); kernel_thread_nonlock_projection_at(&*self, thread_ptr);
    }

    #[verifier::spinoff_prover]
    pub proof fn kernel_step_boundary_process_added(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr)
        requires
            old(self).inv(),
            kernel_process_added(&old(steps).snapshot_k(), old(self), process_ptr),
            !old(self).prc_mp.spec_index(process_ptr).view().zombie,
            old(self).thr_mp.dom().contains(current_thread_ptr),
            old(lctx).kernel_view_locking_state() is Release,
            old(lctx).process_lock_map().dom().contains(process_ptr),
            old(lctx).thread_lock_map().dom().contains(current_thread_ptr),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), old(self).prc_mp.spec_index(process_ptr).view().pagetable, TypedLockMode::Write),
            {
                let iommu_table = old(self).prc_mp.spec_index(process_ptr).view().iommu_table;
                ||| iommu_table is None
                ||| iommu_table is Some && old(lctx).iommu_table_lock_map().dom().contains(iommu_table.unwrap())
            },
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> {
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3 == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid
                &&& final(self).cpu_published[old(lctx).cpu_id() as int].view() == old(self).cpu_published[old(lctx).cpu_id() as int].view()
            },
            final(self).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|pt: RwLockPageTableRoot|
                #![trigger pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pt))]
                old(lctx).pagetable_lock_map().dom().contains(pt) && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt))
                    ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pt)),
            forall|pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr), final(self).cpu_tlb.spec_index((cpu_id, pcid))]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) && index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID ==> {
                    let before = old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    let after = final(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    after is Some && after.unwrap().pagetable_ptr == pagetable_ptr && (before is None || before.unwrap().pagetable_ptr != pagetable_ptr
                        || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(self).cpu_tlb.spec_index((cpu_id, pcid)), pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pagetable_ptr))
                        || (old(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush && old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                            && (!final(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush || final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)))
                    ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).cpu_tlb.spec_index((cpu_id, pcid)), pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pagetable_ptr))
                },
            forall|cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))]
                old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))
                ==> final(self).pcid_needflush.spec_index(cpu_id, pcid) == old(self).pcid_needflush.spec_index(cpu_id, pcid),
            forall|cpu_id: CpuId|
                #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)]
                old(lctx).cpu_lock_map().dom().contains(cpu_id) ==> final(self).cpu_arr.spec_index(cpu_id).view() == old(self).cpu_arr.spec_index(cpu_id).view(),
            forall|container_ptr: RwLockContainerPtr|
                #![trigger old(lctx).container_lock_map().dom().contains(container_ptr)]
                old(lctx).container_lock_map().dom().contains(container_ptr) ==> {
                    &&& final(self).ctn_mp.dom().contains(container_ptr)
                    &&& final(self).ctn_mp.lock_id_by_key(container_ptr) == old(self).ctn_mp.lock_id_by_key(container_ptr)
                    &&& final(self).ctn_mp.spec_index(container_ptr) == old(self).ctn_mp.spec_index(container_ptr)
                },
            forall|process_ptr: RwLockProcessPtr|
                #![trigger old(lctx).process_lock_map().dom().contains(process_ptr)]
                old(lctx).process_lock_map().dom().contains(process_ptr) ==> {
                    &&& final(self).prc_mp.dom().contains(process_ptr)
                    &&& final(self).prc_mp.lock_id_by_key(process_ptr) == old(self).prc_mp.lock_id_by_key(process_ptr)
                    &&& final(self).prc_mp.spec_index(process_ptr) == old(self).prc_mp.spec_index(process_ptr)
                },
            forall|thread_ptr: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(thread_ptr)]
                old(lctx).thread_lock_map().dom().contains(thread_ptr) ==> {
                    &&& final(self).thr_mp.dom().contains(thread_ptr)
                    &&& final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr)
                    &&& final(self).thr_mp.spec_index(thread_ptr) == old(self).thr_mp.spec_index(thread_ptr)
                },
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) ==> {
                    &&& final(self).pt_mp.dom().contains(pagetable_ptr)
                    &&& final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr)
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) ==> {
                        &&& final(self).pt_mp.spec_index(pagetable_ptr) == old(self).pt_mp.spec_index(pagetable_ptr)
                        &&& pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pagetable_ptr) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pagetable_ptr)
                    }
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read) ==> {
                        &&& final(self).pt_mp.spec_index(pagetable_ptr).view() == old(self).pt_mp.spec_index(pagetable_ptr).view()
                        &&& final(self).pt_mp.spec_index(pagetable_ptr).rlocked_by_thread(old(lctx).thread_id())
                        &&& final(self).pt_mp.spec_index(pagetable_ptr).being_killed() == old(self).pt_mp.spec_index(pagetable_ptr).being_killed()
                    }
                },
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep {
                old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*old(self)),
            }),
            final(steps).snapshot_k() == *final(self),
            final(steps).nonlock_view().last().new_u.process_map.dom().contains(process_ptr),
            kernel_k_to_nonlock_kernel_u(*final(self)).process_map.dom().contains(process_ptr),
            final(steps).nonlock_view().last().new_u.process_map.spec_index(process_ptr) == kernel_k_to_nonlock_kernel_u(*final(self)).process_map.spec_index(process_ptr),
            final(steps).nonlock_view().last().new_u.thread_map.dom().contains(current_thread_ptr),
            kernel_k_to_nonlock_kernel_u(*final(self)).thread_map.dom().contains(current_thread_ptr),
            final(steps).nonlock_view().last().new_u.thread_map.spec_index(current_thread_ptr) == kernel_k_to_nonlock_kernel_u(*final(self)).thread_map.spec_index(current_thread_ptr),
            final(self).dflt_pt == old(self).dflt_pt,
            containers_rodata_unchanged(old(self).ctn_mp, final(self).ctn_mp),
            processes_rodata_unchanged(old(self).prc_mp, final(self).prc_mp),
            held_containers_unchanged(old(self).ctn_mp, final(self).ctn_mp, old(lctx)),
            held_processes_unchanged(old(self).prc_mp, final(self).prc_mp, old(lctx)),
            held_threads_unchanged(old(self).thr_mp, final(self).thr_mp, old(lctx)),
            held_endpoints_unchanged(old(self).ep_mp, final(self).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(self).sched_mp, final(self).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(self).pcid_allc_mp, final(self).pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(self).cpu_set_mp, final(self).cpu_set_mp, old(lctx)),
            held_pagetables_unchanged(old(self).pt_mp, final(self).pt_mp, old(lctx)),
            held_pagetable_windows_unchanged(old(self).pt_mp, old(self).pt_lower.view(), final(self).pt_mp, final(self).pt_lower.view(), old(lctx)),
            held_iommu_tables_unchanged(old(self).it_mp, final(self).it_mp, old(lctx)),
            held_pages_unchanged(old(self).pg_arr, final(self).pg_arr, old(lctx)),
            held_cpus_unchanged(old(self).cpu_arr, final(self).cpu_arr, old(lctx)),
            held_allocator_objects_unchanged(old(self).allc_4k_mp, final(self).allc_4k_mp, old(lctx), PageSize::SZ4k),
            held_allocator_objects_unchanged(old(self).allc_2m_mp, final(self).allc_2m_mp, old(lctx), PageSize::SZ2m),
            held_allocator_objects_unchanged(old(self).allc_1g_mp, final(self).allc_1g_mp, old(lctx), PageSize::SZ1g),
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        assert(old(self).prc_mp.dom().contains(process_ptr)) by { reveal(kernel_process_added); };
        kernel_process_added_implies_u_neq(&steps.snapshot_k(), &*self, process_ptr);
        assert(kernel_k_to_nonlock_kernel_u(*self).process_map.dom().contains(process_ptr)
            && kernel_k_to_nonlock_kernel_u(*self).thread_map.dom().contains(current_thread_ptr)) by { reveal(kernel_k_to_nonlock_kernel_u); };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        kernel_process_nonlock_projection_at(old(self), process_ptr); kernel_process_nonlock_projection_at(&*self, process_ptr);
        kernel_thread_nonlock_projection_at(old(self), current_thread_ptr); kernel_thread_nonlock_projection_at(&*self, current_thread_ptr);
        let pagetable = old(self).prc_mp.spec_index(process_ptr).view().pagetable;
        old(self).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable);
        pagetable_lower_backup_wf_at(old(self).pt_mp, old(self).pt_lower.view(), pagetable); pagetable_lower_backup_wf_at(self.pt_mp, self.pt_lower.view(), pagetable);
        let iommu_table = old(self).prc_mp.spec_index(process_ptr).view().iommu_table;
        if iommu_table is Some {
            assert(old(self).it_mp.dom().contains(iommu_table.unwrap())) by { reveal(process_iommu_table_match); };
        }
    }

    #[verifier::spinoff_prover]
    pub proof fn kernel_step_boundary_process_4k_mapping_changed(
        tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, process_ptr: RwLockProcessPtr,
        pagetable_ptr: RwLockPageTableRoot, va: VAddr, stable_process_ptr: RwLockProcessPtr, stable_pagetable_ptr: RwLockPageTableRoot,
        stable_thread_ptr: RwLockThreadPtr, stable_owner_thread_ptr: RwLockThreadPtr,
    )
        requires
            old(self).inv(),
            kernel_process_4k_mapping_changed(&old(steps).snapshot_k(), old(self), process_ptr, pagetable_ptr, va),
            old(self).thr_mp.dom().contains(stable_thread_ptr),
            old(lctx).kernel_view_locking_state() is Release,
            old(self).prc_mp.dom().contains(stable_process_ptr),
            old(self).prc_mp.spec_index(stable_process_ptr).view().pagetable == stable_pagetable_ptr,
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), stable_pagetable_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            old(lctx).thread_lock_map().dom().contains(stable_thread_ptr),
            old(lctx).thread_lock_map().dom().contains(stable_owner_thread_ptr),
            old(self).thr_mp.dom().contains(stable_owner_thread_ptr),
            old(self).thr_mp.spec_index(stable_owner_thread_ptr).view().owning_proc == stable_process_ptr,
            !thread_is_dangling(old(self).thr_mp.spec_index(stable_owner_thread_ptr)),
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> {
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3 == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid
                &&& final(self).cpu_published[old(lctx).cpu_id() as int].view() == old(self).cpu_published[old(lctx).cpu_id() as int].view()
            },
            final(self).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|pt: RwLockPageTableRoot|
                #![trigger pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pt))]
                old(lctx).pagetable_lock_map().dom().contains(pt) && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt))
                    ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pt)),
            forall|pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr), final(self).cpu_tlb.spec_index((cpu_id, pcid))]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) && index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID ==> {
                    let before = old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    let after = final(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    after is Some && after.unwrap().pagetable_ptr == pagetable_ptr && (before is None || before.unwrap().pagetable_ptr != pagetable_ptr
                        || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(self).cpu_tlb.spec_index((cpu_id, pcid)), pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pagetable_ptr))
                        || (old(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush && old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                            && (!final(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush || final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)))
                    ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).cpu_tlb.spec_index((cpu_id, pcid)), pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pagetable_ptr))
                },
            forall|cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))]
                old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))
                ==> final(self).pcid_needflush.spec_index(cpu_id, pcid) == old(self).pcid_needflush.spec_index(cpu_id, pcid),
            forall|cpu_id: CpuId|
                #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)]
                old(lctx).cpu_lock_map().dom().contains(cpu_id) ==> final(self).cpu_arr.spec_index(cpu_id).view() == old(self).cpu_arr.spec_index(cpu_id).view(),
            forall|container_ptr: RwLockContainerPtr|
                #![trigger old(lctx).container_lock_map().dom().contains(container_ptr)]
                old(lctx).container_lock_map().dom().contains(container_ptr) ==> {
                    &&& final(self).ctn_mp.dom().contains(container_ptr)
                    &&& final(self).ctn_mp.lock_id_by_key(container_ptr) == old(self).ctn_mp.lock_id_by_key(container_ptr)
                    &&& final(self).ctn_mp.spec_index(container_ptr) == old(self).ctn_mp.spec_index(container_ptr)
                },
            forall|process_ptr: RwLockProcessPtr|
                #![trigger old(lctx).process_lock_map().dom().contains(process_ptr)]
                old(lctx).process_lock_map().dom().contains(process_ptr) ==> {
                    &&& final(self).prc_mp.dom().contains(process_ptr)
                    &&& final(self).prc_mp.lock_id_by_key(process_ptr) == old(self).prc_mp.lock_id_by_key(process_ptr)
                    &&& final(self).prc_mp.spec_index(process_ptr) == old(self).prc_mp.spec_index(process_ptr)
                },
            forall|thread_ptr: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(thread_ptr)]
                old(lctx).thread_lock_map().dom().contains(thread_ptr) ==> {
                    &&& final(self).thr_mp.dom().contains(thread_ptr)
                    &&& final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr)
                    &&& final(self).thr_mp.spec_index(thread_ptr) == old(self).thr_mp.spec_index(thread_ptr)
                },
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) ==> {
                    &&& final(self).pt_mp.dom().contains(pagetable_ptr)
                    &&& final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr)
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) ==> {
                        &&& final(self).pt_mp.spec_index(pagetable_ptr) == old(self).pt_mp.spec_index(pagetable_ptr)
                        &&& pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), pagetable_ptr) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pagetable_ptr)
                    }
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read) ==> {
                        &&& final(self).pt_mp.spec_index(pagetable_ptr).view() == old(self).pt_mp.spec_index(pagetable_ptr).view()
                        &&& final(self).pt_mp.spec_index(pagetable_ptr).rlocked_by_thread(old(lctx).thread_id())
                        &&& final(self).pt_mp.spec_index(pagetable_ptr).being_killed() == old(self).pt_mp.spec_index(pagetable_ptr).being_killed()
                    }
                },
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep {
                old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*old(self)),
            }),
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
            final(steps).nonlock_view().last().new_u.process_map.dom().contains(stable_process_ptr),
            kernel_k_to_nonlock_kernel_u(*final(self)).process_map.dom().contains(stable_process_ptr),
            final(steps).nonlock_view().last().new_u.process_map.spec_index(stable_process_ptr).pagetable == kernel_k_to_nonlock_kernel_u(*final(self)).process_map.spec_index(stable_process_ptr).pagetable,
            final(steps).nonlock_view().last().new_u.process_map.dom().contains(process_ptr),
            final(steps).nonlock_view().last().new_u.thread_map.dom().contains(stable_thread_ptr),
            kernel_k_to_nonlock_kernel_u(*final(self)).thread_map.dom().contains(stable_thread_ptr),
            final(steps).nonlock_view().last().new_u.thread_map.spec_index(stable_thread_ptr) == kernel_k_to_nonlock_kernel_u(*final(self)).thread_map.spec_index(stable_thread_ptr),
            old(lctx).process_lock_map().dom().contains(process_ptr) && ({
                let iommu_table = old(self).prc_mp.spec_index(process_ptr).view().iommu_table;
                ||| iommu_table is None
                ||| iommu_table is Some && old(lctx).iommu_table_lock_map().dom().contains(iommu_table.unwrap())
            }) ==> {
                &&& kernel_k_to_nonlock_kernel_u(*final(self)).process_map.dom().contains(process_ptr)
                &&& final(steps).nonlock_view().last().new_u.process_map.spec_index(process_ptr) == kernel_k_to_nonlock_kernel_u(*final(self)).process_map.spec_index(process_ptr)
            },
            final(self).dflt_pt == old(self).dflt_pt,
            containers_rodata_unchanged(old(self).ctn_mp, final(self).ctn_mp),
            processes_rodata_unchanged(old(self).prc_mp, final(self).prc_mp),
            held_containers_unchanged(old(self).ctn_mp, final(self).ctn_mp, old(lctx)),
            held_processes_unchanged(old(self).prc_mp, final(self).prc_mp, old(lctx)),
            held_threads_unchanged(old(self).thr_mp, final(self).thr_mp, old(lctx)),
            held_endpoints_unchanged(old(self).ep_mp, final(self).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(self).sched_mp, final(self).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(self).pcid_allc_mp, final(self).pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(self).cpu_set_mp, final(self).cpu_set_mp, old(lctx)),
            held_pagetables_unchanged(old(self).pt_mp, final(self).pt_mp, old(lctx)),
            held_pagetable_windows_unchanged(old(self).pt_mp, old(self).pt_lower.view(), final(self).pt_mp, final(self).pt_lower.view(), old(lctx)),
            held_iommu_tables_unchanged(old(self).it_mp, final(self).it_mp, old(lctx)),
            held_pages_unchanged(old(self).pg_arr, final(self).pg_arr, old(lctx)),
            held_cpus_unchanged(old(self).cpu_arr, final(self).cpu_arr, old(lctx)),
            held_allocator_objects_unchanged(old(self).allc_4k_mp, final(self).allc_4k_mp, old(lctx), PageSize::SZ4k),
            held_allocator_objects_unchanged(old(self).allc_2m_mp, final(self).allc_2m_mp, old(lctx), PageSize::SZ2m),
            held_allocator_objects_unchanged(old(self).allc_1g_mp, final(self).allc_1g_mp, old(lctx), PageSize::SZ1g),
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        assert(old(self).prc_mp.dom().contains(process_ptr) && !old(self).prc_mp.spec_index(process_ptr).view().zombie && old(self).prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr) by { reveal(kernel_process_4k_mapping_changed); };
        kernel_process_4k_mapping_changed_implies_u_neq(&steps.snapshot_k(), &*self, process_ptr, pagetable_ptr, va);
        assert(kernel_k_to_nonlock_kernel_u(*self).process_map.dom().contains(process_ptr) && kernel_k_to_nonlock_kernel_u(*self).process_map.dom().contains(stable_process_ptr)
            && kernel_k_to_nonlock_kernel_u(*self).thread_map.dom().contains(stable_thread_ptr)) by { kernel_u_nonlock_domains_projection(&*self); };
        assert(!self.prc_mp.spec_index(stable_process_ptr).view().zombie) by { process_thread_wf_at(self.prc_mp, self.thr_mp, stable_owner_thread_ptr); };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        assert(!self.prc_mp.spec_index(stable_process_ptr).view().zombie) by { process_thread_wf_at(self.prc_mp, self.thr_mp, stable_owner_thread_ptr); };
        old(self).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        old(self).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), stable_pagetable_ptr);
        pagetable_lower_backup_wf_at(old(self).pt_mp, old(self).pt_lower.view(), pagetable_ptr); pagetable_lower_backup_wf_at(self.pt_mp, self.pt_lower.view(), pagetable_ptr);
        pagetable_lower_backup_wf_at(old(self).pt_mp, old(self).pt_lower.view(), stable_pagetable_ptr); pagetable_lower_backup_wf_at(self.pt_mp, self.pt_lower.view(), stable_pagetable_ptr);
        reveal(process_pagetable_match); reveal(process_iommu_table_match); kernel_u_nonlock_domains_projection(old(self)); kernel_u_nonlock_domains_projection(&*self);
        kernel_process_nonlock_projection_at(old(self), stable_process_ptr); kernel_process_nonlock_projection_at(&*self, stable_process_ptr);
        kernel_thread_nonlock_projection_at(old(self), stable_thread_ptr); kernel_thread_nonlock_projection_at(&*self, stable_thread_ptr);
        kernel_process_nonlock_projection_at(old(self), process_ptr); kernel_process_nonlock_projection_at(&*self, process_ptr);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*self);
    }
}

/// Project endpoint creation together with releasing the caller's cpu, container, process, and thread.
#[verifier::spinoff_prover]
pub proof fn kernel_new_endpoint_fields_and_unlocks_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    endpoint_index: EndpointIdx, new_endpoint_ptr: RwLockEndpointPtr,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        pre.prc_mp.dom().contains(process_ptr),
        kernel_new_endpoint_fields(pre, post, container_ptr, thread_ptr, endpoint_index, new_endpoint_ptr, None),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
            pre.ctn_mp.dom().contains(p) ==> if p == container_ptr { post.ctn_mp.spec_index(p).locking_thread() is None } else { post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread() },
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) ==> if p == process_ptr { post.prc_mp.spec_index(p).locking_thread() is None } else { post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
            pre.thr_mp.dom().contains(p) ==> if p == thread_ptr { post.thr_mp.spec_index(p).locking_thread() is None } else { post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread() },
        forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)] pre.ep_mp.dom().contains(p) ==> post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread(),
        post.ep_mp.spec_index(new_endpoint_ptr).locking_thread() is None,
        forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> if i == cpu_id { post.cpu_arr.spec_index(i).value.locking_thread() is None } else { post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread() },
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let mode = LockStateU::Unlocked;
            kernel_u_new_endpoint_changed(KernelU {
                cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, ..old_u.cpu_array[cpu_id as int] }),
                container_map: old_u.container_map.insert(container_ptr, ContainerU { lock_state: mode, ..old_u.container_map[container_ptr] }),
                process_map: old_u.process_map.insert(process_ptr, ProcessU { lock_state: mode, ..old_u.process_map[process_ptr] }),
                thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: mode, ..old_u.thread_map.spec_index(thread_ptr) }),
                ..old_u
            }, kernel_k_to_kernel_u(*post), container_ptr, thread_ptr, endpoint_index, new_endpoint_ptr)
        }),
        kernel_k_to_kernel_u(*post).thread_map.spec_index(thread_ptr).endpoint_descriptors[endpoint_index as int] == Some(new_endpoint_ptr),
{
    kernel_u_domains_projection(post); kernel_u_domains_projection(pre);
    let old_u = kernel_k_to_kernel_u(*pre);
    let mode = LockStateU::Unlocked;
    let pre_u = KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, ..old_u.cpu_array[cpu_id as int] }),
        container_map: old_u.container_map.insert(container_ptr, ContainerU { lock_state: mode, ..old_u.container_map[container_ptr] }),
        process_map: old_u.process_map.insert(process_ptr, ProcessU { lock_state: mode, ..old_u.process_map[process_ptr] }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: mode, ..old_u.thread_map.spec_index(thread_ptr) }),
        ..old_u
    };
    let post_u = kernel_k_to_kernel_u(*post);
    if post.thr_mp.dom().contains(thread_ptr) { kernel_thread_projection_at(post, thread_ptr); } if pre.thr_mp.dom().contains(thread_ptr) { kernel_thread_projection_at(pre, thread_ptr); }
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(kernel_new_endpoint_fields); reveal(IommuRootTable::user_view); };
    assert(post_u.thread_map.spec_index(thread_ptr).endpoint_descriptors[endpoint_index as int] == Some(new_endpoint_ptr)
        && kernel_u_new_endpoint_changed(pre_u, post_u, container_ptr, thread_ptr, endpoint_index, new_endpoint_ptr)) by {
        kernel_new_endpoint_fields_and_unlocks_implies_u_cpu_array(pre, post, cpu_id, container_ptr, thread_ptr, endpoint_index, new_endpoint_ptr);
        kernel_new_endpoint_fields_and_unlocks_implies_u_container_map(pre, post, container_ptr, thread_ptr, endpoint_index, new_endpoint_ptr);
        kernel_new_endpoint_fields_and_unlocks_implies_u_process_map(pre, post, container_ptr, process_ptr, thread_ptr, endpoint_index, new_endpoint_ptr);
        kernel_new_endpoint_fields_and_unlocks_implies_u_thread_map(pre, post, container_ptr, thread_ptr, endpoint_index, new_endpoint_ptr);
        kernel_new_endpoint_fields_and_unlocks_implies_u_endpoint_map(pre, post, container_ptr, thread_ptr, endpoint_index, new_endpoint_ptr);
        reveal(kernel_new_endpoint_fields); reveal(kernel_u_new_endpoint_changed);
    };
}

/// Endpoint creation with the caller's cpu released projects to the cpu array with only that cpu unlocked.
#[verifier::spinoff_prover]
pub proof fn kernel_new_endpoint_fields_and_unlocks_implies_u_cpu_array(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx,
    new_endpoint_ptr: RwLockEndpointPtr,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        kernel_new_endpoint_fields(pre, post, container_ptr, thread_ptr, endpoint_index, new_endpoint_ptr, None),
        forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> if i == cpu_id { post.cpu_arr.spec_index(i).value.locking_thread() is None } else { post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread() },
    ensures
        kernel_k_to_kernel_u(*post).cpu_array == kernel_k_to_kernel_u(*pre).cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..kernel_k_to_kernel_u(*pre).cpu_array[cpu_id as int] }),
{
    kernel_u_domains_projection(post); kernel_u_domains_projection(pre);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    assert_seqs_equal!(post_u.cpu_array == old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..old_u.cpu_array[cpu_id as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(post, i as usize); kernel_cpu_projection_at(pre, i as usize); }
        reveal(kernel_new_endpoint_fields); reveal(kernel_cpu_nonlock_fields_unchanged);
    });
}

/// Endpoint creation with the caller's container released projects to that container, unlocked, owning the new endpoint.
#[verifier::spinoff_prover]
pub proof fn kernel_new_endpoint_fields_and_unlocks_implies_u_container_map(
    pre: &KernelK, post: &KernelK, container_ptr: RwLockContainerPtr, thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx, new_endpoint_ptr: RwLockEndpointPtr,
)
    requires
        kernel_new_endpoint_fields(pre, post, container_ptr, thread_ptr, endpoint_index, new_endpoint_ptr, None),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
            pre.ctn_mp.dom().contains(p) ==> if p == container_ptr { post.ctn_mp.spec_index(p).locking_thread() is None } else { post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread() },
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let unlocked = old_u.container_map.insert(container_ptr, ContainerU { lock_state: LockStateU::Unlocked, ..old_u.container_map[container_ptr] });
            kernel_k_to_kernel_u(*post).container_map == unlocked.insert(container_ptr, ContainerU {
                owned_endpoints: unlocked.spec_index(container_ptr).owned_endpoints.insert(new_endpoint_ptr), ..unlocked.spec_index(container_ptr)
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let unlocked = old_u.container_map.insert(container_ptr, ContainerU { lock_state: LockStateU::Unlocked, ..old_u.container_map[container_ptr] });
    reveal(kernel_new_endpoint_fields);
    assert_maps_equal!(post_u.container_map, unlocked.insert(container_ptr, ContainerU {
        owned_endpoints: unlocked.spec_index(container_ptr).owned_endpoints.insert(new_endpoint_ptr), ..unlocked.spec_index(container_ptr)
    }), p => { if pre.ctn_mp.dom().contains(p) { kernel_container_projection_at(pre, p); } if post.ctn_mp.dom().contains(p) { kernel_container_projection_at(post, p); } });
}

/// Endpoint creation with the caller's process released projects to that process unlocked and otherwise unchanged.
#[verifier::spinoff_prover]
pub proof fn kernel_new_endpoint_fields_and_unlocks_implies_u_process_map(
    pre: &KernelK, post: &KernelK, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx,
    new_endpoint_ptr: RwLockEndpointPtr,
)
    requires
        pre.prc_mp.dom().contains(process_ptr),
        kernel_new_endpoint_fields(pre, post, container_ptr, thread_ptr, endpoint_index, new_endpoint_ptr, None),
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) ==> if p == process_ptr { post.prc_mp.spec_index(p).locking_thread() is None } else { post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread() },
    ensures
        kernel_k_to_kernel_u(*post).process_map == kernel_k_to_kernel_u(*pre).process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::Unlocked, ..kernel_k_to_kernel_u(*pre).process_map[process_ptr] }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    reveal(kernel_new_endpoint_fields); reveal(kernel_process_nonlock_fields_unchanged);
    assert_maps_equal!(post_u.process_map, old_u.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::Unlocked, ..old_u.process_map[process_ptr] }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
    });
}

/// Endpoint creation with the caller's thread released projects to that thread, unlocked, paying one quota for the
/// endpoint installed at `endpoint_index` and with its progress cleared.
#[verifier::spinoff_prover]
pub proof fn kernel_new_endpoint_fields_and_unlocks_implies_u_thread_map(
    pre: &KernelK, post: &KernelK, container_ptr: RwLockContainerPtr, thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx, new_endpoint_ptr: RwLockEndpointPtr,
)
    requires
        kernel_new_endpoint_fields(pre, post, container_ptr, thread_ptr, endpoint_index, new_endpoint_ptr, None),
        forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
            pre.thr_mp.dom().contains(p) ==> if p == thread_ptr { post.thr_mp.spec_index(p).locking_thread() is None } else { post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread() },
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let unlocked = old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..old_u.thread_map.spec_index(thread_ptr) });
            let thread = unlocked.spec_index(thread_ptr);
            kernel_k_to_kernel_u(*post).thread_map == unlocked.insert(thread_ptr, ThreadU {
                quota_4k: (thread.quota_4k as int - 1) as usize, endpoint_descriptors: thread.endpoint_descriptors.update(endpoint_index as int, Some(new_endpoint_ptr)),
                syscall_progress: None, ..thread
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let unlocked = old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..old_u.thread_map.spec_index(thread_ptr) });
    let thread = unlocked.spec_index(thread_ptr);
    reveal(kernel_new_endpoint_fields);
    assert_maps_equal!(post_u.thread_map, unlocked.insert(thread_ptr, ThreadU {
        quota_4k: (thread.quota_4k as int - 1) as usize, endpoint_descriptors: thread.endpoint_descriptors.update(endpoint_index as int, Some(new_endpoint_ptr)),
        syscall_progress: None, ..thread
    }), p => { if pre.thr_mp.dom().contains(p) { kernel_thread_projection_at(pre, p); } if post.thr_mp.dom().contains(p) { kernel_thread_projection_at(post, p); } });
}

/// Endpoint creation projects to the new endpoint, unlocked and empty, held only at the caller's `endpoint_index`.
#[verifier::spinoff_prover]
pub proof fn kernel_new_endpoint_fields_and_unlocks_implies_u_endpoint_map(
    pre: &KernelK, post: &KernelK, container_ptr: RwLockContainerPtr, thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx, new_endpoint_ptr: RwLockEndpointPtr,
)
    requires
        kernel_new_endpoint_fields(pre, post, container_ptr, thread_ptr, endpoint_index, new_endpoint_ptr, None),
        forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)] pre.ep_mp.dom().contains(p) ==> post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread(),
        post.ep_mp.spec_index(new_endpoint_ptr).locking_thread() is None,
    ensures
        kernel_k_to_kernel_u(*post).endpoint_map == kernel_k_to_kernel_u(*pre).endpoint_map.insert(new_endpoint_ptr, EndpointU {
            lock_state: LockStateU::Unlocked, queue: Seq::empty(), queue_state: EndpointState::RECEIVE, owning_threads: set![(thread_ptr, endpoint_index)],
            owning_container: container_ptr, killed: false,
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    reveal(kernel_new_endpoint_fields);
    assert_maps_equal!(kernel_k_to_kernel_u(*post).endpoint_map, kernel_k_to_kernel_u(*pre).endpoint_map.insert(new_endpoint_ptr, EndpointU {
        lock_state: LockStateU::Unlocked, queue: Seq::empty(), queue_state: EndpointState::RECEIVE, owning_threads: set![(thread_ptr, endpoint_index)],
        owning_container: container_ptr, killed: false,
    }), p => { if pre.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(pre, p); } if post.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(post, p); } });
}

/// A thread exit with the exiting cpu, container, and process released projects to `kernel_u_thread_exit_changed`
/// from the snapshot with those three objects unlocked.
pub proof fn kernel_thread_exit_fields_and_unlocks_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, flushed_default_pcid: bool,
)
    requires
        kernel_thread_exit_fields(pre, post, cpu_id, thread_ptr, flushed_default_pcid),
        pre.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        post.cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
            pre.ctn_mp.dom().contains(p) ==> if p == container_ptr { post.ctn_mp.spec_index(p).locking_thread() is None } else { post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread() },
        post.prc_mp.spec_index(process_ptr).locking_thread() is None,
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let mode = LockStateU::Unlocked;
            kernel_u_thread_exit_changed(KernelU {
                cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, ..old_u.cpu_array[cpu_id as int] }),
                container_map: old_u.container_map.insert(container_ptr, ContainerU { lock_state: mode, ..old_u.container_map[container_ptr] }),
                process_map: old_u.process_map.insert(process_ptr, ProcessU { lock_state: mode, ..old_u.process_map[process_ptr] }),
                ..old_u
            }, kernel_k_to_kernel_u(*post), cpu_id, thread_ptr, flushed_default_pcid)
        }),
{
    kernel_u_domains_projection(post); kernel_u_domains_projection(pre);
    let old_u = kernel_k_to_kernel_u(*pre);
    let mode = LockStateU::Unlocked;
    let pre_u = KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, ..old_u.cpu_array[cpu_id as int] }),
        container_map: old_u.container_map.insert(container_ptr, ContainerU { lock_state: mode, ..old_u.container_map[container_ptr] }),
        process_map: old_u.process_map.insert(process_ptr, ProcessU { lock_state: mode, ..old_u.process_map[process_ptr] }),
        ..old_u
    };
    let post_u = kernel_k_to_kernel_u(*post);
    assert(pre.thr_mp.dom().contains(thread_ptr)) by { reveal(kernel_thread_exit_fields); };
    kernel_thread_projection_at(pre, thread_ptr);
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(kernel_thread_exit_fields); reveal(IommuRootTable::user_view); };
    assert(kernel_u_thread_exit_changed(pre_u, post_u, cpu_id, thread_ptr, flushed_default_pcid)) by {
        kernel_thread_exit_fields_and_unlocks_implies_u_cpu_array(pre, post, cpu_id, thread_ptr, flushed_default_pcid);
        kernel_thread_exit_fields_and_unlocks_implies_u_container_map(pre, post, cpu_id, container_ptr, process_ptr, thread_ptr, flushed_default_pcid);
        kernel_thread_exit_fields_and_unlocks_implies_u_process_map(pre, post, cpu_id, process_ptr, thread_ptr, flushed_default_pcid);
        kernel_thread_exit_fields_and_unlocks_implies_u_thread_map(pre, post, cpu_id, thread_ptr, flushed_default_pcid);
        kernel_thread_exit_fields_and_unlocks_implies_u_endpoint_map(pre, post, cpu_id, thread_ptr, flushed_default_pcid);
        reveal(kernel_thread_exit_fields); reveal(kernel_u_thread_exit_changed);
    };
}

/// A thread exit with the exiting cpu released projects to that cpu, unlocked and idle.
proof fn kernel_thread_exit_fields_and_unlocks_implies_u_cpu_array(pre: &KernelK, post: &KernelK, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, flushed_default_pcid: bool)
    requires
        kernel_thread_exit_fields(pre, post, cpu_id, thread_ptr, flushed_default_pcid),
        post.cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let cpus = old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..old_u.cpu_array[cpu_id as int] });
            kernel_k_to_kernel_u(*post).cpu_array == cpus.update(cpu_id as int, CpuU { state: CpuState::Idle, current_process: None, current_thread: None, ..cpus[cpu_id as int] })
        }),
{
    kernel_u_domains_projection(post); kernel_u_domains_projection(pre);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let cpus = old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..old_u.cpu_array[cpu_id as int] });
    assert(index_valid(NUM_CPUS, cpu_id)) by { reveal(kernel_thread_exit_fields); };
    assert_seqs_equal!(post_u.cpu_array == cpus.update(cpu_id as int, CpuU { state: CpuState::Idle, current_process: None, current_thread: None, ..cpus[cpu_id as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(post, i as usize); kernel_cpu_projection_at(pre, i as usize); }
        reveal(kernel_thread_exit_fields);
    });
}

/// A thread exit with the exiting container released projects to that container, unlocked, without the thread, and a
/// zombie once its root process becomes one, and to one more 4K quota for the container owning the thread's page.
proof fn kernel_thread_exit_fields_and_unlocks_implies_u_container_map(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, flushed_default_pcid: bool,
)
    requires
        kernel_thread_exit_fields(pre, post, cpu_id, thread_ptr, flushed_default_pcid),
        pre.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
            pre.ctn_mp.dom().contains(p) ==> if p == container_ptr { post.ctn_mp.spec_index(p).locking_thread() is None } else { post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread() },
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let new_u = kernel_k_to_kernel_u(*post);
            let containers = old_u.container_map.insert(container_ptr, ContainerU { lock_state: LockStateU::Unlocked, ..old_u.container_map[container_ptr] });
            let zombie = old_u.process_map.spec_index(process_ptr).owned_threads.remove_value(thread_ptr).len() == 0;
            let pcid = old_u.process_map.spec_index(process_ptr).pcid;
            &&& new_u.container_map.dom() =~= containers.dom()
            &&& forall|c: RwLockContainerPtr| #![trigger new_u.container_map.spec_index(c)]
                containers.dom().contains(c) ==> {
                    let container = containers.spec_index(c);
                    let quota_4k = if container.owned_pages.contains(thread_ptr) { (container.quota_4k + 1) as usize } else { container.quota_4k };
                    new_u.container_map.spec_index(c) == if c == container_ptr {
                        ContainerU {
                            zombie: container.zombie || (zombie && container.root_process == process_ptr), owned_threads: container.owned_threads.remove(thread_ptr), quota_4k,
                            free_pcids: if zombie { container.free_pcids.insert(pcid) } else { container.free_pcids }, ..container
                        }
                    } else { ContainerU { quota_4k, ..container } }
                }
        }),
{
    reveal(kernel_k_to_kernel_u); reveal(kernel_thread_exit_fields);
}

/// A thread exit with the exiting process released projects to that process, unlocked, without the thread, holding
/// the thread's quota, and without page tables once it becomes a zombie.
proof fn kernel_thread_exit_fields_and_unlocks_implies_u_process_map(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, flushed_default_pcid: bool,
)
    requires
        kernel_thread_exit_fields(pre, post, cpu_id, thread_ptr, flushed_default_pcid),
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        post.prc_mp.spec_index(process_ptr).locking_thread() is None,
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let processes = old_u.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::Unlocked, ..old_u.process_map[process_ptr] });
            let thread = old_u.thread_map.spec_index(thread_ptr);
            let process = processes.spec_index(process_ptr);
            let threads = process.owned_threads.remove_value(thread_ptr);
            let zombie = threads.len() == 0;
            kernel_k_to_kernel_u(*post).process_map == processes.insert(process_ptr, ProcessU {
                zombie, pagetable: if zombie { None } else { process.pagetable }, iommu_table: if zombie { None } else { process.iommu_table },
                quota_4k: (process.quota_4k + thread.quota_4k) as usize, quota_2m: (process.quota_2m + thread.quota_2m) as usize,
                quota_1g: (process.quota_1g + thread.quota_1g) as usize, owned_threads: threads, ..process
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    reveal(kernel_thread_exit_fields);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let processes = old_u.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::Unlocked, ..old_u.process_map[process_ptr] });
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let process = processes.spec_index(process_ptr);
    let threads = process.owned_threads.remove_value(thread_ptr);
    let zombie = threads.len() == 0;
    kernel_thread_projection_at(pre, thread_ptr);
    assert_maps_equal!(post_u.process_map, processes.insert(process_ptr, ProcessU {
        zombie, pagetable: if zombie { None } else { process.pagetable }, iommu_table: if zombie { None } else { process.iommu_table },
        quota_4k: (process.quota_4k + thread.quota_4k) as usize, quota_2m: (process.quota_2m + thread.quota_2m) as usize,
        quota_1g: (process.quota_1g + thread.quota_1g) as usize, owned_threads: threads, ..process
    }), p => { if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } });
}

/// A thread exit removes the thread from the thread projection.
proof fn kernel_thread_exit_fields_and_unlocks_implies_u_thread_map(pre: &KernelK, post: &KernelK, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, flushed_default_pcid: bool)
    requires kernel_thread_exit_fields(pre, post, cpu_id, thread_ptr, flushed_default_pcid),
    ensures kernel_k_to_kernel_u(*post).thread_map == kernel_k_to_kernel_u(*pre).thread_map.remove(thread_ptr),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    reveal(kernel_thread_exit_fields);
    assert_maps_equal!(kernel_k_to_kernel_u(*post).thread_map, kernel_k_to_kernel_u(*pre).thread_map.remove(thread_ptr), t => {
        if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_projection_at(post, t); }
    });
}

/// A thread exit leaves the endpoint projection unchanged.
proof fn kernel_thread_exit_fields_and_unlocks_implies_u_endpoint_map(pre: &KernelK, post: &KernelK, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, flushed_default_pcid: bool)
    requires kernel_thread_exit_fields(pre, post, cpu_id, thread_ptr, flushed_default_pcid),
    ensures kernel_k_to_kernel_u(*post).endpoint_map == kernel_k_to_kernel_u(*pre).endpoint_map,
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    reveal(kernel_thread_exit_fields);
    assert_maps_equal!(kernel_k_to_kernel_u(*post).endpoint_map, kernel_k_to_kernel_u(*pre).endpoint_map, e => {
        if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(post, e); }
    });
}

/// Returning an exiting last thread's `size` quota grows only its container's `size` quota in the container projection.
proof fn kernel_thread_exit_quota_returned_implies_u_container_map(pre: &KernelK, post: &KernelK, thread_ptr: RwLockThreadPtr, size: PageSize)
    requires kernel_thread_exit_quota_returned(pre, post, thread_ptr, size),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let t = pre.thr_mp.spec_index(thread_ptr).view();
            let thread = a.thread_map[thread_ptr];
            let process = a.process_map[t.owning_proc];
            let container = a.container_map[t.owning_container];
            kernel_k_to_kernel_u(*post).container_map == a.container_map.insert(t.owning_container, match size {
                PageSize::SZ4k => ContainerU { quota_4k: (container.quota_4k + process.quota_4k + thread.quota_4k) as usize, ..container },
                PageSize::SZ2m => ContainerU { quota_2m: (container.quota_2m + process.quota_2m + thread.quota_2m) as usize, ..container },
                PageSize::SZ1g => ContainerU { quota_1g: (container.quota_1g + process.quota_1g + thread.quota_1g) as usize, ..container },
            })
        }),
{
    reveal(kernel_thread_exit_quota_returned); kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let t = pre.thr_mp.spec_index(thread_ptr).view();
    kernel_thread_projection_at(pre, thread_ptr); kernel_process_projection_at(pre, t.owning_proc);
    kernel_container_projection_at(pre, t.owning_container);
    let thread = a.thread_map[thread_ptr];
    let process = a.process_map[t.owning_proc];
    let container = a.container_map[t.owning_container];
    let new_c = match size {
        PageSize::SZ4k => ContainerU { quota_4k: (container.quota_4k + process.quota_4k + thread.quota_4k) as usize, ..container },
        PageSize::SZ2m => ContainerU { quota_2m: (container.quota_2m + process.quota_2m + thread.quota_2m) as usize, ..container },
        PageSize::SZ1g => ContainerU { quota_1g: (container.quota_1g + process.quota_1g + thread.quota_1g) as usize, ..container },
    };
    assert(kernel_k_to_kernel_u(*post).container_map[t.owning_container] == new_c) by { kernel_container_projection_at(post, t.owning_container); };
    assert_maps_equal!(kernel_k_to_kernel_u(*post).container_map, a.container_map.insert(t.owning_container, new_c), c => {
        if pre.ctn_mp.dom().contains(c) && c != t.owning_container { kernel_container_projection_at(pre, c); kernel_container_projection_at(post, c); }
    });
}

/// Returning an exiting last thread's `size` quota clears only its process's `size` quota in the process projection.
proof fn kernel_thread_exit_quota_returned_implies_u_process_map(pre: &KernelK, post: &KernelK, thread_ptr: RwLockThreadPtr, size: PageSize)
    requires kernel_thread_exit_quota_returned(pre, post, thread_ptr, size),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let t = pre.thr_mp.spec_index(thread_ptr).view();
            let process = a.process_map[t.owning_proc];
            kernel_k_to_kernel_u(*post).process_map == a.process_map.insert(t.owning_proc, match size {
                PageSize::SZ4k => ProcessU { quota_4k: 0, ..process },
                PageSize::SZ2m => ProcessU { quota_2m: 0, ..process },
                PageSize::SZ1g => ProcessU { quota_1g: 0, ..process },
            })
        }),
{
    reveal(kernel_thread_exit_quota_returned); kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let t = pre.thr_mp.spec_index(thread_ptr).view();
    kernel_process_projection_at(pre, t.owning_proc); kernel_process_projection_at(post, t.owning_proc);
    let process = a.process_map[t.owning_proc];
    assert_maps_equal!(kernel_k_to_kernel_u(*post).process_map, a.process_map.insert(t.owning_proc, match size {
        PageSize::SZ4k => ProcessU { quota_4k: 0, ..process },
        PageSize::SZ2m => ProcessU { quota_2m: 0, ..process },
        PageSize::SZ1g => ProcessU { quota_1g: 0, ..process },
    }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); kernel_process_projection_at(post, p); }
    });
}

/// Returning an exiting last thread's `size` quota clears only that thread's `size` quota and records its progress in
/// the thread projection.
proof fn kernel_thread_exit_quota_returned_implies_u_thread_map(pre: &KernelK, post: &KernelK, thread_ptr: RwLockThreadPtr, size: PageSize)
    requires kernel_thread_exit_quota_returned(pre, post, thread_ptr, size),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let thread = a.thread_map[thread_ptr];
            let progress = post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view();
            kernel_k_to_kernel_u(*post).thread_map == a.thread_map.insert(thread_ptr, match size {
                PageSize::SZ4k => ThreadU { quota_4k: 0, syscall_progress: progress, ..thread },
                PageSize::SZ2m => ThreadU { quota_2m: 0, syscall_progress: progress, ..thread },
                PageSize::SZ1g => ThreadU { quota_1g: 0, syscall_progress: progress, ..thread },
            })
        }),
{
    reveal(kernel_thread_exit_quota_returned); kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    kernel_thread_projection_at(pre, thread_ptr); kernel_thread_projection_at(post, thread_ptr);
    let thread = a.thread_map[thread_ptr];
    let progress = post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view();
    assert_maps_equal!(kernel_k_to_kernel_u(*post).thread_map, a.thread_map.insert(thread_ptr, match size {
        PageSize::SZ4k => ThreadU { quota_4k: 0, syscall_progress: progress, ..thread },
        PageSize::SZ2m => ThreadU { quota_2m: 0, syscall_progress: progress, ..thread },
        PageSize::SZ1g => ThreadU { quota_1g: 0, syscall_progress: progress, ..thread },
    }), x => {
        if pre.thr_mp.dom().contains(x) { kernel_thread_projection_at(pre, x); kernel_thread_projection_at(post, x); }
    });
}

/// Returning the `size` quota of an exiting last thread and of its process to their container is one U step that
/// also carries the thread's new progress.
pub proof fn kernel_thread_exit_quota_returned_implies_u_step(pre: &KernelK, post: &KernelK, thread_ptr: RwLockThreadPtr, size: PageSize)
    requires
        kernel_thread_exit_quota_returned(pre, post, thread_ptr, size),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let thread = a.thread_map[thread_ptr];
            let process = a.process_map[thread.owning_proc];
            let container = a.container_map[thread.owning_container];
            let progress = post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view();
            &&& a.thread_map.dom().contains(thread_ptr)
            &&& a.process_map.dom().contains(thread.owning_proc)
            &&& a.container_map.dom().contains(thread.owning_container)
            &&& thread.owning_proc == pre.thr_mp.spec_index(thread_ptr).view().owning_proc
            &&& thread.owning_container == pre.thr_mp.spec_index(thread_ptr).view().owning_container
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                container_map: a.container_map.insert(thread.owning_container, match size {
                    PageSize::SZ4k => ContainerU { quota_4k: (container.quota_4k + process.quota_4k + thread.quota_4k) as usize, ..container },
                    PageSize::SZ2m => ContainerU { quota_2m: (container.quota_2m + process.quota_2m + thread.quota_2m) as usize, ..container },
                    PageSize::SZ1g => ContainerU { quota_1g: (container.quota_1g + process.quota_1g + thread.quota_1g) as usize, ..container },
                }),
                process_map: a.process_map.insert(thread.owning_proc, match size {
                    PageSize::SZ4k => ProcessU { quota_4k: 0, ..process },
                    PageSize::SZ2m => ProcessU { quota_2m: 0, ..process },
                    PageSize::SZ1g => ProcessU { quota_1g: 0, ..process },
                }),
                thread_map: a.thread_map.insert(thread_ptr, match size {
                    PageSize::SZ4k => ThreadU { quota_4k: 0, syscall_progress: progress, ..thread },
                    PageSize::SZ2m => ThreadU { quota_2m: 0, syscall_progress: progress, ..thread },
                    PageSize::SZ1g => ThreadU { quota_1g: 0, syscall_progress: progress, ..thread },
                }),
                ..a
            })
        }),
{
    reveal(kernel_thread_exit_quota_returned); kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    let t = pre.thr_mp.spec_index(thread_ptr).view();
    kernel_thread_projection_at(pre, thread_ptr); kernel_thread_projection_at(post, thread_ptr);
    kernel_process_projection_at(pre, t.owning_proc); kernel_process_projection_at(post, t.owning_proc);
    kernel_container_projection_at(pre, t.owning_container); kernel_container_projection_at(post, t.owning_container);
    kernel_thread_exit_quota_returned_implies_u_container_map(pre, post, thread_ptr, size);
    kernel_thread_exit_quota_returned_implies_u_process_map(pre, post, thread_ptr, size);
    kernel_thread_exit_quota_returned_implies_u_thread_map(pre, post, thread_ptr, size);
    assert_seqs_equal!(b.cpu_array == a.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(b.endpoint_map, a.endpoint_map, e => {
        if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); kernel_endpoint_projection_at(post, e); }
    });
}

/// Waking the caller of an exiting thread schedules the caller on `cpu_id` with `ErrorIpcCalleeExited` and drops the
/// exiting thread's caller link, with every lock mode unchanged.
pub proof fn kernel_caller_woken_implies_u_step(before: &KernelK, after: &KernelK, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, caller_ptr: RwLockThreadPtr)
    requires
        after.inv(),
        before.thr_mp.dom().contains(thread_ptr),
        before.thr_mp.dom().contains(caller_ptr),
        *after == (KernelK { thr_mp: after.thr_mp, sched_mp: after.sched_mp, ..*before }),
        after.thr_mp.dom() == before.thr_mp.dom(),
        forall|t: RwLockThreadPtr| #![trigger after.thr_mp.spec_index(t)]
            before.thr_mp.dom().contains(t) && t != thread_ptr && t != caller_ptr ==> after.thr_mp.spec_index(t) == before.thr_mp.spec_index(t),
        after.thr_mp.spec_index(thread_ptr).view() == (Thread { caller: None, ..before.thr_mp.spec_index(thread_ptr).view() }),
        after.thr_mp.spec_index(thread_ptr).locking_thread() == before.thr_mp.spec_index(thread_ptr).locking_thread(),
        after.thr_mp.spec_index(thread_ptr).being_killed() == before.thr_mp.spec_index(thread_ptr).being_killed(),
        after.thr_mp.spec_index(caller_ptr).view() == (Thread {
            state: ThreadState::SCHEDULED { cpu_id }, callee: None, error_code: Some(RetValueType::ErrorIpcCalleeExited),
            scheduler_linkedlist_node: after.thr_mp.spec_index(caller_ptr).view().scheduler_linkedlist_node, ..before.thr_mp.spec_index(caller_ptr).view()
        }),
        after.thr_mp.spec_index(caller_ptr).locking_thread() == before.thr_mp.spec_index(caller_ptr).locking_thread(),
        after.thr_mp.spec_index(caller_ptr).being_killed() == before.thr_mp.spec_index(caller_ptr).being_killed(),
        after.sched_mp.dom() == before.sched_mp.dom(),
        forall|s: RwLockSchedulerPtr| #![trigger after.sched_mp.spec_index(s)] before.sched_mp.dom().contains(s) ==>
            scheduler_shards_of(after.sched_mp.spec_index(s)) == if s == before.ctn_mp.spec_index(before.thr_mp.spec_index(caller_ptr).view().owning_container).view_rodata().view().scheduler {
                scheduler_shards_of(before.sched_mp.spec_index(s)).update(cpu_id as int, scheduler_shards_of(before.sched_mp.spec_index(s))[cpu_id as int].push(caller_ptr))
            } else { scheduler_shards_of(before.sched_mp.spec_index(s)) },
    ensures
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let container = pre.thread_map[caller_ptr].owning_container;
            kernel_k_to_kernel_u(*after) == (KernelU {
                container_map: pre.container_map.insert(container, ContainerU {
                    scheduler: pre.container_map[container].scheduler.update(cpu_id as int, pre.container_map[container].scheduler[cpu_id as int].push(caller_ptr)),
                    ..pre.container_map[container]
                }),
                thread_map: pre.thread_map.insert(thread_ptr, ThreadU { caller: None, ..pre.thread_map[thread_ptr] }).insert(caller_ptr, ThreadU {
                    state: ThreadState::SCHEDULED { cpu_id }, callee: None, error_code: Some(RetValueType::ErrorIpcCalleeExited), ..pre.thread_map[caller_ptr]
                }),
                ..pre
            })
        }),
{
    reveal(kernel_k_to_kernel_u);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    let container = pre.thread_map[caller_ptr].owning_container;
    assert_seqs_equal!(post.cpu_array == pre.cpu_array);
    assert_maps_equal!(post.process_map, pre.process_map);
    assert_maps_equal!(post.container_map, pre.container_map.insert(container, ContainerU {
        scheduler: pre.container_map[container].scheduler.update(cpu_id as int, pre.container_map[container].scheduler[cpu_id as int].push(caller_ptr)), ..pre.container_map[container]
    }), p => { reveal(container_thread_wf); reveal(container_scheduler_wf); });
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thread_ptr, ThreadU { caller: None, ..pre.thread_map[thread_ptr] }).insert(caller_ptr, ThreadU {
        state: ThreadState::SCHEDULED { cpu_id }, callee: None, error_code: Some(RetValueType::ErrorIpcCalleeExited), ..pre.thread_map[caller_ptr]
    }));
    assert_maps_equal!(post.endpoint_map, pre.endpoint_map);
}

/// Dropping descriptor `endpoint_index` of an exiting thread clears that descriptor, records the thread's new
/// progress, and removes the reference from its endpoint, with every lock mode unchanged.
pub proof fn kernel_descriptor_dropped_implies_u_step(
    before: &KernelK, after: &KernelK, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
)
    requires
        *after == (KernelK { thr_mp: after.thr_mp, ep_mp: after.ep_mp, ..*before }),
        before.thr_mp.dom().contains(thread_ptr),
        after.thr_mp.unchanged_except(&before.thr_mp, thread_ptr),
        after.thr_mp.spec_index(thread_ptr).view() == (Thread {
            endpoint_descriptors: after.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors,
            syscall_progress: after.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..before.thr_mp.spec_index(thread_ptr).view()
        }),
        after.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view() == before.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view().update(endpoint_index as int, None),
        after.thr_mp.spec_index(thread_ptr).locking_thread() == before.thr_mp.spec_index(thread_ptr).locking_thread(),
        after.thr_mp.spec_index(thread_ptr).being_killed() == before.thr_mp.spec_index(thread_ptr).being_killed(),
        before.ep_mp.dom().contains(endpoint_ptr),
        after.ep_mp.unchanged_except(&before.ep_mp, endpoint_ptr),
        after.ep_mp.spec_index(endpoint_ptr).view().queue.view() == before.ep_mp.spec_index(endpoint_ptr).view().queue.view(),
        after.ep_mp.spec_index(endpoint_ptr).view().queue_state == before.ep_mp.spec_index(endpoint_ptr).view().queue_state,
        after.ep_mp.spec_index(endpoint_ptr).view().owning_container == before.ep_mp.spec_index(endpoint_ptr).view().owning_container,
        after.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view() == before.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().remove((thread_ptr, endpoint_index)),
        after.ep_mp.spec_index(endpoint_ptr).locking_thread() == before.ep_mp.spec_index(endpoint_ptr).locking_thread(),
        after.ep_mp.spec_index(endpoint_ptr).being_killed() == before.ep_mp.spec_index(endpoint_ptr).being_killed(),
    ensures
        ({
            let thread = before.thr_mp.spec_index(thread_ptr);
            let t = thread.view();
            kernel_k_to_kernel_u(*before).thread_map[thread_ptr] == (ThreadU {
                lock_state: thread.lock_state_u(), state: t.state, caller: t.caller, callee: t.callee, owning_container: t.owning_container, owning_proc: t.owning_proc,
                last_cpu: t.last_cpu, quota_4k: t.quota_4k, quota_2m: t.quota_2m, quota_1g: t.quota_1g, endpoint_descriptors: t.endpoint_descriptors.view(),
                blocking_endpoint_ptr: t.blocking_endpoint_ptr, ipc_payload: t.ipc_payload, error_code: t.error_code,
                trap_frame: if t.trap_frame.is_some() { Some(*t.trap_frame.get_some_0()) } else { None }, syscall_progress: t.syscall_progress.view(), killed: thread.being_killed(),
            })
        }),
        ({
            let e = before.ep_mp.spec_index(endpoint_ptr);
            kernel_k_to_kernel_u(*before).endpoint_map[endpoint_ptr] == (EndpointU {
                lock_state: e.lock_state_u(), queue: e.view().queue.view(), queue_state: e.view().queue_state,
                owning_threads: e.view().owning_threads.view(), owning_container: e.view().owning_container, killed: e.being_killed(),
            })
        }),
        kernel_k_to_kernel_u(*before).thread_map.dom().contains(thread_ptr),
        kernel_k_to_kernel_u(*before).endpoint_map.dom().contains(endpoint_ptr),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after) == (KernelU {
                thread_map: pre.thread_map.insert(thread_ptr, ThreadU {
                    endpoint_descriptors: pre.thread_map[thread_ptr].endpoint_descriptors.update(endpoint_index as int, None),
                    syscall_progress: after.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..pre.thread_map[thread_ptr]
                }),
                endpoint_map: pre.endpoint_map.insert(endpoint_ptr, EndpointU {
                    owning_threads: pre.endpoint_map[endpoint_ptr].owning_threads.remove((thread_ptr, endpoint_index)), ..pre.endpoint_map[endpoint_ptr]
                }),
                ..pre
            })
        }),
{
    kernel_thread_projection_at(before, thread_ptr); kernel_endpoint_projection_at(before, endpoint_ptr);
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thread_ptr, ThreadU {
        endpoint_descriptors: pre.thread_map[thread_ptr].endpoint_descriptors.update(endpoint_index as int, None),
        syscall_progress: after.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..pre.thread_map[thread_ptr]
    }), t => { if before.thr_mp.dom().contains(t) { kernel_thread_projection_at(before, t); } if after.thr_mp.dom().contains(t) { kernel_thread_projection_at(after, t); } });
    assert_maps_equal!(post.endpoint_map, pre.endpoint_map.insert(endpoint_ptr, EndpointU {
        owning_threads: pre.endpoint_map[endpoint_ptr].owning_threads.remove((thread_ptr, endpoint_index)), ..pre.endpoint_map[endpoint_ptr]
    }), e => { if before.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(before, e); } if after.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(after, e); } });
    assert_seqs_equal!(post.cpu_array == pre.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(before, i as usize); kernel_cpu_projection_at(after, i as usize); } });
    assert_maps_equal!(post.container_map, pre.container_map, p => {
        if before.ctn_mp.dom().contains(p) { kernel_container_projection_at(before, p); } if after.ctn_mp.dom().contains(p) { kernel_container_projection_at(after, p); }
    });
    assert_maps_equal!(post.process_map, pre.process_map, p => {
        if before.prc_mp.dom().contains(p) { kernel_process_projection_at(before, p); } if after.prc_mp.dom().contains(p) { kernel_process_projection_at(after, p); }
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
