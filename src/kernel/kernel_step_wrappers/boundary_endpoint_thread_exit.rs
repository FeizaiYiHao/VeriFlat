use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;

verus! {
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
            pre.ctn_mp.dom().contains(p) ==> if p == container_ptr { post.ctn_mp.spec_index(p).locking_thread() is None } else {
                &&& post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread()
                &&& post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u()
            },
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) ==> if p == process_ptr { post.prc_mp.spec_index(p).locking_thread() is None } else { post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
            pre.thr_mp.dom().contains(p) ==> if p == thread_ptr { post.thr_mp.spec_index(p).locking_thread() is None } else { post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread() },
        forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)] pre.ep_mp.dom().contains(p) ==> post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread(),
        post.ep_mp.spec_index(new_endpoint_ptr).locking_thread() is None,
        forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> if i == cpu_id { post.cpu_arr.spec_index(i).value.locking_thread() is None } else { post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread() },
        forall|i: CpuId| #![trigger post.cpu_op.view().view()[i as int]] index_valid(NUM_CPUS, i) && i != cpu_id ==> post.cpu_op.view().view()[i as int] == pre.cpu_op.view().view()[i as int],
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let mode = LockStateU::Unlocked;
            kernel_u_new_endpoint_changed(KernelU {
                cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, op: post.cpu_op.view().view()[cpu_id as int], ..old_u.cpu_array[cpu_id as int] }),
                container_map: old_u.container_map.insert(container_ptr, ContainerU { lock_state: mode, lock_process_owner: None, ..old_u.container_map[container_ptr] }),
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
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, op: post.cpu_op.view().view()[cpu_id as int], ..old_u.cpu_array[cpu_id as int] }),
        container_map: old_u.container_map.insert(container_ptr, ContainerU { lock_state: mode, lock_process_owner: None, ..old_u.container_map[container_ptr] }),
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

/// Endpoint creation with the caller's cpu released projects to the cpu array with only that cpu unlocked and its running
/// state taken from `post`.
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
        forall|i: CpuId| #![trigger post.cpu_op.view().view()[i as int]] index_valid(NUM_CPUS, i) && i != cpu_id ==> post.cpu_op.view().view()[i as int] == pre.cpu_op.view().view()[i as int],
    ensures
        kernel_k_to_kernel_u(*post).cpu_array == kernel_k_to_kernel_u(*pre).cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: post.cpu_op.view().view()[cpu_id as int], ..kernel_k_to_kernel_u(*pre).cpu_array[cpu_id as int] }),
{
    kernel_u_domains_projection(post); kernel_u_domains_projection(pre);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    assert_seqs_equal!(post_u.cpu_array == old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: post.cpu_op.view().view()[cpu_id as int], ..old_u.cpu_array[cpu_id as int] }), i => {
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
            pre.ctn_mp.dom().contains(p) ==> if p == container_ptr { post.ctn_mp.spec_index(p).locking_thread() is None } else {
                &&& post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread()
                &&& post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u()
            },
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let unlocked = old_u.container_map.insert(container_ptr, ContainerU { lock_state: LockStateU::Unlocked, lock_process_owner: None, ..old_u.container_map[container_ptr] });
            kernel_k_to_kernel_u(*post).container_map == unlocked.insert(container_ptr, ContainerU {
                owned_endpoints: unlocked.spec_index(container_ptr).owned_endpoints.insert(new_endpoint_ptr), ..unlocked.spec_index(container_ptr)
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let unlocked = old_u.container_map.insert(container_ptr, ContainerU { lock_state: LockStateU::Unlocked, lock_process_owner: None, ..old_u.container_map[container_ptr] });
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
/// from the snapshot with those three objects unlocked and the cpu on its trap path.
pub proof fn kernel_thread_exit_fields_and_unlocks_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, flushed_default_pcid: bool,
)
    requires
        kernel_thread_exit_fields(pre, post, cpu_id, thread_ptr, flushed_default_pcid),
        pre.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        post.cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
            pre.ctn_mp.dom().contains(p) ==> if p == container_ptr { post.ctn_mp.spec_index(p).locking_thread() is None } else {
                &&& post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread()
                &&& post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u()
            },
        post.prc_mp.spec_index(process_ptr).locking_thread() is None,
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let mode = LockStateU::Unlocked;
            kernel_u_thread_exit_changed(KernelU {
                cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, op: CpuOpState::Trap, ..old_u.cpu_array[cpu_id as int] }),
                container_map: old_u.container_map.insert(container_ptr, ContainerU { lock_state: mode, lock_process_owner: None, ..old_u.container_map[container_ptr] }),
                process_map: old_u.process_map.insert(process_ptr, ProcessU { lock_state: mode, ..old_u.process_map[process_ptr] }),
                ..old_u
            }, kernel_k_to_kernel_u(*post), cpu_id, thread_ptr, flushed_default_pcid)
        }),
{
    kernel_u_domains_projection(post); kernel_u_domains_projection(pre);
    let old_u = kernel_k_to_kernel_u(*pre);
    let mode = LockStateU::Unlocked;
    let pre_u = KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, op: CpuOpState::Trap, ..old_u.cpu_array[cpu_id as int] }),
        container_map: old_u.container_map.insert(container_ptr, ContainerU { lock_state: mode, lock_process_owner: None, ..old_u.container_map[container_ptr] }),
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
            let cpus = old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..old_u.cpu_array[cpu_id as int] });
            kernel_k_to_kernel_u(*post).cpu_array == cpus.update(cpu_id as int, CpuU { state: CpuState::Idle, op: CpuOpState::Idle, current_process: None, current_thread: None, ..cpus[cpu_id as int] })
        }),
{
    kernel_u_domains_projection(post); kernel_u_domains_projection(pre);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let cpus = old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..old_u.cpu_array[cpu_id as int] });
    assert(index_valid(NUM_CPUS, cpu_id)) by { reveal(kernel_thread_exit_fields); };
    assert_seqs_equal!(post_u.cpu_array == cpus.update(cpu_id as int, CpuU { state: CpuState::Idle, op: CpuOpState::Idle, current_process: None, current_thread: None, ..cpus[cpu_id as int] }), i => {
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
            pre.ctn_mp.dom().contains(p) ==> if p == container_ptr { post.ctn_mp.spec_index(p).locking_thread() is None } else {
                &&& post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread()
                &&& post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u()
            },
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let new_u = kernel_k_to_kernel_u(*post);
            let containers = old_u.container_map.insert(container_ptr, ContainerU { lock_state: LockStateU::Unlocked, lock_process_owner: None, ..old_u.container_map[container_ptr] });
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
            let thread = a.thread_map[thread_ptr];
            let process = a.process_map[thread.owning_proc];
            let container = a.container_map[thread.owning_container];
            kernel_k_to_kernel_u(*post).container_map == a.container_map.insert(thread.owning_container, match size {
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
    let process = a.process_map[thread.owning_proc];
    let container = a.container_map[thread.owning_container];
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
            let process = a.process_map[a.thread_map[thread_ptr].owning_proc];
            kernel_k_to_kernel_u(*post).process_map == a.process_map.insert(a.thread_map[thread_ptr].owning_proc, match size {
                PageSize::SZ4k => ProcessU { quota_4k: 0, ..process },
                PageSize::SZ2m => ProcessU { quota_2m: 0, ..process },
                PageSize::SZ1g => ProcessU { quota_1g: 0, ..process },
            })
        }),
{
    reveal(kernel_thread_exit_quota_returned); kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let t = pre.thr_mp.spec_index(thread_ptr).view();
    kernel_thread_projection_at(pre, thread_ptr); kernel_process_projection_at(pre, t.owning_proc); kernel_process_projection_at(post, t.owning_proc);
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
            &&& a.thread_map.dom().contains(thread_ptr)
            &&& a.process_map.dom().contains(thread.owning_proc)
            &&& a.container_map.dom().contains(thread.owning_container)
            &&& thread.owning_proc == pre.thr_mp.spec_index(thread_ptr).view().owning_proc
            &&& thread.owning_container == pre.thr_mp.spec_index(thread_ptr).view().owning_container
            &&& kernel_k_to_kernel_u(*post).thread_map == a.thread_map.insert(thread_ptr, match size {
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

/// Returning an exiting last thread's `size` quota leaves the cpu array, the endpoint map, and the remaining non-map
/// projection fields unchanged.
proof fn kernel_thread_exit_quota_returned_implies_u_cpu_array_and_endpoint_map(pre: &KernelK, post: &KernelK, thread_ptr: RwLockThreadPtr, size: PageSize)
    requires kernel_thread_exit_quota_returned(pre, post, thread_ptr, size),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let b = kernel_k_to_kernel_u(*post);
            &&& b.cpu_array == a.cpu_array
            &&& b.endpoint_map == a.endpoint_map
            &&& b.iommu_root_table == a.iommu_root_table
            &&& b.cpu_tlb == a.cpu_tlb
            &&& b.iommu_tlb == a.iommu_tlb
            &&& b.kernel_l4_end == a.kernel_l4_end
        }),
{
    reveal(kernel_thread_exit_quota_returned); kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    assert_seqs_equal!(b.cpu_array == a.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(b.endpoint_map, a.endpoint_map, e => {
        if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); kernel_endpoint_projection_at(post, e); }
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
    kernel_thread_exit_quota_returned_implies_u_container_map(pre, post, thread_ptr, size);
    kernel_thread_exit_quota_returned_implies_u_process_map(pre, post, thread_ptr, size);
    kernel_thread_exit_quota_returned_implies_u_thread_map(pre, post, thread_ptr, size);
    kernel_thread_exit_quota_returned_implies_u_cpu_array_and_endpoint_map(pre, post, thread_ptr, size);
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
} // verus!
