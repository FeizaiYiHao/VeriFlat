use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;

verus! {
/// Write-locking and marking the unmarked process `process_ptr` changes only its lock mode, kill mark, and K-only state.
pub proof fn kernel_process_locked_and_marked_implies_u_step(before: &KernelK, after: &KernelK, process_ptr: RwLockProcessPtr)
    requires
        *after == (KernelK { prc_mp: after.prc_mp, ..*before }),
        before.prc_mp.dom().contains(process_ptr),
        after.prc_mp.unchanged_except(&before.prc_mp, process_ptr),
        after.prc_mp.spec_index(process_ptr).view() == (Process { state: after.prc_mp.spec_index(process_ptr).view().state, ..before.prc_mp.spec_index(process_ptr).view() }),
        after.prc_mp.spec_index(process_ptr).view_rodata() == before.prc_mp.spec_index(process_ptr).view_rodata(),
        after.prc_mp.spec_index(process_ptr).view_ghost() == before.prc_mp.spec_index(process_ptr).view_ghost(),
        after.prc_mp.spec_index(process_ptr).locking_thread() is Write,
        after.prc_mp.spec_index(process_ptr).being_killed(),
    ensures
        kernel_k_to_kernel_u(*before).process_map.dom().contains(process_ptr),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after) == (KernelU {
                process_map: pre.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::WriteLocked, killed: true, ..pre.process_map[process_ptr] }), ..pre
            })
        }),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    assert_maps_equal!(post.process_map, pre.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::WriteLocked, killed: true, ..pre.process_map[process_ptr] }), p => {
        if before.prc_mp.dom().contains(p) { kernel_process_projection_at(before, p); kernel_process_projection_at(after, p); }
    });
    assert_seqs_equal!(post.cpu_array == pre.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(before, i as usize); kernel_cpu_projection_at(after, i as usize); } });
    assert_maps_equal!(post.container_map, pre.container_map, c => {
        if before.ctn_mp.dom().contains(c) { kernel_container_projection_at(before, c); kernel_container_projection_at(after, c); }
    });
    assert_maps_equal!(post.thread_map, pre.thread_map, t => {
        if before.thr_mp.dom().contains(t) { kernel_thread_projection_at(before, t); kernel_thread_projection_at(after, t); }
    });
    assert_maps_equal!(post.endpoint_map, pre.endpoint_map, e => {
        if before.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(before, e); kernel_endpoint_projection_at(after, e); }
    });
    reveal(kernel_k_to_kernel_u);
}

/// Write-locking and marking the unmarked thread `thread_ptr` changes only its lock mode and kill mark, and changes both
/// projections.
pub proof fn kernel_thread_locked_and_marked_implies_u_step(before: &KernelK, after: &KernelK, thread_ptr: RwLockThreadPtr)
    requires
        *after == (KernelK { thr_mp: after.thr_mp, ..*before }),
        before.thr_mp.dom().contains(thread_ptr),
        after.thr_mp.unchanged_except(&before.thr_mp, thread_ptr),
        after.thr_mp.spec_index(thread_ptr).view() == before.thr_mp.spec_index(thread_ptr).view(),
        after.thr_mp.spec_index(thread_ptr).locking_thread() is Write,
        !before.thr_mp.spec_index(thread_ptr).being_killed(),
        after.thr_mp.spec_index(thread_ptr).being_killed(),
    ensures
        kernel_k_to_kernel_u(*before).thread_map.dom().contains(thread_ptr),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after) == (KernelU {
                thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, killed: true, ..pre.thread_map[thread_ptr] }), ..pre
            })
        }),
        kernel_k_to_kernel_u(*before) != kernel_k_to_kernel_u(*after),
        kernel_k_to_nonlock_kernel_u(*before) != kernel_k_to_nonlock_kernel_u(*after),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    kernel_thread_projection_at(before, thread_ptr); kernel_thread_projection_at(after, thread_ptr);
    kernel_thread_nonlock_projection_at(before, thread_ptr); kernel_thread_nonlock_projection_at(after, thread_ptr);
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, killed: true, ..pre.thread_map[thread_ptr] }), t => {
        if before.thr_mp.dom().contains(t) { kernel_thread_projection_at(before, t); kernel_thread_projection_at(after, t); }
    });
    assert_seqs_equal!(post.cpu_array == pre.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(before, i as usize); kernel_cpu_projection_at(after, i as usize); } });
    assert_maps_equal!(post.container_map, pre.container_map, c => {
        if before.ctn_mp.dom().contains(c) { kernel_container_projection_at(before, c); kernel_container_projection_at(after, c); }
    });
    assert_maps_equal!(post.process_map, pre.process_map, p => {
        if before.prc_mp.dom().contains(p) { kernel_process_projection_at(before, p); kernel_process_projection_at(after, p); }
    });
    assert_maps_equal!(post.endpoint_map, pre.endpoint_map, e => {
        if before.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(before, e); kernel_endpoint_projection_at(after, e); }
    });
}

/// The thread `thread_ptr` leaving the process `process_ptr`, which absorbs its quota, changes only that process's
/// threads and quota and that thread's state and quota, whatever proof-only state other threads carry; a changed state changes
/// both projections.
pub proof fn kernel_thread_left_process_implies_u_step(before: &KernelK, after: &KernelK, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr)
    requires
        *after == (KernelK { prc_mp: after.prc_mp, thr_mp: after.thr_mp, ..*before }),
        before.prc_mp.dom().contains(process_ptr),
        before.thr_mp.dom().contains(thread_ptr),
        after.prc_mp.unchanged_except(&before.prc_mp, process_ptr),
        after.prc_mp.spec_index(process_ptr).view() == (Process {
            quota_4k: (before.prc_mp.spec_index(process_ptr).view().quota_4k + before.thr_mp.spec_index(thread_ptr).view().quota_4k) as usize,
            quota_2m: (before.prc_mp.spec_index(process_ptr).view().quota_2m + before.thr_mp.spec_index(thread_ptr).view().quota_2m) as usize,
            quota_1g: (before.prc_mp.spec_index(process_ptr).view().quota_1g + before.thr_mp.spec_index(thread_ptr).view().quota_1g) as usize,
            owned_threads: after.prc_mp.spec_index(process_ptr).view().owned_threads, ..before.prc_mp.spec_index(process_ptr).view()
        }),
        after.prc_mp.spec_index(process_ptr).view().owned_threads.view() == before.prc_mp.spec_index(process_ptr).view().owned_threads.view().remove_value(thread_ptr),
        after.prc_mp.spec_index(process_ptr).view_rodata() == before.prc_mp.spec_index(process_ptr).view_rodata(),
        after.prc_mp.spec_index(process_ptr).view_ghost() == before.prc_mp.spec_index(process_ptr).view_ghost(),
        after.prc_mp.spec_index(process_ptr).locking_thread() == before.prc_mp.spec_index(process_ptr).locking_thread(),
        after.prc_mp.spec_index(process_ptr).being_killed() == before.prc_mp.spec_index(process_ptr).being_killed(),
        after.thr_mp.dom() == before.thr_mp.dom(),
        forall|t: RwLockThreadPtr| #![trigger after.thr_mp.spec_index(t)] before.thr_mp.dom().contains(t) && t != thread_ptr ==> {
            &&& after.thr_mp.spec_index(t).view() == before.thr_mp.spec_index(t).view()
            &&& after.thr_mp.spec_index(t).locking_thread() == before.thr_mp.spec_index(t).locking_thread()
            &&& after.thr_mp.spec_index(t).being_killed() == before.thr_mp.spec_index(t).being_killed()
        },
        after.thr_mp.spec_index(thread_ptr).view() == (Thread {
            state: after.thr_mp.spec_index(thread_ptr).view().state, quota_4k: 0, quota_2m: 0, quota_1g: 0,
            proc_linkedlist_node: after.thr_mp.spec_index(thread_ptr).view().proc_linkedlist_node, ..before.thr_mp.spec_index(thread_ptr).view()
        }),
        after.thr_mp.spec_index(thread_ptr).locking_thread() == before.thr_mp.spec_index(thread_ptr).locking_thread(),
        after.thr_mp.spec_index(thread_ptr).being_killed() == before.thr_mp.spec_index(thread_ptr).being_killed(),
    ensures
        kernel_k_to_kernel_u(*before).process_map.dom().contains(process_ptr),
        kernel_k_to_kernel_u(*before).thread_map.dom().contains(thread_ptr),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let process = pre.process_map[process_ptr];
            let thread = pre.thread_map[thread_ptr];
            kernel_k_to_kernel_u(*after) == (KernelU {
                process_map: pre.process_map.insert(process_ptr, ProcessU {
                    owned_threads: process.owned_threads.remove_value(thread_ptr), quota_4k: (process.quota_4k + thread.quota_4k) as usize,
                    quota_2m: (process.quota_2m + thread.quota_2m) as usize, quota_1g: (process.quota_1g + thread.quota_1g) as usize, ..process
                }),
                thread_map: pre.thread_map.insert(thread_ptr, ThreadU { state: after.thr_mp.spec_index(thread_ptr).view().state, quota_4k: 0, quota_2m: 0, quota_1g: 0, ..thread }),
                ..pre
            })
        }),
        after.thr_mp.spec_index(thread_ptr).view().state != before.thr_mp.spec_index(thread_ptr).view().state ==> {
            &&& kernel_k_to_kernel_u(*before) != kernel_k_to_kernel_u(*after)
            &&& kernel_k_to_nonlock_kernel_u(*before) != kernel_k_to_nonlock_kernel_u(*after)
        },
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    kernel_process_projection_at(before, process_ptr); kernel_thread_projection_at(before, thread_ptr); kernel_thread_projection_at(after, thread_ptr);
    kernel_thread_nonlock_projection_at(before, thread_ptr); kernel_thread_nonlock_projection_at(after, thread_ptr);
    let process = pre.process_map[process_ptr];
    let thread = pre.thread_map[thread_ptr];
    assert_maps_equal!(post.process_map, pre.process_map.insert(process_ptr, ProcessU {
        owned_threads: process.owned_threads.remove_value(thread_ptr), quota_4k: (process.quota_4k + thread.quota_4k) as usize,
        quota_2m: (process.quota_2m + thread.quota_2m) as usize, quota_1g: (process.quota_1g + thread.quota_1g) as usize, ..process
    }), p => {
        if before.prc_mp.dom().contains(p) { kernel_process_projection_at(before, p); kernel_process_projection_at(after, p); }
    });
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thread_ptr, ThreadU { state: after.thr_mp.spec_index(thread_ptr).view().state, quota_4k: 0, quota_2m: 0, quota_1g: 0, ..thread }), t => {
        if before.thr_mp.dom().contains(t) { kernel_thread_projection_at(before, t); kernel_thread_projection_at(after, t); }
    });
    assert_seqs_equal!(post.cpu_array == pre.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(before, i as usize); kernel_cpu_projection_at(after, i as usize); } });
    assert_maps_equal!(post.container_map, pre.container_map, c => {
        if before.ctn_mp.dom().contains(c) { kernel_container_projection_at(before, c); kernel_container_projection_at(after, c); }
    });
    assert_maps_equal!(post.endpoint_map, pre.endpoint_map, e => {
        if before.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(before, e); kernel_endpoint_projection_at(after, e); }
    });
    reveal(kernel_k_to_kernel_u);
}

/// The scheduled thread `thread_ptr` leaving shard `shard` of its container's scheduler `scheduler_ptr` and becoming
/// killed changes only that shard and the thread's state and error code, and changes both projections.
pub proof fn kernel_scheduled_thread_killed_implies_u_step(
    before: &KernelK, after: &KernelK, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr, shard: CpuId,
)
    requires
        index_valid(NUM_CPUS, shard),
        container_scheduler_wf(before.ctn_mp, before.sched_mp),
        *after == (KernelK { sched_mp: after.sched_mp, thr_mp: after.thr_mp, ..*before }),
        before.ctn_mp.dom().contains(container_ptr),
        before.ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        after.sched_mp.unchanged_except(&before.sched_mp, scheduler_ptr),
        scheduler_shards_of(after.sched_mp.spec_index(scheduler_ptr)) == scheduler_shards_of(before.sched_mp.spec_index(scheduler_ptr)).update(shard as int, scheduler_shards_of(before.sched_mp.spec_index(scheduler_ptr))[shard as int].remove_value(thread_ptr)),
        before.thr_mp.dom().contains(thread_ptr),
        !(before.thr_mp.spec_index(thread_ptr).view().state is KILLED),
        after.thr_mp.unchanged_except(&before.thr_mp, thread_ptr),
        after.thr_mp.spec_index(thread_ptr).view() == (Thread {
            state: ThreadState::KILLED, error_code: None, scheduler_linkedlist_node: after.thr_mp.spec_index(thread_ptr).view().scheduler_linkedlist_node, ..before.thr_mp.spec_index(thread_ptr).view()
        }),
        after.thr_mp.spec_index(thread_ptr).locking_thread() == before.thr_mp.spec_index(thread_ptr).locking_thread(),
        after.thr_mp.spec_index(thread_ptr).being_killed() == before.thr_mp.spec_index(thread_ptr).being_killed(),
    ensures
        kernel_k_to_kernel_u(*before).container_map.dom().contains(container_ptr),
        kernel_k_to_kernel_u(*before).thread_map.dom().contains(thread_ptr),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let container = pre.container_map[container_ptr];
            kernel_k_to_kernel_u(*after) == (KernelU {
                container_map: pre.container_map.insert(container_ptr, ContainerU {
                    scheduler: container.scheduler.update(shard as int, container.scheduler[shard as int].remove_value(thread_ptr)), ..container
                }),
                thread_map: pre.thread_map.insert(thread_ptr, ThreadU { state: ThreadState::KILLED, error_code: None, ..pre.thread_map[thread_ptr] }),
                ..pre
            })
        }),
        kernel_k_to_kernel_u(*before) != kernel_k_to_kernel_u(*after),
        kernel_k_to_nonlock_kernel_u(*before) != kernel_k_to_nonlock_kernel_u(*after),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    kernel_container_projection_at(before, container_ptr); kernel_thread_projection_at(before, thread_ptr); kernel_thread_projection_at(after, thread_ptr);
    kernel_thread_nonlock_projection_at(before, thread_ptr); kernel_thread_nonlock_projection_at(after, thread_ptr);
    let container = pre.container_map[container_ptr];
    assert_maps_equal!(post.container_map, pre.container_map.insert(container_ptr, ContainerU {
        scheduler: container.scheduler.update(shard as int, container.scheduler[shard as int].remove_value(thread_ptr)), ..container
    }), c => {
        if before.ctn_mp.dom().contains(c) {
            kernel_container_projection_at(before, c); kernel_container_projection_at(after, c);
            if c != container_ptr { container_scheduler_wf_at(before.ctn_mp, before.sched_mp, c); container_scheduler_wf_at(before.ctn_mp, before.sched_mp, container_ptr); }
        }
    });
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thread_ptr, ThreadU { state: ThreadState::KILLED, error_code: None, ..pre.thread_map[thread_ptr] }), t => {
        if before.thr_mp.dom().contains(t) { kernel_thread_projection_at(before, t); kernel_thread_projection_at(after, t); }
    });
    assert_seqs_equal!(post.cpu_array == pre.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(before, i as usize); kernel_cpu_projection_at(after, i as usize); } });
    assert_maps_equal!(post.process_map, pre.process_map, p => {
        if before.prc_mp.dom().contains(p) { kernel_process_projection_at(before, p); kernel_process_projection_at(after, p); }
    });
    assert_maps_equal!(post.endpoint_map, pre.endpoint_map, e => {
        if before.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(before, e); kernel_endpoint_projection_at(after, e); }
    });
}

/// The thread `thread_ptr` leaving the queue of the endpoint `endpoint_ptr` it waits on and becoming killed changes only
/// that queue and the thread's state and blocking endpoint, and changes both projections.
pub proof fn kernel_endpoint_waiter_killed_implies_u_step(before: &KernelK, after: &KernelK, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr)
    requires
        *after == (KernelK { ep_mp: after.ep_mp, thr_mp: after.thr_mp, ..*before }),
        before.ep_mp.dom().contains(endpoint_ptr),
        after.ep_mp.unchanged_except(&before.ep_mp, endpoint_ptr),
        after.ep_mp.spec_index(endpoint_ptr).view().queue.view() == before.ep_mp.spec_index(endpoint_ptr).view().queue.view().remove_value(thread_ptr),
        after.ep_mp.spec_index(endpoint_ptr).view().queue_state == before.ep_mp.spec_index(endpoint_ptr).view().queue_state,
        after.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view() == before.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view(),
        after.ep_mp.spec_index(endpoint_ptr).view().owning_container == before.ep_mp.spec_index(endpoint_ptr).view().owning_container,
        after.ep_mp.spec_index(endpoint_ptr).locking_thread() == before.ep_mp.spec_index(endpoint_ptr).locking_thread(),
        after.ep_mp.spec_index(endpoint_ptr).being_killed() == before.ep_mp.spec_index(endpoint_ptr).being_killed(),
        before.thr_mp.dom().contains(thread_ptr),
        !(before.thr_mp.spec_index(thread_ptr).view().state is KILLED),
        after.thr_mp.unchanged_except(&before.thr_mp, thread_ptr),
        after.thr_mp.spec_index(thread_ptr).view() == (Thread {
            state: ThreadState::KILLED, blocking_endpoint_ptr: None, blocking_endpoint_index: None,
            endpoint_linkedlist_node: after.thr_mp.spec_index(thread_ptr).view().endpoint_linkedlist_node, ..before.thr_mp.spec_index(thread_ptr).view()
        }),
        after.thr_mp.spec_index(thread_ptr).locking_thread() == before.thr_mp.spec_index(thread_ptr).locking_thread(),
        after.thr_mp.spec_index(thread_ptr).being_killed() == before.thr_mp.spec_index(thread_ptr).being_killed(),
    ensures
        kernel_k_to_kernel_u(*before).endpoint_map.dom().contains(endpoint_ptr),
        kernel_k_to_kernel_u(*before).thread_map.dom().contains(thread_ptr),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after) == (KernelU {
                endpoint_map: pre.endpoint_map.insert(endpoint_ptr, EndpointU { queue: pre.endpoint_map[endpoint_ptr].queue.remove_value(thread_ptr), ..pre.endpoint_map[endpoint_ptr] }),
                thread_map: pre.thread_map.insert(thread_ptr, ThreadU { state: ThreadState::KILLED, blocking_endpoint_ptr: None, ..pre.thread_map[thread_ptr] }),
                ..pre
            })
        }),
        kernel_k_to_kernel_u(*before) != kernel_k_to_kernel_u(*after),
        kernel_k_to_nonlock_kernel_u(*before) != kernel_k_to_nonlock_kernel_u(*after),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    kernel_endpoint_projection_at(before, endpoint_ptr); kernel_thread_projection_at(before, thread_ptr); kernel_thread_projection_at(after, thread_ptr);
    kernel_thread_nonlock_projection_at(before, thread_ptr); kernel_thread_nonlock_projection_at(after, thread_ptr);
    assert_maps_equal!(post.endpoint_map, pre.endpoint_map.insert(endpoint_ptr, EndpointU { queue: pre.endpoint_map[endpoint_ptr].queue.remove_value(thread_ptr), ..pre.endpoint_map[endpoint_ptr] }), e => {
        if before.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(before, e); kernel_endpoint_projection_at(after, e); }
    });
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thread_ptr, ThreadU { state: ThreadState::KILLED, blocking_endpoint_ptr: None, ..pre.thread_map[thread_ptr] }), t => {
        if before.thr_mp.dom().contains(t) { kernel_thread_projection_at(before, t); kernel_thread_projection_at(after, t); }
    });
    assert_seqs_equal!(post.cpu_array == pre.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(before, i as usize); kernel_cpu_projection_at(after, i as usize); } });
    assert_maps_equal!(post.container_map, pre.container_map, c => {
        if before.ctn_mp.dom().contains(c) { kernel_container_projection_at(before, c); kernel_container_projection_at(after, c); }
    });
    assert_maps_equal!(post.process_map, pre.process_map, p => {
        if before.prc_mp.dom().contains(p) { kernel_process_projection_at(before, p); kernel_process_projection_at(after, p); }
    });
}

/// Evicting the thread `thread_ptr` running on the remote cpu `remote` leaves that cpu idle without a process or thread
/// and kills the thread, and changes both projections.
pub proof fn kernel_running_thread_evicted_implies_u_step(before: &KernelK, after: &KernelK, thread_ptr: RwLockThreadPtr, remote: CpuId)
    requires
        index_valid(NUM_CPUS, remote),
        *after == (KernelK { cpu_arr: after.cpu_arr, cpu_hw_cr3_pcid: after.cpu_hw_cr3_pcid, cpu_op: after.cpu_op, thr_mp: after.thr_mp, ..*before }),
        before.cpu_op.view().view().len() == NUM_CPUS,
        after.cpu_op.view().view() == before.cpu_op.view().view().update(remote as int, CpuOpState::Idle),
        forall|c: CpuId| #![trigger after.cpu_arr.spec_index(c)] index_valid(NUM_CPUS, c) && c != remote ==> after.cpu_arr.spec_index(c) == before.cpu_arr.spec_index(c),
        after.cpu_arr.spec_index(remote).value.lock_state_u() == before.cpu_arr.spec_index(remote).value.lock_state_u(),
        after.cpu_arr.spec_index(remote).value.being_killed() == before.cpu_arr.spec_index(remote).value.being_killed(),
        after.cpu_arr.spec_index(remote).value.view().view().state is Idle,
        after.cpu_arr.spec_index(remote).value.view().view().current_process is None,
        after.cpu_arr.spec_index(remote).value.view().view().current_thread is None,
        after.cpu_arr.spec_index(remote).value.view().view().owning_container == before.cpu_arr.spec_index(remote).value.view().view().owning_container,
        before.thr_mp.dom().contains(thread_ptr),
        !(before.thr_mp.spec_index(thread_ptr).view().state is KILLED),
        after.thr_mp.unchanged_except(&before.thr_mp, thread_ptr),
        after.thr_mp.spec_index(thread_ptr).view() == (Thread { state: ThreadState::KILLED, ..before.thr_mp.spec_index(thread_ptr).view() }),
        after.thr_mp.spec_index(thread_ptr).locking_thread() == before.thr_mp.spec_index(thread_ptr).locking_thread(),
        after.thr_mp.spec_index(thread_ptr).being_killed() == before.thr_mp.spec_index(thread_ptr).being_killed(),
    ensures
        kernel_k_to_kernel_u(*before).thread_map.dom().contains(thread_ptr),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after) == (KernelU {
                cpu_array: pre.cpu_array.update(remote as int, CpuU { state: CpuState::Idle, op: CpuOpState::Idle, current_process: None, current_thread: None, ..pre.cpu_array[remote as int] }),
                thread_map: pre.thread_map.insert(thread_ptr, ThreadU { state: ThreadState::KILLED, ..pre.thread_map[thread_ptr] }),
                ..pre
            })
        }),
        kernel_k_to_kernel_u(*before) != kernel_k_to_kernel_u(*after),
        kernel_k_to_nonlock_kernel_u(*before) != kernel_k_to_nonlock_kernel_u(*after),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    kernel_thread_projection_at(before, thread_ptr); kernel_thread_projection_at(after, thread_ptr);
    kernel_thread_nonlock_projection_at(before, thread_ptr); kernel_thread_nonlock_projection_at(after, thread_ptr);
    assert_seqs_equal!(post.cpu_array == pre.cpu_array.update(remote as int, CpuU { state: CpuState::Idle, op: CpuOpState::Idle, current_process: None, current_thread: None, ..pre.cpu_array[remote as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(before, i as usize); kernel_cpu_projection_at(after, i as usize); }
    });
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thread_ptr, ThreadU { state: ThreadState::KILLED, ..pre.thread_map[thread_ptr] }), t => {
        if before.thr_mp.dom().contains(t) { kernel_thread_projection_at(before, t); kernel_thread_projection_at(after, t); }
    });
    assert_maps_equal!(post.container_map, pre.container_map, c => {
        if before.ctn_mp.dom().contains(c) { kernel_container_projection_at(before, c); kernel_container_projection_at(after, c); }
    });
    assert_maps_equal!(post.process_map, pre.process_map, p => {
        if before.prc_mp.dom().contains(p) { kernel_process_projection_at(before, p); kernel_process_projection_at(after, p); }
    });
    assert_maps_equal!(post.endpoint_map, pre.endpoint_map, e => {
        if before.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(before, e); kernel_endpoint_projection_at(after, e); }
    });
}
} // verus!
