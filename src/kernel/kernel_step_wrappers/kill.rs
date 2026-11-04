use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;

verus! {
/// Write-locking and marking the unmarked process `prc_ptr` changes only its lock mode, kill mark, and K-only state.
pub proof fn kernel_process_locked_and_marked_implies_u_step(before: &KernelK, after: &KernelK, prc_ptr: RwLockProcessPtr)
    requires
        *after == (KernelK { prc_mp: after.prc_mp, ..*before }),
        before.prc_mp.dom().contains(prc_ptr),
        after.prc_mp.unchanged_except(&before.prc_mp, prc_ptr),
        after.prc_mp.spec_index(prc_ptr).view() == (Process { state: after.prc_mp.spec_index(prc_ptr).view().state, ..before.prc_mp.spec_index(prc_ptr).view() }),
        after.prc_mp.spec_index(prc_ptr).view_rodata() == before.prc_mp.spec_index(prc_ptr).view_rodata(),
        after.prc_mp.spec_index(prc_ptr).view_ghost() == before.prc_mp.spec_index(prc_ptr).view_ghost(),
        after.prc_mp.spec_index(prc_ptr).locking_thread() is Write,
        after.prc_mp.spec_index(prc_ptr).being_killed(),
    ensures
        kernel_k_to_kernel_u(*before).process_map.dom().contains(prc_ptr),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after) == (KernelU {
                process_map: pre.process_map.insert(prc_ptr, ProcessU { lock_state: LockStateU::WriteLocked, killed: true, ..pre.process_map[prc_ptr] }), ..pre
            })
        }),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    assert_maps_equal!(post.process_map, pre.process_map.insert(prc_ptr, ProcessU { lock_state: LockStateU::WriteLocked, killed: true, ..pre.process_map[prc_ptr] }), p => {
        if before.prc_mp.dom().contains(p) { kernel_process_projection_at(before, p); kernel_process_projection_at(after, p); }
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(before, after); kernel_container_maps_unchanged_implies_u_container_map(before, after);
    kernel_thread_map_unchanged_implies_u_thread_map(before, after); kernel_endpoint_map_unchanged_implies_u_endpoint_map(before, after);
}

/// Write-locking and marking the unmarked thread `thrd_ptr` changes only its lock mode and kill mark, and changes the
/// projection.
pub proof fn kernel_thread_locked_and_marked_implies_u_step(before: &KernelK, after: &KernelK, thrd_ptr: RwLockThreadPtr)
    requires
        *after == (KernelK { thrd_mp: after.thrd_mp, ..*before }),
        before.thrd_mp.dom().contains(thrd_ptr),
        after.thrd_mp.unchanged_except(&before.thrd_mp, thrd_ptr),
        after.thrd_mp.spec_index(thrd_ptr).view() == before.thrd_mp.spec_index(thrd_ptr).view(),
        after.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
        !before.thrd_mp.spec_index(thrd_ptr).being_killed(),
        after.thrd_mp.spec_index(thrd_ptr).being_killed(),
    ensures
        kernel_k_to_kernel_u(*before).thread_map.dom().contains(thrd_ptr),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after) == (KernelU {
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::WriteLocked, killed: true, ..pre.thread_map[thrd_ptr] }), ..pre
            })
        }),
        kernel_k_to_kernel_u(*before) != kernel_k_to_kernel_u(*after),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    kernel_thread_projection_at(before, thrd_ptr); kernel_thread_projection_at(after, thrd_ptr);
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::WriteLocked, killed: true, ..pre.thread_map[thrd_ptr] }), t => {
        if before.thrd_mp.dom().contains(t) { kernel_thread_projection_at(before, t); kernel_thread_projection_at(after, t); }
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(before, after); kernel_container_maps_unchanged_implies_u_container_map(before, after);
    kernel_process_maps_unchanged_implies_u_process_map(before, after); kernel_endpoint_map_unchanged_implies_u_endpoint_map(before, after);
}

/// The thread `thrd_ptr` leaving the process `prc_ptr`, which absorbs its quota, changes only that process's
/// threads and quota and that thread's state and quota, whatever proof-only state other threads carry; a changed state changes
/// the projection.
pub proof fn kernel_thread_left_process_implies_u_step(before: &KernelK, after: &KernelK, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr)
    requires
        *after == (KernelK { prc_mp: after.prc_mp, thrd_mp: after.thrd_mp, ..*before }),
        before.prc_mp.dom().contains(prc_ptr),
        before.thrd_mp.dom().contains(thrd_ptr),
        after.prc_mp.unchanged_except(&before.prc_mp, prc_ptr),
        after.prc_mp.spec_index(prc_ptr).view() == (Process {
            quota_4k: (before.prc_mp.spec_index(prc_ptr).view().quota_4k + before.thrd_mp.spec_index(thrd_ptr).view().quota_4k) as usize,
            quota_2m: (before.prc_mp.spec_index(prc_ptr).view().quota_2m + before.thrd_mp.spec_index(thrd_ptr).view().quota_2m) as usize,
            quota_1g: (before.prc_mp.spec_index(prc_ptr).view().quota_1g + before.thrd_mp.spec_index(thrd_ptr).view().quota_1g) as usize,
            owned_threads: after.prc_mp.spec_index(prc_ptr).view().owned_threads, ..before.prc_mp.spec_index(prc_ptr).view()
        }),
        after.prc_mp.spec_index(prc_ptr).view().owned_threads.view() == before.prc_mp.spec_index(prc_ptr).view().owned_threads.view().remove_value(thrd_ptr),
        after.prc_mp.spec_index(prc_ptr).view_rodata() == before.prc_mp.spec_index(prc_ptr).view_rodata(),
        after.prc_mp.spec_index(prc_ptr).view_ghost() == before.prc_mp.spec_index(prc_ptr).view_ghost(),
        after.prc_mp.spec_index(prc_ptr).locking_thread() == before.prc_mp.spec_index(prc_ptr).locking_thread(),
        after.prc_mp.spec_index(prc_ptr).being_killed() == before.prc_mp.spec_index(prc_ptr).being_killed(),
        after.thrd_mp.dom() == before.thrd_mp.dom(),
        forall|t: RwLockThreadPtr| #![trigger after.thrd_mp.spec_index(t)] before.thrd_mp.dom().contains(t) && t != thrd_ptr ==> {
            &&& after.thrd_mp.spec_index(t).view() == before.thrd_mp.spec_index(t).view()
            &&& after.thrd_mp.spec_index(t).locking_thread() == before.thrd_mp.spec_index(t).locking_thread()
            &&& after.thrd_mp.spec_index(t).being_killed() == before.thrd_mp.spec_index(t).being_killed()
        },
        after.thrd_mp.spec_index(thrd_ptr).view() == (Thread {
            state: after.thrd_mp.spec_index(thrd_ptr).view().state, quota_4k: 0, quota_2m: 0, quota_1g: 0,
            proc_linkedlist_node: after.thrd_mp.spec_index(thrd_ptr).view().proc_linkedlist_node, ..before.thrd_mp.spec_index(thrd_ptr).view()
        }),
        after.thrd_mp.spec_index(thrd_ptr).locking_thread() == before.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        after.thrd_mp.spec_index(thrd_ptr).being_killed() == before.thrd_mp.spec_index(thrd_ptr).being_killed(),
    ensures
        kernel_k_to_kernel_u(*before).process_map.dom().contains(prc_ptr),
        kernel_k_to_kernel_u(*before).thread_map.dom().contains(thrd_ptr),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let process = pre.process_map[prc_ptr];
            let thread = pre.thread_map[thrd_ptr];
            kernel_k_to_kernel_u(*after) == (KernelU {
                process_map: pre.process_map.insert(prc_ptr, ProcessU {
                    owned_threads: process.owned_threads.remove_value(thrd_ptr), quota_4k: (process.quota_4k + thread.quota_4k) as usize,
                    quota_2m: (process.quota_2m + thread.quota_2m) as usize, quota_1g: (process.quota_1g + thread.quota_1g) as usize, ..process
                }),
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { state: after.thrd_mp.spec_index(thrd_ptr).view().state, quota_4k: 0, quota_2m: 0, quota_1g: 0, ..thread }),
                ..pre
            })
        }),
        after.thrd_mp.spec_index(thrd_ptr).view().state != before.thrd_mp.spec_index(thrd_ptr).view().state ==> {
            &&& kernel_k_to_kernel_u(*before) != kernel_k_to_kernel_u(*after)
        },
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    kernel_process_projection_at(before, prc_ptr); kernel_thread_projection_at(before, thrd_ptr); kernel_thread_projection_at(after, thrd_ptr);
    kernel_thread_left_process_implies_u_process_map(before, after, prc_ptr, thrd_ptr); kernel_thread_left_process_implies_u_thread_map(before, after, thrd_ptr);
    assert_seqs_equal!(post.cpu_array == pre.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(before, i as usize); kernel_cpu_projection_at(after, i as usize); } });
    assert_maps_equal!(post.container_map, pre.container_map, c => {
        if before.ctn_mp.dom().contains(c) { kernel_container_projection_at(before, c); kernel_container_projection_at(after, c); }
    });
    assert_maps_equal!(post.endpoint_map, pre.endpoint_map, e => {
        if before.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(before, e); kernel_endpoint_projection_at(after, e); }
    });
}

/// The thread `thrd_ptr` leaving the process `prc_ptr`, which absorbs its quota, changes only that process's threads and
/// quota in the process map projection.
proof fn kernel_thread_left_process_implies_u_process_map(before: &KernelK, after: &KernelK, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr)
    requires
        after.pt_mp == before.pt_mp,
        after.pt_lower == before.pt_lower,
        after.it_mp == before.it_mp,
        before.prc_mp.dom().contains(prc_ptr),
        before.thrd_mp.dom().contains(thrd_ptr),
        after.prc_mp.unchanged_except(&before.prc_mp, prc_ptr),
        after.prc_mp.spec_index(prc_ptr).view() == (Process {
            quota_4k: (before.prc_mp.spec_index(prc_ptr).view().quota_4k + before.thrd_mp.spec_index(thrd_ptr).view().quota_4k) as usize,
            quota_2m: (before.prc_mp.spec_index(prc_ptr).view().quota_2m + before.thrd_mp.spec_index(thrd_ptr).view().quota_2m) as usize,
            quota_1g: (before.prc_mp.spec_index(prc_ptr).view().quota_1g + before.thrd_mp.spec_index(thrd_ptr).view().quota_1g) as usize,
            owned_threads: after.prc_mp.spec_index(prc_ptr).view().owned_threads, ..before.prc_mp.spec_index(prc_ptr).view()
        }),
        after.prc_mp.spec_index(prc_ptr).view().owned_threads.view() == before.prc_mp.spec_index(prc_ptr).view().owned_threads.view().remove_value(thrd_ptr),
        after.prc_mp.spec_index(prc_ptr).view_rodata() == before.prc_mp.spec_index(prc_ptr).view_rodata(),
        after.prc_mp.spec_index(prc_ptr).view_ghost() == before.prc_mp.spec_index(prc_ptr).view_ghost(),
        after.prc_mp.spec_index(prc_ptr).locking_thread() == before.prc_mp.spec_index(prc_ptr).locking_thread(),
        after.prc_mp.spec_index(prc_ptr).being_killed() == before.prc_mp.spec_index(prc_ptr).being_killed(),
    ensures
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let process = pre.process_map[prc_ptr];
            let thread = pre.thread_map[thrd_ptr];
            kernel_k_to_kernel_u(*after).process_map == pre.process_map.insert(prc_ptr, ProcessU {
                owned_threads: process.owned_threads.remove_value(thrd_ptr), quota_4k: (process.quota_4k + thread.quota_4k) as usize,
                quota_2m: (process.quota_2m + thread.quota_2m) as usize, quota_1g: (process.quota_1g + thread.quota_1g) as usize, ..process
            })
        }),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    kernel_process_projection_at(before, prc_ptr); kernel_thread_projection_at(before, thrd_ptr);
    let process = pre.process_map[prc_ptr];
    let thread = pre.thread_map[thrd_ptr];
    assert_maps_equal!(post.process_map, pre.process_map.insert(prc_ptr, ProcessU {
        owned_threads: process.owned_threads.remove_value(thrd_ptr), quota_4k: (process.quota_4k + thread.quota_4k) as usize,
        quota_2m: (process.quota_2m + thread.quota_2m) as usize, quota_1g: (process.quota_1g + thread.quota_1g) as usize, ..process
    }), p => {
        if before.prc_mp.dom().contains(p) { kernel_process_projection_at(before, p); kernel_process_projection_at(after, p); }
    });
}

/// The thread `thrd_ptr` leaving its process, with its quota moved out and only its state otherwise changed, changes only
/// that thread's state and quota in the thread map projection.
proof fn kernel_thread_left_process_implies_u_thread_map(before: &KernelK, after: &KernelK, thrd_ptr: RwLockThreadPtr)
    requires
        before.thrd_mp.dom().contains(thrd_ptr),
        after.thrd_mp.dom() == before.thrd_mp.dom(),
        forall|t: RwLockThreadPtr| #![trigger after.thrd_mp.spec_index(t)] before.thrd_mp.dom().contains(t) && t != thrd_ptr ==> {
            &&& after.thrd_mp.spec_index(t).view() == before.thrd_mp.spec_index(t).view()
            &&& after.thrd_mp.spec_index(t).locking_thread() == before.thrd_mp.spec_index(t).locking_thread()
            &&& after.thrd_mp.spec_index(t).being_killed() == before.thrd_mp.spec_index(t).being_killed()
        },
        after.thrd_mp.spec_index(thrd_ptr).view() == (Thread {
            state: after.thrd_mp.spec_index(thrd_ptr).view().state, quota_4k: 0, quota_2m: 0, quota_1g: 0,
            proc_linkedlist_node: after.thrd_mp.spec_index(thrd_ptr).view().proc_linkedlist_node, ..before.thrd_mp.spec_index(thrd_ptr).view()
        }),
        after.thrd_mp.spec_index(thrd_ptr).locking_thread() == before.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        after.thrd_mp.spec_index(thrd_ptr).being_killed() == before.thrd_mp.spec_index(thrd_ptr).being_killed(),
    ensures
        ({
            let pre = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after).thread_map == pre.thread_map.insert(thrd_ptr, ThreadU {
                state: after.thrd_mp.spec_index(thrd_ptr).view().state, quota_4k: 0, quota_2m: 0, quota_1g: 0, ..pre.thread_map[thrd_ptr]
            })
        }),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    kernel_thread_projection_at(before, thrd_ptr);
    let thread = pre.thread_map[thrd_ptr];
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thrd_ptr, ThreadU { state: after.thrd_mp.spec_index(thrd_ptr).view().state, quota_4k: 0, quota_2m: 0, quota_1g: 0, ..thread }), t => {
        if before.thrd_mp.dom().contains(t) { kernel_thread_projection_at(before, t); kernel_thread_projection_at(after, t); }
    });
}

/// The scheduled thread `thrd_ptr` leaving shard `shard` of its container's scheduler `sched_ptr` and becoming
/// killed changes only that shard and the thread's state and error code, and changes the projection.
pub proof fn kernel_scheduled_thread_killed_implies_u_step(
    before: &KernelK, after: &KernelK, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, sched_ptr: RwLockSchedulerPtr, shard: CpuId,
)
    requires
        index_valid(NUM_CPUS, shard),
        container_scheduler_wf(before.ctn_mp, before.sched_mp),
        *after == (KernelK { sched_mp: after.sched_mp, thrd_mp: after.thrd_mp, ..*before }),
        before.ctn_mp.dom().contains(ctn_ptr),
        before.ctn_mp.spec_index(ctn_ptr).view_rodata().view().scheduler == sched_ptr,
        after.sched_mp.unchanged_except(&before.sched_mp, sched_ptr),
        scheduler_shards_of(after.sched_mp.spec_index(sched_ptr)) == scheduler_shards_of(before.sched_mp.spec_index(sched_ptr)).update(shard as int, scheduler_shards_of(before.sched_mp.spec_index(sched_ptr))[shard as int].remove_value(thrd_ptr)),
        before.thrd_mp.dom().contains(thrd_ptr),
        !(before.thrd_mp.spec_index(thrd_ptr).view().state is KILLED),
        after.thrd_mp.unchanged_except(&before.thrd_mp, thrd_ptr),
        after.thrd_mp.spec_index(thrd_ptr).view() == (Thread {
            state: ThreadState::KILLED, error_code: None, scheduler_linkedlist_node: after.thrd_mp.spec_index(thrd_ptr).view().scheduler_linkedlist_node, ..before.thrd_mp.spec_index(thrd_ptr).view()
        }),
        after.thrd_mp.spec_index(thrd_ptr).locking_thread() == before.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        after.thrd_mp.spec_index(thrd_ptr).being_killed() == before.thrd_mp.spec_index(thrd_ptr).being_killed(),
    ensures
        kernel_k_to_kernel_u(*before).container_map.dom().contains(ctn_ptr),
        kernel_k_to_kernel_u(*before).thread_map.dom().contains(thrd_ptr),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let container = pre.container_map[ctn_ptr];
            kernel_k_to_kernel_u(*after) == (KernelU {
                container_map: pre.container_map.insert(ctn_ptr, ContainerU {
                    scheduler: container.scheduler.update(shard as int, container.scheduler[shard as int].remove_value(thrd_ptr)), ..container
                }),
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { state: ThreadState::KILLED, error_code: None, ..pre.thread_map[thrd_ptr] }),
                ..pre
            })
        }),
        kernel_k_to_kernel_u(*before) != kernel_k_to_kernel_u(*after),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    kernel_container_projection_at(before, ctn_ptr); kernel_thread_projection_at(before, thrd_ptr); kernel_thread_projection_at(after, thrd_ptr);
    let container = pre.container_map[ctn_ptr];
    assert_maps_equal!(post.container_map, pre.container_map.insert(ctn_ptr, ContainerU {
        scheduler: container.scheduler.update(shard as int, container.scheduler[shard as int].remove_value(thrd_ptr)), ..container
    }), c => {
        if before.ctn_mp.dom().contains(c) {
            kernel_container_projection_at(before, c); kernel_container_projection_at(after, c);
            if c != ctn_ptr { container_scheduler_wf_at(before.ctn_mp, before.sched_mp, c); container_scheduler_wf_at(before.ctn_mp, before.sched_mp, ctn_ptr); }
        }
    });
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thrd_ptr, ThreadU { state: ThreadState::KILLED, error_code: None, ..pre.thread_map[thrd_ptr] }), t => {
        if before.thrd_mp.dom().contains(t) { kernel_thread_projection_at(before, t); kernel_thread_projection_at(after, t); }
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(before, after); kernel_process_maps_unchanged_implies_u_process_map(before, after);
    kernel_endpoint_map_unchanged_implies_u_endpoint_map(before, after);
}

/// The thread `thrd_ptr` leaving the queue of the endpoint `ep_ptr` it waits on and becoming killed changes only
/// that queue and the thread's state and blocking endpoint, and changes the projection.
pub proof fn kernel_endpoint_waiter_killed_implies_u_step(before: &KernelK, after: &KernelK, thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr)
    requires
        *after == (KernelK { ep_mp: after.ep_mp, thrd_mp: after.thrd_mp, ..*before }),
        before.ep_mp.dom().contains(ep_ptr),
        after.ep_mp.unchanged_except(&before.ep_mp, ep_ptr),
        after.ep_mp.spec_index(ep_ptr).view().queue.view() == before.ep_mp.spec_index(ep_ptr).view().queue.view().remove_value(thrd_ptr),
        after.ep_mp.spec_index(ep_ptr).view().queue_state == before.ep_mp.spec_index(ep_ptr).view().queue_state,
        after.ep_mp.spec_index(ep_ptr).view().owning_threads.view() == before.ep_mp.spec_index(ep_ptr).view().owning_threads.view(),
        after.ep_mp.spec_index(ep_ptr).view().owning_container == before.ep_mp.spec_index(ep_ptr).view().owning_container,
        after.ep_mp.spec_index(ep_ptr).locking_thread() == before.ep_mp.spec_index(ep_ptr).locking_thread(),
        after.ep_mp.spec_index(ep_ptr).being_killed() == before.ep_mp.spec_index(ep_ptr).being_killed(),
        before.thrd_mp.dom().contains(thrd_ptr),
        !(before.thrd_mp.spec_index(thrd_ptr).view().state is KILLED),
        after.thrd_mp.unchanged_except(&before.thrd_mp, thrd_ptr),
        after.thrd_mp.spec_index(thrd_ptr).view() == (Thread {
            state: ThreadState::KILLED, blocking_endpoint_ptr: None, blocking_endpoint_index: None,
            endpoint_linkedlist_node: after.thrd_mp.spec_index(thrd_ptr).view().endpoint_linkedlist_node, ..before.thrd_mp.spec_index(thrd_ptr).view()
        }),
        after.thrd_mp.spec_index(thrd_ptr).locking_thread() == before.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        after.thrd_mp.spec_index(thrd_ptr).being_killed() == before.thrd_mp.spec_index(thrd_ptr).being_killed(),
    ensures
        kernel_k_to_kernel_u(*before).endpoint_map.dom().contains(ep_ptr),
        kernel_k_to_kernel_u(*before).thread_map.dom().contains(thrd_ptr),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after) == (KernelU {
                endpoint_map: pre.endpoint_map.insert(ep_ptr, EndpointU { queue: pre.endpoint_map[ep_ptr].queue.remove_value(thrd_ptr), ..pre.endpoint_map[ep_ptr] }),
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { state: ThreadState::KILLED, blocking_endpoint_ptr: None, ..pre.thread_map[thrd_ptr] }),
                ..pre
            })
        }),
        kernel_k_to_kernel_u(*before) != kernel_k_to_kernel_u(*after),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    kernel_endpoint_projection_at(before, ep_ptr); kernel_thread_projection_at(before, thrd_ptr); kernel_thread_projection_at(after, thrd_ptr);
    assert_maps_equal!(post.endpoint_map, pre.endpoint_map.insert(ep_ptr, EndpointU { queue: pre.endpoint_map[ep_ptr].queue.remove_value(thrd_ptr), ..pre.endpoint_map[ep_ptr] }), e => {
        if before.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(before, e); kernel_endpoint_projection_at(after, e); }
    });
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thrd_ptr, ThreadU { state: ThreadState::KILLED, blocking_endpoint_ptr: None, ..pre.thread_map[thrd_ptr] }), t => {
        if before.thrd_mp.dom().contains(t) { kernel_thread_projection_at(before, t); kernel_thread_projection_at(after, t); }
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(before, after); kernel_container_maps_unchanged_implies_u_container_map(before, after);
    kernel_process_maps_unchanged_implies_u_process_map(before, after);
}

/// Forcing the remote cpu `remote` running the thread `thrd_ptr` from running to idle leaves it without a process or
/// thread and kills the thread, and changes the projection.
pub proof fn kernel_running_thread_cpu_to_idle_implies_u_step(before: &KernelK, after: &KernelK, thrd_ptr: RwLockThreadPtr, remote: CpuId)
    requires
        index_valid(NUM_CPUS, remote),
        *after == (KernelK { cpu_arr: after.cpu_arr, cpu_hw_cr3_pcid: after.cpu_hw_cr3_pcid, cpu_op: after.cpu_op, thrd_mp: after.thrd_mp, ..*before }),
        before.cpu_op.view().view().len() == NUM_CPUS,
        after.cpu_op.view().view() == before.cpu_op.view().view().update(remote as int, CpuOpState::Idle),
        forall|c: CpuId| #![trigger after.cpu_arr.spec_index(c)] index_valid(NUM_CPUS, c) && c != remote ==> after.cpu_arr.spec_index(c) == before.cpu_arr.spec_index(c),
        after.cpu_arr.spec_index(remote).value.lock_state_u() == before.cpu_arr.spec_index(remote).value.lock_state_u(),
        after.cpu_arr.spec_index(remote).value.being_killed() == before.cpu_arr.spec_index(remote).value.being_killed(),
        after.cpu_arr.spec_index(remote).value.view().view().state is Idle,
        after.cpu_arr.spec_index(remote).value.view().view().current_process is None,
        after.cpu_arr.spec_index(remote).value.view().view().current_thread is None,
        after.cpu_arr.spec_index(remote).value.view().view().owning_container == before.cpu_arr.spec_index(remote).value.view().view().owning_container,
        before.thrd_mp.dom().contains(thrd_ptr),
        !(before.thrd_mp.spec_index(thrd_ptr).view().state is KILLED),
        after.thrd_mp.unchanged_except(&before.thrd_mp, thrd_ptr),
        after.thrd_mp.spec_index(thrd_ptr).view() == (Thread { state: ThreadState::KILLED, ..before.thrd_mp.spec_index(thrd_ptr).view() }),
        after.thrd_mp.spec_index(thrd_ptr).locking_thread() == before.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        after.thrd_mp.spec_index(thrd_ptr).being_killed() == before.thrd_mp.spec_index(thrd_ptr).being_killed(),
    ensures
        kernel_k_to_kernel_u(*before).thread_map.dom().contains(thrd_ptr),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after) == (KernelU {
                cpu_array: pre.cpu_array.update(remote as int, CpuU { state: CpuState::Idle, op: CpuOpState::Idle, current_process: None, current_thread: None, ..pre.cpu_array[remote as int] }),
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { state: ThreadState::KILLED, ..pre.thread_map[thrd_ptr] }),
                ..pre
            })
        }),
        kernel_k_to_kernel_u(*before) != kernel_k_to_kernel_u(*after),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    kernel_thread_projection_at(before, thrd_ptr); kernel_thread_projection_at(after, thrd_ptr);
    assert_seqs_equal!(post.cpu_array == pre.cpu_array.update(remote as int, CpuU { state: CpuState::Idle, op: CpuOpState::Idle, current_process: None, current_thread: None, ..pre.cpu_array[remote as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(before, i as usize); kernel_cpu_projection_at(after, i as usize); }
    });
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thrd_ptr, ThreadU { state: ThreadState::KILLED, ..pre.thread_map[thrd_ptr] }), t => {
        if before.thrd_mp.dom().contains(t) { kernel_thread_projection_at(before, t); kernel_thread_projection_at(after, t); }
    });
    kernel_container_maps_unchanged_implies_u_container_map(before, after); kernel_process_maps_unchanged_implies_u_process_map(before, after);
    kernel_endpoint_map_unchanged_implies_u_endpoint_map(before, after);
}
} // verus!
