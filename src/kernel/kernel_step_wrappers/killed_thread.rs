use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal, assert_sets_equal};
use crate::*;

verus! {
/// Releasing descriptor `index` of the write-held killed thread `thrd_ptr` projects to
/// `kernel_u_killed_descriptor_dropped`, changes the projection, and changes no thread outside `thrd_ptr`'s container.
pub proof fn kernel_killed_descriptor_dropped_implies_u_step(before: &KernelK, after: &KernelK, thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr, index: EndpointIdx)
    requires
        index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        *after == (KernelK { thrd_mp: after.thrd_mp, ep_mp: after.ep_mp, ..*before }),
        before.thrd_mp.dom().contains(thrd_ptr),
        before.thrd_mp.spec_index(thrd_ptr).view().state is KILLED,
        before.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
        before.thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view().len() == MAX_NUM_ENDPOINT_DESCRIPTORS,
        before.thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view()[index as int] == Some(ep_ptr),
        after.thrd_mp.unchanged_except(&before.thrd_mp, thrd_ptr),
        after.thrd_mp.spec_index(thrd_ptr).view() == (Thread { endpoint_descriptors: after.thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors, ..before.thrd_mp.spec_index(thrd_ptr).view() }),
        after.thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view() == before.thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view().update(index as int, None),
        after.thrd_mp.spec_index(thrd_ptr).locking_thread() == before.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        after.thrd_mp.spec_index(thrd_ptr).being_killed() == before.thrd_mp.spec_index(thrd_ptr).being_killed(),
        before.ep_mp.dom().contains(ep_ptr),
        before.ep_mp.spec_index(ep_ptr).locking_thread() is None,
        before.ep_mp.spec_index(ep_ptr).view().owning_threads.view().len() > 1,
        after.ep_mp.unchanged_except(&before.ep_mp, ep_ptr),
        after.ep_mp.spec_index(ep_ptr).view().queue.view() == before.ep_mp.spec_index(ep_ptr).view().queue.view(),
        after.ep_mp.spec_index(ep_ptr).view().queue_state == before.ep_mp.spec_index(ep_ptr).view().queue_state,
        after.ep_mp.spec_index(ep_ptr).view().owning_container == before.ep_mp.spec_index(ep_ptr).view().owning_container,
        after.ep_mp.spec_index(ep_ptr).view().owning_threads.view() == before.ep_mp.spec_index(ep_ptr).view().owning_threads.view().remove((thrd_ptr, index)),
        after.ep_mp.spec_index(ep_ptr).locking_thread() == before.ep_mp.spec_index(ep_ptr).locking_thread(),
        after.ep_mp.spec_index(ep_ptr).being_killed() == before.ep_mp.spec_index(ep_ptr).being_killed(),
    ensures
        kernel_u_killed_descriptor_dropped(kernel_k_to_kernel_u(*before), kernel_k_to_kernel_u(*after)),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let post = kernel_k_to_kernel_u(*after);
            forall|t: RwLockThreadPtr| #![trigger pre.thread_map[t]]
                pre.thread_map.dom().contains(t) && (!post.thread_map.dom().contains(t) || post.thread_map[t] != pre.thread_map[t]) ==> pre.thread_map[t].owning_container == before.thrd_mp.spec_index(thrd_ptr).view().owning_container
        }),
        kernel_k_to_kernel_u(*before) != kernel_k_to_kernel_u(*after),
{
    kernel_descriptor_dropped_implies_u_step(before, after, thrd_ptr, ep_ptr, index);
    kernel_thread_projection_at(before, thrd_ptr); kernel_thread_projection_at(after, thrd_ptr); kernel_endpoint_projection_at(before, ep_ptr);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    let thread = pre.thread_map[thrd_ptr];
    assert_sets_equal!(pre.thread_map.dom().filter(|t: RwLockThreadPtr| post.thread_map[t] != pre.thread_map[t]), set![thrd_ptr]);
    assert_sets_equal!(Set::<int>::range(0, MAX_NUM_ENDPOINT_DESCRIPTORS as int).filter(|j: int| post.thread_map[thrd_ptr].endpoint_descriptors[j] != thread.endpoint_descriptors[j]), set![index as int]);
    reveal(kernel_u_killed_descriptor_dropped);
}

/// Waking `caller_ptr`, the unlocked caller of the write-held killed thread `thrd_ptr` waiting for its reply in the same
/// container, projects to `kernel_u_killed_caller_woken`, changes the projection, and changes no thread outside that
/// container.
pub proof fn kernel_killed_caller_woken_implies_u_step(before: &KernelK, after: &KernelK, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, caller_ptr: RwLockThreadPtr)
    requires
        after.inv(),
        before.thrd_mp.dom().contains(thrd_ptr),
        before.thrd_mp.dom().contains(caller_ptr),
        before.thrd_mp.spec_index(thrd_ptr).view().state is KILLED,
        before.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
        before.thrd_mp.spec_index(thrd_ptr).view().caller == Some(caller_ptr),
        before.thrd_mp.spec_index(caller_ptr).view().state is WAITING_REPLY,
        before.thrd_mp.spec_index(caller_ptr).view().callee == Some(thrd_ptr),
        before.thrd_mp.spec_index(caller_ptr).locking_thread() is None,
        before.thrd_mp.spec_index(caller_ptr).view().owning_container == before.thrd_mp.spec_index(thrd_ptr).view().owning_container,
        *after == (KernelK { thrd_mp: after.thrd_mp, sched_mp: after.sched_mp, ..*before }),
        after.thrd_mp.dom() == before.thrd_mp.dom(),
        forall|t: RwLockThreadPtr| #![trigger after.thrd_mp.spec_index(t)]
            before.thrd_mp.dom().contains(t) && t != thrd_ptr && t != caller_ptr ==> after.thrd_mp.spec_index(t) == before.thrd_mp.spec_index(t),
        after.thrd_mp.spec_index(thrd_ptr).view() == (Thread { caller: None, ..before.thrd_mp.spec_index(thrd_ptr).view() }),
        after.thrd_mp.spec_index(thrd_ptr).locking_thread() == before.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        after.thrd_mp.spec_index(thrd_ptr).being_killed() == before.thrd_mp.spec_index(thrd_ptr).being_killed(),
        after.thrd_mp.spec_index(caller_ptr).view() == (Thread {
            state: ThreadState::SCHEDULED { cpu_id }, callee: None, error_code: Some(RetValueType::ErrorIpcCalleeExited),
            scheduler_linkedlist_node: after.thrd_mp.spec_index(caller_ptr).view().scheduler_linkedlist_node, ..before.thrd_mp.spec_index(caller_ptr).view()
        }),
        after.thrd_mp.spec_index(caller_ptr).locking_thread() == before.thrd_mp.spec_index(caller_ptr).locking_thread(),
        after.thrd_mp.spec_index(caller_ptr).being_killed() == before.thrd_mp.spec_index(caller_ptr).being_killed(),
        after.sched_mp.dom() == before.sched_mp.dom(),
        forall|s: RwLockSchedulerPtr| #![trigger after.sched_mp.spec_index(s)] before.sched_mp.dom().contains(s) ==>
            scheduler_shards_of(after.sched_mp.spec_index(s)) == if s == before.ctn_mp.spec_index(before.thrd_mp.spec_index(caller_ptr).view().owning_container).view_rodata().view().scheduler {
                scheduler_shards_of(before.sched_mp.spec_index(s)).update(cpu_id as int, scheduler_shards_of(before.sched_mp.spec_index(s))[cpu_id as int].push(caller_ptr))
            } else { scheduler_shards_of(before.sched_mp.spec_index(s)) },
    ensures
        kernel_u_killed_caller_woken(kernel_k_to_kernel_u(*before), kernel_k_to_kernel_u(*after), cpu_id),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let post = kernel_k_to_kernel_u(*after);
            forall|t: RwLockThreadPtr| #![trigger pre.thread_map[t]]
                pre.thread_map.dom().contains(t) && (!post.thread_map.dom().contains(t) || post.thread_map[t] != pre.thread_map[t]) ==> pre.thread_map[t].owning_container == before.thrd_mp.spec_index(thrd_ptr).view().owning_container
        }),
        kernel_k_to_kernel_u(*before) != kernel_k_to_kernel_u(*after),
{
    kernel_caller_woken_implies_u_step(before, after, cpu_id, thrd_ptr, caller_ptr);
    kernel_thread_projection_at(before, thrd_ptr); kernel_thread_projection_at(before, caller_ptr); kernel_thread_projection_at(after, caller_ptr);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    assert_sets_equal!(pre.thread_map.dom().filter(|t: RwLockThreadPtr| pre.thread_map[t].state is WAITING_REPLY && post.thread_map[t].state is SCHEDULED), set![caller_ptr]);
    reveal(kernel_u_killed_caller_woken);
}

/// Taking over `caller_ptr`, the unlocked dangling thread of the killed caller of the write-held killed thread `thrd_ptr`
/// in the same container, projects to `kernel_u_killed_caller_taken_over`, changes the projection, and changes no thread
/// outside that container.
pub proof fn kernel_killed_caller_taken_over_implies_u_step(before: &KernelK, after: &KernelK, thrd_ptr: RwLockThreadPtr, caller_ptr: RwLockThreadPtr)
    requires
        before.thrd_mp.dom().contains(thrd_ptr),
        before.thrd_mp.dom().contains(caller_ptr),
        thrd_ptr != caller_ptr,
        before.thrd_mp.spec_index(thrd_ptr).view().state is KILLED,
        before.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
        before.thrd_mp.spec_index(thrd_ptr).view().caller == Some(caller_ptr),
        before.thrd_mp.spec_index(caller_ptr).view().state is DANGLING,
        before.thrd_mp.spec_index(caller_ptr).view().callee == Some(thrd_ptr),
        before.thrd_mp.spec_index(caller_ptr).locking_thread() is None,
        before.thrd_mp.spec_index(caller_ptr).view().owning_container == before.thrd_mp.spec_index(thrd_ptr).view().owning_container,
        *after == (KernelK { thrd_mp: after.thrd_mp, ..*before }),
        after.thrd_mp.dom() == before.thrd_mp.dom(),
        forall|t: RwLockThreadPtr| #![trigger after.thrd_mp.spec_index(t)]
            before.thrd_mp.dom().contains(t) && t != thrd_ptr && t != caller_ptr ==> after.thrd_mp.spec_index(t) == before.thrd_mp.spec_index(t),
        after.thrd_mp.spec_index(thrd_ptr).view() == (Thread { caller: None, ..before.thrd_mp.spec_index(thrd_ptr).view() }),
        after.thrd_mp.spec_index(thrd_ptr).locking_thread() == before.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        after.thrd_mp.spec_index(thrd_ptr).being_killed() == before.thrd_mp.spec_index(thrd_ptr).being_killed(),
        after.thrd_mp.spec_index(caller_ptr).view() == (Thread { state: ThreadState::KILLED, callee: None, ..before.thrd_mp.spec_index(caller_ptr).view() }),
        after.thrd_mp.spec_index(caller_ptr).locking_thread() is Write,
        after.thrd_mp.spec_index(caller_ptr).being_killed() == before.thrd_mp.spec_index(caller_ptr).being_killed(),
    ensures
        kernel_u_killed_caller_taken_over(kernel_k_to_kernel_u(*before), kernel_k_to_kernel_u(*after)),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let post = kernel_k_to_kernel_u(*after);
            forall|t: RwLockThreadPtr| #![trigger pre.thread_map[t]]
                pre.thread_map.dom().contains(t) && (!post.thread_map.dom().contains(t) || post.thread_map[t] != pre.thread_map[t]) ==> pre.thread_map[t].owning_container == before.thrd_mp.spec_index(thrd_ptr).view().owning_container
        }),
        kernel_k_to_kernel_u(*before) != kernel_k_to_kernel_u(*after),
{
    kernel_dangling_caller_taken_over_implies_u_step(before, after, thrd_ptr, caller_ptr, None);
    kernel_thread_projection_at(before, thrd_ptr); kernel_thread_projection_at(before, caller_ptr); kernel_thread_projection_at(after, caller_ptr);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    assert_sets_equal!(pre.thread_map.dom().filter(|t: RwLockThreadPtr| pre.thread_map[t].state is DANGLING && post.thread_map[t].state is KILLED), set![caller_ptr]);
    reveal(kernel_u_killed_caller_taken_over);
}

/// A callee taking over its dangling caller `dangling_ptr` drops its caller link and turns the write-locked dangling thread into a
/// killed thread without a callee; the write-held `endpoint`, if any, is released.
pub proof fn kernel_dangling_caller_taken_over_implies_u_step(
    before: &KernelK, after: &KernelK, callee_ptr: RwLockThreadPtr, dangling_ptr: RwLockThreadPtr, endpoint: Option<RwLockEndpointPtr>,
)
    requires
        before.thrd_mp.dom().contains(callee_ptr),
        before.thrd_mp.dom().contains(dangling_ptr),
        callee_ptr != dangling_ptr,
        *after == (KernelK { thrd_mp: after.thrd_mp, ep_mp: after.ep_mp, ..*before }),
        match endpoint {
            Some(e) => before.ep_mp.dom().contains(e) && after.ep_mp.unchanged_except(&before.ep_mp, e) && wunlock_ensures(before.ep_mp.spec_index(e), after.ep_mp.spec_index(e)),
            None => after.ep_mp == before.ep_mp,
        },
        after.thrd_mp.dom() == before.thrd_mp.dom(),
        forall|t: RwLockThreadPtr| #![trigger after.thrd_mp.spec_index(t)]
            before.thrd_mp.dom().contains(t) && t != callee_ptr && t != dangling_ptr ==> after.thrd_mp.spec_index(t) == before.thrd_mp.spec_index(t),
        after.thrd_mp.spec_index(callee_ptr).view() == (Thread { caller: None, ..before.thrd_mp.spec_index(callee_ptr).view() }),
        after.thrd_mp.spec_index(callee_ptr).locking_thread() == before.thrd_mp.spec_index(callee_ptr).locking_thread(),
        after.thrd_mp.spec_index(callee_ptr).being_killed() == before.thrd_mp.spec_index(callee_ptr).being_killed(),
        after.thrd_mp.spec_index(dangling_ptr).view() == (Thread { state: ThreadState::KILLED, callee: None, ..before.thrd_mp.spec_index(dangling_ptr).view() }),
        after.thrd_mp.spec_index(dangling_ptr).locking_thread() is Write,
        after.thrd_mp.spec_index(dangling_ptr).being_killed() == before.thrd_mp.spec_index(dangling_ptr).being_killed(),
    ensures
        ({
            let pre = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after) == (KernelU {
                thread_map: pre.thread_map.insert(callee_ptr, ThreadU { caller: None, ..pre.thread_map[callee_ptr] }) .insert(dangling_ptr, ThreadU { state: ThreadState::KILLED, callee: None, lock_state: LockStateU::WriteLocked, ..pre.thread_map[dangling_ptr] }),
                endpoint_map: match endpoint { Some(e) => pre.endpoint_map.insert(e, EndpointU { lock_state: LockStateU::Unlocked, ..pre.endpoint_map[e] }), None => pre.endpoint_map },
                ..pre
            })
        }),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(callee_ptr, ThreadU { caller: None, ..pre.thread_map[callee_ptr] }) .insert(dangling_ptr, ThreadU { state: ThreadState::KILLED, callee: None, lock_state: LockStateU::WriteLocked, ..pre.thread_map[dangling_ptr] }), t => {
        if before.thrd_mp.dom().contains(t) { kernel_thread_projection_at(before, t); kernel_thread_projection_at(after, t); }
    });
    assert_maps_equal!(post.endpoint_map, match endpoint { Some(e) => pre.endpoint_map.insert(e, EndpointU { lock_state: LockStateU::Unlocked, ..pre.endpoint_map[e] }), None => pre.endpoint_map }, e => {
        if before.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(before, e); kernel_endpoint_projection_at(after, e); }
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(before, after); kernel_container_maps_unchanged_implies_u_container_map(before, after); kernel_process_maps_unchanged_implies_u_process_map(before, after);
}

/// Releasing a held cpu and its running thread changes only their lock modes and the cpu's running state.
pub proof fn kernel_cpu_and_thread_unlocked_implies_u_step(before: &KernelK, after: &KernelK, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr)
    requires
        index_valid(NUM_CPUS, cpu_id),
        before.thrd_mp.dom().contains(thrd_ptr),
        *after == (KernelK { cpu_arr: after.cpu_arr, cpu_op: after.cpu_op, thrd_mp: after.thrd_mp, ..*before }),
        after.cpu_arr.entries_unchanged_except(&before.cpu_arr, cpu_id),
        forall|i: CpuId| #![trigger after.cpu_op.view().view()[i as int]] index_valid(NUM_CPUS, i) && i != cpu_id ==> after.cpu_op.view().view()[i as int] == before.cpu_op.view().view()[i as int],
        after.cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        after.cpu_arr.spec_index(cpu_id).value.being_killed() == before.cpu_arr.spec_index(cpu_id).value.being_killed(),
        after.thrd_mp.unchanged_except(&before.thrd_mp, thrd_ptr),
        after.thrd_mp.spec_index(thrd_ptr).locking_thread() is None,
        kernel_cpu_process_thread_nonlock_fields_unchanged(before, after),
    ensures
        ({
            let pre = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after) == (KernelU {
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: after.cpu_op.view().view()[cpu_id as int], ..pre.cpu_array[cpu_id as int] }),
                thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..pre.thread_map[thrd_ptr] }),
                ..pre
            })
        }),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..pre.thread_map[thrd_ptr] }), t => {
        if before.thrd_mp.dom().contains(t) { kernel_thread_projection_at(before, t); kernel_thread_projection_at(after, t); }
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
    });
    assert_seqs_equal!(post.cpu_array == pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: after.cpu_op.view().view()[cpu_id as int], ..pre.cpu_array[cpu_id as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(before, i as usize); kernel_cpu_projection_at(after, i as usize); }
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
    });
    kernel_container_maps_unchanged_implies_u_container_map(before, after); kernel_process_maps_unchanged_implies_u_process_map(before, after);
    kernel_endpoint_map_unchanged_implies_u_endpoint_map(before, after);
}

/// Reclaiming a killed dangling thread projects to `kernel_u_dangling_thread_reclaimed` and changes or removes no thread
/// outside its container.
pub proof fn kernel_dangling_thread_reclaimed_implies_u_step(before: &KernelK, after: &KernelK, dangling_ptr: RwLockThreadPtr)
    requires kernel_dangling_thread_reclaimed_fields(before, after, dangling_ptr),
    ensures
        kernel_u_dangling_thread_reclaimed(kernel_k_to_kernel_u(*before), kernel_k_to_kernel_u(*after)),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let post = kernel_k_to_kernel_u(*after);
            forall|t: RwLockThreadPtr| #![trigger pre.thread_map[t]]
                pre.thread_map.dom().contains(t) && (!post.thread_map.dom().contains(t) || post.thread_map[t] != pre.thread_map[t]) ==> pre.thread_map[t].owning_container == before.thrd_mp.spec_index(dangling_ptr).view().owning_container
        }),
        kernel_k_to_kernel_u(*before) != kernel_k_to_kernel_u(*after),
{
    reveal(kernel_dangling_thread_reclaimed_fields);
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    assert_sets_equal!(pre.thread_map.dom().difference(post.thread_map.dom()), set![dangling_ptr]);
    kernel_thread_projection_at(before, dangling_ptr);
    assert_maps_equal!(post.thread_map, pre.thread_map.remove(dangling_ptr), t => {
        if after.thrd_mp.dom().contains(t) { kernel_thread_projection_at(before, t); kernel_thread_projection_at(after, t); }
    });
    let dangling = pre.thread_map[dangling_ptr];
    assert_maps_equal!(post.container_map, Map::new(pre.container_map.dom(), |c: RwLockContainerPtr| {
        let container = pre.container_map[c];
        ContainerU {
            owned_threads: if c == dangling.owning_container { container.owned_threads.remove(dangling_ptr) } else { container.owned_threads },
            quota_4k: if container.owned_pages.contains(dangling_ptr) { (container.quota_4k + 1) as usize } else { container.quota_4k }, ..container
        }
    }), c => {
        if before.ctn_mp.dom().contains(c) { kernel_container_projection_at(before, c); kernel_container_projection_at(after, c); }
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(before, after); kernel_process_maps_unchanged_implies_u_process_map(before, after);
    kernel_endpoint_map_unchanged_implies_u_endpoint_map(before, after);
    reveal(kernel_u_dangling_thread_reclaimed);
}

/// The lock mode, kill mark, and owning container of process `ptr` in the user projection, without unfolding the rest
/// of its entry.
pub broadcast proof fn kernel_process_lock_state_projection_at(krnl: &KernelK, ptr: RwLockProcessPtr)
    requires krnl.prc_mp.dom().contains(ptr),
    ensures
        kernel_k_to_kernel_u(*krnl).process_map.dom().contains(ptr),
        (#[trigger] kernel_k_to_kernel_u(*krnl).process_map[ptr]).lock_state == krnl.prc_mp.spec_index(ptr).lock_state_u(),
        kernel_k_to_kernel_u(*krnl).process_map[ptr].killed == krnl.prc_mp.spec_index(ptr).being_killed(),
        kernel_k_to_kernel_u(*krnl).process_map[ptr].owning_container == krnl.prc_mp.spec_index(ptr).view_rodata().view().owning_container,
{ kernel_process_projection_at(krnl, ptr); }

/// The lock mode and upper tree of container `ptr` in the user projection, without unfolding the rest of its entry.
pub broadcast proof fn kernel_container_lock_state_projection_at(krnl: &KernelK, ptr: RwLockContainerPtr)
    requires krnl.ctn_mp.dom().contains(ptr),
    ensures
        kernel_k_to_kernel_u(*krnl).container_map.dom().contains(ptr),
        (#[trigger] kernel_k_to_kernel_u(*krnl).container_map[ptr]).lock_state == krnl.ctn_mp.spec_index(ptr).lock_state_u(),
        kernel_k_to_kernel_u(*krnl).container_map[ptr].uppertree_seq == krnl.ctn_mp.spec_index(ptr).view_ghost().uppertree_seq.view(),
{ kernel_container_projection_at(krnl, ptr); }

/// K states agreeing on the lock modes, kill marks, and owning containers of `processes` and on the lock modes and upper
/// trees of `containers` project to user states agreeing on them.
pub proof fn kernel_process_container_lock_states_projection_eq(a: &KernelK, b: &KernelK, processes: Set<RwLockProcessPtr>, containers: Set<RwLockContainerPtr>)
    requires
        forall|p: RwLockProcessPtr| #![trigger processes.contains(p)] processes.contains(p) ==> {
            &&& a.prc_mp.dom().contains(p)
            &&& b.prc_mp.dom().contains(p)
            &&& a.prc_mp.spec_index(p).locking_thread() == b.prc_mp.spec_index(p).locking_thread()
            &&& a.prc_mp.spec_index(p).being_killed() == b.prc_mp.spec_index(p).being_killed()
            &&& a.prc_mp.spec_index(p).view_rodata().view().owning_container == b.prc_mp.spec_index(p).view_rodata().view().owning_container
        },
        forall|c: RwLockContainerPtr| #![trigger containers.contains(c)] containers.contains(c) ==> {
            &&& a.ctn_mp.dom().contains(c)
            &&& b.ctn_mp.dom().contains(c)
            &&& a.ctn_mp.spec_index(c).locking_thread() == b.ctn_mp.spec_index(c).locking_thread()
            &&& a.ctn_mp.spec_index(c).view_ghost().uppertree_seq == b.ctn_mp.spec_index(c).view_ghost().uppertree_seq
        },
    ensures
        forall|p: RwLockProcessPtr| #![trigger processes.contains(p)] processes.contains(p) ==> {
            &&& kernel_k_to_kernel_u(*a).process_map.dom().contains(p)
            &&& kernel_k_to_kernel_u(*a).process_map[p].lock_state == kernel_k_to_kernel_u(*b).process_map[p].lock_state
            &&& kernel_k_to_kernel_u(*a).process_map[p].killed == kernel_k_to_kernel_u(*b).process_map[p].killed
            &&& kernel_k_to_kernel_u(*a).process_map[p].owning_container == kernel_k_to_kernel_u(*b).process_map[p].owning_container
        },
        forall|c: RwLockContainerPtr| #![trigger containers.contains(c)] containers.contains(c) ==> {
            &&& kernel_k_to_kernel_u(*a).container_map.dom().contains(c)
            &&& kernel_k_to_kernel_u(*a).container_map[c].lock_state == kernel_k_to_kernel_u(*b).container_map[c].lock_state
            &&& kernel_k_to_kernel_u(*a).container_map[c].uppertree_seq == kernel_k_to_kernel_u(*b).container_map[c].uppertree_seq
        },
{ broadcast use kernel_process_lock_state_projection_at, kernel_container_lock_state_projection_at; }
} // verus!
