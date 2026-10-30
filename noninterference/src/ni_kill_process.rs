use vstd::prelude::*;
use crate::*;
use veriflat_syscall_kill_process::syscall_kill_process::syscall_kill_process_spec::*;

verus! {
/// The container clause of the killed-thread reclaim alternative of `kill_process_middle_step`, as that step states it:
/// every thread the step changes or removes belongs to the target's container.
pub open spec fn kill_process_reclaim_in_target(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    forall|t: RwLockThreadPtr| #![trigger old_u.thread_map[t]]
        old_u.thread_map.dom().contains(t) && (!new_u.thread_map.dom().contains(t) || new_u.thread_map[t] != old_u.thread_map[t])
        ==> old_u.thread_map[t].owning_container == old_u.process_map[kill_target(old_u, cpu_id)].owning_container
}

/// Entering a process kill on a cpu of `a` locks the cpu and its running process and thread, and marks a child of that
/// process, which shares its container, so it leaves the view of `b` unchanged.
pub proof fn kill_process_enter_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, child_index: usize, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_enter_step_pre(old_u, cpu_id, child_index),
        kill_process_enter_step(old_u, new_u, cpu_id, child_index),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_process_enter_step_pre); reveal(kill_process_enter_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_process_children_wf);
    let process = old_u.process_map[old_u.cpu_array[cpu_id as int].current_process->Some_0];
    assert(process.children.contains(process.children[child_index as int]));
}

/// The step of `kill_process_enter_step_lr` preserves isolation.
pub proof fn kill_process_enter_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, child_index: usize, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_enter_step_pre(old_u, cpu_id, child_index),
        kill_process_enter_step(old_u, new_u, cpu_id, child_index),
    ensures isolated(new_u, a, b),
{
    assert({
        &&& new_u.process_map.dom() =~= old_u.process_map.dom() && new_u.thread_map.dom() =~= old_u.thread_map.dom()
        &&& new_u.container_map == old_u.container_map && new_u.endpoint_map == old_u.endpoint_map
        &&& forall|p: RwLockProcessPtr| #![trigger new_u.process_map[p]] new_u.process_map[p].owning_container == old_u.process_map[p].owning_container
            && new_u.process_map[p].pagetable == old_u.process_map[p].pagetable && new_u.process_map[p].iommu_table == old_u.process_map[p].iommu_table
        &&& forall|t: RwLockThreadPtr| #![trigger new_u.thread_map[t]] new_u.thread_map[t].owning_container == old_u.thread_map[t].owning_container
            && new_u.thread_map[t].state == old_u.thread_map[t].state
    }) by { reveal(kill_process_enter_step_pre); reveal(kill_process_enter_step); };
}

/// Descending from the target of a process kill on a cpu of `a`, which lies in `a`, marks a child of the target, which
/// shares its container, so it leaves the view of `b` unchanged.
pub proof fn kill_process_mark_child_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_mark_child_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_process_step_pre); reveal(kill_process_mark_child_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_process_children_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let target = old_u.process_map[kill_target(old_u, cpu_id)];
    assert(in_domain(old_u, a, target.owning_container)) by {
        reveal(kernel_u_container_tree_wf); reveal(kernel_u_process_ownership_wf);
        if target.owning_container != owner {
            if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
            assert(old_u.container_map[target.owning_container].uppertree_seq.contains(a));
        }
    };
    assert(target.children.contains(target.children[0]));
}

/// The step of `kill_process_mark_child_step_lr` preserves isolation.
pub proof fn kill_process_mark_child_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_mark_child_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kill_process_mark_child_step); assert(old_u.thread_map.dom().contains(kill_killer(old_u, cpu_id))) by { reveal(kill_process_step_pre); }; }

/// Turning the first thread of the target of a process kill on a cpu of `a`, which lies in `a`, into a dangling thread
/// changes only the target and that thread, which shares its container, so it leaves the view of `b` unchanged.
pub proof fn kill_process_dangling_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_dangling_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_process_step_pre); reveal(kill_process_dangling_step); reveal(kernel_u_process_threads_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let target = old_u.process_map[kill_target(old_u, cpu_id)];
    assert(in_domain(old_u, a, target.owning_container)) by {
        reveal(kernel_u_container_tree_wf); reveal(kernel_u_process_ownership_wf);
        if target.owning_container != owner {
            if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
            assert(old_u.container_map[target.owning_container].uppertree_seq.contains(a));
        }
    };
    assert(target.owned_threads.contains(target.owned_threads[0]));
}

/// The step of `kill_process_dangling_step_lr` preserves isolation.
pub proof fn kill_process_dangling_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_dangling_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kill_process_step_pre); reveal(kill_process_dangling_step); }

/// Marking the first thread of the target of a process kill on a cpu of `a`, which lies in `a`, changes only that
/// thread, which shares the target's container, and the killer, so it leaves the view of `b` unchanged.
pub proof fn kill_process_mark_thread_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_mark_thread_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_process_step_pre); reveal(kill_process_mark_thread_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_process_threads_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let target = old_u.process_map[kill_target(old_u, cpu_id)];
    assert(in_domain(old_u, a, target.owning_container)) by {
        reveal(kernel_u_container_tree_wf); reveal(kernel_u_process_ownership_wf);
        if target.owning_container != owner {
            if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
            assert(old_u.container_map[target.owning_container].uppertree_seq.contains(a));
        }
    };
    assert(target.owned_threads.contains(target.owned_threads[0]));
}

/// The step of `kill_process_mark_thread_step_lr` preserves isolation.
pub proof fn kill_process_mark_thread_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_mark_thread_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kill_process_mark_thread_step); assert(old_u.thread_map.dom().contains(kill_killer(old_u, cpu_id))) by { reveal(kill_process_step_pre); }; }

/// Dequeuing the marked victim of a process kill on a cpu of `a` from a scheduler shard changes only the victim, a thread
/// of the target in `a`, and its container, so it leaves the view of `b` unchanged.
pub proof fn kill_process_dequeue_scheduled_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_dequeue_scheduled_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_process_step_pre); reveal(kill_process_dequeue_scheduled_step); reveal(kernel_u_process_threads_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let target = old_u.process_map[kill_target(old_u, cpu_id)];
    assert(in_domain(old_u, a, target.owning_container)) by {
        reveal(kernel_u_container_tree_wf); reveal(kernel_u_process_ownership_wf);
        if target.owning_container != owner {
            if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
            assert(old_u.container_map[target.owning_container].uppertree_seq.contains(a));
        }
    };
}

/// The step of `kill_process_dequeue_scheduled_step_lr` preserves isolation.
pub proof fn kill_process_dequeue_scheduled_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_dequeue_scheduled_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kill_process_dequeue_scheduled_step); }

/// Dequeuing the marked victim of a process kill on a cpu of `a` from the queue of its endpoint changes only the victim, a
/// thread of the target in `a`, and that endpoint. The endpoint queues a thread of `a`, so no thread of `b` holds it, and
/// it belongs to a container of one of its holders or an ancestor of it, so `b` does not own it either.
pub proof fn kill_process_dequeue_endpoint_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_dequeue_endpoint_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_process_step_pre); reveal(kill_process_dequeue_endpoint_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_process_threads_wf);
    reveal(kernel_u_endpoint_ownership_wf); reveal(kernel_u_thread_ownership_wf); reveal(kernel_u_endpoint_wait_wf); reveal(kernel_u_endpoint_holder_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let target = old_u.process_map[kill_target(old_u, cpu_id)];
    let victim_ptr = kill_stage(old_u, cpu_id)->Thread_thread;
    let endpoint_ptr = old_u.thread_map[victim_ptr].blocking_endpoint_ptr->Some_0;
    let endpoint = old_u.endpoint_map[endpoint_ptr];
    assert(in_domain(old_u, a, target.owning_container)) by {
        reveal(kernel_u_container_tree_wf); reveal(kernel_u_process_ownership_wf);
        if target.owning_container != owner {
            if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
            assert(old_u.container_map[target.owning_container].uppertree_seq.contains(a));
        }
    };
    assert(old_u.thread_map[victim_ptr].owning_container == target.owning_container);
    assert(endpoint.queue.contains(victim_ptr));
    endpoint.queue.index_of_first_ensures(victim_ptr);
    let j = endpoint.queue.index_of_first(victim_ptr)->Some_0;
    assert forall|h: (RwLockThreadPtr, EndpointIdx)| #![trigger endpoint.owning_threads.contains(h)] endpoint.owning_threads.contains(h)
        implies !in_domain(old_u, b, endpoint.owning_container) by {
        let holder = old_u.thread_map[h.0].owning_container;
        assert(h == (h.0, h.1));
        assert(endpoint.queue[j] == victim_ptr);
        assert(old_u.thread_map[h.0].endpoint_descriptors[h.1 as int] == Some(endpoint_ptr));
        assert(!in_domain(old_u, b, holder));
        if in_domain(old_u, b, endpoint.owning_container) && endpoint.owning_container != holder && endpoint.owning_container != b {
            reveal(kernel_u_container_tree_wf);
            assert(old_u.container_map[endpoint.owning_container].uppertree_seq.contains(b));
            assert(old_u.container_map[holder].uppertree_seq.contains(endpoint.owning_container));
            assert(old_u.container_map[holder].uppertree_seq.contains(b));
        }
    };
    if in_domain(old_u, b, endpoint.owning_container) { assert(endpoint.owning_threads =~= Set::<(RwLockThreadPtr, EndpointIdx)>::empty()); }
    assert forall|t: RwLockThreadPtr, i: int| #![trigger old_u.thread_map[t].endpoint_descriptors[i]]
        old_u.thread_map.dom().contains(t) && in_domain(old_u, b, old_u.thread_map[t].owning_container) && 0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS
        implies old_u.thread_map[t].endpoint_descriptors[i] != Some(endpoint_ptr) by {
        if old_u.thread_map[t].endpoint_descriptors[i] == Some(endpoint_ptr) {
            assert(endpoint.owning_threads.contains((t, i as EndpointIdx)));
            assert(endpoint.queue[j] == victim_ptr);
        }
    };
}

/// The step of `kill_process_dequeue_endpoint_step_lr` preserves isolation: the endpoint's queue only shrinks.
pub proof fn kill_process_dequeue_endpoint_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_dequeue_endpoint_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(kill_process_dequeue_endpoint_step); reveal(kernel_u_endpoint_ownership_wf);
    let victim_ptr = kill_stage(old_u, cpu_id)->Thread_thread;
    let endpoint_ptr = old_u.thread_map[victim_ptr].blocking_endpoint_ptr->Some_0;
    let queue = old_u.endpoint_map[endpoint_ptr].queue;
    queue.index_of_first_ensures(victim_ptr);
}

/// Forcing the cpu running the marked victim of a process kill on a cpu of `a` to idle changes only the victim, a thread
/// of the target in `a`, and that cpu, which shares the victim's container, so it leaves the view of `b` unchanged.
pub proof fn kill_process_cpu_to_idle_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_cpu_to_idle_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_process_step_pre); reveal(kill_process_cpu_to_idle_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_process_threads_wf); reveal(kernel_u_running_thread_cpu_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let target = old_u.process_map[kill_target(old_u, cpu_id)];
    assert(in_domain(old_u, a, target.owning_container)) by {
        reveal(kernel_u_container_tree_wf); reveal(kernel_u_process_ownership_wf);
        if target.owning_container != owner {
            if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
            assert(old_u.container_map[target.owning_container].uppertree_seq.contains(a));
        }
    };
}

/// The step of `kill_process_cpu_to_idle_step_lr` preserves isolation.
pub proof fn kill_process_cpu_to_idle_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_cpu_to_idle_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kill_process_cpu_to_idle_step); }

/// Unlinking the killed victim of a process kill on a cpu of `a` from the target, which lies in `a`, changes only the
/// target, the victim, which shares its container, and the killer, so it leaves the view of `b` unchanged.
pub proof fn kill_process_unlink_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_unlink_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_process_step_pre); reveal(kill_process_unlink_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_process_threads_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let target = old_u.process_map[kill_target(old_u, cpu_id)];
    assert(in_domain(old_u, a, target.owning_container)) by {
        reveal(kernel_u_container_tree_wf); reveal(kernel_u_process_ownership_wf);
        if target.owning_container != owner {
            if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
            assert(old_u.container_map[target.owning_container].uppertree_seq.contains(a));
        }
    };
}

/// The step of `kill_process_unlink_step_lr` preserves isolation.
pub proof fn kill_process_unlink_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_unlink_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kill_process_step_pre); reveal(kill_process_unlink_step); }

/// A killed thread of the target's container in `a` releasing one descriptor of a process kill on a cpu of `a` changes
/// only that thread and the endpoint it held, which `b` neither owns nor holds, so it leaves the view of `b` unchanged.
pub proof fn kill_process_descriptor_dropped_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_reclaim_in_target(old_u, new_u, cpu_id),
        kernel_u_killed_descriptor_dropped(old_u, new_u),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_process_step_pre); reveal(kernel_u_killed_descriptor_dropped); reveal(kernel_u_endpoint_ownership_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let container = old_u.process_map[kill_target(old_u, cpu_id)].owning_container;
    assert(in_domain(old_u, a, container)) by {
        reveal(kernel_u_container_tree_wf); reveal(kernel_u_process_ownership_wf);
        if container != owner {
            if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
            assert(old_u.container_map[container].uppertree_seq.contains(a));
        }
    };
    let changed = old_u.thread_map.dom().filter(|t: RwLockThreadPtr| new_u.thread_map[t] != old_u.thread_map[t]);
    assert forall|t: RwLockThreadPtr| #![trigger changed.contains(t)] changed.contains(t) implies domain_view(new_u, b) =~~= domain_view(old_u, b) by {
        let thread = old_u.thread_map[t];
        let dropped = Set::<int>::range(0, MAX_NUM_ENDPOINT_DESCRIPTORS as int).filter(|j: int| new_u.thread_map[t].endpoint_descriptors[j] != thread.endpoint_descriptors[j]);
        assert forall|index: int| #![trigger dropped.contains(index)] dropped.contains(index) implies domain_view(new_u, b) =~~= domain_view(old_u, b) by {
            let endpoint_ptr = thread.endpoint_descriptors[index]->Some_0;
            assert forall|t2: RwLockThreadPtr, i: int| #![trigger old_u.thread_map[t2].endpoint_descriptors[i]]
                old_u.thread_map.dom().contains(t2) && in_domain(old_u, b, old_u.thread_map[t2].owning_container) && 0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS
                implies old_u.thread_map[t2].endpoint_descriptors[i] != Some(endpoint_ptr) by {
                if old_u.thread_map[t2].endpoint_descriptors[i] == Some(endpoint_ptr) { assert(old_u.endpoint_map[endpoint_ptr].owning_threads.contains((t2, i as EndpointIdx))); }
            };
        };
        if !(domain_view(new_u, b) =~~= domain_view(old_u, b)) { assert(dropped =~= Set::<int>::empty()); }
    };
    if !(domain_view(new_u, b) =~~= domain_view(old_u, b)) { assert(changed =~= Set::<RwLockThreadPtr>::empty()); }
}

/// The step of `kill_process_descriptor_dropped_step_lr` preserves isolation: the endpoint only loses a holder.
pub proof fn kill_process_descriptor_dropped_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_reclaim_in_target(old_u, new_u, cpu_id),
        kernel_u_killed_descriptor_dropped(old_u, new_u),
    ensures isolated(new_u, a, b),
{
    reveal(kernel_u_killed_descriptor_dropped); reveal(kernel_u_endpoint_ownership_wf);
    let changed = old_u.thread_map.dom().filter(|t: RwLockThreadPtr| new_u.thread_map[t] != old_u.thread_map[t]);
    assert forall|t: RwLockThreadPtr| #![trigger changed.contains(t)] changed.contains(t) implies isolated(new_u, a, b) by {
        let thread = old_u.thread_map[t];
        let dropped = Set::<int>::range(0, MAX_NUM_ENDPOINT_DESCRIPTORS as int).filter(|j: int| new_u.thread_map[t].endpoint_descriptors[j] != thread.endpoint_descriptors[j]);
        if !isolated(new_u, a, b) { assert(dropped =~= Set::<int>::empty()); }
    };
    if !isolated(new_u, a, b) { assert(changed =~= Set::<RwLockThreadPtr>::empty()); }
}

/// Waking the caller of a killed thread of the target's container in `a`, in a process kill on a cpu of `a`, changes only
/// those two threads and the scheduler of the caller's container, the target's container, so it leaves the view of `b`
/// unchanged.
pub proof fn kill_process_caller_woken_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_reclaim_in_target(old_u, new_u, cpu_id),
        kernel_u_killed_caller_woken(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_process_step_pre); reveal(kernel_u_killed_caller_woken);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let container = old_u.process_map[kill_target(old_u, cpu_id)].owning_container;
    assert(in_domain(old_u, a, container)) by {
        reveal(kernel_u_container_tree_wf); reveal(kernel_u_process_ownership_wf);
        if container != owner {
            if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
            assert(old_u.container_map[container].uppertree_seq.contains(a));
        }
    };
    let woken = old_u.thread_map.dom().filter(|t: RwLockThreadPtr| old_u.thread_map[t].state is WAITING_REPLY && new_u.thread_map[t].state is SCHEDULED);
    assert forall|caller_ptr: RwLockThreadPtr| #![trigger woken.contains(caller_ptr)] woken.contains(caller_ptr) implies domain_view(new_u, b) =~~= domain_view(old_u, b) by {};
    if !(domain_view(new_u, b) =~~= domain_view(old_u, b)) { assert(woken =~= Set::<RwLockThreadPtr>::empty()); }
}

/// The step of `kill_process_caller_woken_step_lr` preserves isolation.
pub proof fn kill_process_caller_woken_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_reclaim_in_target(old_u, new_u, cpu_id),
        kernel_u_killed_caller_woken(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(kernel_u_killed_caller_woken);
    let woken = old_u.thread_map.dom().filter(|t: RwLockThreadPtr| old_u.thread_map[t].state is WAITING_REPLY && new_u.thread_map[t].state is SCHEDULED);
    if !isolated(new_u, a, b) { assert(woken =~= Set::<RwLockThreadPtr>::empty()); }
}

/// Taking over the dangling caller of a killed thread of the target's container in `a`, in a process kill on a cpu of
/// `a`, changes only those two threads, so it leaves the view of `b` unchanged.
pub proof fn kill_process_caller_taken_over_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_reclaim_in_target(old_u, new_u, cpu_id),
        kernel_u_killed_caller_taken_over(old_u, new_u),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_process_step_pre); reveal(kernel_u_killed_caller_taken_over);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let container = old_u.process_map[kill_target(old_u, cpu_id)].owning_container;
    assert(in_domain(old_u, a, container)) by {
        reveal(kernel_u_container_tree_wf); reveal(kernel_u_process_ownership_wf);
        if container != owner {
            if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
            assert(old_u.container_map[container].uppertree_seq.contains(a));
        }
    };
    let taken = old_u.thread_map.dom().filter(|t: RwLockThreadPtr| old_u.thread_map[t].state is DANGLING && new_u.thread_map[t].state is KILLED);
    assert forall|caller_ptr: RwLockThreadPtr| #![trigger taken.contains(caller_ptr)] taken.contains(caller_ptr) implies domain_view(new_u, b) =~~= domain_view(old_u, b) by {};
    if !(domain_view(new_u, b) =~~= domain_view(old_u, b)) { assert(taken =~= Set::<RwLockThreadPtr>::empty()); }
}

/// The step of `kill_process_caller_taken_over_step_lr` preserves isolation.
pub proof fn kill_process_caller_taken_over_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_reclaim_in_target(old_u, new_u, cpu_id),
        kernel_u_killed_caller_taken_over(old_u, new_u),
    ensures isolated(new_u, a, b),
{
    reveal(kernel_u_killed_caller_taken_over);
    let taken = old_u.thread_map.dom().filter(|t: RwLockThreadPtr| old_u.thread_map[t].state is DANGLING && new_u.thread_map[t].state is KILLED);
    if !isolated(new_u, a, b) { assert(taken =~= Set::<RwLockThreadPtr>::empty()); }
}

/// Reclaiming a killed dangling thread of the target's container in `a`, in a process kill on a cpu of `a`, removes that
/// thread from its container and refunds its page to the container owning the page, which is that container, so it
/// leaves the view of `b` unchanged.
pub proof fn kill_process_dangling_reclaimed_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_reclaim_in_target(old_u, new_u, cpu_id),
        kernel_u_dangling_thread_reclaimed(old_u, new_u),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_process_step_pre); reveal(kernel_u_dangling_thread_reclaimed); reveal(kernel_u_object_page_owner_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let container = old_u.process_map[kill_target(old_u, cpu_id)].owning_container;
    assert(in_domain(old_u, a, container)) by {
        reveal(kernel_u_container_tree_wf); reveal(kernel_u_process_ownership_wf);
        if container != owner {
            if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
            assert(old_u.container_map[container].uppertree_seq.contains(a));
        }
    };
    let removed = old_u.thread_map.dom().difference(new_u.thread_map.dom());
    assert forall|dangling_ptr: RwLockThreadPtr| #![trigger removed.contains(dangling_ptr)] removed.contains(dangling_ptr) implies domain_view(new_u, b) =~~= domain_view(old_u, b) by {};
    if !(domain_view(new_u, b) =~~= domain_view(old_u, b)) { assert(removed =~= Set::<RwLockThreadPtr>::empty()); }
}

/// The step of `kill_process_dangling_reclaimed_step_lr` preserves isolation. The reclaimed thread holds no endpoint in
/// the well-formed state after the step, and no rendezvous peer is the reclaimed thread.
pub proof fn kill_process_dangling_reclaimed_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        kernel_u_ownership_wf(new_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_reclaim_in_target(old_u, new_u, cpu_id),
        kernel_u_dangling_thread_reclaimed(old_u, new_u),
    ensures isolated(new_u, a, b),
{
    reveal(kernel_u_dangling_thread_reclaimed); reveal(kernel_u_endpoint_ownership_wf);
    let removed = old_u.thread_map.dom().difference(new_u.thread_map.dom());
    if !isolated(new_u, a, b) { assert(removed =~= Set::<RwLockThreadPtr>::empty()); }
}

/// A killed thread of the target's container in `a` releasing the last reference of an endpoint, in a process kill on a
/// cpu of `a`, changes only that thread and removes the endpoint, which `b` neither owns nor holds, refunding its page to
/// the endpoint's owner, so it leaves the view of `b` unchanged.
pub proof fn kill_process_endpoint_released_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_reclaim_in_target(old_u, new_u, cpu_id),
        kernel_u_killed_endpoint_released(old_u, new_u),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_process_step_pre); reveal(kernel_u_killed_endpoint_released); reveal(kernel_u_endpoint_released);
    reveal(kernel_u_endpoint_ownership_wf); reveal(kernel_u_object_page_owner_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let container = old_u.process_map[kill_target(old_u, cpu_id)].owning_container;
    assert(in_domain(old_u, a, container)) by {
        reveal(kernel_u_container_tree_wf); reveal(kernel_u_process_ownership_wf);
        if container != owner {
            if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
            assert(old_u.container_map[container].uppertree_seq.contains(a));
        }
    };
    let changed = old_u.thread_map.dom().filter(|t: RwLockThreadPtr| new_u.thread_map[t] != old_u.thread_map[t]);
    assert forall|t: RwLockThreadPtr| #![trigger changed.contains(t)] changed.contains(t) implies domain_view(new_u, b) =~~= domain_view(old_u, b) by {
        let thread = old_u.thread_map[t];
        let dropped = Set::<int>::range(0, MAX_NUM_ENDPOINT_DESCRIPTORS as int).filter(|j: int| new_u.thread_map[t].endpoint_descriptors[j] != thread.endpoint_descriptors[j]);
        assert forall|index: int| #![trigger dropped.contains(index)] dropped.contains(index) implies domain_view(new_u, b) =~~= domain_view(old_u, b) by {
            let endpoint_ptr = thread.endpoint_descriptors[index]->Some_0;
            assert forall|t2: RwLockThreadPtr, i: int| #![trigger old_u.thread_map[t2].endpoint_descriptors[i]]
                old_u.thread_map.dom().contains(t2) && in_domain(old_u, b, old_u.thread_map[t2].owning_container) && 0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS
                implies old_u.thread_map[t2].endpoint_descriptors[i] != Some(endpoint_ptr) by {
                if old_u.thread_map[t2].endpoint_descriptors[i] == Some(endpoint_ptr) { assert(old_u.endpoint_map[endpoint_ptr].owning_threads.contains((t2, i as EndpointIdx))); }
            };
        };
        if !(domain_view(new_u, b) =~~= domain_view(old_u, b)) { assert(dropped =~= Set::<int>::empty()); }
    };
    if !(domain_view(new_u, b) =~~= domain_view(old_u, b)) { assert(changed =~= Set::<RwLockThreadPtr>::empty()); }
}

/// The step of `kill_process_endpoint_released_step_lr` preserves isolation: no thread waits on the released endpoint,
/// whose queue is empty, so no rendezvous peer's channel is gone.
pub proof fn kill_process_endpoint_released_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_reclaim_in_target(old_u, new_u, cpu_id),
        kernel_u_killed_endpoint_released(old_u, new_u),
    ensures isolated(new_u, a, b),
{
    reveal(kernel_u_killed_endpoint_released); reveal(kernel_u_endpoint_released); reveal(kernel_u_endpoint_ownership_wf);
    let changed = old_u.thread_map.dom().filter(|t: RwLockThreadPtr| new_u.thread_map[t] != old_u.thread_map[t]);
    assert forall|t: RwLockThreadPtr| #![trigger changed.contains(t)] changed.contains(t) implies isolated(new_u, a, b) by {
        let thread = old_u.thread_map[t];
        let dropped = Set::<int>::range(0, MAX_NUM_ENDPOINT_DESCRIPTORS as int).filter(|j: int| new_u.thread_map[t].endpoint_descriptors[j] != thread.endpoint_descriptors[j]);
        if !isolated(new_u, a, b) { assert(dropped =~= Set::<int>::empty()); }
    };
    if !isolated(new_u, a, b) { assert(changed =~= Set::<RwLockThreadPtr>::empty()); }
}

/// Handing the PCI functions of the empty target of a process kill on a cpu of `a`, which lies in `a`, to the killer's
/// process detaches only functions the target owns, none of which a process of `b` owns, and clears only the DID of the
/// target's IOMMU table, so it leaves the view of `b` unchanged.
pub proof fn kill_process_reassign_functions_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_reassign_functions_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_process_step_pre); reveal(kill_process_reassign_functions_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_pci_ownership_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let target_ptr = kill_target(old_u, cpu_id);
    let target = old_u.process_map[target_ptr];
    assert(in_domain(old_u, a, target.owning_container)) by {
        reveal(kernel_u_container_tree_wf); reveal(kernel_u_process_ownership_wf);
        if target.owning_container != owner {
            if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
            assert(old_u.container_map[target.owning_container].uppertree_seq.contains(a));
        }
    };
    assert forall|q: RwLockProcessPtr, bdf: PciBdf| #![trigger old_u.process_map[q].owned_pci_functions.contains(bdf)]
        old_u.process_map.dom().contains(q) && in_domain(old_u, b, old_u.process_map[q].owning_container) && old_u.process_map[q].owned_pci_functions.contains(bdf)
        implies new_u.iommu_root_table.attached[bdf.0 as int][bdf.1 as int][bdf.2 as int] == old_u.iommu_root_table.attached[bdf.0 as int][bdf.1 as int][bdf.2 as int] by {};
}

/// The step of `kill_process_reassign_functions_step_lr` preserves isolation.
pub proof fn kill_process_reassign_functions_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_reassign_functions_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    assert({
        &&& new_u.process_map.dom() =~= old_u.process_map.dom()
        &&& new_u.container_map == old_u.container_map && new_u.thread_map == old_u.thread_map && new_u.endpoint_map == old_u.endpoint_map
        &&& forall|p: RwLockProcessPtr| #![trigger new_u.process_map[p]] old_u.process_map.dom().contains(p) ==> new_u.process_map[p].owning_container == old_u.process_map[p].owning_container
            && new_u.process_map[p].pagetable == old_u.process_map[p].pagetable && (new_u.process_map[p].iommu_table is Some) == (old_u.process_map[p].iommu_table is Some)
            && new_u.process_map[p].iommu_table->Some_0.mapping_4k == old_u.process_map[p].iommu_table->Some_0.mapping_4k
            && new_u.process_map[p].iommu_table->Some_0.mapping_2m == old_u.process_map[p].iommu_table->Some_0.mapping_2m
            && new_u.process_map[p].iommu_table->Some_0.mapping_1g == old_u.process_map[p].iommu_table->Some_0.mapping_1g
    }) by { reveal(kill_process_step_pre); reveal(kill_process_reassign_functions_step); };
}

/// Locking the tables of the target of a process kill on a cpu of `a`, which lies in `a`, changes only the target and
/// the killer, so it leaves the view of `b` unchanged.
pub proof fn kill_process_lock_table_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_lock_table_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_process_step_pre); reveal(kill_process_lock_table_step); reveal(kernel_u_cpu_ownership_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let target = old_u.process_map[kill_target(old_u, cpu_id)];
    assert(in_domain(old_u, a, target.owning_container)) by {
        reveal(kernel_u_container_tree_wf); reveal(kernel_u_process_ownership_wf);
        if target.owning_container != owner {
            if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
            assert(old_u.container_map[target.owning_container].uppertree_seq.contains(a));
        }
    };
}

/// The step of `kill_process_lock_table_step_lr` preserves isolation.
pub proof fn kill_process_lock_table_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_lock_table_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kill_process_step_pre); reveal(kill_process_lock_table_step); }

/// A process kill leaf step on a cpu of `a` removes one mapping of the target, which lies in `a`, so it leaves the view of
/// `b` unchanged.
pub proof fn kill_process_leaf_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_leaf_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_process_step_pre); reveal(kill_process_leaf_step);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let target = old_u.process_map[kill_target(old_u, cpu_id)];
    assert(in_domain(old_u, a, target.owning_container)) by {
        reveal(kernel_u_container_tree_wf); reveal(kernel_u_process_ownership_wf);
        if target.owning_container != owner {
            if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
            assert(old_u.container_map[target.owning_container].uppertree_seq.contains(a));
        }
    };
}

/// The step of `kill_process_leaf_step_lr` preserves isolation: the target's mappings only shrink.
pub proof fn kill_process_leaf_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_leaf_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kill_process_step_pre); reveal(kill_process_leaf_step); }

/// A process kill TLB flush changes only cpu TLBs, which no domain view contains.
pub proof fn kill_process_tlb_cleared_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_flush_step_pre(old_u, cpu_id),
        kernel_u_cpu_tlb_cleared(old_u, new_u, old_u.process_map[kill_target(old_u, cpu_id)].pcid),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kernel_u_cpu_tlb_cleared); }

/// The step of `kill_process_tlb_cleared_step_lr` preserves isolation.
pub proof fn kill_process_tlb_cleared_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_flush_step_pre(old_u, cpu_id),
        kernel_u_cpu_tlb_cleared(old_u, new_u, old_u.process_map[kill_target(old_u, cpu_id)].pcid),
    ensures isolated(new_u, a, b),
{ reveal(kernel_u_cpu_tlb_cleared); }

/// Recording the flush of a process kill on a cpu of `a` changes only the killer, a thread of `a`.
pub proof fn kill_process_flushed_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_flush_step_pre(old_u, cpu_id),
        kill_process_flushed_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kill_process_step_pre); reveal(kill_process_flushed_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `kill_process_flushed_step_lr` preserves isolation.
pub proof fn kill_process_flushed_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_flush_step_pre(old_u, cpu_id),
        kill_process_flushed_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kill_process_flushed_step); assert(old_u.thread_map.dom().contains(kill_killer(old_u, cpu_id))) by { reveal(kill_process_step_pre); }; }

/// A process kill IOMMU leaf step on a cpu of `a` removes one IOMMU mapping of the target, which lies in `a`, so it
/// leaves the view of `b` unchanged.
pub proof fn kill_process_iommu_leaf_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_iommu_leaf_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_process_step_pre); reveal(kill_process_iommu_leaf_step);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let target = old_u.process_map[kill_target(old_u, cpu_id)];
    assert(in_domain(old_u, a, target.owning_container)) by {
        reveal(kernel_u_container_tree_wf); reveal(kernel_u_process_ownership_wf);
        if target.owning_container != owner {
            if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
            assert(old_u.container_map[target.owning_container].uppertree_seq.contains(a));
        }
    };
}

/// The step of `kill_process_iommu_leaf_step_lr` preserves isolation: the target's IOMMU mappings only shrink, and they are
/// empty when the target lies in either domain.
pub proof fn kill_process_iommu_leaf_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_iommu_leaf_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(kill_process_step_pre); reveal(kill_process_iommu_leaf_step);
}

/// A process kill window step on a cpu of `a` changes only window locks of the target's page table, and the target lies
/// in `a`, so it leaves the view of `b` unchanged.
pub proof fn kill_process_pagetable_windows_changed_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_pagetable_windows_changed_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_process_step_pre); reveal(kill_process_pagetable_windows_changed_step);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let target = old_u.process_map[kill_target(old_u, cpu_id)];
    assert(in_domain(old_u, a, target.owning_container)) by {
        reveal(kernel_u_container_tree_wf); reveal(kernel_u_process_ownership_wf);
        if target.owning_container != owner {
            if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
            assert(old_u.container_map[target.owning_container].uppertree_seq.contains(a));
        }
    };
}

/// The step of `kill_process_pagetable_windows_changed_step_lr` preserves isolation: it changes no mapping.
pub proof fn kill_process_pagetable_windows_changed_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_pagetable_windows_changed_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kill_process_step_pre); reveal(kill_process_pagetable_windows_changed_step); }

/// Refunding 4K quota of a process kill on a cpu of `a` may unlock a window of the target, which lies in `a`, and raises the
/// quota of the target's container or of an ancestor of it, neither of which lies in `b`.
pub proof fn kill_process_refund_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_refund_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_process_step_pre); reveal(kill_process_refund_step); reveal(kernel_u_container_quota_4k_increased); reveal(kernel_u_container_tree_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let container = old_u.process_map[kill_target(old_u, cpu_id)].owning_container;
    let mid = KernelU { process_map: new_u.process_map, ..old_u };
    assert(in_domain(old_u, a, container)) by {
        reveal(kernel_u_process_ownership_wf);
        if container != owner {
            if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
            assert(old_u.container_map[container].uppertree_seq.contains(a));
        }
    };
    assert(domain_view(mid, b) =~~= domain_view(old_u, b));
}

/// The step of `kill_process_refund_step_lr` preserves isolation: it changes no mapping.
pub proof fn kill_process_refund_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_refund_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(kill_process_step_pre); reveal(kill_process_refund_step); reveal(kernel_u_container_quota_4k_increased);
    assert(isolated(KernelU { process_map: new_u.process_map, ..old_u }, a, b));
}

/// Returning one size of the quota of the target of a process kill on a cpu of `a`, which lies in `a`, to its container
/// changes only the target, its container, and the killer, so it leaves the view of `b` unchanged.
pub proof fn kill_process_quota_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_quota_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_process_step_pre); reveal(kill_process_quota_step); reveal(kernel_u_cpu_ownership_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let container = old_u.process_map[kill_target(old_u, cpu_id)].owning_container;
    assert(in_domain(old_u, a, container)) by {
        reveal(kernel_u_container_tree_wf); reveal(kernel_u_process_ownership_wf);
        if container != owner {
            if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
            assert(old_u.container_map[container].uppertree_seq.contains(a));
        }
    };
}

/// The step of `kill_process_quota_step_lr` preserves isolation.
pub proof fn kill_process_quota_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_quota_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kill_process_step_pre); reveal(kill_process_quota_step); }

/// Unlocking the reclaimed tables of the target of a process kill on a cpu of `a`, which lies in `a`, changes only the
/// target and the killer, so it leaves the view of `b` unchanged.
pub proof fn kill_process_unlock_table_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_unlock_table_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_process_step_pre); reveal(kill_process_unlock_table_step); reveal(kernel_u_cpu_ownership_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let target = old_u.process_map[kill_target(old_u, cpu_id)];
    assert(in_domain(old_u, a, target.owning_container)) by {
        reveal(kernel_u_container_tree_wf); reveal(kernel_u_process_ownership_wf);
        if target.owning_container != owner {
            if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
            assert(old_u.container_map[target.owning_container].uppertree_seq.contains(a));
        }
    };
}

/// The step of `kill_process_unlock_table_step_lr` preserves isolation.
pub proof fn kill_process_unlock_table_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_unlock_table_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kill_process_step_pre); reveal(kill_process_unlock_table_step); }

/// Making the target of a process kill on a cpu of `a`, which lies in `a`, a zombie changes only the target, its
/// container, and the killer, so it leaves the view of `b` unchanged.
pub proof fn kill_process_zombify_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_zombify_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_process_step_pre); reveal(kill_process_zombify_step); reveal(kernel_u_cpu_ownership_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let container = old_u.process_map[kill_target(old_u, cpu_id)].owning_container;
    assert(in_domain(old_u, a, container)) by {
        reveal(kernel_u_container_tree_wf); reveal(kernel_u_process_ownership_wf);
        if container != owner {
            if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
            assert(old_u.container_map[container].uppertree_seq.contains(a));
        }
    };
}

/// The step of `kill_process_zombify_step_lr` preserves isolation: the target's tables are hidden.
pub proof fn kill_process_zombify_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_zombify_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kill_process_zombify_step); assert(old_u.thread_map.dom().contains(kill_killer(old_u, cpu_id))) by { reveal(kill_process_step_pre); }; }

/// Moving an already zombie target of a process kill on a cpu of `a` to retiring changes only the killer, a thread of
/// `a`.
pub proof fn kill_process_zombie_retire_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_zombie_retire_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kill_process_step_pre); reveal(kill_process_zombie_retire_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `kill_process_zombie_retire_step_lr` preserves isolation.
pub proof fn kill_process_zombie_retire_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_zombie_retire_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kill_process_zombie_retire_step); assert(old_u.thread_map.dom().contains(kill_killer(old_u, cpu_id))) by { reveal(kill_process_step_pre); }; }

/// Retiring the empty zombie target of a process kill on a cpu of `a`, which lies in `a`, removes it from its ancestors,
/// which share its container, and from its container, so it leaves the view of `b` unchanged.
pub proof fn kill_process_retire_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_retire_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_process_step_pre); reveal(kill_process_retire_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_process_ownership_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let container = old_u.process_map[kill_target(old_u, cpu_id)].owning_container;
    assert(in_domain(old_u, a, container)) by {
        reveal(kernel_u_container_tree_wf);
        if container != owner {
            if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
            assert(old_u.container_map[container].uppertree_seq.contains(a));
        }
    };
}

/// The step of `kill_process_retire_step_lr` preserves isolation.
pub proof fn kill_process_retire_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_step_pre(old_u, cpu_id),
        kill_process_retire_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    assert(old_u.thread_map.dom().contains(kill_killer(old_u, cpu_id))) by { reveal(kill_process_step_pre); };
    assert(memory_iso(new_u, a, b)) by { reveal(kill_process_retire_step); };
    reveal(kill_process_retire_step);
}

/// Finishing a process kill on a cpu of `a` unlocks the cpu and its running process and thread, all of `a`, so it leaves
/// the view of `b` unchanged.
pub proof fn kill_process_finish_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_finish_step_pre(old_u, cpu_id),
        kill_process_finish_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kill_process_finish_step_pre); reveal(kill_process_finish_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `kill_process_finish_step_lr` preserves isolation.
pub proof fn kill_process_finish_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_process_finish_step_pre(old_u, cpu_id),
        kill_process_finish_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kill_process_finish_step_pre); reveal(kill_process_finish_step); }

/// The process kill result of a cpu of `b` reads only the view of `b`: the cpu, its running process and thread, and the
/// child process at `child_index`, which shares the running process's container.
pub proof fn kill_process_syscall_result_oc(u1: KernelU, u2: KernelU, cpu_id: CpuId, child_index: usize, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u1),
        steps_in_domain(u1, cpu_id, b),
        domain_view(u1, b) =~~= domain_view(u2, b),
    ensures kill_process_syscall_result(u1, cpu_id, child_index) == kill_process_syscall_result(u2, cpu_id, child_index),
{
    let cpu = u1.cpu_array[cpu_id as int];
    let process = u1.process_map[cpu.current_process->Some_0];
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        &&& v1.cpus[cpu_id as int] == Some(cpu)
        &&& cpu.state is Running ==> v1.processes.dom().contains(cpu.current_process->Some_0) && v1.processes[cpu.current_process->Some_0] == v2.processes[cpu.current_process->Some_0]
        &&& cpu.state is Running ==> v1.threads.dom().contains(cpu.current_thread->Some_0) && v1.threads[cpu.current_thread->Some_0] == v2.threads[cpu.current_thread->Some_0]
    }) by { reveal(kernel_u_cpu_ownership_wf); };
    if cpu.state is Running && child_index < process.children.len() {
        let child = process.children[child_index as int];
        assert(domain_view(u1, b).processes.dom().contains(child)) by {
            reveal(kernel_u_process_children_wf);
            assert(process.children.contains(child));
        };
        assert(domain_view(u1, b).processes[child] == domain_view(u2, b).processes[child]);
    }
}
} // verus!
