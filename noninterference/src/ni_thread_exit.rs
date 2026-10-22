use vstd::prelude::*;
use crate::*;
use veriflat_map_4k::*;
use veriflat_syscall_thread_exit::syscall_thread_exit::syscall_thread_exit_spec::*;

verus! {
/// The container clause of the killed-thread reclaim alternative of `thread_exit_middle_step`, as that step states it:
/// every thread the step changes or removes belongs to the exiting thread's container.
pub open spec fn thread_exit_reclaim_in_container(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    forall|t: RwLockThreadPtr| #![trigger old_u.thread_map[t]]
        old_u.thread_map.dom().contains(t) && (!new_u.thread_map.dom().contains(t) || new_u.thread_map[t] != old_u.thread_map[t])
        ==> old_u.thread_map[t].owning_container == old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].owning_container
}

/// Entering an exit on a cpu of `a` locks the cpu, its container, the running process and thread, and wakes or takes
/// over the caller the thread serves, which shares its container, so it leaves the view of `b` unchanged.
pub proof fn thread_exit_enter_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_enter_step_pre(old_u, cpu_id),
        thread_exit_enter_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(thread_exit_enter_step_pre); reveal(thread_exit_enter_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_caller_wf); }

/// The step of `thread_exit_enter_step_lr` preserves isolation.
pub proof fn thread_exit_enter_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_enter_step_pre(old_u, cpu_id),
        thread_exit_enter_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(thread_exit_enter_step_pre); reveal(thread_exit_enter_step); }

/// A killed thread of the exiting thread's container, in `a`, dropping a descriptor changes only that thread and an endpoint
/// that `b` neither owns nor holds, so it leaves the view of `b` unchanged.
pub proof fn thread_exit_descriptor_dropped_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_drop_step_pre(old_u, cpu_id),
        thread_exit_reclaim_in_container(old_u, new_u, cpu_id),
        kernel_u_killed_descriptor_dropped(old_u, new_u),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(thread_exit_drop_step_pre); reveal(kernel_u_killed_descriptor_dropped); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_endpoint_ownership_wf);
    let changed = old_u.thread_map.dom().filter(|t: RwLockThreadPtr| new_u.thread_map[t] != old_u.thread_map[t]);
    assert forall|t: RwLockThreadPtr| #![trigger changed.contains(t)] changed.contains(t) implies domain_view(new_u, b) =~~= domain_view(old_u, b) by {
        let dropped = Set::<int>::range(0, MAX_NUM_ENDPOINT_DESCRIPTORS as int).filter(|j: int| new_u.thread_map[t].endpoint_descriptors[j] != old_u.thread_map[t].endpoint_descriptors[j]);
        if !(domain_view(new_u, b) =~~= domain_view(old_u, b)) { assert(dropped =~= Set::<int>::empty()); }
    };
    if !(domain_view(new_u, b) =~~= domain_view(old_u, b)) { assert(changed =~= Set::<RwLockThreadPtr>::empty()); }
}

/// The step of `thread_exit_descriptor_dropped_step_lr` preserves isolation.
pub proof fn thread_exit_descriptor_dropped_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_drop_step_pre(old_u, cpu_id),
        kernel_u_killed_descriptor_dropped(old_u, new_u),
    ensures isolated(new_u, a, b),
{
    reveal(kernel_u_killed_descriptor_dropped);
    let changed = old_u.thread_map.dom().filter(|t: RwLockThreadPtr| new_u.thread_map[t] != old_u.thread_map[t]);
    assert forall|t: RwLockThreadPtr| #![trigger changed.contains(t)] changed.contains(t) implies isolated(new_u, a, b) by {
        let dropped = Set::<int>::range(0, MAX_NUM_ENDPOINT_DESCRIPTORS as int).filter(|j: int| new_u.thread_map[t].endpoint_descriptors[j] != old_u.thread_map[t].endpoint_descriptors[j]);
        if !isolated(new_u, a, b) { assert(dropped =~= Set::<int>::empty()); }
    };
    if !isolated(new_u, a, b) { assert(changed =~= Set::<RwLockThreadPtr>::empty()); }
}

/// Waking the caller of a killed thread of the exiting thread's container changes only those two threads and their
/// container, all of `a`, so it leaves the view of `b` unchanged.
pub proof fn thread_exit_caller_woken_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_drop_step_pre(old_u, cpu_id),
        thread_exit_reclaim_in_container(old_u, new_u, cpu_id),
        kernel_u_killed_caller_woken(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(thread_exit_drop_step_pre); reveal(kernel_u_killed_caller_woken); reveal(kernel_u_cpu_ownership_wf);
    let woken = old_u.thread_map.dom().filter(|t: RwLockThreadPtr| old_u.thread_map[t].state is WAITING_REPLY && new_u.thread_map[t].state is SCHEDULED);
    if !(domain_view(new_u, b) =~~= domain_view(old_u, b)) { assert(woken =~= Set::<RwLockThreadPtr>::empty()); }
}

/// The step of `thread_exit_caller_woken_step_lr` preserves isolation.
pub proof fn thread_exit_caller_woken_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_drop_step_pre(old_u, cpu_id),
        kernel_u_killed_caller_woken(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(kernel_u_killed_caller_woken);
    let woken = old_u.thread_map.dom().filter(|t: RwLockThreadPtr| old_u.thread_map[t].state is WAITING_REPLY && new_u.thread_map[t].state is SCHEDULED);
    if !isolated(new_u, a, b) { assert(woken =~= Set::<RwLockThreadPtr>::empty()); }
}

/// Taking over the dangling caller of a killed thread of the exiting thread's container changes only those two threads,
/// both of `a`, so it leaves the view of `b` unchanged.
pub proof fn thread_exit_caller_taken_over_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_drop_step_pre(old_u, cpu_id),
        thread_exit_reclaim_in_container(old_u, new_u, cpu_id),
        kernel_u_killed_caller_taken_over(old_u, new_u),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(thread_exit_drop_step_pre); reveal(kernel_u_killed_caller_taken_over); reveal(kernel_u_cpu_ownership_wf);
    let taken = old_u.thread_map.dom().filter(|t: RwLockThreadPtr| old_u.thread_map[t].state is DANGLING && new_u.thread_map[t].state is KILLED);
    if !(domain_view(new_u, b) =~~= domain_view(old_u, b)) { assert(taken =~= Set::<RwLockThreadPtr>::empty()); }
}

/// The step of `thread_exit_caller_taken_over_step_lr` preserves isolation.
pub proof fn thread_exit_caller_taken_over_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_drop_step_pre(old_u, cpu_id),
        kernel_u_killed_caller_taken_over(old_u, new_u),
    ensures isolated(new_u, a, b),
{
    reveal(kernel_u_killed_caller_taken_over);
    let taken = old_u.thread_map.dom().filter(|t: RwLockThreadPtr| old_u.thread_map[t].state is DANGLING && new_u.thread_map[t].state is KILLED);
    if !isolated(new_u, a, b) { assert(taken =~= Set::<RwLockThreadPtr>::empty()); }
}

/// Reclaiming a killed dangling thread of the exiting thread's container removes a thread of `a` and refunds its page to
/// that container, so it leaves the view of `b` unchanged.
pub proof fn thread_exit_dangling_reclaimed_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_drop_step_pre(old_u, cpu_id),
        thread_exit_reclaim_in_container(old_u, new_u, cpu_id),
        kernel_u_dangling_thread_reclaimed(old_u, new_u),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(thread_exit_drop_step_pre); reveal(kernel_u_dangling_thread_reclaimed); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_object_page_owner_wf);
    let removed = old_u.thread_map.dom().difference(new_u.thread_map.dom());
    if !(domain_view(new_u, b) =~~= domain_view(old_u, b)) { assert(removed =~= Set::<RwLockThreadPtr>::empty()); }
}

/// The step of `thread_exit_dangling_reclaimed_step_lr` preserves isolation. The reclaimed thread holds no endpoint in the
/// well-formed state after the step, and no rendezvous peer is the reclaimed thread.
pub proof fn thread_exit_dangling_reclaimed_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        kernel_u_ownership_wf(new_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_drop_step_pre(old_u, cpu_id),
        kernel_u_dangling_thread_reclaimed(old_u, new_u),
    ensures isolated(new_u, a, b),
{
    reveal(kernel_u_dangling_thread_reclaimed); reveal(kernel_u_endpoint_ownership_wf);
    let removed = old_u.thread_map.dom().difference(new_u.thread_map.dom());
    if !isolated(new_u, a, b) { assert(removed =~= Set::<RwLockThreadPtr>::empty()); }
}

/// A killed thread of the exiting thread's container, in `a`, releasing the last reference of an endpoint changes only that
/// thread and removes the endpoint, which `b` neither owns nor holds, refunding its page to the endpoint's owner, so it
/// leaves the view of `b` unchanged.
pub proof fn thread_exit_endpoint_released_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_drop_step_pre(old_u, cpu_id),
        thread_exit_reclaim_in_container(old_u, new_u, cpu_id),
        kernel_u_killed_endpoint_released(old_u, new_u),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(thread_exit_drop_step_pre); reveal(kernel_u_killed_endpoint_released); reveal(kernel_u_endpoint_released); reveal(kernel_u_cpu_ownership_wf);
    reveal(kernel_u_endpoint_ownership_wf); reveal(kernel_u_object_page_owner_wf);
    let changed = old_u.thread_map.dom().filter(|t: RwLockThreadPtr| new_u.thread_map[t] != old_u.thread_map[t]);
    assert forall|t: RwLockThreadPtr| #![trigger changed.contains(t)] changed.contains(t) implies domain_view(new_u, b) =~~= domain_view(old_u, b) by {
        let dropped = Set::<int>::range(0, MAX_NUM_ENDPOINT_DESCRIPTORS as int).filter(|j: int| new_u.thread_map[t].endpoint_descriptors[j] != old_u.thread_map[t].endpoint_descriptors[j]);
        if !(domain_view(new_u, b) =~~= domain_view(old_u, b)) { assert(dropped =~= Set::<int>::empty()); }
    };
    if !(domain_view(new_u, b) =~~= domain_view(old_u, b)) { assert(changed =~= Set::<RwLockThreadPtr>::empty()); }
}

/// The step of `thread_exit_endpoint_released_step_lr` preserves isolation: no thread waits on the released endpoint,
/// whose queue is empty, so no rendezvous peer's channel is gone.
pub proof fn thread_exit_endpoint_released_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_drop_step_pre(old_u, cpu_id),
        kernel_u_killed_endpoint_released(old_u, new_u),
    ensures isolated(new_u, a, b),
{
    reveal(kernel_u_killed_endpoint_released); reveal(kernel_u_endpoint_released); reveal(kernel_u_thread_ownership_wf); reveal(kernel_u_endpoint_wait_wf);
    let changed = old_u.thread_map.dom().filter(|t: RwLockThreadPtr| new_u.thread_map[t] != old_u.thread_map[t]);
    assert forall|t: RwLockThreadPtr| #![trigger changed.contains(t)] changed.contains(t) implies isolated(new_u, a, b) by {
        let dropped = Set::<int>::range(0, MAX_NUM_ENDPOINT_DESCRIPTORS as int).filter(|j: int| new_u.thread_map[t].endpoint_descriptors[j] != old_u.thread_map[t].endpoint_descriptors[j]);
        if !isolated(new_u, a, b) { assert(dropped =~= Set::<int>::empty()); }
    };
    if !isolated(new_u, a, b) { assert(changed =~= Set::<RwLockThreadPtr>::empty()); }
}

/// Dropping a descriptor of the exiting thread on a cpu of `a` drops a reference to an endpoint that `b` neither owns
/// nor holds, so it leaves the view of `b` unchanged.
pub proof fn thread_exit_drop_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_drop_step_pre(old_u, cpu_id),
        thread_exit_drop_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(thread_exit_drop_step_pre); reveal(thread_exit_drop_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_endpoint_ownership_wf); }

/// The step of `thread_exit_drop_step_lr` preserves isolation.
pub proof fn thread_exit_drop_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_drop_step_pre(old_u, cpu_id),
        thread_exit_drop_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(thread_exit_drop_step); }

/// Releasing the last descriptor of an endpoint held by the exiting thread on a cpu of `a` removes an endpoint that `b`
/// neither owns nor holds, so it leaves the view of `b` unchanged.
pub proof fn thread_exit_release_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_drop_step_pre(old_u, cpu_id),
        thread_exit_release_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(thread_exit_drop_step_pre); reveal(thread_exit_release_step); reveal(kernel_u_endpoint_released); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_endpoint_ownership_wf);
    let thread = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let index = new_u.thread_map[thread].syscall_progress->Some_0->ThreadExit_next - 1;
    let endpoint_ptr = old_u.thread_map[thread].endpoint_descriptors[index]->Some_0;
    assert forall|c: RwLockContainerPtr| #![trigger new_u.container_map[c]] old_u.container_map.dom().contains(c) && in_domain(old_u, b, c) implies new_u.container_map[c] == old_u.container_map[c] by {
        if old_u.container_map[c].owned_pages.contains(endpoint_ptr) { reveal(kernel_u_object_page_owner_wf); }
    };
}

/// The step of `thread_exit_release_step_lr` preserves isolation.
pub proof fn thread_exit_release_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_drop_step_pre(old_u, cpu_id),
        thread_exit_release_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(thread_exit_release_step); reveal(kernel_u_endpoint_released); reveal(kernel_u_thread_ownership_wf); reveal(kernel_u_endpoint_wait_wf); }

/// Locking the tables of the exiting thread's process on a cpu of `a` detaches only PCI functions that process owns, so
/// it leaves the view of `b` unchanged.
pub proof fn thread_exit_lock_table_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_lock_table_step_pre(old_u, cpu_id),
        thread_exit_lock_table_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(thread_exit_lock_table_step_pre); reveal(thread_exit_lock_table_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_pci_ownership_wf); }

/// The step of `thread_exit_lock_table_step_lr` preserves isolation.
pub proof fn thread_exit_lock_table_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_lock_table_step_pre(old_u, cpu_id),
        thread_exit_lock_table_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(thread_exit_lock_table_step_pre); reveal(thread_exit_lock_table_step); }

/// A reclaim leaf on a cpu of `a` removes one mapping of the exiting thread's process, a process of `a`.
pub proof fn thread_exit_leaf_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_reclaim_step_pre(old_u, cpu_id, false),
        thread_exit_leaf_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(thread_exit_reclaim_step_pre); reveal(thread_exit_leaf_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `thread_exit_leaf_step_lr` preserves isolation.
pub proof fn thread_exit_leaf_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_reclaim_step_pre(old_u, cpu_id, false),
        thread_exit_leaf_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(thread_exit_reclaim_step_pre); reveal(thread_exit_leaf_step); }

/// A reclaim TLB flush changes only cpu TLBs, which no domain view contains.
pub proof fn thread_exit_tlb_cleared_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_flush_step_pre(old_u, cpu_id),
        kernel_u_cpu_tlb_cleared(old_u, new_u, old_u.process_map[old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].owning_proc].pcid),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kernel_u_cpu_tlb_cleared); }

/// The step of `thread_exit_tlb_cleared_step_lr` preserves isolation.
pub proof fn thread_exit_tlb_cleared_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_flush_step_pre(old_u, cpu_id),
        kernel_u_cpu_tlb_cleared(old_u, new_u, old_u.process_map[old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].owning_proc].pcid),
    ensures isolated(new_u, a, b),
{ reveal(kernel_u_cpu_tlb_cleared); }

/// Recording the flush on a cpu of `a` changes only its running thread.
pub proof fn thread_exit_flushed_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_flush_step_pre(old_u, cpu_id),
        thread_exit_flushed_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(thread_exit_flush_step_pre); reveal(thread_exit_reclaim_step_pre); reveal(thread_exit_flushed_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `thread_exit_flushed_step_lr` preserves isolation.
pub proof fn thread_exit_flushed_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_flush_step_pre(old_u, cpu_id),
        thread_exit_flushed_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(thread_exit_flushed_step); }

/// An IOMMU reclaim leaf on a cpu of `a` removes one IOMMU mapping of the exiting thread's process, a process of `a`.
pub proof fn thread_exit_iommu_leaf_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_reclaim_step_pre(old_u, cpu_id, true),
        thread_exit_iommu_leaf_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(thread_exit_reclaim_step_pre); reveal(thread_exit_iommu_leaf_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `thread_exit_iommu_leaf_step_lr` preserves isolation.
pub proof fn thread_exit_iommu_leaf_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_reclaim_step_pre(old_u, cpu_id, true),
        thread_exit_iommu_leaf_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(thread_exit_reclaim_step_pre); reveal(thread_exit_iommu_leaf_step); reveal(kernel_u_cpu_ownership_wf); }

/// Refunding 4K quota on a cpu of `a` raises the quota of the exiting thread's container, which lies in `a`, or of an
/// ancestor of `a`, neither of which lies in `b`.
pub proof fn thread_exit_refund_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_reclaim_step_pre(old_u, cpu_id, true),
        kernel_u_container_quota_4k_increased(old_u, new_u, old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].owning_container),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(thread_exit_reclaim_step_pre); reveal(kernel_u_container_quota_4k_increased); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_container_tree_wf); }

/// The step of `thread_exit_refund_step_lr` preserves isolation.
pub proof fn thread_exit_refund_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_reclaim_step_pre(old_u, cpu_id, true),
        kernel_u_container_quota_4k_increased(old_u, new_u, old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].owning_container),
    ensures isolated(new_u, a, b),
{ reveal(kernel_u_container_quota_4k_increased); }

/// Returning one size of quota on a cpu of `a` moves quota from the exiting thread and its process to their container,
/// all of `a`.
pub proof fn thread_exit_quota_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_quota_step_pre(old_u, cpu_id),
        thread_exit_quota_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(thread_exit_quota_step_pre); reveal(thread_exit_quota_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `thread_exit_quota_step_lr` preserves isolation.
pub proof fn thread_exit_quota_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_quota_step_pre(old_u, cpu_id),
        thread_exit_quota_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(thread_exit_quota_step_pre); reveal(thread_exit_quota_step); }

/// Unlocking the reclaimed tables on a cpu of `a` changes only the exiting thread and its process, both of `a`.
pub proof fn thread_exit_unlock_table_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_unlock_table_step_pre(old_u, cpu_id),
        thread_exit_unlock_table_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(thread_exit_unlock_table_step_pre); reveal(thread_exit_unlock_table_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `thread_exit_unlock_table_step_lr` preserves isolation.
pub proof fn thread_exit_unlock_table_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_unlock_table_step_pre(old_u, cpu_id),
        thread_exit_unlock_table_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(thread_exit_unlock_table_step_pre); reveal(thread_exit_unlock_table_step); }

/// Finishing an exit on a cpu of `a` removes the exiting thread, changes its cpu, process, and container, and returns
/// its page to that container, all of `a`, so it leaves the view of `b` unchanged.
pub proof fn thread_exit_finish_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_finish_step_pre(old_u, cpu_id),
        thread_exit_finish_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(thread_exit_finish_step_pre); reveal(thread_exit_finish_step); reveal(kernel_u_thread_exit_changed); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_object_page_owner_wf); }

/// The step of `thread_exit_finish_step_lr` preserves isolation: the exiting thread holds no descriptor, waits on no
/// endpoint, and is no thread's rendezvous peer.
pub proof fn thread_exit_finish_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        thread_exit_finish_step_pre(old_u, cpu_id),
        thread_exit_finish_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(thread_exit_finish_step_pre); reveal(thread_exit_finish_step); reveal(kernel_u_thread_exit_changed); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_endpoint_ownership_wf); }

/// The exit result of a cpu of `b` reads only the view of `b`: the cpu, its container with the running process and
/// thread, and the caller that thread serves, which shares its container.
pub proof fn thread_exit_syscall_result_oc(u1: KernelU, u2: KernelU, cpu_id: CpuId, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u1),
        u1.container_map.dom().contains(b),
        steps_in_domain(u1, cpu_id, b),
        domain_view(u1, b) =~~= domain_view(u2, b),
    ensures thread_exit_syscall_result(u1, cpu_id) == thread_exit_syscall_result(u2, cpu_id),
{
    let cpu = u1.cpu_array[cpu_id as int];
    let thread = u1.thread_map[cpu.current_thread->Some_0];
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        &&& v1.cpus[cpu_id as int] == Some(cpu)
        &&& v1.containers.dom().contains(cpu.owning_container) && v1.containers[cpu.owning_container] == v2.containers[cpu.owning_container]
        &&& cpu.state is Running ==> v1.processes.dom().contains(cpu.current_process->Some_0) && v1.processes[cpu.current_process->Some_0] == v2.processes[cpu.current_process->Some_0]
        &&& cpu.state is Running ==> v1.threads.dom().contains(cpu.current_thread->Some_0) && v1.threads[cpu.current_thread->Some_0] == v2.threads[cpu.current_thread->Some_0]
        &&& cpu.state is Running && thread.caller is Some ==> v1.threads.dom().contains(thread.caller->Some_0) && v1.threads[thread.caller->Some_0] == v2.threads[thread.caller->Some_0]
    }) by { reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_caller_wf); };
}
} // verus!
