use vstd::prelude::*;
use crate::*;

verus! {
/// Step `step` reclaims killed threads of `container` on cpu `cpu_id`, changing or removing no other thread, while that
/// cpu, its running thread, the lock modes, kill marks, and owning containers of the held `processes`, and the lock modes
/// and upper trees of the held `containers` keep their projection at `entry`.
pub open spec fn killed_thread_reclaim_step(
    step: KernelStep, entry: KernelU, cpu_id: CpuId, processes: Set<RwLockProcessPtr>, containers: Set<RwLockContainerPtr>, container: RwLockContainerPtr,
) -> bool {
    let u = step.old_u;
    let current_thread = entry.cpu_array[cpu_id as int].current_thread->Some_0;
    &&& kernel_u_killed_thread_reclaim_step(u, step.new_u, cpu_id)
    &&& forall|t: RwLockThreadPtr| #![trigger u.thread_map[t]]
        u.thread_map.dom().contains(t) && (!step.new_u.thread_map.dom().contains(t) || step.new_u.thread_map[t] != u.thread_map[t]) ==> u.thread_map[t].owning_container == container
    &&& u.cpu_array[cpu_id as int] == entry.cpu_array[cpu_id as int]
    &&& u.thread_map.dom().contains(current_thread)
    &&& u.thread_map[current_thread] == entry.thread_map[current_thread]
    &&& forall|p: RwLockProcessPtr| #![trigger processes.contains(p)] #![trigger u.process_map[p]] processes.contains(p) ==> {
        &&& u.process_map.dom().contains(p)
        &&& u.process_map[p].lock_state == entry.process_map[p].lock_state
        &&& u.process_map[p].killed == entry.process_map[p].killed
        &&& u.process_map[p].owning_container == entry.process_map[p].owning_container
    }
    &&& forall|c: RwLockContainerPtr| #![trigger containers.contains(c)] #![trigger u.container_map[c]] containers.contains(c) ==> {
        &&& u.container_map.dom().contains(c)
        &&& u.container_map[c].lock_state == entry.container_map[c].lock_state
        &&& u.container_map[c].uppertree_seq == entry.container_map[c].uppertree_seq
    }
}

/// Every step of `steps` from `start` reclaims killed threads of `container` on cpu `cpu_id` while keeping its projection
/// at `entry`.
pub open spec fn killed_thread_reclaim_partial_trace(
    steps: Seq<KernelStep>, start: int, entry: KernelU, cpu_id: CpuId, processes: Set<RwLockProcessPtr>, containers: Set<RwLockContainerPtr>, container: RwLockContainerPtr,
) -> bool {
    forall|j: int| #![trigger steps[j]] start <= j < steps.len() ==> killed_thread_reclaim_step(steps[j], entry, cpu_id, processes, containers, container)
}

/// A state that keeps the cpu `cpu_id` of `entry` and its running thread, the lock modes, kill marks, and owning
/// containers of the held `processes`, and the lock modes and upper trees of the held `containers` keeps the projection at
/// `entry` that a killed thread reclaim step from it needs.
pub(super) proof fn killed_thread_reclaim_step_pre_from_k(krnl: &KernelK, entry: &KernelK, cpu_id: CpuId, processes: Set<RwLockProcessPtr>, containers: Set<RwLockContainerPtr>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        krnl.cpu_arr.spec_index(cpu_id).view() == entry.cpu_arr.spec_index(cpu_id).view(),
        entry.thr_mp.dom().contains(entry.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0),
        krnl.thr_mp.dom().contains(entry.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0),
        krnl.thr_mp.spec_index(entry.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0)
            == entry.thr_mp.spec_index(entry.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0),
        forall|p: RwLockProcessPtr| #![trigger processes.contains(p)] processes.contains(p) ==> {
            &&& krnl.prc_mp.dom().contains(p)
            &&& entry.prc_mp.dom().contains(p)
            &&& krnl.prc_mp.spec_index(p).locking_thread() == entry.prc_mp.spec_index(p).locking_thread()
            &&& krnl.prc_mp.spec_index(p).being_killed() == entry.prc_mp.spec_index(p).being_killed()
            &&& krnl.prc_mp.spec_index(p).view_rodata().view().owning_container == entry.prc_mp.spec_index(p).view_rodata().view().owning_container
        },
        forall|c: RwLockContainerPtr| #![trigger containers.contains(c)] containers.contains(c) ==> {
            &&& krnl.ctn_mp.dom().contains(c)
            &&& entry.ctn_mp.dom().contains(c)
            &&& krnl.ctn_mp.spec_index(c).locking_thread() == entry.ctn_mp.spec_index(c).locking_thread()
            &&& krnl.ctn_mp.spec_index(c).view_ghost().uppertree_seq == entry.ctn_mp.spec_index(c).view_ghost().uppertree_seq
        },
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            let e = kernel_k_to_kernel_u(*entry);
            let current_thread = e.cpu_array[cpu_id as int].current_thread->Some_0;
            &&& u.cpu_array[cpu_id as int] == e.cpu_array[cpu_id as int]
            &&& u.thread_map.dom().contains(current_thread)
            &&& u.thread_map[current_thread] == e.thread_map[current_thread]
            &&& forall|p: RwLockProcessPtr| #![trigger processes.contains(p)] processes.contains(p) ==> {
                &&& u.process_map.dom().contains(p)
                &&& u.process_map[p].lock_state == e.process_map[p].lock_state
                &&& u.process_map[p].killed == e.process_map[p].killed
                &&& u.process_map[p].owning_container == e.process_map[p].owning_container
            }
            &&& forall|c: RwLockContainerPtr| #![trigger containers.contains(c)] containers.contains(c) ==> {
                &&& u.container_map.dom().contains(c)
                &&& u.container_map[c].lock_state == e.container_map[c].lock_state
                &&& u.container_map[c].uppertree_seq == e.container_map[c].uppertree_seq
            }
        }),
{
    let current_thread = entry.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0;
    kernel_process_container_lock_states_projection_eq(krnl, entry, processes, containers);
    kernel_cpu_projection_at(krnl, cpu_id); kernel_cpu_projection_at(entry, cpu_id);
    kernel_thread_projection_at(krnl, current_thread); kernel_thread_projection_at(entry, current_thread);
}

/// One link of a killed thread reclaim chain of `container` recorded in `trace` extends the partial trace of `before`
/// from `start` at `entry`: the descriptor steps ending `desc` taken at `desc_entry`, the caller steps ending `caller`
/// taken at `caller_entry`, and the dangling thread step, once both entries agree with `entry`.
pub(super) proof fn killed_thread_reclaim_chain_trace(
    trace: Seq<KernelStep>, start: int, before: Seq<KernelStep>, desc: Seq<KernelStep>, caller: Seq<KernelStep>, entry: KernelU, desc_entry: KernelU,
    caller_entry: KernelU, cpu_id: CpuId, processes: Set<RwLockProcessPtr>, containers: Set<RwLockContainerPtr>, container: RwLockContainerPtr,
)
    requires
        0 <= start <= before.len(),
        kernel_steps_prefix_unchanged(before, desc),
        kernel_steps_prefix_unchanged(desc, caller),
        kernel_steps_prefix_unchanged(caller, trace),
        trace.len() == caller.len() + 1,
        killed_thread_reclaim_partial_trace(before, start, entry, cpu_id, processes, containers, container),
        killed_thread_reclaim_partial_trace(desc, before.len() as int, desc_entry, cpu_id, processes, containers, container),
        killed_thread_reclaim_partial_trace(caller, desc.len() as int, caller_entry, cpu_id, processes, containers, container),
        killed_thread_reclaim_step(trace[caller.len() as int], entry, cpu_id, processes, containers, container),
        desc_entry.cpu_array[cpu_id as int] == entry.cpu_array[cpu_id as int],
        desc_entry.thread_map[entry.cpu_array[cpu_id as int].current_thread->Some_0] == entry.thread_map[entry.cpu_array[cpu_id as int].current_thread->Some_0],
        forall|p: RwLockProcessPtr| #![trigger processes.contains(p)] processes.contains(p) ==> {
            &&& desc_entry.process_map[p].lock_state == entry.process_map[p].lock_state
            &&& desc_entry.process_map[p].killed == entry.process_map[p].killed
            &&& desc_entry.process_map[p].owning_container == entry.process_map[p].owning_container
        },
        forall|c: RwLockContainerPtr| #![trigger containers.contains(c)]
            containers.contains(c) ==> desc_entry.container_map[c].lock_state == entry.container_map[c].lock_state && desc_entry.container_map[c].uppertree_seq == entry.container_map[c].uppertree_seq,
        caller_entry.cpu_array[cpu_id as int] == entry.cpu_array[cpu_id as int],
        caller_entry.thread_map[entry.cpu_array[cpu_id as int].current_thread->Some_0] == entry.thread_map[entry.cpu_array[cpu_id as int].current_thread->Some_0],
        forall|p: RwLockProcessPtr| #![trigger processes.contains(p)] processes.contains(p) ==> {
            &&& caller_entry.process_map[p].lock_state == entry.process_map[p].lock_state
            &&& caller_entry.process_map[p].killed == entry.process_map[p].killed
            &&& caller_entry.process_map[p].owning_container == entry.process_map[p].owning_container
        },
        forall|c: RwLockContainerPtr| #![trigger containers.contains(c)]
            containers.contains(c) ==> caller_entry.container_map[c].lock_state == entry.container_map[c].lock_state && caller_entry.container_map[c].uppertree_seq == entry.container_map[c].uppertree_seq,
    ensures
        killed_thread_reclaim_partial_trace(trace, start, entry, cpu_id, processes, containers, container),
{
    reveal(kernel_steps_prefix_unchanged);
    assert(trace =~= (before + desc.subrange(before.len() as int, desc.len() as int) + caller.subrange(desc.len() as int, caller.len() as int)).push(trace[caller.len() as int]));
}

/// The steps of `trace` after `before`, recorded while keeping the projection at `link_entry`, extend the partial trace
/// of `before` from `start` at `entry`, once `link_entry` agrees with `entry`.
pub(super) proof fn killed_thread_reclaim_link_trace(
    trace: Seq<KernelStep>, start: int, before: Seq<KernelStep>, entry: KernelU, link_entry: KernelU, cpu_id: CpuId, processes: Set<RwLockProcessPtr>,
    containers: Set<RwLockContainerPtr>, container: RwLockContainerPtr,
)
    requires
        0 <= start <= before.len(),
        kernel_steps_prefix_unchanged(before, trace),
        killed_thread_reclaim_partial_trace(before, start, entry, cpu_id, processes, containers, container),
        killed_thread_reclaim_partial_trace(trace, before.len() as int, link_entry, cpu_id, processes, containers, container),
        link_entry.cpu_array[cpu_id as int] == entry.cpu_array[cpu_id as int],
        link_entry.thread_map[entry.cpu_array[cpu_id as int].current_thread->Some_0] == entry.thread_map[entry.cpu_array[cpu_id as int].current_thread->Some_0],
        forall|p: RwLockProcessPtr| #![trigger processes.contains(p)] processes.contains(p) ==> {
            &&& link_entry.process_map[p].lock_state == entry.process_map[p].lock_state
            &&& link_entry.process_map[p].killed == entry.process_map[p].killed
            &&& link_entry.process_map[p].owning_container == entry.process_map[p].owning_container
        },
        forall|c: RwLockContainerPtr| #![trigger containers.contains(c)]
            containers.contains(c) ==> link_entry.container_map[c].lock_state == entry.container_map[c].lock_state && link_entry.container_map[c].uppertree_seq == entry.container_map[c].uppertree_seq,
    ensures
        killed_thread_reclaim_partial_trace(trace, start, entry, cpu_id, processes, containers, container),
{
    reveal(kernel_steps_prefix_unchanged);
    assert(trace =~= before + trace.subrange(before.len() as int, trace.len() as int));
}
} // verus!
