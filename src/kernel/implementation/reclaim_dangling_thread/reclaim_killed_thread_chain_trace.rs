use vstd::prelude::*;
use crate::*;

verus! {
/// Step `step` reclaims killed threads on cpu `cpu_id` while that cpu, its running thread, the lock modes and kill
/// marks of the held `processes`, and the lock modes of the held `containers` keep their projection at `entry`.
pub open spec fn killed_thread_reclaim_step(step: KernelStep, entry: KernelU, cpu_id: CpuId, processes: Set<RwLockProcessPtr>, containers: Set<RwLockContainerPtr>) -> bool {
    let u = step.old_u;
    let current_thread = entry.cpu_array[cpu_id as int].current_thread->Some_0;
    &&& kernel_u_killed_thread_reclaim_step(u, step.new_u, cpu_id)
    &&& u.cpu_array[cpu_id as int] == entry.cpu_array[cpu_id as int]
    &&& u.thread_map.dom().contains(current_thread)
    &&& u.thread_map[current_thread] == entry.thread_map[current_thread]
    &&& forall|p: RwLockProcessPtr| #![trigger processes.contains(p)] #![trigger u.process_map[p]] processes.contains(p) ==> {
        &&& u.process_map.dom().contains(p)
        &&& u.process_map[p].lock_state == entry.process_map[p].lock_state
        &&& u.process_map[p].killed == entry.process_map[p].killed
    }
    &&& forall|c: RwLockContainerPtr| #![trigger containers.contains(c)] #![trigger u.container_map[c]] containers.contains(c) ==> {
        &&& u.container_map.dom().contains(c)
        &&& u.container_map[c].lock_state == entry.container_map[c].lock_state
    }
}

/// Every step of `steps` from `start` reclaims killed threads on cpu `cpu_id` while keeping its projection at `entry`.
pub open spec fn killed_thread_reclaim_partial_trace(steps: Seq<KernelStep>, start: int, entry: KernelU, cpu_id: CpuId, processes: Set<RwLockProcessPtr>, containers: Set<RwLockContainerPtr>) -> bool {
    forall|j: int| #![trigger steps[j]] start <= j < steps.len() ==> killed_thread_reclaim_step(steps[j], entry, cpu_id, processes, containers)
}

/// A state that keeps the cpu `cpu_id` of `entry` and its running thread, the lock modes and kill marks of the held
/// `processes`, and the lock modes of the held `containers` keeps the projection at `entry` that a killed thread reclaim
/// step from it needs.
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
        },
        forall|c: RwLockContainerPtr| #![trigger containers.contains(c)] containers.contains(c) ==> {
            &&& krnl.ctn_mp.dom().contains(c)
            &&& entry.ctn_mp.dom().contains(c)
            &&& krnl.ctn_mp.spec_index(c).locking_thread() == entry.ctn_mp.spec_index(c).locking_thread()
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
            }
            &&& forall|c: RwLockContainerPtr| #![trigger containers.contains(c)] containers.contains(c) ==> {
                &&& u.container_map.dom().contains(c)
                &&& u.container_map[c].lock_state == e.container_map[c].lock_state
            }
        }),
{
    let current_thread = entry.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0;
    kernel_process_container_lock_states_projection_eq(krnl, entry, processes, containers);
    kernel_cpu_projection_at(krnl, cpu_id); kernel_cpu_projection_at(entry, cpu_id);
    kernel_thread_projection_at(krnl, current_thread); kernel_thread_projection_at(entry, current_thread);
}

/// One link of a killed thread reclaim chain recorded in `trace` extends the partial trace of `before` from `start` at
/// `entry`: the descriptor steps ending `desc` taken at `desc_entry`, the caller steps ending `caller` taken at
/// `caller_entry`, and the dangling thread step, once both entries agree with `entry`.
pub(super) proof fn killed_thread_reclaim_chain_trace(
    trace: Seq<KernelStep>, start: int, before: Seq<KernelStep>, desc: Seq<KernelStep>, caller: Seq<KernelStep>, entry: KernelU, desc_entry: KernelU,
    caller_entry: KernelU, cpu_id: CpuId, processes: Set<RwLockProcessPtr>, containers: Set<RwLockContainerPtr>,
)
    requires
        0 <= start <= before.len(),
        kernel_steps_prefix_unchanged(before, desc),
        kernel_steps_prefix_unchanged(desc, caller),
        kernel_steps_prefix_unchanged(caller, trace),
        trace.len() == caller.len() + 1,
        killed_thread_reclaim_partial_trace(before, start, entry, cpu_id, processes, containers),
        killed_thread_reclaim_partial_trace(desc, before.len() as int, desc_entry, cpu_id, processes, containers),
        killed_thread_reclaim_partial_trace(caller, desc.len() as int, caller_entry, cpu_id, processes, containers),
        killed_thread_reclaim_step(trace[caller.len() as int], entry, cpu_id, processes, containers),
        desc_entry.cpu_array[cpu_id as int] == entry.cpu_array[cpu_id as int],
        desc_entry.thread_map[entry.cpu_array[cpu_id as int].current_thread->Some_0] == entry.thread_map[entry.cpu_array[cpu_id as int].current_thread->Some_0],
        forall|p: RwLockProcessPtr| #![trigger processes.contains(p)]
            processes.contains(p) ==> desc_entry.process_map[p].lock_state == entry.process_map[p].lock_state && desc_entry.process_map[p].killed == entry.process_map[p].killed,
        forall|c: RwLockContainerPtr| #![trigger containers.contains(c)] containers.contains(c) ==> desc_entry.container_map[c].lock_state == entry.container_map[c].lock_state,
        caller_entry.cpu_array[cpu_id as int] == entry.cpu_array[cpu_id as int],
        caller_entry.thread_map[entry.cpu_array[cpu_id as int].current_thread->Some_0] == entry.thread_map[entry.cpu_array[cpu_id as int].current_thread->Some_0],
        forall|p: RwLockProcessPtr| #![trigger processes.contains(p)]
            processes.contains(p) ==> caller_entry.process_map[p].lock_state == entry.process_map[p].lock_state && caller_entry.process_map[p].killed == entry.process_map[p].killed,
        forall|c: RwLockContainerPtr| #![trigger containers.contains(c)] containers.contains(c) ==> caller_entry.container_map[c].lock_state == entry.container_map[c].lock_state,
    ensures
        killed_thread_reclaim_partial_trace(trace, start, entry, cpu_id, processes, containers),
{
    reveal(kernel_steps_prefix_unchanged);
    assert(trace =~= (before + desc.subrange(before.len() as int, desc.len() as int) + caller.subrange(desc.len() as int, caller.len() as int)).push(trace[caller.len() as int]));
}
} // verus!
