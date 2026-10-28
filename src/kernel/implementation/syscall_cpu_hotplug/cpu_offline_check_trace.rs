use vstd::prelude::*;
use crate::*;
use super::cpu_offline_check_spec::*;
use super::cpu_offline_check::OfflineCheckResult;

verus! {
/// Each return path's entry-state K facts give its value as the user-view result.
pub(super) proof fn cpu_offline_check_result_from_k(krnl: &KernelK, cpu_id: CpuId, ret: OfflineCheckResult)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let c = cpu.view().view();
            let process_ptr = c.current_process->Some_0;
            let thread_ptr = c.current_thread->Some_0;
            let requested = krnl.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(c.owning_container)).flags.spec_index(cpu_id).view().view().requested;
            let dead = c.current_process is Some && (krnl.prc_mp.spec_index(process_ptr).being_killed() || krnl.thr_mp.spec_index(thread_ptr).being_killed());
            let set_killed = krnl.cpu_set_mp.spec_index(krnl.ctn_mp.spec_index(c.owning_container).view_rodata().view().cpu_set).being_killed();
            &&& !cpu.being_killed() ==> krnl.ctn_mp.dom().contains(c.owning_container)
            &&& !cpu.being_killed() && requested && c.current_process is Some ==> c.current_thread is Some && krnl.prc_mp.dom().contains(process_ptr)
            &&& !cpu.being_killed() && requested && c.current_process is Some && !krnl.prc_mp.spec_index(process_ptr).being_killed() ==> krnl.thr_mp.dom().contains(thread_ptr)
            &&& (ret is Continue) == (cpu.being_killed() || !requested || set_killed || dead)
        },
    ensures
        cpu_offline_check_result(kernel_k_to_kernel_u(*krnl), cpu_id) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
    kernel_cpu_projection_at(krnl, cpu_id);
    reveal(cpu_offline_requests_of);
    if krnl.ctn_mp.dom().contains(c.owning_container) { kernel_container_projection_at(krnl, c.owning_container); }
    if krnl.prc_mp.dom().contains(c.current_process->Some_0) { kernel_process_projection_at(krnl, c.current_process->Some_0); }
    if krnl.thr_mp.dom().contains(c.current_thread->Some_0) { kernel_thread_projection_at(krnl, c.current_thread->Some_0); }
}

/// The entry state's K facts on the unlocked, live, non-Off cpu `cpu_id` with a set request bit give the hold step's
/// precondition.
pub(super) proof fn cpu_offline_check_hold_step_pre_from_k(krnl: &KernelK, cpu_id: CpuId)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let c = cpu.view().view();
            &&& cpu.locking_thread() is None
            &&& !cpu.being_killed()
            &&& !(c.state is Off)
            &&& krnl.ctn_mp.dom().contains(c.owning_container)
            &&& krnl.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(c.owning_container)).flags.spec_index(cpu_id).view().view().requested
        },
    ensures cpu_offline_check_hold_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
{
    kernel_cpu_projection_at(krnl, cpu_id); kernel_container_projection_at(krnl, krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container);
    reveal(cpu_offline_requests_of); reveal(cpu_offline_check_hold_step_pre);
}

/// Write-locking cpu `cpu_id` inside its kernel step and changing no other projection is the hold step from `before` to
/// `after`.
pub(super) proof fn cpu_offline_check_hold_step_from_u(before: &KernelK, after: &KernelK, cpu_id: CpuId)
    requires
        after.cpu_arr.spec_index(cpu_id).value.locking_thread() is Write,
        after.cpu_op.view().view()[cpu_id as int] is InStep,
        ({
            let pre_u = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after) == (KernelU {
                cpu_array: pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state: after.cpu_arr.spec_index(cpu_id).value.lock_state_u(), op: after.cpu_op.view().view()[cpu_id as int], ..pre_u.cpu_array[cpu_id as int] }),
                ..pre_u
            })
        }),
    ensures cpu_offline_check_hold_step(kernel_k_to_kernel_u(*before), kernel_k_to_kernel_u(*after), cpu_id),
{ reveal(cpu_offline_check_hold_step); }

/// Unlocking cpu `cpu_id`, write-held since the hold step, as it leaves its kernel step for the resting state of its
/// scheduling state, and changing no other projection is the release step from `before` to `after`.
pub(super) proof fn cpu_offline_check_release_step_from_u(before: &KernelK, after: &KernelK, cpu_id: CpuId)
    requires
        index_valid(NUM_CPUS, cpu_id),
        before.cpu_arr.spec_index(cpu_id).value.locking_thread() is Write,
        after.cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        after.cpu_op.view().view()[cpu_id as int] == cpu_op_after_step(before.cpu_arr.spec_index(cpu_id).view().view().view().state),
        ({
            let pre_u = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after) == (KernelU {
                cpu_array: pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state: after.cpu_arr.spec_index(cpu_id).value.lock_state_u(), op: after.cpu_op.view().view()[cpu_id as int], ..pre_u.cpu_array[cpu_id as int] }),
                ..pre_u
            })
        }),
    ensures
        cpu_offline_check_release_step_pre(kernel_k_to_kernel_u(*before), cpu_id),
        cpu_offline_check_release_step(kernel_k_to_kernel_u(*before), kernel_k_to_kernel_u(*after), cpu_id),
{ kernel_cpu_projection_at(before, cpu_id); reveal(cpu_offline_check_release_step_pre); reveal(cpu_offline_check_release_step); }

/// The went-off wrapper's user-view facts from the decision snapshot `snap`, which write-holds the cpu since the hold step,
/// are exactly the offline step from `snap` to `post`.
pub(super) proof fn cpu_offline_check_step_from_u(snap: &KernelK, post: KernelU, cpu_id: CpuId, regs: Registers, flushed_default_pcid: bool)
    requires
        kernel_u_cpu_went_off_changed(kernel_k_to_kernel_u(*snap), post, cpu_id, regs, flushed_default_pcid),
        {
            let old_u = kernel_k_to_kernel_u(*snap);
            let cpu = old_u.cpu_array[cpu_id as int];
            &&& cpu.lock_state is WriteLocked
            &&& old_u.container_map[cpu.owning_container].cpu_set_lock is Unlocked
            &&& (cpu.current_thread is Some ==> old_u.thread_map[cpu.current_thread.unwrap()].lock_state is Unlocked && old_u.process_map[cpu.current_process.unwrap()].lock_state is Unlocked)
        },
    ensures
        cpu_offline_check_step_pre(kernel_k_to_kernel_u(*snap), cpu_id),
        cpu_offline_check_step(kernel_k_to_kernel_u(*snap), post, cpu_id, regs, flushed_default_pcid),
{ reveal(cpu_offline_check_step_pre); reveal(kernel_u_cpu_went_off_changed); }

/// The hold step recorded at the boundary after `before` is the one step pushed onto it and the partial trace after
/// holding.
pub(super) proof fn cpu_offline_check_trace_hold_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId)
    requires
        steps.view() == record_user_view_change(before, pre, post),
        cpu_offline_check_hold_step_pre(pre, cpu_id),
        cpu_offline_check_hold_step(pre, post, cpu_id),
    ensures
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        cpu_offline_check_trace_after_hold(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, cpu_id),
{ reveal(cpu_offline_check_hold_step_pre); reveal(cpu_offline_check_hold_step); reveal(cpu_offline_check_trace_after_hold); }

/// The release step recorded after the partial trace after holding from `entry`, which starts at `start`, completes the
/// continuing trace.
pub(super) proof fn cpu_offline_check_trace_release_step(
    steps: &KernelSteps, start: int, before: Seq<KernelStep>, entry: KernelU, pre: KernelU, post: KernelU, cpu_id: CpuId, regs: Registers,
)
    requires
        0 <= start <= before.len(),
        cpu_offline_check_trace_after_hold(before.subrange(start, before.len() as int), entry, cpu_id),
        steps.view() == record_user_view_change(before, pre, post),
        cpu_offline_check_release_step_pre(pre, cpu_id),
        cpu_offline_check_release_step(pre, post, cpu_id),
    ensures cpu_offline_check_entry_trace(steps.view().subrange(start, steps.view().len() as int), entry, post, cpu_id, regs, false, false),
{
    reveal(cpu_offline_check_release_step_pre); reveal(cpu_offline_check_release_step); reveal(cpu_offline_check_trace_after_hold); reveal(cpu_offline_check_entry_trace);
}

/// The offline step pushed after the partial trace after holding from `entry`, which starts at `start`, completes the
/// went-off trace.
pub(super) proof fn cpu_offline_check_trace_went_off_step(
    steps: &KernelSteps, start: int, before: Seq<KernelStep>, entry: KernelU, pre: KernelU, post: KernelU, cpu_id: CpuId, regs: Registers, flushed_default_pcid: bool,
)
    requires
        0 <= start <= before.len(),
        cpu_offline_check_trace_after_hold(before.subrange(start, before.len() as int), entry, cpu_id),
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        cpu_offline_check_step_pre(pre, cpu_id),
        cpu_offline_check_step(pre, post, cpu_id, regs, flushed_default_pcid),
    ensures cpu_offline_check_entry_trace(steps.view().subrange(start, steps.view().len() as int), entry, post, cpu_id, regs, true, flushed_default_pcid),
{ reveal(cpu_offline_check_trace_after_hold); reveal(cpu_offline_check_entry_trace); }

/// A check whose entry cpu is killed or not requested continues before holding and records no step.
pub(super) proof fn cpu_offline_check_trace_stutter(trace: Seq<KernelStep>, krnl: &KernelK, cpu_id: CpuId, regs: Registers)
    requires
        index_valid(NUM_CPUS, cpu_id),
        trace.len() == 0,
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let c = cpu.view().view();
            let requested = krnl.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(c.owning_container)).flags.spec_index(cpu_id).view().view().requested;
            &&& !cpu.being_killed() ==> krnl.ctn_mp.dom().contains(c.owning_container)
            &&& cpu.being_killed() || !requested
        },
    ensures cpu_offline_check_entry_trace(trace, kernel_k_to_kernel_u(*krnl), kernel_k_to_kernel_u(*krnl), cpu_id, regs, false, false),
{
    let c = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
    kernel_cpu_projection_at(krnl, cpu_id);
    if krnl.ctn_mp.dom().contains(c.owning_container) { kernel_container_projection_at(krnl, c.owning_container); }
    reveal(cpu_offline_requests_of); reveal(cpu_offline_check_hold_step_pre); reveal(cpu_offline_check_entry_trace);
}

/// A check that reads a clear request bit and releases the cpu `cpu_id` it locked, back in the running state it entered
/// with and changing nothing else from `entry` but the offline flags' lock states, records no step at the release after
/// `before` and continues before holding.
pub(super) proof fn cpu_offline_check_trace_stutter_released(
    steps: &KernelSteps, before: Seq<KernelStep>, entry: &KernelK, post: &KernelK, cpu_id: CpuId, regs: Registers,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        steps.view() == record_user_view_change(before, kernel_k_to_kernel_u(*entry), kernel_k_to_kernel_u(*post)),
        post.inv(),
        *post == (KernelK { cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, cpu_offline_mp: post.cpu_offline_mp, ..*entry }),
        post.cpu_op.view().view() == entry.cpu_op.view().view(),
        post.cpu_arr.entries_unchanged_except(&entry.cpu_arr, cpu_id),
        entry.cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        post.cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        kernel_cpu_process_thread_nonlock_fields_unchanged(entry, post),
        kernel_container_nonlock_fields_and_quotas_unchanged(entry, post),
        kernel_endpoint_nonlock_fields_unchanged(entry.ep_mp, post.ep_mp),
        {
            let c = entry.cpu_arr.spec_index(cpu_id).view().view().view();
            &&& entry.ctn_mp.dom().contains(c.owning_container)
            &&& !entry.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(c.owning_container)).flags.spec_index(cpu_id).view().view().requested
        },
    ensures cpu_offline_check_entry_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*entry), kernel_k_to_kernel_u(*post), cpu_id, regs, false, false),
{
    kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(entry, post);
    cpu_offline_check_trace_stutter(steps.view().subrange(before.len() as int, steps.view().len() as int), entry, cpu_id, regs);
}
} // verus!
