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
            &&& !(c.state is Off) && !cpu.being_killed() ==> krnl.ctn_mp.dom().contains(c.owning_container)
            &&& !(c.state is Off) && !cpu.being_killed() && requested && c.current_process is Some ==> c.current_thread is Some && krnl.prc_mp.dom().contains(process_ptr)
            &&& !(c.state is Off) && !cpu.being_killed() && requested && c.current_process is Some && !krnl.prc_mp.spec_index(process_ptr).being_killed() ==> krnl.thr_mp.dom().contains(thread_ptr)
            &&& (ret is Continue) == (c.state is Off || cpu.being_killed() || !requested || set_killed || dead)
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

/// The went-off wrapper's user-view facts are exactly the offline step on `pre`/`post`.
pub(super) proof fn cpu_offline_check_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, regs: Registers, flushed_default_pcid: bool)
    requires
        kernel_u_cpu_went_off_changed(pre, post, cpu_id, regs, flushed_default_pcid),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            &&& cpu.lock_state is Unlocked
            &&& pre.container_map[cpu.owning_container].cpu_set_lock is Unlocked
            &&& (cpu.current_thread is Some ==> pre.thread_map[cpu.current_thread.unwrap()].lock_state is Unlocked && pre.process_map[cpu.current_process.unwrap()].lock_state is Unlocked)
        },
    ensures
        cpu_offline_check_step_pre(pre, cpu_id),
        cpu_offline_check_step(pre, post, cpu_id, regs, flushed_default_pcid),
{ reveal(cpu_offline_check_step_pre); reveal(kernel_u_cpu_went_off_changed); }

/// The one step pushed since `before` is the complete went-off trace.
pub(super) proof fn cpu_offline_check_trace_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, regs: Registers, flushed_default_pcid: bool)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        cpu_offline_check_step_pre(pre, cpu_id),
        cpu_offline_check_step(pre, post, cpu_id, regs, flushed_default_pcid),
    ensures
        cpu_offline_check_entry_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, regs, true, flushed_default_pcid),
{ reveal(cpu_offline_check_entry_trace); }

/// A check that continues to the scheduler records no step.
pub(super) proof fn cpu_offline_check_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, regs: Registers)
    requires
        trace.len() == 0,
    ensures
        cpu_offline_check_entry_trace(trace, pre, pre, cpu_id, regs, false, false),
{ reveal(cpu_offline_check_entry_trace); }
} // verus!
