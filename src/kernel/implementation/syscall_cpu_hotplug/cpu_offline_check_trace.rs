use vstd::prelude::*;
use crate::*;
use super::cpu_offline_check_spec::*;

verus! {
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
