use vstd::prelude::*;
use crate::*;
use super::syscall_schedule_spec::*;
verus! {
/// The context-switch wrapper's user-view facts are exactly the schedule step on `pre`/`post`.
pub(super) proof fn schedule_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, next_thread: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>)
    requires
        kernel_u_context_switch_changed(pre, post, cpu_id, next_thread, regs, flushed_pcid),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let container = pre.container_map.spec_index(cpu.owning_container);
            let next = pre.thread_map.spec_index(next_thread);
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& cpu.lock_state is Unlocked
            &&& !(cpu.state is Off)
            &&& pre.container_map.dom().contains(cpu.owning_container)
            &&& container.scheduler.len() > 0
            &&& container.scheduler[0] == next_thread
            &&& pre.thread_map.dom().contains(next_thread)
            &&& next.lock_state is Unlocked
            &&& !next.killed
            &&& next.state is SCHEDULED
            &&& next.owning_container == cpu.owning_container
            &&& pre.process_map.dom().contains(next.owning_proc)
            &&& cpu.current_thread != Some(next_thread)
            &&& cpu.current_process is Some == cpu.current_thread is Some
            &&& (cpu.current_thread is Some ==> {
                let prev = pre.thread_map.spec_index(cpu.current_thread.unwrap());
                &&& pre.thread_map.dom().contains(cpu.current_thread.unwrap())
                &&& prev.lock_state is Unlocked
                &&& !prev.killed
                &&& prev.state == (ThreadState::RUNNING { cpu_id })
                &&& prev.owning_proc == cpu.current_process.unwrap()
                &&& pre.process_map.dom().contains(cpu.current_process.unwrap())
                &&& pre.process_map.spec_index(cpu.current_process.unwrap()).lock_state is Unlocked
                &&& !pre.process_map.spec_index(cpu.current_process.unwrap()).killed
            })
        },
    ensures
        schedule_step_pre(pre, cpu_id),
        schedule_step(pre, post, cpu_id, regs, flushed_pcid),
{ reveal(schedule_step_pre); }

/// The one step pushed since `before` is the complete switching trace.
pub(super) proof fn schedule_trace_switch_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, regs: Registers, flushed_pcid: Option<Pcid>)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        schedule_step_pre(pre, cpu_id),
        schedule_step(pre, post, cpu_id, regs, flushed_pcid),
    ensures
        schedule_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, regs, true, flushed_pcid),
{ reveal(schedule_syscall_trace); }

/// A call that does not switch records no step.
pub(super) proof fn schedule_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, regs: Registers)
    requires
        trace.len() == 0,
    ensures
        schedule_syscall_trace(trace, pre, pre, cpu_id, regs, false, None),
{ reveal(schedule_syscall_trace); }
} // verus!
