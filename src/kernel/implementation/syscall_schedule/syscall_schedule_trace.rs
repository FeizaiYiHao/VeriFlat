use vstd::prelude::*;
use crate::*;
use super::syscall_schedule_spec::*;
use super::syscall_schedule::ScheduleResult;
verus! {
/// Each return path's entry-state K facts give its value as the user-view result.
pub(super) proof fn schedule_result_from_k(krnl: &KernelK, cpu_id: CpuId, ret: ScheduleResult)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let c = cpu.view().view();
            let process_ptr = c.current_process->Some_0;
            let thread_ptr = c.current_thread->Some_0;
            let queue = scheduler_shards_of(krnl.sched_mp.spec_index(krnl.ctn_mp.spec_index(c.owning_container).view_rodata().view().scheduler))[cpu_id as int];
            let dead = c.current_process is Some && (krnl.prc_mp.spec_index(process_ptr).being_killed() || krnl.thr_mp.spec_index(thread_ptr).being_killed());
            let empty = queue.len() == 0 || krnl.thr_mp.spec_index(queue[0]).being_killed();
            &&& (ret is Off) == (c.state is Off)
            &&& !(ret is Off) && !cpu.being_killed() && c.current_process is Some ==> c.current_thread is Some && krnl.prc_mp.dom().contains(process_ptr)
            &&& !(ret is Off) && !cpu.being_killed() && c.current_process is Some && !krnl.prc_mp.spec_index(process_ptr).being_killed() ==> krnl.thr_mp.dom().contains(thread_ptr)
            &&& !(ret is Off) && !cpu.being_killed() && !dead ==> krnl.ctn_mp.dom().contains(c.owning_container) && (queue.len() > 0 ==> krnl.thr_mp.dom().contains(queue[0]))
            &&& ret is Idle ==> cpu.being_killed() || (c.state is Idle && (dead || empty))
            &&& ret is Continue ==> !cpu.being_killed() && !(c.state is Idle) && (dead || empty)
            &&& ret is Switched ==> !cpu.being_killed() && !dead && !empty && ret == (ScheduleResult::Switched { thread_ptr: queue[0], syscall_return: krnl.thr_mp.spec_index(queue[0]).view().error_code })
        },
    ensures
        schedule_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
    let queue = scheduler_shards_of(krnl.sched_mp.spec_index(krnl.ctn_mp.spec_index(c.owning_container).view_rodata().view().scheduler))[cpu_id as int];
    kernel_cpu_projection_at(krnl, cpu_id);
    if krnl.ctn_mp.dom().contains(c.owning_container) { kernel_container_projection_at(krnl, c.owning_container); }
    if krnl.prc_mp.dom().contains(c.current_process->Some_0) { kernel_process_projection_at(krnl, c.current_process->Some_0); }
    if krnl.thr_mp.dom().contains(c.current_thread->Some_0) { kernel_thread_projection_at(krnl, c.current_thread->Some_0); }
    if queue.len() > 0 && krnl.thr_mp.dom().contains(queue[0]) { kernel_thread_projection_at(krnl, queue[0]); }
}

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
            &&& container.scheduler[cpu_id as int].len() > 0
            &&& container.scheduler[cpu_id as int][0] == next_thread
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
