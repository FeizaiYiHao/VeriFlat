//! Round 5: scheduling, `schedule`, the idle cpu's `rebalance_pull`, and the periodic `rebalance_orphan_pull`. Each is one
//! step from an unlocked cpu, so it has no inside and is never blocked; its call records at most one step. A switch touches
//! only the cpu's own entry, its previous thread, which runs on it, and the next thread, which is scheduled and so runs on
//! no cpu; a pull or an orphan pull moves a scheduled thread between run queues of the cpu's container.
use vstd::prelude::*;
use crate::*;
use crate::frame::*;
use crate::pagetable_locks::*;
use veriflat_syscall_schedule::{rebalance_pull::rebalance_pull_spec::*, syscall_schedule::syscall_schedule_spec::*};

verus! {
pub open spec fn schedule_label(l: StepLabel) -> bool { l is Schedule || l is RebalancePull || l is OrphanPull }

/// One call: a switch with the PCID whose TLB entry it may flush, a pull, or an orphan pull from `cursor`.
pub ghost enum ScheduleCall { Schedule { flushed_pcid: Option<Pcid> }, RebalancePull, OrphanPull { cursor: CpuId } }

pub open spec fn schedule_call_trace_ok(call: ScheduleCall, t: Seq<KernelStep>, c: CpuId) -> bool {
    t.len() == 0 || match call {
        ScheduleCall::Schedule { flushed_pcid } => schedule_syscall_trace(t, t[0].old_u, t[0].new_u, c, true, flushed_pcid),
        ScheduleCall::RebalancePull => rebalance_pull_syscall_trace(t, t[0].old_u, t[0].new_u, c, true),
        ScheduleCall::OrphanPull { cursor } => orphan_pull_syscall_trace(t, t[0].old_u, t[0].new_u, c, cursor, true),
    }
}

pub open spec fn schedule_call_bound(call: ScheduleCall) -> nat { 1 }

pub proof fn schedule_call_trace_ok_implies_len_bounded(call: ScheduleCall, t: Seq<KernelStep>, c: CpuId)
    requires schedule_call_trace_ok(call, t, c),
    ensures t.len() <= schedule_call_bound(call),
{ reveal(schedule_syscall_trace); reveal(rebalance_pull_syscall_trace); reveal(orphan_pull_syscall_trace); }

/// A switch, pull, or orphan pull step of `d` keeps every other cpu, every lock, and every pagetable; `d` is unlocked before and after.
pub proof fn schedule_step_implies_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), schedule_label(l), labeled_step(l, u, u2, d),
    ensures single_step_frame(u, u2, d),
{
    reveal(kernel_u_cpu_ownership_wf);
    match l {
        StepLabel::Schedule { flushed_pcid } => { reveal(schedule_step_pre); reveal(kernel_u_context_switch_changed); },
        StepLabel::RebalancePull => { reveal(rebalance_pull_step_pre); reveal(kernel_u_rebalance_pull_changed); },
        StepLabel::OrphanPull { cursor } => { reveal(orphan_pull_step_pre); reveal(kernel_u_orphan_pull_changed); },
        _ => {},
    }
    assert forall|x: CpuId| #![trigger cpu_kept(u, u2, x)] index_valid(NUM_CPUS, x) && x != d implies cpu_kept(u, u2, x) by {
        let ux = u.cpu_array[x as int];
        if ux.current_thread is Some { assert(u.thread_map[ux.current_thread->Some_0].state == (ThreadState::RUNNING { cpu_id: x })); }
    };
}
} // verus!
