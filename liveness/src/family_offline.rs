//! Round 11: `cpu_offline_check`. A hold step write-locks the cpu inside its kernel step without locking its running
//! thread, and a release step or an offline step ends the check. Between them the cpu is `cpu_unbound`: write-locked
//! without holding its thread, which another cpu may lock and mark for a kill, so `cpus_wf` and `cpu_kept` keep only the
//! running thread's progress, which stays empty, for such a cpu. The release step is always enabled inside, and a call
//! records at most two steps.
//!
//! Restrictions this family adds to the world (`world_allowed`), each a gap of U recorded in `u_gaps.md`:
//! - `offline_window_only` (G19) is gone since round 12: the mmap release and fill-enter steps now require the acting cpu
//!   to write-hold its thread, so an unbound cpu takes no traced step.
//! - `offline_hold_at_rest` (G20): the hold step starts from a running thread that records no syscall progress and
//!   that the cpu does not write-hold; `cpu_offline_check_hold_step_pre` does not say so.
use vstd::prelude::*;
use crate::*;
use crate::frame::*;
use crate::pagetable_locks::*;
use crate::family_env::*;
use crate::family_kill::*;
use crate::kill_frame::*;
use veriflat_syscall_cpu_hotplug::syscall_cpu_hotplug::syscall_cpu_offline_check_spec::*;

verus! {
pub open spec fn offline_label(l: StepLabel) -> bool { l is CpuOfflineCheckHold || l is CpuOfflineCheck || l is CpuOfflineCheckRelease }

/// Restriction `offline_hold_at_rest` (G20): the hold step starts from a running thread that records no syscall progress
/// and that the cpu does not write-hold.
pub open spec fn offline_hold_at_rest(u: KernelU, l: StepLabel, d: CpuId) -> bool {
    l is CpuOfflineCheckHold && u.cpu_array[d as int].current_thread is Some
        ==> cur_thread(u, d).syscall_progress is None && cur_thread(u, d).lock_state != (LockStateU::WriteLocked { writer: d })
}

/// `c` is inside `cpu_offline_check`: write-locked by itself without holding its running thread.
pub open spec fn in_offline_check(u: KernelU, c: CpuId) -> bool { cpu_unbound(u, c) && u.cpu_array[c as int].lock_state == (LockStateU::WriteLocked { writer: c }) }

/// One call: whether the cpu went Off, and whether it flushed its default-PCID TLB entry.
pub ghost struct OfflineCall { pub went_off: bool, pub flushed_default_pcid: bool }

/// `t` is a complete trace of `call` on `c` as its exec contract ensures it: nothing, or the hold step and the release or
/// offline step.
pub open spec fn offline_call_trace_ok(call: OfflineCall, t: Seq<KernelStep>, c: CpuId) -> bool {
    t.len() == 0 || cpu_offline_check_entry_trace(t, t[0].old_u, t[t.len() - 1].new_u, c, call.went_off, call.flushed_default_pcid)
}

pub open spec fn offline_call_bound(call: OfflineCall) -> nat { 2 }

pub proof fn offline_call_trace_ok_implies_len_bounded(call: OfflineCall, t: Seq<KernelStep>, c: CpuId)
    requires offline_call_trace_ok(call, t, c),
    ensures t.len() <= offline_call_bound(call),
{ reveal(cpu_offline_check_entry_trace); }

/// Property (a) for the check: a cpu inside, running inside its kernel step, can release.
pub proof fn in_offline_check_implies_release_enabled(u: KernelU, c: CpuId)
    requires kernel_u_ownership_wf(u), locked_cpus_in_step(u), in_offline_check(u, c),
    ensures cpu_offline_check_release_step_pre(u, c),
{
    reveal(kernel_u_cpu_ownership_wf); reveal(cpu_offline_check_release_step_pre);
    assert(u.cpu_array[c as int] == u.cpu_array[c as int]);
}

/// The running thread of `d` records no syscall progress before and after a check step, which touches no lock but the
/// cpu's own, no pagetable, and no other cpu; `d` is inside the check after the hold and outside after the other steps.
pub proof fn offline_step_implies_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires
        kernel_u_ownership_wf(u), kill_world_inv(u), locked_cpus_in_step(u), offline_label(l), labeled_step(l, u, u2, d),
        offline_hold_at_rest(u, l, d),
    ensures
        others_kept(u, u2, d), object_locks_same(u, u2), tables_kept(u, u2), op_in_step_kept(u, u2, d), kill_frame(u, u2, d),
        u.cpu_array[d as int].current_thread is Some ==> cur_thread(u, d).syscall_progress is None,
        u2.cpu_array[d as int].current_thread is Some ==> cur_thread(u2, d).syscall_progress is None,
        u2.cpu_array[d as int].current_thread == u.cpu_array[d as int].current_thread || u2.cpu_array[d as int].current_thread is None,
        index_valid(NUM_CPUS, d), !cpu_outside(u2, d) ==> in_offline_check(u2, d),
{
    reveal(kernel_u_cpu_ownership_wf);
    let ud = u.cpu_array[d as int];
    match l {
        StepLabel::CpuOfflineCheckHold => { reveal(cpu_offline_check_hold_step_pre); reveal(cpu_offline_check_hold_step); },
        StepLabel::CpuOfflineCheck { flushed_default_pcid } => {
            reveal(cpu_offline_check_step_pre); reveal(kernel_u_cpu_went_off_changed);
            assert(thread_wf_at(u.thread_map[ud.current_thread->Some_0]) || ud.current_thread is None);
        },
        StepLabel::CpuOfflineCheckRelease => {
            reveal(cpu_offline_check_release_step_pre); reveal(cpu_offline_check_release_step);
            assert(u.cpu_array[d as int] == ud);
        },
        _ => {},
    }
    assert forall|x: CpuId| #![trigger cpu_kept(u, u2, x)] index_valid(NUM_CPUS, x) && x != d implies cpu_kept(u, u2, x) by {
        let ux = u.cpu_array[x as int];
        if ux.current_thread is Some { assert(u.thread_map[ux.current_thread->Some_0].state == (ThreadState::RUNNING { cpu_id: x })); }
    };
    assert forall|t: RwLockThreadPtr| #![trigger u2.thread_map[t]] u2.thread_map.dom().contains(t) implies thread_kept(u, u2, d, t) by {
        if u.thread_map.dom().contains(t) && u2.thread_map[t] != u.thread_map[t] { assert(thread_wf_view(u2.thread_map[t]) == thread_wf_view(u.thread_map[t])); }
    };
    assert forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u.process_map.dom().contains(p) implies proc_kept(u, u2, d, p) by {};
}
} // verus!
