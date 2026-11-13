//! Round 5: cpu hotplug requests `cpu_offline_request`, `cpu_online`, `cpu_offline_request_child`, and
//! `cpu_online_child`. Each is one step from an unlocked cpu, so it has no inside and is never blocked; its call records at
//! most one step. Bringing a cpu online changes only the entry of an Off, unlocked cpu.
use vstd::prelude::*;
use crate::*;
use crate::frame::*;
use crate::pagetable_locks::*;
use veriflat_syscall_cpu_hotplug::syscall_cpu_hotplug::syscall_cpu_hotplug_spec::*;

verus! {
pub open spec fn cpu_label(l: StepLabel) -> bool { l is CpuOfflineRequest || l is CpuOnline || l is CpuOfflineRequestChild || l is CpuOnlineChild }

/// One call of this family with its target cpu.
pub ghost enum CpuCall { OfflineRequest { target: CpuId }, Online { target: CpuId }, OfflineRequestChild { target: CpuId }, OnlineChild { target: CpuId } }

/// `t` is a complete trace of `call` on `c` as its exec contract ensures it: the success step or nothing.
pub open spec fn cpu_call_trace_ok(call: CpuCall, t: Seq<KernelStep>, c: CpuId) -> bool {
    t.len() == 0 || match call {
        CpuCall::OfflineRequest { target } => cpu_offline_request_syscall_trace(t, t[0].old_u, t[0].new_u, c, target, RetValueType::Success),
        CpuCall::Online { target } => cpu_online_syscall_trace(t, t[0].old_u, t[0].new_u, c, target, RetValueType::Success),
        CpuCall::OfflineRequestChild { target } => cpu_offline_request_child_syscall_trace(t, t[0].old_u, t[0].new_u, c, target, RetValueType::Success),
        CpuCall::OnlineChild { target } => cpu_online_child_syscall_trace(t, t[0].old_u, t[0].new_u, c, target, RetValueType::Success),
    }
}

pub open spec fn cpu_call_bound(call: CpuCall) -> nat { 1 }

pub proof fn cpu_call_trace_ok_implies_len_bounded(call: CpuCall, t: Seq<KernelStep>, c: CpuId)
    requires cpu_call_trace_ok(call, t, c),
    ensures t.len() <= cpu_call_bound(call),
{
    reveal(cpu_offline_request_syscall_trace); reveal(cpu_online_syscall_trace); reveal(cpu_offline_request_child_syscall_trace); reveal(cpu_online_child_syscall_trace);
}

/// A hotplug request step of `d` keeps every other write-locked cpu, every lock, and every pagetable; `d` is unlocked
/// before and after.
pub proof fn cpu_step_implies_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), cpu_label(l), labeled_step(l, u, u2, d),
    ensures single_step_frame(u, u2, d),
{
    match l {
        StepLabel::CpuOfflineRequest { target } => { reveal(cpu_offline_request_step_pre); reveal(kernel_u_cpu_offline_request_changed); },
        StepLabel::CpuOnline { target } => { reveal(cpu_online_step_pre); reveal(kernel_u_cpu_online_changed); },
        StepLabel::CpuOfflineRequestChild { target } => { reveal(cpu_offline_request_child_step_pre); reveal(kernel_u_cpu_offline_request_changed); },
        StepLabel::CpuOnlineChild { target } => { reveal(cpu_online_child_step_pre); reveal(kernel_u_cpu_online_changed); },
        _ => {},
    }
    assert forall|x: CpuId| #![trigger cpu_kept(u, u2, x)] index_valid(NUM_CPUS, x) && x != d implies cpu_kept(u, u2, x) by {};
}
} // verus!
