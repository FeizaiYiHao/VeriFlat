//! Round 5: the quota moves `alloc_thread_quota_4k`, `alloc_quota_2m`, `alloc_thread_quota_2m`, `alloc_quota_1g`, and
//! `alloc_thread_quota_1g` (`alloc_quota_4k` is a round-1 pilot label). Each is one step from an unlocked cpu, so it has no
//! inside and is never blocked; its call records at most one step.
use vstd::prelude::*;
use crate::*;
use crate::frame::*;
use crate::pagetable_locks::*;
use veriflat_syscall_alloc_quota::syscall_alloc_quota::{syscall_alloc_quota_spec::*, syscall_alloc_quota_1g_spec::*};

verus! {
/// The labels of this family.
pub open spec fn alloc_label(l: StepLabel) -> bool {
    l is AllocThreadQuota4k || l is AllocQuota2m || l is AllocThreadQuota2m || l is AllocQuota1g || l is AllocThreadQuota1g
}

/// One call of this family with its argument.
pub ghost enum AllocCall { ThreadQuota4k { amount: usize }, Quota2m { amount: usize }, ThreadQuota2m { amount: usize }, Quota1g { amount: usize }, ThreadQuota1g { amount: usize } }

/// `t` is a complete trace of `call` on `c` as its exec contract ensures it: the success step or nothing.
pub open spec fn alloc_call_trace_ok(call: AllocCall, t: Seq<KernelStep>, c: CpuId) -> bool {
    t.len() == 0 || match call {
        AllocCall::ThreadQuota4k { amount } => alloc_thread_quota_4k_syscall_trace(t, t[0].old_u, t[0].new_u, c, amount, RetValueType::Success),
        AllocCall::Quota2m { amount } => alloc_quota_2m_syscall_trace(t, t[0].old_u, t[0].new_u, c, amount, RetValueType::Success),
        AllocCall::ThreadQuota2m { amount } => alloc_thread_quota_2m_syscall_trace(t, t[0].old_u, t[0].new_u, c, amount, RetValueType::Success),
        AllocCall::Quota1g { amount } => alloc_quota_1g_syscall_trace(t, t[0].old_u, t[0].new_u, c, amount, RetValueType::Success),
        AllocCall::ThreadQuota1g { amount } => alloc_thread_quota_1g_syscall_trace(t, t[0].old_u, t[0].new_u, c, amount, RetValueType::Success),
    }
}

pub open spec fn alloc_call_bound(call: AllocCall) -> nat { 1 }

/// Every complete trace of an allocation has at most one step.
pub proof fn alloc_call_trace_ok_implies_len_bounded(call: AllocCall, t: Seq<KernelStep>, c: CpuId)
    requires alloc_call_trace_ok(call, t, c),
    ensures t.len() <= alloc_call_bound(call),
{
    reveal(alloc_thread_quota_4k_syscall_trace); reveal(alloc_quota_2m_syscall_trace); reveal(alloc_thread_quota_2m_syscall_trace);
    reveal(alloc_quota_1g_syscall_trace); reveal(alloc_thread_quota_1g_syscall_trace);
}

/// An allocation step of `d` keeps every other cpu, every lock, and every pagetable; `d` is unlocked before and after.
pub proof fn alloc_step_implies_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), alloc_label(l), labeled_step(l, u, u2, d),
    ensures single_step_frame(u, u2, d),
{
    reveal(kernel_u_cpu_ownership_wf);
    match l {
        StepLabel::AllocThreadQuota4k { alloc_amount } => { reveal(alloc_thread_quota_4k_step_pre); reveal(kernel_u_only_process2thread_quota_4k_changed); },
        StepLabel::AllocQuota2m { alloc_amount } => { reveal(alloc_quota_2m_step_pre); reveal(kernel_u_only_process_quota_2m_changed); },
        StepLabel::AllocThreadQuota2m { alloc_amount } => { reveal(alloc_thread_quota_2m_step_pre); reveal(kernel_u_only_process2thread_quota_2m_changed); },
        StepLabel::AllocQuota1g { alloc_amount } => { reveal(alloc_quota_1g_step_pre); reveal(kernel_u_only_process_quota_1g_changed); },
        StepLabel::AllocThreadQuota1g { alloc_amount } => { reveal(alloc_thread_quota_1g_step_pre); reveal(kernel_u_only_process2thread_quota_1g_changed); },
        _ => {},
    }
    let ud = u.cpu_array[d as int];
    assert forall|x: CpuId| #![trigger cpu_kept(u, u2, x)] index_valid(NUM_CPUS, x) && x != d implies cpu_kept(u, u2, x) by {
        let ux = u.cpu_array[x as int];
        if ux.current_thread is Some && ux.current_thread == ud.current_thread { assert(u.thread_map[ux.current_thread->Some_0].state == (ThreadState::RUNNING { cpu_id: x })); }
    };
}
} // verus!
