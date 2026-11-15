//! Round 2: behaviours whose per-cpu invocations follow the syscall trace specifications that the exec contracts
//! ensure, adding `unmap_4k` to the pilot. Explicit-index style.
use vstd::prelude::*;
use crate::*;
use veriflat_map_4k::*;
use veriflat_syscall_mmap_4k::syscall_mmap_4k::syscall_mmap_4k_spec::*;
use veriflat_syscall_unmap_4k::syscall_unmap_4k::syscall_unmap_4k_spec::*;
use veriflat_syscall_new_thread::syscall_new_endpoint::syscall_new_endpoint_spec::*;
use veriflat_syscall_alloc_quota::syscall_alloc_quota::syscall_alloc_quota_spec::*;

verus! {
/// One pilot syscall invocation with its arguments.
pub ghost enum PilotCall { NewEndpoint { ep_idx: EndpointIdx }, AllocQuota4k { amount: usize }, Mmap4k { va: VAddr, range: usize }, Unmap4k { va: VAddr, range: usize } }

/// `t` is a complete trace of `call` on cpu `c` as the syscall's exec contract ensures it, over all results: endpoint
/// creation and quota allocation record their success trace or nothing, `mmap_4k` its success trace entering to read or
/// to fill, its hold-and-release failure trace, or nothing, and `unmap_4k` its success trace or nothing.
pub open spec fn call_trace_ok(call: PilotCall, t: Seq<KernelStep>, c: CpuId) -> bool {
    match call {
        PilotCall::NewEndpoint { ep_idx } => t.len() == 0 || new_endpoint_syscall_trace(t, t[0].old_u, t[1].new_u, c, ep_idx, true),
        PilotCall::AllocQuota4k { amount } => t.len() == 0 || alloc_quota_4k_syscall_trace(t, t[0].old_u, t[0].new_u, c, amount, RetValueType::Success),
        PilotCall::Mmap4k { va, range } => {
            ||| t.len() == 0 || mmap_4k_syscall_trace(t, c, va, range, Mmap4kPhase::Read) || mmap_4k_syscall_trace(t, c, va, range, Mmap4kPhase::Fill)
            ||| mmap_4k_syscall_failure_trace(t, c, va, range)
        },
        PilotCall::Unmap4k { va, range } => t.len() == 0 || unmap_4k_syscall_trace(t, c, va, range),
    }
}

/// The most steps one invocation of `call` records, read off its trace specification.
pub open spec fn call_bound(call: PilotCall) -> nat {
    match call {
        PilotCall::NewEndpoint { ep_idx } => 2,
        PilotCall::AllocQuota4k { amount } => 1,
        PilotCall::Mmap4k { va, range } => 4 * range as nat + 4,
        PilotCall::Unmap4k { va, range } => range as nat + NUM_CPUS as nat + MAX_CONTAINER_TREE_DEPTH as nat + 4,
    }
}

/// `p` is a prefix of a complete trace of `call` on `c`.
pub open spec fn call_prefix_ok(call: PilotCall, p: Seq<KernelStep>, c: CpuId) -> bool {
    exists|t: Seq<KernelStep>| #[trigger] call_trace_ok(call, t, c) && p.len() <= t.len() && p == t.subrange(0, p.len() as int)
}

/// Every complete trace of `call` has at most `call_bound(call)` steps.
pub proof fn call_trace_ok_implies_len_bounded(call: PilotCall, t: Seq<KernelStep>, c: CpuId)
    requires call_trace_ok(call, t, c),
    ensures t.len() <= call_bound(call),
{
    reveal(new_endpoint_syscall_trace); reveal(alloc_quota_4k_syscall_trace); reveal(mmap_4k_syscall_trace); reveal(mmap_4k_syscall_failure_trace);
    reveal(unmap_4k_syscall_trace);
}

/// The steps of `c` at the indices `i..j` as a trace.
pub open spec fn own_trace(b: Execution<Snap>, c: CpuId, i: nat, j: nat) -> Seq<KernelStep>
    decreases j - i,
{
    if j <= i { Seq::empty() }
    else {
        let k = (j - 1) as nat;
        own_trace(b, c, i, k) + if b(k).cpu == c { seq![KernelStep { old_u: b(k).u, new_u: b(j).u }] } else { Seq::empty() }
    }
}

/// The own trace has one step per own step.
pub proof fn own_trace_len_implies_own_steps(b: Execution<Snap>, c: CpuId, i: nat, j: nat)
    ensures own_trace(b, c, i, j).len() == own_steps(b, c, i, j),
    decreases j - i,
{ if j > i { own_trace_len_implies_own_steps(b, c, i, (j - 1) as nat); } }

/// The labels of `unmap_4k`.
pub open spec fn unmap_4k_label(l: StepLabel) -> bool {
    ||| l is Unmap4kEnter || l is Unmap4kLeaf || l is Unmap4kTlbFlush || l is Unmap4kTlbVaFlush
    ||| l is Unmap4kFlushed || l is Unmap4kRefund || l is Unmap4kExit
}

/// The round-1 pilot labels and those of `unmap_4k`.
pub open spec fn traced_label(l: StepLabel) -> bool { pilot_label(l) || unmap_4k_label(l) }

pub open spec fn traced_step(s: Snap, s2: Snap) -> bool { kernel_u_ownership_wf(s.u) && traced_label(s.label) && labeled_step(s.label, s.u, s2.u, s.cpu) }

/// Every step of `b` is a step of a round-1 pilot syscall or of `unmap_4k` from a well-formed state.
pub open spec fn traced_behavior(b: Execution<Snap>) -> bool { forall|i: nat| #[trigger] traced_step(b(i), b(i + 1)) }

/// `c` is inside a 4K unmapping: its cpu is write-locked and its running thread records `Unmap4k` progress.
pub open spec fn in_unmap_4k(u: KernelU, c: CpuId) -> bool {
    &&& index_valid(NUM_CPUS, c)
    &&& u.cpu_array[c as int].lock_state is WriteLocked
    &&& u.cpu_array[c as int].current_thread is Some
    &&& cur_thread(u, c).syscall_progress is Some
    &&& cur_thread(u, c).syscall_progress->Some_0 is Unmap4k
}

pub open spec fn in_traced(u: KernelU, c: CpuId) -> bool { in_pilot(u, c) || in_unmap_4k(u, c) }

/// Some step of `c` inside a traced syscall is enabled.
pub open spec fn traced_next_pre(u: KernelU, c: CpuId) -> bool {
    pilot_next_pre(u, c) || unmap_4k_leaf_step_pre(u, c) || unmap_4k_flush_step_pre(u, c) || unmap_4k_refund_step_pre(u, c)
}

pub open spec fn traced_enabled(c: CpuId) -> spec_fn(KernelU) -> bool { |u: KernelU| in_traced(u, c) && traced_next_pre(u, c) }

/// The steps of `c` from its entry step at `e`, while it stays inside a traced syscall, are a prefix of one complete trace
/// of `call`.
pub open spec fn invocation_conformant(b: Execution<Snap>, c: CpuId, call: PilotCall, e: nat) -> bool {
    forall|j: nat| #![trigger own_trace(b, c, e, j)]
        e < j && (forall|k: nat| #![trigger b(k)] e < k < j ==> in_traced(b(k).u, c)) ==> call_prefix_ok(call, own_trace(b, c, e, j), c)
}

/// Some step of `c` is enabled at every index from `i` at which `c` is inside a traced syscall.
pub open spec fn traced_never_blocked_from(b: Execution<Snap>, c: CpuId, i: nat) -> bool {
    forall|k: nat| #![trigger b(k)] i <= k && in_traced(b(k).u, c) ==> traced_next_pre(b(k).u, c)
}

/// An `unmap_4k` step of another cpu `d` leaves the cpu entry of `c` and its running thread unchanged.
pub proof fn unmap_4k_other_step_implies_cpu_slice_unchanged(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId, c: CpuId)
    requires kernel_u_ownership_wf(u), unmap_4k_label(l), labeled_step(l, u, u2, d), d != c, index_valid(NUM_CPUS, c),
    ensures u2.cpu_array[c as int] == u.cpu_array[c as int], u.cpu_array[c as int].current_thread is Some ==> cur_thread(u2, c) == cur_thread(u, c),
{
    reveal(kernel_u_cpu_ownership_wf);
    let uc = u.cpu_array[c as int];
    let ud = u.cpu_array[d as int];
    match l {
        StepLabel::Unmap4kEnter { range } => { reveal(unmap_4k_enter_step_pre); reveal(unmap_4k_enter_step); },
        StepLabel::Unmap4kLeaf => { reveal(unmap_4k_leaf_step_pre); reveal(unmap_4k_leaf_step); },
        StepLabel::Unmap4kTlbFlush => { reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_tlb_flush_step); reveal(kernel_u_cpu_tlb_cleared); },
        StepLabel::Unmap4kTlbVaFlush => { reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_tlb_va_flush_step); },
        StepLabel::Unmap4kFlushed => { reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_flushed_step); },
        StepLabel::Unmap4kRefund => { reveal(unmap_4k_refund_step_pre); reveal(unmap_4k_refund_step); reveal(kernel_u_container_quota_4k_increased); },
        StepLabel::Unmap4kExit => { reveal(unmap_4k_refund_step_pre); reveal(unmap_4k_exit_step); },
        _ => {},
    }
    if uc.current_thread is Some && ud.current_thread is Some && uc.current_thread == ud.current_thread {
        assert(u.thread_map[uc.current_thread->Some_0].state == (ThreadState::RUNNING { cpu_id: c }));
    }
}

/// A traced step of another cpu `d` leaves the cpu entry of `c` and its running thread unchanged.
pub proof fn traced_other_step_implies_cpu_slice_unchanged(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId, c: CpuId)
    requires kernel_u_ownership_wf(u), traced_label(l), labeled_step(l, u, u2, d), d != c, index_valid(NUM_CPUS, c),
    ensures u2.cpu_array[c as int] == u.cpu_array[c as int], u.cpu_array[c as int].current_thread is Some ==> cur_thread(u2, c) == cur_thread(u, c),
{
    if pilot_label(l) { pilot_other_step_implies_cpu_slice_unchanged(u, u2, l, d, c); } else { unmap_4k_other_step_implies_cpu_slice_unchanged(u, u2, l, d, c); }
}

/// An own traced step of `c` inside `unmap_4k` stays inside it, or is the exit step, which leaves every traced syscall and
/// drops the read hold of `c` on its process's pagetable.
pub proof fn unmap_4k_own_step_implies_stays_or_exits(u: KernelU, u2: KernelU, l: StepLabel, c: CpuId)
    requires kernel_u_ownership_wf(u), traced_label(l), labeled_step(l, u, u2, c), in_unmap_4k(u, c),
    ensures
        in_unmap_4k(u2, c) || ({
            let prc = cur_thread(u, c).owning_proc;
            &&& l is Unmap4kExit
            &&& !in_traced(u2, c)
            &&& !u2.process_map[prc].pagetable->Some_0.lock_state.read_held_by(c)
        }),
{
    reveal(kernel_u_cpu_ownership_wf);
    match l {
        StepLabel::NewEndpointEnter { slot } => { reveal(new_endpoint_enter_step_pre); },
        StepLabel::NewEndpointFinish => { reveal(new_endpoint_finish_step_pre); },
        StepLabel::AllocQuota4k { alloc_amount } => { reveal(alloc_quota_4k_step_pre); },
        StepLabel::Mmap4kHold { range } => { reveal(mmap_4k_hold_step_pre); },
        StepLabel::Mmap4kEnter { range, phase } => { reveal(mmap_4k_enter_step_pre); },
        StepLabel::Mmap4kDirectory => { reveal(mmap_4k_directory_step_pre); },
        StepLabel::Mmap4kDowngrade => { reveal(mmap_4k_downgrade_step_pre); },
        StepLabel::Mmap4kLeaf => { reveal(mmap_4k_leaf_step_pre); },
        StepLabel::Mmap4kExit => { reveal(mmap_4k_exit_step_pre); },
        StepLabel::Mmap4kRelease => { reveal(mmap_4k_release_step_pre); },
        StepLabel::Unmap4kEnter { range } => { reveal(unmap_4k_enter_step_pre); },
        StepLabel::Unmap4kLeaf => { reveal(unmap_4k_leaf_step_pre); reveal(unmap_4k_leaf_step); },
        StepLabel::Unmap4kTlbFlush => { reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_tlb_flush_step); reveal(kernel_u_cpu_tlb_cleared); },
        StepLabel::Unmap4kTlbVaFlush => { reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_tlb_va_flush_step); },
        StepLabel::Unmap4kFlushed => { reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_flushed_step); },
        StepLabel::Unmap4kRefund => { reveal(unmap_4k_refund_step_pre); reveal(unmap_4k_refund_step); reveal(kernel_u_container_quota_4k_increased); },
        StepLabel::Unmap4kExit => { reveal(unmap_4k_refund_step_pre); reveal(unmap_4k_exit_step); },
        _ => {},
    }
}

/// Step bound: while `c` stays inside after entering `call` at `e`, it has taken at most `call_bound(call)` own steps
/// since `e`, whatever the other cpus do; no measure on the user state is involved.
pub proof fn invocation_conformant_implies_own_steps_bounded(b: Execution<Snap>, c: CpuId, call: PilotCall, e: nat, j: nat)
    requires invocation_conformant(b, c, call, e), e < j, forall|k: nat| #![trigger b(k)] e < k < j ==> in_traced(b(k).u, c),
    ensures own_steps(b, c, e, j) <= call_bound(call),
{
    assert(call_prefix_ok(call, own_trace(b, c, e, j), c));
    let t = choose|t: Seq<KernelStep>| #[trigger] call_trace_ok(call, t, c) && own_trace(b, c, e, j).len() <= t.len() && own_trace(b, c, e, j) == t.subrange(0, own_trace(b, c, e, j).len() as int);
    call_trace_ok_implies_len_bounded(call, t, c);
    own_trace_len_implies_own_steps(b, c, e, j);
}

/// From `t`, while `c` has not stepped since `i` and its slice is the one at `i`, weak fairness finds the first own step
/// of `c` at or after `t`.
proof fn traced_fair_enabled_slice_implies_first_own_step(b: Execution<Snap>, c: CpuId, fair: spec_fn(nat) -> nat, i: nat, t: nat) -> (s: nat)
    requires
        traced_behavior(b), index_valid(NUM_CPUS, c), in_traced(b(i).u, c), i <= t <= fair(i),
        weakly_fair_witness(b, c, traced_enabled(c), any_label(), fair),
        forall|k: nat| #![trigger b(k)] i <= k && cpu_slice(b(k).u, c) == cpu_slice(b(i).u, c) ==> traced_next_pre(b(k).u, c),
        forall|k: nat| #![trigger b(k)] i <= k < t ==> b(k).cpu != c && cpu_slice(b(k).u, c) == cpu_slice(b(i).u, c),
        cpu_slice(b(t).u, c) == cpu_slice(b(i).u, c),
    ensures
        t <= s <= fair(i), b(s).cpu == c, cpu_slice(b(s).u, c) == cpu_slice(b(i).u, c), in_traced(b(s).u, c),
        forall|k: nat| #![trigger b(k)] i <= k < s ==> b(k).cpu != c && cpu_slice(b(k).u, c) == cpu_slice(b(i).u, c),
    decreases fair(i) - t,
{
    assert(in_traced(b(t).u, c));
    if b(t).cpu == c { t }
    else {
        assert(fair(i) == fair(i));
        assert(t < fair(i)) by { if t == fair(i) { assert(traced_next_pre(b(t).u, c)); } };
        assert(traced_step(b(t), b(t + 1)));
        traced_other_step_implies_cpu_slice_unchanged(b(t).u, b(t + 1).u, b(t).label, b(t).cpu, c);
        traced_fair_enabled_slice_implies_first_own_step(b, c, fair, i, t + 1)
    }
}

/// Theorem (a) from traces: a cpu `c` that entered `call` at `e`, whose invocation conforms to the trace specification, is
/// inside from `e + 1` to `i`, is never blocked from `i`, and is weakly fair, leaves at the returned `s` within
/// `call_bound(call)` own steps since `e`, staying inside from `i` to `s`.
pub proof fn conformant_never_blocked_fair_implies_leaves_within_call_bound(b: Execution<Snap>, c: CpuId, call: PilotCall, e: nat, fair: spec_fn(nat) -> nat,
    i: nat) -> (s: nat)
    requires
        traced_behavior(b), invocation_conformant(b, c, call, e), e < i, forall|k: nat| #![trigger b(k)] e < k <= i ==> in_traced(b(k).u, c),
        traced_never_blocked_from(b, c, i), weakly_fair_witness(b, c, traced_enabled(c), any_label(), fair),
    ensures
        i <= s, b(s).cpu == c, !in_traced(b(s + 1).u, c), own_steps(b, c, e, s + 1) <= call_bound(call),
        forall|k: nat| #![trigger b(k)] i <= k <= s ==> in_traced(b(k).u, c),
    decreases call_bound(call) - own_steps(b, c, e, i),
{
    invocation_conformant_implies_own_steps_bounded(b, c, call, e, i);
    assert forall|k: nat| #![trigger b(k)] i <= k && cpu_slice(b(k).u, c) == cpu_slice(b(i).u, c) implies traced_next_pre(b(k).u, c) by { assert(in_traced(b(k).u, c)); };
    let s0 = traced_fair_enabled_slice_implies_first_own_step(b, c, fair, i, i);
    assert forall|k: nat| #![trigger b(k)] e < k < s0 + 1 implies in_traced(b(k).u, c) by { if k > i { assert(cpu_slice(b(k).u, c) == cpu_slice(b(i).u, c)); } };
    invocation_conformant_implies_own_steps_bounded(b, c, call, e, s0 + 1);
    no_step_implies_own_steps_zero(b, c, i, s0);
    own_steps_split_implies_sum(b, c, e, i, s0);
    if !in_traced(b(s0 + 1).u, c) {
        assert forall|k: nat| #![trigger b(k)] i <= k <= s0 implies in_traced(b(k).u, c) by { assert(cpu_slice(b(k).u, c) == cpu_slice(b(i).u, c)); };
        s0
    } else {
        assert forall|k: nat| #![trigger b(k)] e < k <= s0 + 1 implies in_traced(b(k).u, c) by { if k > i && k <= s0 { assert(cpu_slice(b(k).u, c) == cpu_slice(b(i).u, c)); } };
        let s = conformant_never_blocked_fair_implies_leaves_within_call_bound(b, c, call, e, fair, s0 + 1);
        assert forall|k: nat| #![trigger b(k)] i <= k <= s implies in_traced(b(k).u, c) by { if k <= s0 { assert(cpu_slice(b(k).u, c) == cpu_slice(b(i).u, c)); } };
        s
    }
}

/// While `c` stays inside traced syscalls from `i` to `s`, it stays inside `unmap_4k` once there.
proof fn traced_inside_implies_unmap_4k_kept(b: Execution<Snap>, c: CpuId, i: nat, s: nat)
    requires traced_behavior(b), i <= s, in_unmap_4k(b(i).u, c), forall|k: nat| #![trigger b(k)] i <= k <= s ==> in_traced(b(k).u, c),
    ensures in_unmap_4k(b(s).u, c),
    decreases s - i,
{
    if s > i {
        let p = (s - 1) as nat;
        traced_inside_implies_unmap_4k_kept(b, c, i, p);
        assert(traced_step(b(p), b(p + 1)) && in_traced(b(s).u, c));
        if b(p).cpu == c { unmap_4k_own_step_implies_stays_or_exits(b(p).u, b(s).u, b(p).label, c); }
        else { traced_other_step_implies_cpu_slice_unchanged(b(p).u, b(s).u, b(p).label, b(p).cpu, c); }
    }
}

/// Theorem (b) from traces, for `unmap_4k` holders: a cpu `h` inside `unmap_4k` at `i`, which entered `range` pages at
/// `e`, conforms to the trace specification, is never blocked from `i`, and is weakly fair, exits at the returned `s`
/// after at most `range + NUM_CPUS + MAX_CONTAINER_TREE_DEPTH + 4` own steps since `e`, and from `s + 1` no longer holds
/// its pagetable for reading.
pub proof fn conformant_unmap_4k_holder_fair_implies_read_hold_released(b: Execution<Snap>, h: CpuId, va: VAddr, range: usize, e: nat,
    fair: spec_fn(nat) -> nat, i: nat) -> (s: nat)
    requires
        traced_behavior(b), invocation_conformant(b, h, PilotCall::Unmap4k { va, range }, e), e < i, forall|k: nat| #![trigger b(k)] e < k <= i ==> in_traced(b(k).u, h),
        in_unmap_4k(b(i).u, h), traced_never_blocked_from(b, h, i), weakly_fair_witness(b, h, traced_enabled(h), any_label(), fair),
    ensures
        i <= s, b(s).cpu == h, b(s).label is Unmap4kExit, own_steps(b, h, e, s + 1) <= range + NUM_CPUS + MAX_CONTAINER_TREE_DEPTH + 4,
        !b(s + 1).u.process_map[cur_thread(b(s).u, h).owning_proc].pagetable->Some_0.lock_state.read_held_by(h),
{
    let s = conformant_never_blocked_fair_implies_leaves_within_call_bound(b, h, PilotCall::Unmap4k { va, range }, e, fair, i);
    traced_inside_implies_unmap_4k_kept(b, h, i, s);
    assert(traced_step(b(s), b(s + 1)));
    unmap_4k_own_step_implies_stays_or_exits(b(s).u, b(s + 1).u, b(s).label, h);
    s
}
} // verus!
