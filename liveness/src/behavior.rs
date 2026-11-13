use vstd::prelude::*;
use crate::*;

verus! {
/// The user state at one index of a behaviour, with the label and cpu of the step taken from it.
pub ghost struct Snap { pub u: KernelU, pub label: StepLabel, pub cpu: CpuId }

/// An infinite execution.
pub type Execution<T> = spec_fn(nat) -> T;

/// The labels of the pilot syscalls `new_endpoint`, `mmap_4k`, and `alloc_quota_4k`.
pub open spec fn pilot_label(l: StepLabel) -> bool {
    ||| l is NewEndpointEnter || l is NewEndpointFinish || l is AllocQuota4k
    ||| l is Mmap4kHold || l is Mmap4kEnter || l is Mmap4kDirectory || l is Mmap4kDowngrade || l is Mmap4kLeaf || l is Mmap4kExit || l is Mmap4kRelease
}

/// `s2` follows `s` by the pilot step `s` records, from a well-formed state.
pub open spec fn pilot_step(s: Snap, s2: Snap) -> bool { kernel_u_ownership_wf(s.u) && pilot_label(s.label) && labeled_step(s.label, s.u, s2.u, s.cpu) }

/// Every step of `b` is a pilot step from a well-formed state.
pub open spec fn pilot_behavior(b: Execution<Snap>) -> bool { forall|i: nat| #[trigger] pilot_step(b(i), b(i + 1)) }

/// Weak fairness of cpu `c` as an explicit witness: from every index `i`, `fair(i)` is a later index at which `c` takes a
/// step whose label satisfies `taken`, or at which the step is disabled.
pub open spec fn weakly_fair_witness(b: Execution<Snap>, c: CpuId, enabled: spec_fn(KernelU) -> bool, taken: spec_fn(StepLabel) -> bool, fair: spec_fn(nat) -> nat) -> bool {
    forall|i: nat| #![trigger fair(i)] i <= fair(i) && ((b(fair(i)).cpu == c && taken(b(fair(i)).label)) || !enabled(b(fair(i)).u))
}

/// Every label.
pub open spec fn any_label() -> spec_fn(StepLabel) -> bool { |l: StepLabel| true }

/// The number of steps of `c` at the indices `i..j`.
pub open spec fn own_steps(b: Execution<Snap>, c: CpuId, i: nat, j: nat) -> nat
    decreases j - i,
{
    if j <= i { 0 } else { own_steps(b, c, i, (j - 1) as nat) + if b((j - 1) as nat).cpu == c { 1nat } else { 0nat } }
}

/// `c` takes no step at `i..j`.
pub proof fn no_step_implies_own_steps_zero(b: Execution<Snap>, c: CpuId, i: nat, j: nat)
    requires forall|k: nat| #![trigger b(k)] i <= k < j ==> b(k).cpu != c,
    ensures own_steps(b, c, i, j) == 0,
    decreases j - i,
{ if j > i { no_step_implies_own_steps_zero(b, c, i, (j - 1) as nat); } }

/// Own steps add up over consecutive intervals.
pub proof fn own_steps_split_implies_sum(b: Execution<Snap>, c: CpuId, i: nat, j: nat, k: nat)
    requires i <= j <= k,
    ensures own_steps(b, c, i, k) == own_steps(b, c, i, j) + own_steps(b, c, j, k),
    decreases k - j,
{ if k > j { own_steps_split_implies_sum(b, c, i, j, (k - 1) as nat); } }

/// The first step of `c` at `t..n`, if any.
pub proof fn first_own_step_in(b: Execution<Snap>, c: CpuId, t: nat, n: nat) -> (r: Option<nat>)
    ensures
        r is Some ==> t <= r->Some_0 < n && b(r->Some_0).cpu == c,
        forall|m: nat| #![trigger b(m)] t <= m < n && (r is Some ==> m < r->Some_0) ==> b(m).cpu != c,
    decreases n - t,
{ if t >= n { None } else if b(t).cpu == c { Some(t) } else { first_own_step_in(b, c, t + 1, n) } }

/// `c` takes no step at `i..k`.
pub open spec fn no_own_step(b: Execution<Snap>, c: CpuId, i: nat, k: nat) -> bool { forall|m: nat| #![trigger b(m)] i <= m < k ==> b(m).cpu != c }
} // verus!
