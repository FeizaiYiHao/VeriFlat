//! Round 2: lock consistency from a quiescent start, and waiters under bounded contention, over the round-1 pilot
//! behaviours. Explicit-index style.
use vstd::prelude::*;
use crate::*;
use crate::route_explicit::*;
use veriflat_syscall_new_thread::syscall_new_endpoint::syscall_new_endpoint_spec::*;
use veriflat_syscall_alloc_quota::syscall_alloc_quota::syscall_alloc_quota_spec::*;

verus! {
/// No cpu is inside endpoint creation and every container is unlocked without owner, as after boot.
pub open spec fn pilot_quiescent(u: KernelU) -> bool {
    &&& forall|x: CpuId| #![trigger u.cpu_array[x as int]] !in_new_endpoint(u, x)
    &&& forall|ctn: RwLockContainerPtr| #![trigger u.container_map[ctn]] container_unlocked(u, ctn)
}

/// Container `ctn` is unlocked without owner, or write-held with an owner by the cpu that is inside endpoint creation in it.
pub open spec fn container_lock_held(u: KernelU, ctn: RwLockContainerPtr) -> bool {
    let x = u.container_map[ctn].lock_state->WriteLocked_writer;
    ||| container_unlocked(u, ctn)
    ||| u.container_map[ctn].lock_state is WriteLocked && u.container_map[ctn].lock_process_owner is Some && in_new_endpoint(u, x) && u.cpu_array[x as int].owning_container == ctn
}

/// A quiescent state satisfies both lock invariants.
pub proof fn pilot_quiescent_implies_lock_invariants(u: KernelU, ctn: RwLockContainerPtr)
    requires pilot_quiescent(u),
    ensures new_endpoint_locks_held(u), container_lock_held(u, ctn), container_owner_held(u, ctn),
{ assert(container_unlocked(u, ctn)); }

/// Every pilot step keeps `container_lock_held` for container `ctn`.
pub proof fn pilot_step_implies_container_lock_held(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId, ctn: RwLockContainerPtr)
    requires kernel_u_ownership_wf(u), container_lock_held(u, ctn), pilot_label(l), labeled_step(l, u, u2, d),
    ensures container_lock_held(u2, ctn),
{
    pilot_own_step_implies_measure_decreases(u, u2, l, d);
    pilot_step_implies_container_lock_frame(u, u2, l, d, ctn);
    let x = u.container_map[ctn].lock_state->WriteLocked_writer;
    if !container_unlocked(u, ctn) && x != d { pilot_other_step_implies_cpu_slice_unchanged(u, u2, l, d, x); }
}

/// `container_lock_held` of `ctn` at `t` holds at every later index.
pub proof fn pilot_behavior_implies_container_lock_held_kept(b: Execution<Snap>, ctn: RwLockContainerPtr, t: nat, k: nat)
    requires pilot_behavior(b), t <= k, container_lock_held(b(t).u, ctn),
    ensures container_lock_held(b(k).u, ctn),
    decreases k - t,
{
    if k > t {
        let j = (k - 1) as nat;
        pilot_behavior_implies_container_lock_held_kept(b, ctn, t, j);
        assert(pilot_step(b(j), b(j + 1)));
        pilot_step_implies_container_lock_held(b(j).u, b(k).u, b(j).label, b(j).cpu, ctn);
    }
}

/// Index `k` is an entry into endpoint creation in container `ctn`.
pub open spec fn container_entry(b: Execution<Snap>, ctn: RwLockContainerPtr, k: nat) -> bool {
    b(k).label is NewEndpointEnter && b(k).u.cpu_array[b(k).cpu as int].owning_container == ctn
}

/// The number of entries into endpoint creation in `ctn` at the indices `i..j`.
pub open spec fn container_entries(b: Execution<Snap>, ctn: RwLockContainerPtr, i: nat, j: nat) -> nat
    decreases j - i,
{
    if j <= i { 0 } else { container_entries(b, ctn, i, (j - 1) as nat) + if container_entry(b, ctn, (j - 1) as nat) { 1nat } else { 0nat } }
}

/// Bounded contention on `ctn`: from `i` on, at most `bound` steps enter endpoint creation in `ctn`.
pub open spec fn bounded_contention(b: Execution<Snap>, ctn: RwLockContainerPtr, i: nat, bound: nat) -> bool {
    forall|j: nat| #![trigger container_entries(b, ctn, i, j)] i <= j ==> container_entries(b, ctn, i, j) <= bound
}

pub proof fn container_entries_split_implies_sum(b: Execution<Snap>, ctn: RwLockContainerPtr, i: nat, j: nat, k: nat)
    requires i <= j <= k,
    ensures container_entries(b, ctn, i, k) == container_entries(b, ctn, i, j) + container_entries(b, ctn, j, k),
    decreases k - j,
{ if k > j { container_entries_split_implies_sum(b, ctn, i, j, (k - 1) as nat); } }

pub proof fn no_entry_implies_container_entries_zero(b: Execution<Snap>, ctn: RwLockContainerPtr, i: nat, j: nat)
    requires forall|k: nat| #![trigger b(k)] i <= k < j ==> !container_entry(b, ctn, k),
    ensures container_entries(b, ctn, i, j) == 0,
    decreases j - i,
{ if j > i { no_entry_implies_container_entries_zero(b, ctn, i, (j - 1) as nat); } }

/// Without entries into endpoint creation in `ctn` at `t..k`, an unlocked `ctn` stays unlocked: no cpu inside endpoint
/// creation holds it, so no finish step unlocks it from under a holder either.
proof fn no_entry_implies_container_unlocked_kept(b: Execution<Snap>, ctn: RwLockContainerPtr, i: nat, t: nat, k: nat)
    requires
        pilot_behavior(b), i <= t <= k, new_endpoint_locks_held(b(i).u), container_unlocked(b(t).u, ctn),
        forall|m: nat| #![trigger b(m)] t <= m < k ==> !container_entry(b, ctn, m),
    ensures container_unlocked(b(k).u, ctn),
    decreases k - t,
{
    if k > t {
        let p = (k - 1) as nat;
        no_entry_implies_container_unlocked_kept(b, ctn, i, t, p);
        assert(pilot_step(b(p), b(p + 1)) && !container_entry(b, ctn, p));
        pilot_behavior_implies_new_endpoint_locks_held_kept(b, i, p);
        pilot_step_implies_container_lock_frame(b(p).u, b(k).u, b(p).label, b(p).cpu, ctn);
        if b(p).label is NewEndpointFinish {
            reveal(new_endpoint_finish_step_pre);
            assert(in_new_endpoint(b(p).u, b(p).cpu) && b(p).u.cpu_array[b(p).cpu as int] == b(p).u.cpu_array[b(p).cpu as int]);
        }
    }
}

/// The first entry into endpoint creation in `ctn` at or after `t`, given one at `k`.
proof fn first_container_entry(b: Execution<Snap>, ctn: RwLockContainerPtr, t: nat, k: nat) -> (f: nat)
    requires t <= k, container_entry(b, ctn, k),
    ensures t <= f <= k, container_entry(b, ctn, f), forall|m: nat| #![trigger b(m)] t <= m < f ==> !container_entry(b, ctn, m),
    decreases k - t,
{ if container_entry(b, ctn, t) { t } else { first_container_entry(b, ctn, t + 1, k) } }

/// From `t`, bounded contention and fairness of every cpu reach an index from which `ctn` stays unlocked.
proof fn bounded_contention_implies_unlocked_forever_from(b: Execution<Snap>, ctn: RwLockContainerPtr, bound: nat, fair: spec_fn(CpuId) -> spec_fn(nat) -> nat,
    i: nat, t: nat) -> (j: nat)
    requires
        pilot_behavior(b), i <= t, new_endpoint_locks_held(b(i).u), container_lock_held(b(t).u, ctn), bounded_contention(b, ctn, i, bound),
        forall|x: CpuId| #![trigger fair(x)] index_valid(NUM_CPUS, x) ==> weakly_fair_witness(b, x, pilot_enabled(x), any_label(), fair(x)),
    ensures t <= j, forall|k: nat| #![trigger b(k)] j <= k ==> container_unlocked(b(k).u, ctn),
    decreases bound - container_entries(b, ctn, i, t),
{
    assert(container_entries(b, ctn, i, t) <= bound);
    let t1 = if container_unlocked(b(t).u, ctn) { t } else {
        let x = b(t).u.container_map[ctn].lock_state->WriteLocked_writer;
        assert forall|k: nat| #![trigger b(k)] t <= k && in_new_endpoint(b(k).u, x) implies new_endpoint_finish_step_pre(b(k).u, x) by {
            new_endpoint_locks_held_implies_never_blocked(b, i, k, x);
        };
        assert(fair(x) == fair(x));
        new_endpoint_holder_fair_implies_container_released(b, x, fair(x), t) + 1
    };
    container_entries_split_implies_sum(b, ctn, i, t, t1);
    if forall|k: nat| #![trigger b(k)] t1 <= k ==> !container_entry(b, ctn, k) {
        assert forall|k: nat| #![trigger b(k)] t1 <= k implies container_unlocked(b(k).u, ctn) by { no_entry_implies_container_unlocked_kept(b, ctn, i, t1, k); };
        t1
    } else {
        let k0 = choose|k: nat| #![trigger b(k)] t1 <= k && container_entry(b, ctn, k);
        let f = first_container_entry(b, ctn, t1, k0);
        no_entry_implies_container_entries_zero(b, ctn, t1, f);
        container_entries_split_implies_sum(b, ctn, i, t1, f);
        assert(container_entries(b, ctn, i, f + 1) <= bound);
        pilot_behavior_implies_container_lock_held_kept(b, ctn, t, f + 1);
        bounded_contention_implies_unlocked_forever_from(b, ctn, bound, fair, i, f + 1)
    }
}

/// Theorem (b3), release under bounded contention: with the lock invariants at `i` (for example from a quiescent state),
/// every cpu weakly fair, and at most `bound` entries into endpoint creation in `ctn` from `i` on, there is an index `j`
/// from which `ctn` stays unlocked without owner, so no `alloc_quota_4k` started from `j` in `ctn` meets a lock-order
/// conflict.
pub proof fn bounded_contention_and_fairness_implies_container_unlocked_forever(b: Execution<Snap>, ctn: RwLockContainerPtr, bound: nat,
    fair: spec_fn(CpuId) -> spec_fn(nat) -> nat, i: nat) -> (j: nat)
    requires
        pilot_behavior(b), new_endpoint_locks_held(b(i).u), container_lock_held(b(i).u, ctn), bounded_contention(b, ctn, i, bound),
        forall|x: CpuId| #![trigger fair(x)] index_valid(NUM_CPUS, x) ==> weakly_fair_witness(b, x, pilot_enabled(x), any_label(), fair(x)),
    ensures
        i <= j, forall|k: nat| #![trigger b(k)] j <= k ==> container_unlocked(b(k).u, ctn),
        forall|k: nat, depth: usize| #![trigger lock_order_conflict(b(k).u, ctn, depth)] j <= k ==> !lock_order_conflict(b(k).u, ctn, depth),
{
    let j = bounded_contention_implies_unlocked_forever_from(b, ctn, bound, fair, i, i);
    assert forall|k: nat, depth: usize| #![trigger lock_order_conflict(b(k).u, ctn, depth)] j <= k implies !lock_order_conflict(b(k).u, ctn, depth) by {
        assert(container_unlocked(b(k).u, ctn));
    };
    j
}

/// Cpu `w` can enter endpoint creation at descriptor `ep_idx`.
pub open spec fn new_endpoint_enter_enabled(w: CpuId, ep_idx: EndpointIdx) -> spec_fn(KernelU) -> bool { |u: KernelU| new_endpoint_enter_step_pre(u, w, ep_idx) }

/// Entering endpoint creation at descriptor `ep_idx`.
pub open spec fn new_endpoint_enter_taken(ep_idx: EndpointIdx) -> spec_fn(StepLabel) -> bool { |l: StepLabel| l == StepLabel::NewEndpointEnter { slot: ep_idx } }

/// Why round 2 stated the endpoint-creation waiter wrongly: with every entry into `ctn` counted, `w`'s entry enabled at
/// every index from `i` at which `ctn` is unlocked, and `w`'s own container `ctn`, the hypotheses contradict each other,
/// since `ctn` stays unlocked from some index on and fairness then makes `w` enter and lock it.
pub proof fn waiter_enabled_forever_and_bounded_contention_implies_false(b: Execution<Snap>, ctn: RwLockContainerPtr, bound: nat,
    fair: spec_fn(CpuId) -> spec_fn(nat) -> nat, w: CpuId, ep_idx: EndpointIdx, fair_w: spec_fn(nat) -> nat, i: nat)
    requires
        pilot_behavior(b), new_endpoint_locks_held(b(i).u), container_lock_held(b(i).u, ctn), bounded_contention(b, ctn, i, bound),
        forall|x: CpuId| #![trigger fair(x)] index_valid(NUM_CPUS, x) ==> weakly_fair_witness(b, x, pilot_enabled(x), any_label(), fair(x)),
        forall|k: nat| #![trigger b(k)] i <= k && container_unlocked(b(k).u, ctn) ==> new_endpoint_enter_step_pre(b(k).u, w, ep_idx),
        weakly_fair_witness(b, w, new_endpoint_enter_enabled(w, ep_idx), new_endpoint_enter_taken(ep_idx), fair_w),
        forall|k: nat| #![trigger b(k)] i <= k ==> b(k).u.cpu_array[w as int].owning_container == ctn,
    ensures false,
{
    let j = bounded_contention_and_fairness_implies_container_unlocked_forever(b, ctn, bound, fair, i);
    assert(fair_w(j) == fair_w(j));
    let k = fair_w(j);
    assert(container_unlocked(b(k).u, ctn) && pilot_step(b(k), b(k + 1)));
    pilot_step_implies_container_lock_frame(b(k).u, b(k + 1).u, b(k).label, w, ctn);
    assert(container_unlocked(b(k + 1).u, ctn));
}

/// Index `k` is an entry into endpoint creation in `ctn` by a cpu other than the waiter `w`.
pub open spec fn other_container_entry(b: Execution<Snap>, ctn: RwLockContainerPtr, w: CpuId, k: nat) -> bool { container_entry(b, ctn, k) && b(k).cpu != w }

/// The number of entries into endpoint creation in `ctn` by cpus other than `w` at the indices `i..j`.
pub open spec fn other_container_entries(b: Execution<Snap>, ctn: RwLockContainerPtr, w: CpuId, i: nat, j: nat) -> nat
    decreases j - i,
{
    if j <= i { 0 } else { other_container_entries(b, ctn, w, i, (j - 1) as nat) + if other_container_entry(b, ctn, w, (j - 1) as nat) { 1nat } else { 0nat } }
}

/// Bounded contention on `ctn` against the waiter `w`: from `i` on, cpus other than `w` enter endpoint creation in `ctn`
/// at most `bound` times; `w`'s own entries are not counted.
pub open spec fn bounded_other_contention(b: Execution<Snap>, ctn: RwLockContainerPtr, w: CpuId, i: nat, bound: nat) -> bool {
    forall|j: nat| #![trigger other_container_entries(b, ctn, w, i, j)] i <= j ==> other_container_entries(b, ctn, w, i, j) <= bound
}

pub proof fn other_container_entries_split_implies_sum(b: Execution<Snap>, ctn: RwLockContainerPtr, w: CpuId, i: nat, j: nat, k: nat)
    requires i <= j <= k,
    ensures other_container_entries(b, ctn, w, i, k) == other_container_entries(b, ctn, w, i, j) + other_container_entries(b, ctn, w, j, k),
    decreases k - j,
{ if k > j { other_container_entries_split_implies_sum(b, ctn, w, i, j, (k - 1) as nat); } }

/// The first index at `t..n` at which the waiter `w` steps or another cpu enters endpoint creation in `ctn`, if any.
proof fn first_waiter_event(b: Execution<Snap>, ctn: RwLockContainerPtr, w: CpuId, t: nat, n: nat) -> (r: Option<nat>)
    ensures
        r is Some ==> t <= r->Some_0 < n && (b(r->Some_0).cpu == w || other_container_entry(b, ctn, w, r->Some_0)),
        forall|m: nat| #![trigger b(m)] t <= m < n && (r is Some ==> m < r->Some_0) ==> b(m).cpu != w && !other_container_entry(b, ctn, w, m),
    decreases n - t,
{
    if t >= n { None } else if b(t).cpu == w || other_container_entry(b, ctn, w, t) { Some(t) } else { first_waiter_event(b, ctn, w, t + 1, n) }
}

/// From `t`, at which a cpu inside endpoint creation holds `ctn`, the returned index is either the first step of `w` at or
/// after `t` (`true`) or, with no step of `w` before it, one at which `ctn` is unlocked (`false`).
proof fn locked_container_implies_released_or_waiter_steps(b: Execution<Snap>, ctn: RwLockContainerPtr, fair: spec_fn(CpuId) -> spec_fn(nat) -> nat, w: CpuId,
    i: nat, t: nat) -> (r: (nat, bool))
    requires
        pilot_behavior(b), i <= t, new_endpoint_locks_held(b(i).u), container_lock_held(b(t).u, ctn), !container_unlocked(b(t).u, ctn),
        forall|x: CpuId| #![trigger fair(x)] index_valid(NUM_CPUS, x) ==> weakly_fair_witness(b, x, pilot_enabled(x), any_label(), fair(x)),
    ensures
        t <= r.0, forall|m: nat| #![trigger b(m)] t <= m < r.0 ==> b(m).cpu != w,
        r.1 ==> b(r.0).cpu == w, !r.1 ==> t < r.0 && container_unlocked(b(r.0).u, ctn),
{
    let x = b(t).u.container_map[ctn].lock_state->WriteLocked_writer;
    assert forall|k: nat| #![trigger b(k)] t <= k && in_new_endpoint(b(k).u, x) implies new_endpoint_finish_step_pre(b(k).u, x) by {
        new_endpoint_locks_held_implies_never_blocked(b, i, k, x);
    };
    assert(fair(x) == fair(x));
    let s = new_endpoint_holder_fair_implies_container_released(b, x, fair(x), t);
    match first_own_step_in(b, w, t, s + 1) { Some(f) => (f, true), None => (s + 1, false) }
}

/// From `t`, at which `ctn` is unlocked and `w` has not stepped since `i`, the returned index is either the first step of `w`
/// at or after `t` (`true`), found by its weak fairness, or an entry into endpoint creation in `ctn` by another cpu before
/// any step of `w` (`false`).
proof fn unlocked_container_implies_waiter_steps_or_other_entry(b: Execution<Snap>, ctn: RwLockContainerPtr, w: CpuId, enabled: spec_fn(KernelU) -> bool,
    taken: spec_fn(StepLabel) -> bool, fair_w: spec_fn(nat) -> nat, i: nat, t: nat) -> (r: (nat, bool))
    requires
        pilot_behavior(b), i <= t, new_endpoint_locks_held(b(i).u), container_unlocked(b(t).u, ctn), forall|m: nat| #![trigger b(m)] i <= m < t ==> b(m).cpu != w,
        forall|k: nat| #![trigger b(k)] i <= k && no_own_step(b, w, i, k) && container_unlocked(b(k).u, ctn) ==> enabled(b(k).u),
        weakly_fair_witness(b, w, enabled, taken, fair_w),
    ensures
        t <= r.0, forall|m: nat| #![trigger b(m)] t <= m < r.0 ==> b(m).cpu != w,
        r.1 ==> b(r.0).cpu == w, !r.1 ==> other_container_entry(b, ctn, w, r.0),
{
    assert(fair_w(t) == fair_w(t));
    let n = fair_w(t);
    match first_waiter_event(b, ctn, w, t, n) {
        None => {
            no_entry_implies_container_unlocked_kept(b, ctn, i, t, n);
            assert(no_own_step(b, w, i, n));
            assert(enabled(b(n).u));
            (n, true)
        },
        Some(m) => (m, b(m).cpu == w),
    }
}

/// From `t`, at which `w` has not stepped since `i` and `ctn` is consistently locked, bounded contention against `w`,
/// fairness of every cpu inside, and weak fairness of `w` for a step `enabled` whenever `ctn` is unlocked before `w`'s first
/// step since `i` find that first step.
proof fn bounded_other_contention_implies_waiter_steps_from(b: Execution<Snap>, ctn: RwLockContainerPtr, bound: nat, fair: spec_fn(CpuId) -> spec_fn(nat) -> nat,
    w: CpuId, enabled: spec_fn(KernelU) -> bool, taken: spec_fn(StepLabel) -> bool, fair_w: spec_fn(nat) -> nat, i: nat, t: nat) -> (k: nat)
    requires
        pilot_behavior(b), i <= t, new_endpoint_locks_held(b(i).u), container_lock_held(b(t).u, ctn), bounded_other_contention(b, ctn, w, i, bound),
        forall|x: CpuId| #![trigger fair(x)] index_valid(NUM_CPUS, x) ==> weakly_fair_witness(b, x, pilot_enabled(x), any_label(), fair(x)),
        forall|m: nat| #![trigger b(m)] i <= m < t ==> b(m).cpu != w,
        forall|k: nat| #![trigger b(k)] i <= k && no_own_step(b, w, i, k) && container_unlocked(b(k).u, ctn) ==> enabled(b(k).u),
        weakly_fair_witness(b, w, enabled, taken, fair_w),
    ensures t <= k, b(k).cpu == w, forall|m: nat| #![trigger b(m)] i <= m < k ==> b(m).cpu != w,
    decreases bound - other_container_entries(b, ctn, w, i, t), if container_unlocked(b(t).u, ctn) { 0int } else { 1int },
{
    assert(other_container_entries(b, ctn, w, i, t) <= bound);
    if !container_unlocked(b(t).u, ctn) {
        let r = locked_container_implies_released_or_waiter_steps(b, ctn, fair, w, i, t);
        if r.1 { r.0 } else {
            other_container_entries_split_implies_sum(b, ctn, w, i, t, r.0);
            bounded_other_contention_implies_waiter_steps_from(b, ctn, bound, fair, w, enabled, taken, fair_w, i, r.0)
        }
    } else {
        let r = unlocked_container_implies_waiter_steps_or_other_entry(b, ctn, w, enabled, taken, fair_w, i, t);
        if r.1 { r.0 } else {
            let m = r.0;
            other_container_entries_split_implies_sum(b, ctn, w, i, t, m);
            other_container_entries_split_implies_sum(b, ctn, w, i, m, m + 1);
            assert(other_container_entries(b, ctn, w, m, m + 1) == 1) by { reveal_with_fuel(other_container_entries, 2); };
            assert(other_container_entries(b, ctn, w, i, m + 1) <= bound);
            pilot_behavior_implies_container_lock_held_kept(b, ctn, t, m + 1);
            bounded_other_contention_implies_waiter_steps_from(b, ctn, bound, fair, w, enabled, taken, fair_w, i, m + 1)
        }
    }
}

/// Theorem (b3), quota-allocation waiter: with the lock invariants at `i`, every cpu weakly fair inside endpoint creation,
/// cpus other than `w` entering endpoint creation in `ctn` at most `bound` times from `i` on, `w`'s allocation of `amount`
/// enabled whenever `ctn` is unlocked before `w`'s first step since `i`, that first step being the allocation, and `w` weakly
/// fair for it, `w` allocates at the returned index, its first step since `i`.
pub proof fn bounded_contention_and_fair_waiter_implies_alloc(b: Execution<Snap>, ctn: RwLockContainerPtr, bound: nat, fair: spec_fn(CpuId) -> spec_fn(nat) -> nat,
    w: CpuId, amount: usize, fair_w: spec_fn(nat) -> nat, i: nat) -> (k: nat)
    requires
        pilot_behavior(b), new_endpoint_locks_held(b(i).u), container_lock_held(b(i).u, ctn), bounded_other_contention(b, ctn, w, i, bound),
        forall|x: CpuId| #![trigger fair(x)] index_valid(NUM_CPUS, x) ==> weakly_fair_witness(b, x, pilot_enabled(x), any_label(), fair(x)),
        forall|k: nat| #![trigger b(k)] i <= k && no_own_step(b, w, i, k) && container_unlocked(b(k).u, ctn) ==> alloc_quota_4k_step_pre(b(k).u, w, amount),
        forall|k: nat| #![trigger b(k)] i <= k && no_own_step(b, w, i, k) && b(k).cpu == w ==> b(k).label == (StepLabel::AllocQuota4k { alloc_amount: amount }),
        weakly_fair_witness(b, w, alloc_enabled(w, amount), alloc_taken(amount), fair_w),
    ensures i <= k, b(k).cpu == w, b(k).label == (StepLabel::AllocQuota4k { alloc_amount: amount }), own_steps(b, w, i, k) == 0,
{
    let k = bounded_other_contention_implies_waiter_steps_from(b, ctn, bound, fair, w, alloc_enabled(w, amount), alloc_taken(amount), fair_w, i, i);
    assert(no_own_step(b, w, i, k));
    no_step_implies_own_steps_zero(b, w, i, k);
    k
}

/// Theorem (b3), endpoint-creation waiter, end to end: under the hypotheses of the allocation waiter with `w`'s entry into
/// endpoint creation at `ep_idx` in place of the allocation, `w` enters at the returned `ks.0`, its first step since `i`,
/// and finishes at `ks.1`.
pub proof fn bounded_contention_and_fair_waiter_implies_new_endpoint_entered_and_finished(b: Execution<Snap>, ctn: RwLockContainerPtr, bound: nat,
    fair: spec_fn(CpuId) -> spec_fn(nat) -> nat, w: CpuId, ep_idx: EndpointIdx, fair_w: spec_fn(nat) -> nat, i: nat) -> (ks: (nat, nat))
    requires
        pilot_behavior(b), new_endpoint_locks_held(b(i).u), container_lock_held(b(i).u, ctn), bounded_other_contention(b, ctn, w, i, bound),
        forall|x: CpuId| #![trigger fair(x)] index_valid(NUM_CPUS, x) ==> weakly_fair_witness(b, x, pilot_enabled(x), any_label(), fair(x)),
        forall|k: nat| #![trigger b(k)] i <= k && no_own_step(b, w, i, k) && container_unlocked(b(k).u, ctn) ==> new_endpoint_enter_step_pre(b(k).u, w, ep_idx),
        forall|k: nat| #![trigger b(k)] i <= k && no_own_step(b, w, i, k) && b(k).cpu == w ==> b(k).label == (StepLabel::NewEndpointEnter { slot: ep_idx }),
        weakly_fair_witness(b, w, new_endpoint_enter_enabled(w, ep_idx), new_endpoint_enter_taken(ep_idx), fair_w),
    ensures
        i <= ks.0 < ks.1, own_steps(b, w, i, ks.0) == 0, b(ks.0).cpu == w, b(ks.0).label == (StepLabel::NewEndpointEnter { slot: ep_idx }), b(ks.1).cpu == w,
        b(ks.1).label is NewEndpointFinish,
{
    let k = bounded_other_contention_implies_waiter_steps_from(b, ctn, bound, fair, w, new_endpoint_enter_enabled(w, ep_idx), new_endpoint_enter_taken(ep_idx), fair_w, i, i);
    assert(no_own_step(b, w, i, k));
    no_step_implies_own_steps_zero(b, w, i, k);
    assert(pilot_step(b(k), b(k + 1)));
    pilot_own_step_implies_measure_decreases(b(k).u, b(k + 1).u, b(k).label, w);
    assert(index_valid(NUM_CPUS, w));
    assert forall|m: nat| #![trigger b(m)] k + 1 <= m && in_new_endpoint(b(m).u, w) implies new_endpoint_finish_step_pre(b(m).u, w) by {
        new_endpoint_locks_held_implies_never_blocked(b, i, m, w);
    };
    assert(fair(w) == fair(w));
    let s = new_endpoint_holder_fair_implies_container_released(b, w, fair(w), k + 1);
    (k, s)
}

/// Part of the satisfiability of the corrected endpoint-creation waiter: once `w` finishes endpoint creation at descriptor
/// `ep_idx`, its entry at `ep_idx` is disabled because the descriptor is taken, so weak fairness of `w` for that entry no
/// longer forces another entry, unlike the round-2 hypothesis that kept it enabled whenever `ctn` was unlocked. The
/// descriptor table having its full length is not part of `kernel_u_ownership_wf`, so it is a hypothesis here.
pub proof fn new_endpoint_finish_implies_enter_disabled(u: KernelU, u2: KernelU, w: CpuId)
    requires
        kernel_u_ownership_wf(u), labeled_step(StepLabel::NewEndpointFinish, u, u2, w),
        cur_thread(u, w).endpoint_descriptors.len() == MAX_NUM_ENDPOINT_DESCRIPTORS,
    ensures !new_endpoint_enter_step_pre(u2, w, cur_thread(u, w).syscall_progress->Some_0->NewEndpoint_slot),
{
    reveal(kernel_u_cpu_ownership_wf);
    reveal(new_endpoint_finish_step_pre); reveal(new_endpoint_finish_step); reveal(kernel_u_new_endpoint_changed); reveal(new_endpoint_enter_step_pre);
}
} // verus!
