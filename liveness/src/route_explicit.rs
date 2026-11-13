//! Route I, IronFleet style: no temporal operators. Lemmas take the behaviour and an index and return the later index as
//! their result; weak fairness is an explicit witness function (`weakly_fair_witness`). This file uses no `exists` and
//! no `choose`.
use vstd::prelude::*;
use crate::*;
use veriflat_syscall_new_thread::syscall_new_endpoint::syscall_new_endpoint_spec::*;
use veriflat_syscall_alloc_quota::syscall_alloc_quota::syscall_alloc_quota_spec::*;

verus! {
/// Some step of `c` is enabled at every index from `i` at which `c` is inside a pilot syscall.
pub open spec fn pilot_never_blocked_from(b: Execution<Snap>, c: CpuId, i: nat) -> bool {
    forall|k: nat| #![trigger b(k)] i <= k && in_pilot(b(k).u, c) ==> pilot_next_pre(b(k).u, c)
}

/// Theorem (a), counting part: while `c` stays inside a pilot syscall from `i` to `j`, its own steps there plus its
/// measure at `j` do not exceed its measure at `i`. So `c` leaves within `pilot_measure(b(i).u, c) + 1` own steps, with no
/// fairness or enabledness hypothesis.
pub proof fn pilot_behavior_implies_own_steps_bounded_by_measure(b: Execution<Snap>, c: CpuId, i: nat, j: nat)
    requires pilot_behavior(b), i <= j, forall|k: nat| #![trigger b(k)] i <= k <= j ==> in_pilot(b(k).u, c),
    ensures own_steps(b, c, i, j) + pilot_measure(b(j).u, c) <= pilot_measure(b(i).u, c),
    decreases j - i,
{
    if j > i {
        let k = (j - 1) as nat;
        pilot_behavior_implies_own_steps_bounded_by_measure(b, c, i, k);
        assert(pilot_step(b(k), b(k + 1)) && in_pilot(b(k).u, c) && in_pilot(b(j).u, c));
        if b(k).cpu == c { pilot_own_step_implies_measure_decreases(b(k).u, b(j).u, b(k).label, c); }
        else { pilot_other_step_implies_cpu_slice_unchanged(b(k).u, b(j).u, b(k).label, b(k).cpu, c); }
    }
}

/// From `t`, while `c` has not stepped since `i` and its slice is the one at `i`, weak fairness finds the first own step
/// `s` of `c` at or after `t`; the slice of `c` is still the one at `i` there.
proof fn fair_enabled_slice_implies_first_own_step(b: Execution<Snap>, c: CpuId, fair: spec_fn(nat) -> nat, i: nat, t: nat) -> (s: nat)
    requires
        pilot_behavior(b), index_valid(NUM_CPUS, c), in_pilot(b(i).u, c), i <= t <= fair(i),
        weakly_fair_witness(b, c, pilot_enabled(c), any_label(), fair),
        forall|k: nat| #![trigger b(k)] i <= k && cpu_slice(b(k).u, c) == cpu_slice(b(i).u, c) ==> pilot_next_pre(b(k).u, c),
        forall|k: nat| #![trigger b(k)] i <= k < t ==> b(k).cpu != c,
        cpu_slice(b(t).u, c) == cpu_slice(b(i).u, c),
    ensures
        t <= s <= fair(i), b(s).cpu == c, cpu_slice(b(s).u, c) == cpu_slice(b(i).u, c), in_pilot(b(s).u, c),
        forall|k: nat| #![trigger b(k)] i <= k < s ==> b(k).cpu != c,
    decreases fair(i) - t,
{
    assert(in_pilot(b(t).u, c));
    if b(t).cpu == c { t }
    else {
        assert(fair(i) == fair(i));
        assert(t < fair(i)) by { if t == fair(i) { assert(pilot_next_pre(b(t).u, c)); } };
        assert(pilot_step(b(t), b(t + 1)));
        pilot_other_step_implies_cpu_slice_unchanged(b(t).u, b(t + 1).u, b(t).label, b(t).cpu, c);
        fair_enabled_slice_implies_first_own_step(b, c, fair, i, t + 1)
    }
}

/// Theorem (a): a cpu `c` inside a pilot syscall at `i` that is never blocked from `i` and is weakly fair leaves the
/// syscall: it takes its last step inside at the returned `s`, after at most `pilot_measure(b(i).u, c) + 1` own steps.
pub proof fn pilot_cpu_never_blocked_and_fair_implies_leaves(b: Execution<Snap>, c: CpuId, fair: spec_fn(nat) -> nat, i: nat) -> (s: nat)
    requires
        pilot_behavior(b), in_pilot(b(i).u, c), pilot_never_blocked_from(b, c, i),
        weakly_fair_witness(b, c, pilot_enabled(c), any_label(), fair),
    ensures i <= s, b(s).cpu == c, in_pilot(b(s).u, c), !in_pilot(b(s + 1).u, c), own_steps(b, c, i, s + 1) <= pilot_measure(b(i).u, c) + 1,
    decreases pilot_measure(b(i).u, c),
{
    assert forall|k: nat| #![trigger b(k)] i <= k && cpu_slice(b(k).u, c) == cpu_slice(b(i).u, c) implies pilot_next_pre(b(k).u, c) by { assert(in_pilot(b(k).u, c)); };
    let s0 = fair_enabled_slice_implies_first_own_step(b, c, fair, i, i);
    no_step_implies_own_steps_zero(b, c, i, s0);
    assert(pilot_step(b(s0), b(s0 + 1)));
    pilot_own_step_implies_measure_decreases(b(s0).u, b(s0 + 1).u, b(s0).label, c);
    if !in_pilot(b(s0 + 1).u, c) { s0 }
    else {
        let s = pilot_cpu_never_blocked_and_fair_implies_leaves(b, c, fair, s0 + 1);
        own_steps_split_implies_sum(b, c, i, s0 + 1, s + 1);
        s
    }
}

/// Theorem (c), lock invariant: `new_endpoint_locks_held` at `i` holds at every later index.
pub proof fn pilot_behavior_implies_new_endpoint_locks_held_kept(b: Execution<Snap>, i: nat, k: nat)
    requires pilot_behavior(b), i <= k, new_endpoint_locks_held(b(i).u),
    ensures new_endpoint_locks_held(b(k).u),
    decreases k - i,
{
    if k > i {
        let j = (k - 1) as nat;
        pilot_behavior_implies_new_endpoint_locks_held_kept(b, i, j);
        assert(pilot_step(b(j), b(j + 1)));
        pilot_step_implies_new_endpoint_locks_held(b(j).u, b(k).u, b(j).label, b(j).cpu);
    }
}

/// Theorem (c), owner invariant: `container_owner_held` of `ctn` at `i` holds at every later index.
pub proof fn pilot_behavior_implies_container_owner_held_kept(b: Execution<Snap>, ctn: RwLockContainerPtr, i: nat, k: nat)
    requires pilot_behavior(b), i <= k, container_owner_held(b(i).u, ctn),
    ensures container_owner_held(b(k).u, ctn),
    decreases k - i,
{
    if k > i {
        let j = (k - 1) as nat;
        pilot_behavior_implies_container_owner_held_kept(b, ctn, i, j);
        assert(pilot_step(b(j), b(j + 1)));
        pilot_step_implies_container_owner_held(b(j).u, b(k).u, b(j).label, b(j).cpu, ctn);
    }
}

/// Theorem (c), no deadlock in endpoint creation: with `new_endpoint_locks_held` at `i`, a cpu inside endpoint creation
/// at any later index can take its finish step, so it never waits.
pub proof fn new_endpoint_locks_held_implies_never_blocked(b: Execution<Snap>, i: nat, k: nat, x: CpuId)
    requires pilot_behavior(b), i <= k, new_endpoint_locks_held(b(i).u), in_new_endpoint(b(k).u, x),
    ensures new_endpoint_finish_step_pre(b(k).u, x),
{
    pilot_behavior_implies_new_endpoint_locks_held_kept(b, i, k);
    assert(pilot_step(b(k), b(k + 1)));
    new_endpoint_locks_held_implies_finish_enabled(b(k).u, x);
}

/// Theorem (b), release: a weakly fair cpu `h` inside endpoint creation at `i` whose finish step stays enabled finishes at
/// the returned `s` and leaves its container unlocked without owner at `s + 1`.
pub proof fn new_endpoint_holder_fair_implies_container_released(b: Execution<Snap>, h: CpuId, fair: spec_fn(nat) -> nat, i: nat) -> (s: nat)
    requires
        pilot_behavior(b), in_new_endpoint(b(i).u, h), weakly_fair_witness(b, h, pilot_enabled(h), any_label(), fair),
        forall|k: nat| #![trigger b(k)] i <= k && in_new_endpoint(b(k).u, h) ==> new_endpoint_finish_step_pre(b(k).u, h),
    ensures
        i <= s, b(s).cpu == h, b(s).label is NewEndpointFinish, b(s).u.cpu_array[h as int] == b(i).u.cpu_array[h as int],
        container_unlocked(b(s + 1).u, b(i).u.cpu_array[h as int].owning_container),
{
    assert forall|k: nat| #![trigger b(k)] i <= k && cpu_slice(b(k).u, h) == cpu_slice(b(i).u, h) implies pilot_next_pre(b(k).u, h) by { assert(in_new_endpoint(b(k).u, h)); };
    let s = fair_enabled_slice_implies_first_own_step(b, h, fair, i, i);
    assert(pilot_step(b(s), b(s + 1)) && in_new_endpoint(b(s).u, h));
    pilot_own_step_implies_measure_decreases(b(s).u, b(s + 1).u, b(s).label, h);
    pilot_step_implies_container_lock_frame(b(s).u, b(s + 1).u, b(s).label, h, b(i).u.cpu_array[h as int].owning_container);
    s
}

/// From `t`, container `ctn`, unlocked at `t` and kept unlocked by every step but the 4K quota allocation of `w`, stays
/// unlocked up to `k` while `w` does not step.
proof fn unlocked_container_kept_while_waiter_idle(b: Execution<Snap>, w: CpuId, amount: usize, ctn: RwLockContainerPtr, i: nat, t: nat, k: nat)
    requires
        i <= t <= k, container_unlocked(b(t).u, ctn), forall|m: nat| #![trigger b(m)] t <= m < k ==> b(m).cpu != w,
        forall|k: nat| #![trigger b(k)] i <= k && container_unlocked(b(k).u, ctn) && !(b(k).cpu == w && b(k).label == StepLabel::AllocQuota4k { alloc_amount: amount })
            ==> container_unlocked(b(k + 1).u, ctn),
    ensures container_unlocked(b(k).u, ctn),
    decreases k - t,
{
    if k > t {
        let p = (k - 1) as nat;
        unlocked_container_kept_while_waiter_idle(b, w, amount, ctn, i, t, p);
        assert(b(p).cpu != w);
    }
}

/// Theorem (b), waiter: cpu `w` wants to move `amount` 4K quota and is blocked only by container `ctn`, which cpu `h`
/// holds inside endpoint creation at `i`. If `h` is weakly fair with its finish step kept enabled, no other step relocks
/// `ctn` once it is free, `w`'s allocation is enabled whenever `ctn` is unlocked before `w`'s first step since `i`, that
/// first step is the allocation, and `w` is weakly fair for it, then `w` allocates at the returned index, its first step
/// since `i`.
pub proof fn new_endpoint_holder_and_fair_waiter_implies_alloc(b: Execution<Snap>, h: CpuId, w: CpuId, amount: usize, fair_h: spec_fn(nat) -> nat,
    fair_w: spec_fn(nat) -> nat, i: nat) -> (k: nat)
    requires
        pilot_behavior(b), in_new_endpoint(b(i).u, h), weakly_fair_witness(b, h, pilot_enabled(h), any_label(), fair_h),
        forall|k: nat| #![trigger b(k)] i <= k && in_new_endpoint(b(k).u, h) ==> new_endpoint_finish_step_pre(b(k).u, h),
        weakly_fair_witness(b, w, alloc_enabled(w, amount), alloc_taken(amount), fair_w),
        forall|k: nat| #![trigger b(k)] i <= k && no_own_step(b, w, i, k) && container_unlocked(b(k).u, b(i).u.cpu_array[h as int].owning_container)
            ==> alloc_quota_4k_step_pre(b(k).u, w, amount),
        forall|k: nat| #![trigger b(k)] i <= k && no_own_step(b, w, i, k) && b(k).cpu == w ==> b(k).label == (StepLabel::AllocQuota4k { alloc_amount: amount }),
        forall|k: nat| #![trigger b(k)]
            i <= k && container_unlocked(b(k).u, b(i).u.cpu_array[h as int].owning_container) && !(b(k).cpu == w && b(k).label == StepLabel::AllocQuota4k { alloc_amount: amount })
                ==> container_unlocked(b(k + 1).u, b(i).u.cpu_array[h as int].owning_container),
    ensures i <= k, b(k).cpu == w, b(k).label == (StepLabel::AllocQuota4k { alloc_amount: amount }), own_steps(b, w, i, k) == 0,
{
    let ctn = b(i).u.cpu_array[h as int].owning_container;
    let s = new_endpoint_holder_fair_implies_container_released(b, h, fair_h, i);
    assert(fair_w(s + 1) == fair_w(s + 1));
    let n = fair_w(s + 1);
    let k = match first_own_step_in(b, w, i, n) {
        Some(f) => f,
        None => {
            unlocked_container_kept_while_waiter_idle(b, w, amount, ctn, i, s + 1, n);
            assert(no_own_step(b, w, i, n));
            assert(alloc_quota_4k_step_pre(b(n).u, w, amount));
            n
        },
    };
    assert(no_own_step(b, w, i, k));
    no_step_implies_own_steps_zero(b, w, i, k);
    k
}

/// From `j` on, without a conflict at `j` and with no process shallower than `depth` entering endpoint creation in `ctn`,
/// no index has a lock-order conflict.
proof fn no_shallower_entrant_implies_no_conflict_from(b: Execution<Snap>, ctn: RwLockContainerPtr, depth: usize, j: nat, k: nat)
    requires
        pilot_behavior(b), j <= k, !lock_order_conflict(b(j).u, ctn, depth),
        forall|k: nat| #![trigger b(k)] j <= k && b(k).label is NewEndpointEnter && b(k).u.cpu_array[b(k).cpu as int].owning_container == ctn
            ==> b(k).u.process_map[b(k).u.cpu_array[b(k).cpu as int].current_process->Some_0].depth >= depth,
    ensures !lock_order_conflict(b(k).u, ctn, depth),
    decreases k - j,
{
    if k > j {
        let p = (k - 1) as nat;
        no_shallower_entrant_implies_no_conflict_from(b, ctn, depth, j, p);
        assert(pilot_step(b(p), b(p + 1)));
        pilot_step_implies_no_lock_order_conflict_kept(b(p).u, b(k).u, b(p).label, b(p).cpu, ctn, depth);
    }
}

/// Theorem (c), retry after `ErrorContainerLockOrderConflict`: with the lock invariants at `i`, every cpu weakly fair,
/// and no process shallower than `depth` entering endpoint creation in `ctn` from `i` on, there is an index `j` from which
/// `ctn` never has a lock-order conflict for `depth`, so an `alloc_quota_4k` retry of a process at that depth in `ctn`
/// started at any index from `j` does not return `ErrorContainerLockOrderConflict`
/// (`no_lock_order_conflict_implies_alloc_quota_4k_result_not_conflict`).
pub proof fn no_shallower_entrant_and_fairness_implies_lock_order_conflict_ends(b: Execution<Snap>, ctn: RwLockContainerPtr, depth: usize,
    fair: spec_fn(CpuId) -> spec_fn(nat) -> nat, i: nat) -> (j: nat)
    requires
        pilot_behavior(b), new_endpoint_locks_held(b(i).u), container_owner_held(b(i).u, ctn),
        forall|x: CpuId| #![trigger fair(x)] index_valid(NUM_CPUS, x) ==> weakly_fair_witness(b, x, pilot_enabled(x), any_label(), fair(x)),
        forall|k: nat| #![trigger b(k)] i <= k && b(k).label is NewEndpointEnter && b(k).u.cpu_array[b(k).cpu as int].owning_container == ctn
            ==> b(k).u.process_map[b(k).u.cpu_array[b(k).cpu as int].current_process->Some_0].depth >= depth,
    ensures i <= j, forall|k: nat| #![trigger b(k)] j <= k ==> !lock_order_conflict(b(k).u, ctn, depth),
{
    let j = if !lock_order_conflict(b(i).u, ctn, depth) { i } else {
        let h = b(i).u.container_map[ctn].lock_state->WriteLocked_writer;
        assert forall|k: nat| #![trigger b(k)] i <= k && in_new_endpoint(b(k).u, h) implies new_endpoint_finish_step_pre(b(k).u, h) by {
            new_endpoint_locks_held_implies_never_blocked(b, i, k, h);
        };
        assert(fair(h) == fair(h));
        new_endpoint_holder_fair_implies_container_released(b, h, fair(h), i) + 1
    };
    assert forall|k: nat| #![trigger b(k)] j <= k implies !lock_order_conflict(b(k).u, ctn, depth) by {
        no_shallower_entrant_implies_no_conflict_from(b, ctn, depth, j, k);
    };
    j
}
} // verus!
