//! Route A, Anvil style: the theorems of `route_explicit` as temporal formulas over the same behaviours, proved with the
//! rules of `temporal`. Fairness is `weak_fairness` and every environment assumption is an `always` hypothesis.
use vstd::prelude::*;
use crate::*;
use crate::temporal::*;

verus! {
/// A pilot step from a well-formed state.
pub open spec fn pilot_next() -> ActionPred<Snap> { |s: Snap, s2: Snap| pilot_step(s, s2) }
pub open spec fn snap_in_pilot(c: CpuId) -> StatePred<Snap> { |s: Snap| in_pilot(s.u, c) }
pub open spec fn snap_left_pilot(c: CpuId) -> StatePred<Snap> { |s: Snap| !in_pilot(s.u, c) }
pub open spec fn snap_measure(c: CpuId) -> spec_fn(Snap) -> nat { |s: Snap| pilot_measure(s.u, c) }
pub open spec fn snap_enabled(c: CpuId) -> StatePred<Snap> { |s: Snap| pilot_enabled(c)(s.u) }
/// The step is taken by cpu `c`.
pub open spec fn cpu_steps(c: CpuId) -> ActionPred<Snap> { |s: Snap, s2: Snap| s.cpu == c }
/// Cpu `h` is inside endpoint creation in container `ctn`.
pub open spec fn holds_container(h: CpuId, ctn: RwLockContainerPtr) -> StatePred<Snap> { |s: Snap| in_new_endpoint(s.u, h) && s.u.cpu_array[h as int].owning_container == ctn }
pub open spec fn holder_case(ctn: RwLockContainerPtr) -> spec_fn(CpuId) -> StatePred<Snap> { |x: CpuId| holds_container(x, ctn) }
pub open spec fn container_writer(ctn: RwLockContainerPtr) -> spec_fn(Snap) -> CpuId { |s: Snap| s.u.container_map[ctn].lock_state->WriteLocked_writer }
pub open spec fn snap_container_unlocked(ctn: RwLockContainerPtr) -> StatePred<Snap> { |s: Snap| container_unlocked(s.u, ctn) }
pub open spec fn snap_no_conflict(ctn: RwLockContainerPtr, depth: usize) -> StatePred<Snap> { |s: Snap| !lock_order_conflict(s.u, ctn, depth) }
pub open spec fn conflict_held(ctn: RwLockContainerPtr, depth: usize) -> StatePred<Snap> { |s: Snap| lock_order_conflict(s.u, ctn, depth) && container_owner_held(s.u, ctn) }
pub open spec fn snap_locks_held() -> StatePred<Snap> { |s: Snap| new_endpoint_locks_held(s.u) }
pub open spec fn snap_in_new_endpoint(c: CpuId) -> StatePred<Snap> { |s: Snap| in_new_endpoint(s.u, c) }
/// No process shallower than `depth` enters endpoint creation in `ctn`.
pub open spec fn no_shallower_entrant(ctn: RwLockContainerPtr, depth: usize) -> ActionPred<Snap> {
    |s: Snap, s2: Snap| s.label is NewEndpointEnter && s.u.cpu_array[s.cpu as int].owning_container == ctn ==> s.u.process_map[s.u.cpu_array[s.cpu as int].current_process->Some_0].depth >= depth
}

/// Theorem (a): a cpu `c` that is never blocked inside a pilot syscall and is weakly fair leaves every pilot syscall it
/// is inside.
pub proof fn pilot_cpu_never_blocked_and_fair_leads_to_exit(ex: Execution<Snap>, c: CpuId)
    requires
        always(lift_action(pilot_next()))(ex, 0), always(lift_state(state_implies(snap_in_pilot(c), snap_enabled(c))))(ex, 0),
        weak_fairness(snap_enabled(c), cpu_steps(c))(ex, 0),
    ensures leads_to(lift_state(snap_in_pilot(c)), lift_state(snap_left_pilot(c)))(ex, 0),
{
    let p = snap_in_pilot(c);
    let q = snap_left_pilot(c);
    let m = snap_measure(c);
    assert forall|n: nat| #![trigger at_measure(p, m, n)] leads_to(lift_state(at_measure(p, m, n)), lift_state(reached_or_below(q, p, m, n)))(ex, 0) by {
        let pn = at_measure(p, m, n);
        let qn = reached_or_below(q, p, m, n);
        assert forall|j: nat| 0 <= j implies #[trigger] lift_action(wf1_step(pn, qn, cpu_steps(c)))(ex, j) by {
            assert(lift_action(pilot_next())(ex, j));
            let s = ex(j);
            let s2 = ex(j + 1);
            if s.cpu == c { pilot_own_step_implies_measure_decreases(s.u, s2.u, s.label, c); }
            else if in_pilot(s.u, c) { pilot_other_step_implies_cpu_slice_unchanged(s.u, s2.u, s.label, s.cpu, c); }
        };
        assert forall|j: nat| 0 <= j implies #[trigger] lift_state(state_implies(pn, snap_enabled(c)))(ex, j) by {
            assert(lift_state(state_implies(snap_in_pilot(c), snap_enabled(c)))(ex, j));
        };
        wf1(ex, pn, qn, snap_enabled(c), cpu_steps(c));
    };
    measure_step_implies_leads_to(ex, p, q, m);
}

/// Theorem (b), release: a weakly fair cpu `h` inside endpoint creation in container `ctn`, whose step stays enabled
/// there, leads to `ctn` unlocked without owner.
pub proof fn new_endpoint_holder_fair_leads_to_container_unlocked(ex: Execution<Snap>, h: CpuId, ctn: RwLockContainerPtr)
    requires
        always(lift_action(pilot_next()))(ex, 0), always(lift_state(state_implies(holds_container(h, ctn), snap_enabled(h))))(ex, 0),
        weak_fairness(snap_enabled(h), cpu_steps(h))(ex, 0),
    ensures leads_to(lift_state(holds_container(h, ctn)), lift_state(snap_container_unlocked(ctn)))(ex, 0),
{
    let p = holds_container(h, ctn);
    let q = snap_container_unlocked(ctn);
    assert forall|j: nat| 0 <= j implies #[trigger] lift_action(wf1_step(p, q, cpu_steps(h)))(ex, j) by {
        assert(lift_action(pilot_next())(ex, j));
        let s = ex(j);
        let s2 = ex(j + 1);
        if p(s) {
            if s.cpu == h {
                pilot_own_step_implies_measure_decreases(s.u, s2.u, s.label, h);
                pilot_step_implies_container_lock_frame(s.u, s2.u, s.label, h, ctn);
            } else { pilot_other_step_implies_cpu_slice_unchanged(s.u, s2.u, s.label, s.cpu, h); }
        }
    };
    wf1(ex, p, q, snap_enabled(h), cpu_steps(h));
}

/// Theorem (c), no deadlock in endpoint creation: `new_endpoint_locks_held` initially always holds, and then a cpu inside
/// endpoint creation is never blocked.
pub proof fn new_endpoint_locks_held_initially_implies_never_blocked(ex: Execution<Snap>)
    requires always(lift_action(pilot_next()))(ex, 0), new_endpoint_locks_held(ex(0).u),
    ensures
        always(lift_state(snap_locks_held()))(ex, 0),
        forall|x: CpuId| #![trigger snap_in_new_endpoint(x)] always(lift_state(state_implies(snap_in_new_endpoint(x), snap_enabled(x))))(ex, 0),
{
    assert forall|s: Snap, s2: Snap| #![trigger snap_locks_held()(s), pilot_next()(s, s2)] snap_locks_held()(s) && pilot_next()(s, s2) implies snap_locks_held()(s2) by {
        pilot_step_implies_new_endpoint_locks_held(s.u, s2.u, s.label, s.cpu);
    };
    inductive_implies_always(ex, snap_locks_held(), pilot_next());
    assert forall|x: CpuId| #![trigger snap_in_new_endpoint(x)] always(lift_state(state_implies(snap_in_new_endpoint(x), snap_enabled(x))))(ex, 0) by {
        assert forall|j: nat| 0 <= j implies #[trigger] lift_state(state_implies(snap_in_new_endpoint(x), snap_enabled(x)))(ex, j) by {
            assert(lift_state(snap_locks_held())(ex, j) && lift_action(pilot_next())(ex, j));
            if in_new_endpoint(ex(j).u, x) { new_endpoint_locks_held_implies_finish_enabled(ex(j).u, x); }
        };
    };
}

/// Theorem (c), retry after `ErrorContainerLockOrderConflict`: with the lock invariants initially, every cpu weakly
/// fair, and no process shallower than `depth` ever entering endpoint creation in `ctn`, eventually `ctn` never again
/// has a lock-order conflict for `depth`.
pub proof fn no_shallower_entrant_and_fairness_implies_eventually_always_no_conflict(ex: Execution<Snap>, ctn: RwLockContainerPtr, depth: usize)
    requires
        always(lift_action(pilot_next()))(ex, 0), new_endpoint_locks_held(ex(0).u), container_owner_held(ex(0).u, ctn),
        forall|x: CpuId| #![trigger cpu_steps(x)] index_valid(NUM_CPUS, x) ==> weak_fairness(snap_enabled(x), cpu_steps(x))(ex, 0),
        always(lift_action(no_shallower_entrant(ctn, depth)))(ex, 0),
    ensures eventually(always(lift_state(snap_no_conflict(ctn, depth))))(ex, 0),
{
    new_endpoint_locks_held_initially_implies_never_blocked(ex);
    let q = snap_container_unlocked(ctn);
    assert forall|x: CpuId| #![trigger holder_case(ctn)(x)] leads_to(lift_state(holder_case(ctn)(x)), lift_state(q))(ex, 0) by {
        if index_valid(NUM_CPUS, x) {
            assert(weak_fairness(snap_enabled(x), cpu_steps(x))(ex, 0));
            assert forall|j: nat| 0 <= j implies #[trigger] lift_state(state_implies(holds_container(x, ctn), snap_enabled(x)))(ex, j) by {
                assert(lift_state(state_implies(snap_in_new_endpoint(x), snap_enabled(x)))(ex, j));
            };
            new_endpoint_holder_fair_leads_to_container_unlocked(ex, x, ctn);
        } else {
            assert forall|i: nat| #![trigger implies(lift_state(holds_container(x, ctn)), eventually(lift_state(q)))(ex, i)]
                implies(lift_state(holds_container(x, ctn)), eventually(lift_state(q)))(ex, i) by {};
        }
    };
    cases_leads_to_implies_leads_to(ex, conflict_held(ctn, depth), lift_state(q), container_writer(ctn), holder_case(ctn));
    let r = snap_no_conflict(ctn, depth);
    if lock_order_conflict(ex(0).u, ctn, depth) {
        assert(implies(lift_state(conflict_held(ctn, depth)), eventually(lift_state(q)))(ex, 0));
        let k = choose|k: nat| 0 <= k && #[trigger] lift_state(q)(ex, k);
        assert(lift_state(r)(ex, k));
    } else { assert(lift_state(r)(ex, 0)); }
    assert forall|j: nat| 0 <= j implies #[trigger] lift_action(stable(r))(ex, j) by {
        assert(lift_action(pilot_next())(ex, j) && lift_action(no_shallower_entrant(ctn, depth))(ex, j));
        if r(ex(j)) { pilot_step_implies_no_lock_order_conflict_kept(ex(j).u, ex(j + 1).u, ex(j).label, ex(j).cpu, ctn, depth); }
    };
    eventually_stable_implies_eventually_always(ex, r);
}
} // verus!
