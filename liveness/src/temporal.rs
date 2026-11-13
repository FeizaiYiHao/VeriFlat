//! A small linear temporal logic over infinite executions, written for this pilot after the operators and rules of
//! Anvil's `temporal_logic` (MIT); no Anvil code is copied. A temporal predicate holds of an execution at a position, so
//! `p(ex, i)` reads "p holds of `ex` from index `i` on". `eventually` is defined with the only `exists` of the
//! crate, and the rules below take its witness with `choose`; route A itself chooses once more, in the retry theorem.
use vstd::prelude::*;
use crate::*;

verus! {
pub type StatePred<T> = spec_fn(T) -> bool;
pub type ActionPred<T> = spec_fn(T, T) -> bool;
pub type TempPred<T> = spec_fn(Execution<T>, nat) -> bool;

pub open spec fn lift_state<T>(p: StatePred<T>) -> TempPred<T> { |ex: Execution<T>, i: nat| p(ex(i)) }
pub open spec fn lift_action<T>(a: ActionPred<T>) -> TempPred<T> { |ex: Execution<T>, i: nat| a(ex(i), ex(i + 1)) }
pub open spec fn always<T>(p: TempPred<T>) -> TempPred<T> { |ex: Execution<T>, i: nat| forall|j: nat| i <= j ==> #[trigger] p(ex, j) }
pub open spec fn eventually<T>(p: TempPred<T>) -> TempPred<T> { |ex: Execution<T>, i: nat| exists|j: nat| i <= j && #[trigger] p(ex, j) }
pub open spec fn implies<T>(p: TempPred<T>, q: TempPred<T>) -> TempPred<T> { |ex: Execution<T>, i: nat| p(ex, i) ==> q(ex, i) }
pub open spec fn leads_to<T>(p: TempPred<T>, q: TempPred<T>) -> TempPred<T> { always(implies(p, eventually(q))) }
/// Weak fairness of the action `a` whose enabling condition is `en`: if `en` holds from some index on, `a` happens.
pub open spec fn weak_fairness<T>(en: StatePred<T>, a: ActionPred<T>) -> TempPred<T> { leads_to(always(lift_state(en)), lift_action(a)) }

pub open spec fn state_implies<T>(p: StatePred<T>, q: StatePred<T>) -> StatePred<T> { |s: T| p(s) ==> q(s) }
/// `p` survives every step.
pub open spec fn stable<T>(p: StatePred<T>) -> ActionPred<T> { |s: T, s2: T| p(s) ==> p(s2) }
/// The WF1 step premise: from `p` a step reaches `p` or `q`, and an `a` step reaches `q`.
pub open spec fn wf1_step<T>(p: StatePred<T>, q: StatePred<T>, a: ActionPred<T>) -> ActionPred<T> {
    |s: T, s2: T| p(s) ==> (p(s2) || q(s2)) && (a(s, s2) ==> q(s2))
}
pub open spec fn at_measure<T>(p: StatePred<T>, m: spec_fn(T) -> nat, n: nat) -> StatePred<T> { |s: T| p(s) && m(s) == n }
pub open spec fn reached_or_below<T>(q: StatePred<T>, p: StatePred<T>, m: spec_fn(T) -> nat, n: nat) -> StatePred<T> { |s: T| q(s) || (p(s) && m(s) < n) }

/// From `i` on, `p` persists while `q` does not hold, under the WF1 step premise.
proof fn wf1_step_and_no_q_implies_persists<T>(ex: Execution<T>, p: StatePred<T>, q: StatePred<T>, a: ActionPred<T>, i: nat, j: nat)
    requires always(lift_action(wf1_step(p, q, a)))(ex, 0), p(ex(i)), i <= j, forall|k: nat| #![trigger ex(k)] i <= k ==> !q(ex(k)),
    ensures p(ex(j)),
    decreases j - i,
{
    if j > i {
        let k = (j - 1) as nat;
        wf1_step_and_no_q_implies_persists(ex, p, q, a, i, k);
        assert(lift_action(wf1_step(p, q, a))(ex, k));
        assert(!q(ex(k + 1)));
    }
}

/// Rule WF1: if from `p` every step keeps `p` or reaches `q`, an `a` step reaches `q`, `p` enables `a`, and `a` is
/// weakly fair, then `p` leads to `q`.
pub proof fn wf1<T>(ex: Execution<T>, p: StatePred<T>, q: StatePred<T>, en: StatePred<T>, a: ActionPred<T>)
    requires always(lift_action(wf1_step(p, q, a)))(ex, 0), always(lift_state(state_implies(p, en)))(ex, 0), weak_fairness(en, a)(ex, 0),
    ensures leads_to(lift_state(p), lift_state(q))(ex, 0),
{
    assert forall|i: nat| #![trigger implies(lift_state(p), eventually(lift_state(q)))(ex, i)] implies(lift_state(p), eventually(lift_state(q)))(ex, i) by {
        if p(ex(i)) && !eventually(lift_state(q))(ex, i) {
            assert forall|k: nat| #![trigger ex(k)] i <= k implies !q(ex(k)) by { assert(!lift_state(q)(ex, k)); };
            assert forall|j: nat| i <= j implies #[trigger] lift_state(en)(ex, j) by {
                wf1_step_and_no_q_implies_persists(ex, p, q, a, i, j);
                assert(lift_state(state_implies(p, en))(ex, j));
            };
            assert(always(lift_state(en))(ex, i));
            assert(implies(always(lift_state(en)), eventually(lift_action(a)))(ex, i));
            let k = choose|k: nat| i <= k && #[trigger] lift_action(a)(ex, k);
            wf1_step_and_no_q_implies_persists(ex, p, q, a, i, k);
            assert(lift_action(wf1_step(p, q, a))(ex, k));
            assert(!q(ex(k + 1)));
        }
    };
}

/// Every `p` state at measure `n` leads to `q`, by strong induction on `n`.
proof fn measure_step_implies_leads_to_at<T>(ex: Execution<T>, p: StatePred<T>, q: StatePred<T>, m: spec_fn(T) -> nat, n: nat, i: nat)
    requires
        forall|n: nat| #![trigger at_measure(p, m, n)] leads_to(lift_state(at_measure(p, m, n)), lift_state(reached_or_below(q, p, m, n)))(ex, 0),
        p(ex(i)), m(ex(i)) == n,
    ensures eventually(lift_state(q))(ex, i),
    decreases n,
{
    assert(leads_to(lift_state(at_measure(p, m, n)), lift_state(reached_or_below(q, p, m, n)))(ex, 0));
    assert(implies(lift_state(at_measure(p, m, n)), eventually(lift_state(reached_or_below(q, p, m, n))))(ex, i));
    let j = choose|j: nat| i <= j && #[trigger] lift_state(reached_or_below(q, p, m, n))(ex, j);
    if q(ex(j)) { assert(lift_state(q)(ex, j)); }
    else {
        measure_step_implies_leads_to_at(ex, p, q, m, m(ex(j)), j);
        let k = choose|k: nat| j <= k && #[trigger] lift_state(q)(ex, k);
        assert(lift_state(q)(ex, k));
    }
}

/// Rule: if every `p` state leads to `q` or to a `p` state of smaller measure, `p` leads to `q`.
pub proof fn measure_step_implies_leads_to<T>(ex: Execution<T>, p: StatePred<T>, q: StatePred<T>, m: spec_fn(T) -> nat)
    requires forall|n: nat| #![trigger at_measure(p, m, n)] leads_to(lift_state(at_measure(p, m, n)), lift_state(reached_or_below(q, p, m, n)))(ex, 0),
    ensures leads_to(lift_state(p), lift_state(q))(ex, 0),
{
    assert forall|i: nat| #![trigger implies(lift_state(p), eventually(lift_state(q)))(ex, i)] implies(lift_state(p), eventually(lift_state(q)))(ex, i) by {
        if p(ex(i)) { measure_step_implies_leads_to_at(ex, p, q, m, m(ex(i)), i); }
    };
}

/// Rule: if `p` picks, by `sel`, a case `pk(sel(s))` that holds, and every case leads to `q`, then `p` leads to `q`.
pub proof fn cases_leads_to_implies_leads_to<T, X>(ex: Execution<T>, p: StatePred<T>, q: TempPred<T>, sel: spec_fn(T) -> X, pk: spec_fn(X) -> StatePred<T>)
    requires forall|x: X| #![trigger pk(x)] leads_to(lift_state(pk(x)), q)(ex, 0), forall|s: T| #![trigger p(s)] p(s) ==> pk(sel(s))(s),
    ensures leads_to(lift_state(p), q)(ex, 0),
{
    assert forall|i: nat| #![trigger implies(lift_state(p), eventually(q))(ex, i)] implies(lift_state(p), eventually(q))(ex, i) by {
        if p(ex(i)) {
            let x = sel(ex(i));
            assert(leads_to(lift_state(pk(x)), q)(ex, 0));
            assert(implies(lift_state(pk(x)), eventually(q))(ex, i));
        }
    };
}

/// Rule: an inductive state invariant that holds initially always holds.
pub proof fn inductive_implies_always<T>(ex: Execution<T>, inv: StatePred<T>, next: ActionPred<T>)
    requires inv(ex(0)), always(lift_action(next))(ex, 0), forall|s: T, s2: T| #![trigger inv(s), next(s, s2)] inv(s) && next(s, s2) ==> inv(s2),
    ensures always(lift_state(inv))(ex, 0),
{
    assert forall|j: nat| 0 <= j implies #[trigger] lift_state(inv)(ex, j) by { inductive_implies_at(ex, inv, next, j); };
}

proof fn inductive_implies_at<T>(ex: Execution<T>, inv: StatePred<T>, next: ActionPred<T>, j: nat)
    requires inv(ex(0)), always(lift_action(next))(ex, 0), forall|s: T, s2: T| #![trigger inv(s), next(s, s2)] inv(s) && next(s, s2) ==> inv(s2),
    ensures inv(ex(j)),
    decreases j,
{
    if j > 0 {
        let k = (j - 1) as nat;
        inductive_implies_at(ex, inv, next, k);
        assert(lift_action(next)(ex, k));
        assert(ex(k + 1) == ex(j));
    }
}

/// Rule: a stable state predicate that eventually holds eventually always holds.
pub proof fn eventually_stable_implies_eventually_always<T>(ex: Execution<T>, q: StatePred<T>)
    requires eventually(lift_state(q))(ex, 0), always(lift_action(stable(q)))(ex, 0),
    ensures eventually(always(lift_state(q)))(ex, 0),
{
    let j = choose|j: nat| 0 <= j && #[trigger] lift_state(q)(ex, j);
    assert forall|k: nat| j <= k implies #[trigger] lift_state(q)(ex, k) by { stable_implies_at(ex, q, j, k); };
    assert(always(lift_state(q))(ex, j));
}

proof fn stable_implies_at<T>(ex: Execution<T>, q: StatePred<T>, j: nat, k: nat)
    requires q(ex(j)), j <= k, always(lift_action(stable(q)))(ex, 0),
    ensures q(ex(k)),
    decreases k - j,
{
    if k > j {
        let p = (k - 1) as nat;
        stable_implies_at(ex, q, j, p);
        assert(lift_action(stable(q))(ex, p));
        assert(ex(p + 1) == ex(k));
    }
}
} // verus!
