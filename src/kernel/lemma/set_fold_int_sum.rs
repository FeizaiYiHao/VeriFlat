use vstd::prelude::*;
use crate::*;

verus! {
proof fn lemma_iset_fold_int_sum_congruence<A>(s: ISet<A>, lhs: spec_fn(A) -> int, rhs: spec_fn(A) -> int)
    requires
        s.finite(),
        forall|a: A| #![trigger s.contains(a)] s.contains(a) ==> lhs(a) == rhs(a),
    ensures
        s.fold(0int, |sum: int, a: A| sum + lhs(a)) == s.fold(0int, |sum: int, a: A| sum + rhs(a)),
    decreases s.len(),
{
    let lhs_fold = |sum: int, a: A| sum + lhs(a);
    let rhs_fold = |sum: int, a: A| sum + rhs(a);
    let pred = |part: ISet<A>| part.subset_of(s) ==> part.fold(0int, lhs_fold) == part.fold(0int, rhs_fold);
    assert(pred(ISet::empty())) by { vstd::iset::fold::lemma_fold_empty(0int, lhs_fold); vstd::iset::fold::lemma_fold_empty(0int, rhs_fold); };
    assert forall|part: ISet<A>, a: A|
        pred(part) && part.finite() && !part.contains(a)
        implies #[trigger] pred(part.insert(a)) by {
        if part.insert(a).subset_of(s) {
            assert(s.contains(a));
            vstd::iset::fold::lemma_fold_insert(part, 0int, lhs_fold, a);
            vstd::iset::fold::lemma_fold_insert(part, 0int, rhs_fold, a);
        }
    };
    vstd::iset::fold::lemma_finite_set_induct(s, pred);
}

pub proof fn lemma_set_fold_int_sum_congruence<A>(s: Set<A>, lhs: spec_fn(A) -> int, rhs: spec_fn(A) -> int)
    requires
        forall|a: A| #![trigger s.contains(a)] s.contains(a) ==> lhs(a) == rhs(a),
    ensures
        s.fold(0int, |sum: int, a: A| sum + lhs(a)) == s.fold(0int, |sum: int, a: A| sum + rhs(a)),
{ vstd::set::lemma_to_iset_finite(s); lemma_iset_fold_int_sum_congruence(s.to_iset(), lhs, rhs); }

pub proof fn lemma_set_fold_int_sum_empty<A>(s: Set<A>, value: spec_fn(A) -> int)
    requires
        s =~= Set::<A>::empty(),
    ensures
        s.fold(0int, |sum: int, a: A| sum + value(a)) == 0,
{
    let fold = |sum: int, a: A| sum + value(a);
    vstd::iset::fold::lemma_fold_empty(0int, fold);
    assert(s.to_iset() =~= ISet::<A>::empty());
}

pub proof fn lemma_set_fold_int_sum_singleton<A>(s: Set<A>, member: A, value: spec_fn(A) -> int)
    requires
        s =~= Set::<A>::empty().insert(member),
    ensures
        s.fold(0int, |sum: int, a: A| sum + value(a)) == value(member),
{
    let fold = |sum: int, a: A| sum + value(a);
    vstd::iset::fold::lemma_fold_empty(0int, fold);
    vstd::iset::fold::lemma_fold_insert(ISet::<A>::empty(), 0int, fold, member);
    assert(s.to_iset() =~= ISet::<A>::empty().insert(member));
}

proof fn lemma_iset_fold_int_sum_nonneg<A>(s: ISet<A>, value: spec_fn(A) -> int)
    requires
        s.finite(),
        forall|a: A| #![trigger s.contains(a)] s.contains(a) ==> value(a) >= 0,
    ensures
        s.fold(0int, |sum: int, a: A| sum + value(a)) >= 0,
    decreases s.len(),
{
    let fold = |sum: int, a: A| sum + value(a);
    let pred = |part: ISet<A>| part.subset_of(s) ==> part.fold(0int, fold) >= 0;
    assert(pred(ISet::empty())) by { vstd::iset::fold::lemma_fold_empty(0int, fold); };
    assert forall|part: ISet<A>, a: A|
        pred(part) && part.finite() && !part.contains(a)
        implies #[trigger] pred(part.insert(a)) by { if part.insert(a).subset_of(s) { assert(s.contains(a)); vstd::iset::fold::lemma_fold_insert(part, 0int, fold, a); }; };
    vstd::iset::fold::lemma_finite_set_induct(s, pred);
}

pub proof fn lemma_set_fold_int_sum_nonneg<A>(s: Set<A>, value: spec_fn(A) -> int)
    requires
        forall|a: A| #![trigger s.contains(a)] s.contains(a) ==> value(a) >= 0,
    ensures
        s.fold(0int, |sum: int, a: A| sum + value(a)) >= 0,
{ vstd::set::lemma_to_iset_finite(s); lemma_iset_fold_int_sum_nonneg(s.to_iset(), value); }

pub proof fn lemma_set_fold_int_sum_ge_member<A>(s: Set<A>, value: spec_fn(A) -> int, member: A)
    requires
        s.contains(member),
        forall|a: A| #![trigger s.contains(a)] s.contains(a) ==> value(a) >= 0,
    ensures
        s.fold(0int, |sum: int, a: A| sum + value(a)) >= value(member),
{
    let is = s.to_iset();
    let rest = is.remove(member);
    let fold = |sum: int, a: A| sum + value(a);
    vstd::set::lemma_to_iset_finite(s);
    lemma_iset_fold_int_sum_nonneg(rest, value);
    vstd::iset::fold::lemma_fold_insert(rest, 0int, fold, member);
}

pub proof fn lemma_set_fold_int_sum_change_by<A>(s: Set<A>, pre: spec_fn(A) -> int, post: spec_fn(A) -> int, changed: A, delta: int)
    requires
        s.contains(changed),
        post(changed) == pre(changed) + delta,
        forall|a: A| #![trigger s.contains(a)] s.contains(a) && a != changed ==> post(a) == pre(a),
    ensures
        s.fold(0int, |sum: int, a: A| sum + post(a)) == s.fold(0int, |sum: int, a: A| sum + pre(a)) + delta,
{
    let is = s.to_iset();
    let rest = is.remove(changed);
    let pre_fold = |sum: int, a: A| sum + pre(a);
    let post_fold = |sum: int, a: A| sum + post(a);
    vstd::set::lemma_to_iset_finite(s);
    vstd::iset::lemma_iset_remove_finite(is, changed);
    lemma_iset_fold_int_sum_congruence(rest, pre, post);
    vstd::iset::fold::lemma_fold_insert(rest, 0int, pre_fold, changed);
    vstd::iset::fold::lemma_fold_insert(rest, 0int, post_fold, changed);
}

pub proof fn lemma_set_fold_int_sum_insert_zero<A>(s: Set<A>, pre: spec_fn(A) -> int, post: spec_fn(A) -> int, inserted: A)
    requires
        !s.contains(inserted),
        post(inserted) == 0,
        forall|a: A| #![trigger s.contains(a)] s.contains(a) ==> post(a) == pre(a),
    ensures
        s.insert(inserted).fold(0int, |sum: int, a: A| sum + post(a)) == s.fold(0int, |sum: int, a: A| sum + pre(a)),
{
    let post_fold = |sum: int, a: A| sum + post(a);
    lemma_set_fold_int_sum_congruence(s, post, pre);
    vstd::iset::fold::lemma_fold_insert(s.to_iset(), 0int, post_fold, inserted);
    assert(s.insert(inserted).to_iset() =~= s.to_iset().insert(inserted));
}

pub proof fn lemma_set_fold_int_sum_remove<A>(s: Set<A>, pre: spec_fn(A) -> int, post: spec_fn(A) -> int, removed: A)
    requires
        s.contains(removed),
        forall|a: A| #![trigger s.contains(a)] s.contains(a) && a != removed ==> post(a) == pre(a),
    ensures
        s.remove(removed).fold(0int, |sum: int, a: A| sum + post(a)) == s.fold(0int, |sum: int, a: A| sum + pre(a)) - pre(removed),
{
    let rest = s.remove(removed);
    let pre_fold = |sum: int, a: A| sum + pre(a);
    lemma_set_fold_int_sum_congruence(rest, post, pre);
    vstd::set::lemma_to_iset_finite(rest);
    vstd::iset::fold::lemma_fold_insert(rest.to_iset(), 0int, pre_fold, removed);
    assert(s.to_iset() =~= rest.to_iset().insert(removed));
}
}
