use vstd::prelude::*;

use crate::*;

verus! {

/// Congruence for the `total_free_pages_wf` fold: two cache sequences with
/// equal length and pointwise-equal `view().linked_list.len()` produce the
/// same sum. Used to lift the fold across a cache lock/unlock, which changes
/// only an element's lock state (its payload `view()` is preserved by
/// `wlock_ensures`/`wunlock_ensures`), leaving every per-element length equal.
/// The lambda body matches `total_free_pages_wf` verbatim so it unifies at the
/// call sites.
pub proof fn lemma_cache_len_fold_congruence(
    s1: Seq<RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>>,
    s2: Seq<RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>>,
)
    requires
        s1.len() == s2.len(),
        forall|i: int| #![trigger s1[i], s2[i]]
            0 <= i < s1.len() ==>
            s1[i].view().linked_list.len() == s2[i].view().linked_list.len(),
    ensures
        s1.fold_left(0int, |sum: int, cpu_rw_lock: RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>| {sum + cpu_rw_lock.view().linked_list.len()})
            == s2.fold_left(0int, |sum: int, cpu_rw_lock: RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>| {sum + cpu_rw_lock.view().linked_list.len()}),
    decreases s1.len(),
{
    let f = |sum: int, cpu_rw_lock: RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>| {sum + cpu_rw_lock.view().linked_list.len()};
    if s1.len() == 0 {
    } else {
        assert(s1.fold_left(0int, f) == f(s1.drop_last().fold_left(0int, f), s1.last()));
        assert(s2.fold_left(0int, f) == f(s2.drop_last().fold_left(0int, f), s2.last()));
        assert forall|i: int| 0 <= i < s1.drop_last().len()
            implies #[trigger] s1.drop_last()[i].view().linked_list.len() == s2.drop_last()[i].view().linked_list.len()
        by {
            assert(s1.drop_last()[i] == s1[i]);
            assert(s2.drop_last()[i] == s2[i]);
        };
        lemma_cache_len_fold_congruence(s1.drop_last(), s2.drop_last());
        assert(s1.last() == s1[s1.len() - 1]);
        assert(s2.last() == s2[s2.len() - 1]);
    }
}

/// Fold delta: two cache sequences equal everywhere except index `j`, where
/// `s2[j]`'s linked-list length is `s1[j]`'s minus 1, fold to sums differing by
/// 1. Used to re-balance `total_free_pages_wf` after popping one page from
/// `cpu_caches[j]` (cache length −1, matched by ghost total_free_pages −1).
pub proof fn lemma_cache_len_fold_change_one(
    s1: Seq<RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>>,
    s2: Seq<RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>>,
    j: int,
)
    requires
        s1.len() == s2.len(),
        0 <= j < s1.len(),
        s1[j].view().linked_list.len() == s2[j].view().linked_list.len() + 1,
        forall|i: int| #![trigger s1[i]] #![trigger s2[i]]
            0 <= i < s1.len() && i != j ==>
            s1[i].view().linked_list.len() == s2[i].view().linked_list.len(),
    ensures
        s1.fold_left(0int, |sum: int, c: RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>| {sum + c.view().linked_list.len()})
            == s2.fold_left(0int, |sum: int, c: RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>| {sum + c.view().linked_list.len()}) + 1,
    decreases s1.len(),
{
    let f = |sum: int, c: RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>| {sum + c.view().linked_list.len()};
    // s1 nonempty (j is a valid index); peel the last element off each fold.
    assert(s1.fold_left(0int, f) == f(s1.drop_last().fold_left(0int, f), s1.last()));
    assert(s2.fold_left(0int, f) == f(s2.drop_last().fold_left(0int, f), s2.last()));
    assert(s1.last() == s1[s1.len() - 1]);
    assert(s2.last() == s2[s2.len() - 1]);
    if j == s1.len() - 1 {
        // Change is at the last element; prefixes are pointwise-equal length.
        assert forall|i: int| 0 <= i < s1.drop_last().len()
            implies #[trigger] s1.drop_last()[i].view().linked_list.len() == s2.drop_last()[i].view().linked_list.len()
        by {
            assert(s1.drop_last()[i] == s1[i]);
            assert(s2.drop_last()[i] == s2[i]);
        };
        lemma_cache_len_fold_congruence(s1.drop_last(), s2.drop_last());
    } else {
        // Change is in the prefix; last elements have equal length.
        assert forall|i: int| 0 <= i < s1.drop_last().len() && i != j
            implies #[trigger] s1.drop_last()[i].view().linked_list.len() == s2.drop_last()[i].view().linked_list.len()
        by {
            assert(s1.drop_last()[i] == s1[i]);
            assert(s2.drop_last()[i] == s2[i]);
        };
        assert(s1.drop_last()[j] == s1[j]);
        assert(s2.drop_last()[j] == s2[j]);
        lemma_cache_len_fold_change_one(s1.drop_last(), s2.drop_last(), j);
    }
}

/// Array-facing wrapper for `lemma_cache_len_fold_change_one`: takes the two
/// `cpu_caches` arrays directly (not their `view()`), so the "unchanged
/// elsewhere" hypothesis is `new_arr.unchanged_except(old_arr, j)` — the exact
/// term `LockedArray::borrow_mut` delivers, no call-site `spec_index → view`
/// bridge. The `spec_index → view()` congruence lives here, once.
#[verifier::spinoff_prover]
pub proof fn lemma_cache_len_fold_change_one_array(
    old_arr: LockedArray<AllocatorCache, (), (), (), NUM_CPUS, NO_KILL_STATE>,
    new_arr: LockedArray<AllocatorCache, (), (), (), NUM_CPUS, NO_KILL_STATE>,
    j: int,
)
    requires
        old_arr.inv(),
        new_arr.inv(),
        0 <= j < NUM_CPUS,
        new_arr.unchanged_except(&old_arr, j as usize),
        old_arr.spec_index(j as usize).view().view().linked_list.len()
            == new_arr.spec_index(j as usize).view().view().linked_list.len() + 1,
    ensures
        old_arr.view().fold_left(0int, |sum: int, c: RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>| {sum + c.view().linked_list.len()})
            == new_arr.view().fold_left(0int, |sum: int, c: RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>| {sum + c.view().linked_list.len()}) + 1,
{
    assert forall|i: int| #![trigger old_arr.view()[i], new_arr.view()[i]]
        0 <= i < old_arr.view().len() && i != j
        implies old_arr.view()[i].view().linked_list.len() == new_arr.view()[i].view().linked_list.len()
    by {
        assert(new_arr[i as usize] === old_arr[i as usize]);
    };
    lemma_cache_len_fold_change_one(old_arr.view(), new_arr.view(), j);
}

/// The `total_free_pages_wf` fold is nonnegative — every summand is a
/// `usize` length. Peeled-last induction; used to bound the fold from below.
pub proof fn lemma_cache_len_fold_nonneg(
    s: Seq<RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>>,
)
    ensures
        s.fold_left(0int, |sum: int, c: RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>| {sum + c.view().linked_list.len()}) >= 0,
    decreases s.len(),
{
    let f = |sum: int, c: RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>| {sum + c.view().linked_list.len()};
    if s.len() == 0 {
    } else {
        assert(s.fold_left(0int, f) == f(s.drop_last().fold_left(0int, f), s.last()));
        lemma_cache_len_fold_nonneg(s.drop_last());
    }
}

/// Lower bound: the `total_free_pages_wf` fold is at least any single cache's
/// length. Used to prove `total_free_pages >= 1` before decrementing on a pop
/// (the popped cache is nonempty, so the fold — and thus the total — is >= 1).
pub proof fn lemma_cache_len_fold_ge_elem(
    s: Seq<RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>>,
    j: int,
)
    requires
        0 <= j < s.len(),
    ensures
        s.fold_left(0int, |sum: int, c: RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>| {sum + c.view().linked_list.len()}) >= s[j].view().linked_list.len(),
    decreases s.len(),
{
    let f = |sum: int, c: RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>| {sum + c.view().linked_list.len()};
    assert(s.fold_left(0int, f) == f(s.drop_last().fold_left(0int, f), s.last()));
    assert(s.last() == s[s.len() - 1]);
    if j == s.len() - 1 {
        lemma_cache_len_fold_nonneg(s.drop_last());
    } else {
        assert(s.drop_last()[j] == s[j]);
        lemma_cache_len_fold_ge_elem(s.drop_last(), j);
    }
}

/// The `total_free_pages_wf` fold is zero when every cache's list is empty.
/// Peeled-last induction; used to show that after a failed cache scan (all
/// caches empty) the whole free-page total sits in the global pool.
pub proof fn lemma_cache_len_fold_all_zero(
    s: Seq<RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>>,
)
    requires
        forall|j: int| #![trigger s[j]] 0 <= j < s.len() ==> s[j].view().linked_list.view().len() == 0,
    ensures
        s.fold_left(0int, |sum: int, c: RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>| {sum + c.view().linked_list.len()}) == 0,
    decreases s.len(),
{
    let f = |sum: int, c: RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>| {sum + c.view().linked_list.len()};
    if s.len() == 0 {
    } else {
        assert(s.fold_left(0int, f) == f(s.drop_last().fold_left(0int, f), s.last()));
        assert(s.last() == s[s.len() - 1]);
        assert forall|j: int| #![trigger s.drop_last()[j]] 0 <= j < s.drop_last().len() implies s.drop_last()[j].view().linked_list.view().len() == 0 by {
            assert(s.drop_last()[j] == s[j]);
        };
        lemma_cache_len_fold_all_zero(s.drop_last());
    }
}

}
