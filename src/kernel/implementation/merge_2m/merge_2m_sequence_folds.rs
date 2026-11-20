use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::{assert_sets_equal, assert_sets_equal_internal, assert_multisets_equal, assert_multisets_equal_internal};

verus! {
pub open spec fn sequence_sum_step<A>(value: spec_fn(A) -> int) -> spec_fn(int, A) -> int {
    |sum: int, entry: A| sum + value(entry)
}

pub open spec fn sequence_sum_fold<A>(values: Seq<A>, value: spec_fn(A) -> int) -> int {
    values.fold_left(0int, sequence_sum_step(value))
}

pub proof fn sequence_index_identity_implies_range_set(values: Seq<usize>)
    requires
        values.len() <= usize::MAX,
        forall|i: int| #![trigger values.spec_index(i)] 0 <= i < values.len() ==> values.spec_index(i) == i,
    ensures
        values.no_duplicates(),
        values.to_set() == Set::<usize>::range(0, values.len() as usize),
{
    assert_sets_equal!(values.to_set(), Set::<usize>::range(0, values.len() as usize), value => {
        values.to_set_ensures();
        if value < values.len() { values.lemma_index_contains(value as int); }
    });
}

pub proof fn sequence_multiset_equality_implies_set_and_distinctness<A>(before: Seq<A>, after: Seq<A>)
    requires
        before.to_multiset() == after.to_multiset(),
    ensures
        before.to_set() == after.to_set(),
        before.no_duplicates() ==> after.no_duplicates(),
{
    assert_sets_equal!(before.to_set(), after.to_set(), value => {
        before.to_set_ensures(); after.to_set_ensures();
        vstd::seq_lib::to_multiset_contains(before, value); vstd::seq_lib::to_multiset_contains(after, value);
    });
    if before.no_duplicates() {
        assert(after.no_duplicates()) by { before.lemma_multiset_has_no_duplicates(); after.lemma_multiset_has_no_duplicates_conv(); };
    }
}

pub proof fn sequence_predicate_implies_zero_failure_fold<A>(values: Seq<A>, predicate: spec_fn(A) -> bool)
    ensures
        values.fold_left(0int, |sum: int, value: A| sum + if predicate(value) { 0int } else { 1int }) >= 0,
        (values.fold_left(0int, |sum: int, value: A| sum + if predicate(value) { 0int } else { 1int }) == 0)
            == (forall|i: int| #![trigger values.spec_index(i)] 0 <= i < values.len() ==> predicate(values.spec_index(i))),
    decreases values.len(),
{
    if values.len() > 0 {
        sequence_predicate_implies_zero_failure_fold(values.drop_last(), predicate);
        values.lemma_add_last_back();
    }
}

pub proof fn sequence_multiset_equality_implies_entry_predicate<A>(before: Seq<A>, after: Seq<A>, predicate: spec_fn(A) -> bool)
    requires
        before.to_multiset() == after.to_multiset(),
        forall|i: int| #![trigger before.spec_index(i)] 0 <= i < before.len() ==> predicate(before.spec_index(i)),
    ensures
        forall|i: int| #![trigger after.spec_index(i)] 0 <= i < after.len() ==> predicate(after.spec_index(i)),
{
    sequence_predicate_implies_zero_failure_fold(before, predicate);
    sequence_predicate_implies_zero_failure_fold(after, predicate);
    vstd::seq_lib::lemma_fold_left_permutation(before, after,
        |sum: int, value: A| sum + if predicate(value) { 0int } else { 1int }, 0int);
}

pub proof fn sequence_mapped_multiset_count_implies_indicator_fold<A, B>(values: Seq<A>, map: spec_fn(A) -> B, target: B)
    ensures
        values.map_values(map).to_multiset().count(target) == values.fold_left(0int, |sum: int, value: A| sum + if map(value) == target { 1int } else { 0int }),
    decreases values.len(),
{
    assert(values.map_values(map).to_multiset().count(target) == values.fold_left(0int, |sum: int, value: A| sum + if map(value) == target { 1int } else { 0int })) by {
        broadcast use { vstd::multiset::axiom_multiset_add, vstd::multiset::axiom_multiset_singleton,
            vstd::multiset::axiom_multiset_singleton_different, vstd::multiset::axiom_multiset_empty };
        if values.len() > 0 {
            sequence_mapped_multiset_count_implies_indicator_fold(values.drop_last(), map, target);
            values.lemma_add_last_back();
            values.drop_last().lemma_push_map_commute(map, values.last());
            vstd::seq_lib::to_multiset_build(values.drop_last().map_values(map), map(values.last()));
        } else {
            vstd::seq_lib::to_multiset_len(values.map_values(map));
            vstd::multiset::lemma_multiset_empty_len(values.map_values(map).to_multiset());
        }
    };
}

pub proof fn sequence_multiset_equality_implies_mapped_multiset_equality<A, B>(before: Seq<A>, after: Seq<A>, map: spec_fn(A) -> B)
    requires
        before.to_multiset() == after.to_multiset(),
    ensures
        before.map_values(map).to_multiset() == after.map_values(map).to_multiset(),
{
    assert_multisets_equal!(before.map_values(map).to_multiset(), after.map_values(map).to_multiset(), target => {
        sequence_mapped_multiset_count_implies_indicator_fold(before, map, target);
        sequence_mapped_multiset_count_implies_indicator_fold(after, map, target);
        vstd::seq_lib::lemma_fold_left_permutation(before, after, |sum: int, value: A| sum + if map(value) == target { 1int } else { 0int }, 0int);
    });
}

pub proof fn sequence_nonnegative_entries_implies_sum_fold_nonnegative<A>(values: Seq<A>, value: spec_fn(A) -> int)
    requires
        forall|i: int| #![trigger values.spec_index(i)] 0 <= i < values.len() ==> value(values.spec_index(i)) >= 0,
    ensures
        sequence_sum_fold(values, value) >= 0,
    decreases values.len(),
{
    if values.len() > 0 { sequence_nonnegative_entries_implies_sum_fold_nonnegative(values.drop_last(), value); }
}

pub proof fn sequence_update_implies_sum_fold_delta<A>(values: Seq<A>, index: int, replacement: A, value: spec_fn(A) -> int)
    requires
        0 <= index < values.len(),
    ensures
        sequence_sum_fold(values.update(index, replacement), value)
            == sequence_sum_fold(values, value) - value(values.spec_index(index)) + value(replacement),
    decreases values.len(),
{
    if index < values.len() - 1 {
        sequence_update_implies_sum_fold_delta(values.drop_last(), index, replacement, value);
        vstd::seq_lib::lemma_seq_take_update_commut1(values, index, replacement, values.len() as int - 1);
    } else {
        vstd::seq_lib::lemma_seq_take_update_commut2(values, index, replacement, values.len() as int - 1);
    }
}

}
