use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::{assert_sets_equal, assert_sets_equal_internal};

verus! {
pub proof fn sequence_union_fold_implies_entry_subset<A>(values: Seq<Set<A>>, index: int)
    requires
        0 <= index < values.len(),
    ensures
        values.spec_index(index).subset_of(values.fold_left(Set::<A>::empty(), |state: Set<A>, value: Set<A>| state.union(value))),
    decreases values.len(),
{
    reveal_with_fuel(Seq::fold_left, 2);
    if index < values.len() - 1 { sequence_union_fold_implies_entry_subset(values.drop_last(), index); }
}

pub proof fn sequence_entries_subset_implies_union_fold_subset<A>(values: Seq<Set<A>>, target: Set<A>)
    requires
        forall|i: int| #![trigger values.spec_index(i)] 0 <= i < values.len() ==> values.spec_index(i).subset_of(target),
    ensures
        values.fold_left(Set::<A>::empty(), |state: Set<A>, value: Set<A>| state.union(value)).subset_of(target),
    decreases values.len(),
{
    reveal_with_fuel(Seq::fold_left, 2);
    if values.len() > 0 { sequence_entries_subset_implies_union_fold_subset(values.drop_last(), target); }
}

pub proof fn sequence_entries_exclude_implies_union_fold_excludes<A>(values: Seq<Set<A>>, removed: A)
    requires
        forall|i: int| #![trigger values.spec_index(i)] 0 <= i < values.len() ==> !values.spec_index(i).contains(removed),
    ensures
        !values.fold_left(Set::<A>::empty(), |state: Set<A>, value: Set<A>| state.union(value)).contains(removed),
    decreases values.len(),
{
    reveal_with_fuel(Seq::fold_left, 2);
    if values.len() > 0 { sequence_entries_exclude_implies_union_fold_excludes(values.drop_last(), removed); }
}

pub proof fn sequence_update_implies_union_fold_remove<A>(values: Seq<Set<A>>, index: int, replacement: Set<A>, removed: A)
    requires
        0 <= index < values.len(),
        values.spec_index(index) == replacement.insert(removed),
        !replacement.contains(removed),
        forall|i: int| #![trigger values.spec_index(i)] 0 <= i < values.len() && i != index ==> !values.spec_index(i).contains(removed),
    ensures
        values.update(index, replacement).fold_left(Set::<A>::empty(), |state: Set<A>, value: Set<A>| state.union(value))
            == values.fold_left(Set::<A>::empty(), |state: Set<A>, value: Set<A>| state.union(value)).remove(removed),
    decreases values.len(),
{
    reveal_with_fuel(Seq::fold_left, 2);
    if index < values.len() - 1 {
        sequence_update_implies_union_fold_remove(values.drop_last(), index, replacement, removed);
        vstd::seq_lib::lemma_seq_take_update_commut1(values, index, replacement, values.len() as int - 1);
    } else {
        vstd::seq_lib::lemma_seq_take_update_commut2(values, index, replacement, values.len() as int - 1);
        sequence_entries_exclude_implies_union_fold_excludes(values.drop_last(), removed);
    }
    assert_sets_equal!(values.update(index, replacement).fold_left(Set::<A>::empty(), |state: Set<A>, value: Set<A>| state.union(value)),
        values.fold_left(Set::<A>::empty(), |state: Set<A>, value: Set<A>| state.union(value)).remove(removed));
}
pub proof fn sequence_multiset_subset_implies_union_fold_subset<A>(before: Seq<Set<A>>, after: Seq<Set<A>>)
    requires
        before.to_multiset().subset_of(after.to_multiset()),
    ensures
        before.fold_left(Set::<A>::empty(), |state: Set<A>, value: Set<A>| state.union(value)).subset_of(after.fold_left(Set::<A>::empty(), |state: Set<A>, value: Set<A>| state.union(value))),
    decreases before.len(),
{
    reveal_with_fuel(Seq::fold_left, 2);
    if before.len() > 0 {
        before.lemma_add_last_back(); before.drop_last().to_multiset_ensures(); after.to_multiset_ensures();
        vstd::multiset::lemma_insert_increases_count_by_1(before.drop_last().to_multiset(), before.last());
        sequence_multiset_subset_implies_union_fold_subset(before.drop_last(), after);
        after.index_of_first_ensures(before.last());
        sequence_union_fold_implies_entry_subset(after, after.index_of_first(before.last()).unwrap());
    }
}

pub proof fn sequence_multiset_equality_implies_union_fold_equality<A>(before: Seq<Set<A>>, after: Seq<Set<A>>)
    requires
        before.to_multiset() == after.to_multiset(),
    ensures
        before.fold_left(Set::<A>::empty(), |state: Set<A>, value: Set<A>| state.union(value)) == after.fold_left(Set::<A>::empty(), |state: Set<A>, value: Set<A>| state.union(value)),
{
    sequence_multiset_subset_implies_union_fold_subset(before, after); sequence_multiset_subset_implies_union_fold_subset(after, before);
    assert_sets_equal!(before.fold_left(Set::<A>::empty(), |state: Set<A>, value: Set<A>| state.union(value)), after.fold_left(Set::<A>::empty(), |state: Set<A>, value: Set<A>| state.union(value)));
}

pub proof fn sequence_pointwise_subset_implies_union_fold_subset<A>(before: Seq<Set<A>>, after: Seq<Set<A>>)
    requires
        before.len() == after.len(),
        forall|i: int| #![trigger after.spec_index(i)] 0 <= i < before.len() ==> after.spec_index(i).subset_of(before.spec_index(i)),
    ensures
        after.fold_left(Set::<A>::empty(), |state: Set<A>, value: Set<A>| state.union(value)).subset_of(before.fold_left(Set::<A>::empty(), |state: Set<A>, value: Set<A>| state.union(value))),
    decreases before.len(),
{
    reveal_with_fuel(Seq::fold_left, 2);
    if before.len() > 0 { sequence_pointwise_subset_implies_union_fold_subset(before.drop_last(), after.drop_last()); }
}

pub proof fn sequence_pointwise_filter_implies_union_fold_filter<A>(before: Seq<Set<A>>, after: Seq<Set<A>>, predicate: spec_fn(A) -> bool)
    requires
        before.len() == after.len(),
        forall|i: int, x: A| #![trigger after.spec_index(i).contains(x)] #![trigger before.spec_index(i).contains(x)] 0 <= i < before.len() ==>
            after.spec_index(i).contains(x) == (before.spec_index(i).contains(x) && predicate(x)),
    ensures
        after.fold_left(Set::<A>::empty(), |state: Set<A>, value: Set<A>| state.union(value))
            == before.fold_left(Set::<A>::empty(), |state: Set<A>, value: Set<A>| state.union(value)).filter(predicate),
    decreases before.len(),
{
    reveal_with_fuel(Seq::fold_left, 2);
    if before.len() > 0 { sequence_pointwise_filter_implies_union_fold_filter(before.drop_last(), after.drop_last(), predicate); }
    assert_sets_equal!(after.fold_left(Set::<A>::empty(), |state: Set<A>, value: Set<A>| state.union(value)),
        before.fold_left(Set::<A>::empty(), |state: Set<A>, value: Set<A>| state.union(value)).filter(predicate));
}

}
