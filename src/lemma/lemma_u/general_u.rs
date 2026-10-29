use vstd::prelude::*;
verus! {
pub proof fn seq_filter_map_push_lemma<A, B>(s: Seq<A>, value: A, f: spec_fn(A) -> Option<B>)
    ensures
        s.push(value).filter_map(f) == match f(value) {
            Some(v) => s.filter_map(f).push(v),
            None => s.filter_map(f),
        },
{
    vstd::assert_seqs_equal!(s.push(value).drop_last() == s);
    if let Some(v) = f(value) {
        vstd::assert_seqs_equal!(s.filter_map(f) + seq![v] == s.filter_map(f).push(v));
    }
}

pub proof fn map_insert_remove_absent_lemma<K, V>(m: Map<K, V>, key: K, value: V)
    requires
        !m.dom().contains(key),
    ensures
        m.insert(key, value).remove(key) == m,
{
}

pub proof fn map_insert_overwrite_lemma<K, V>(m: Map<K, V>, key: K, old_value: V, new_value: V)
    ensures
        m.insert(key, old_value).insert(key, new_value) == m.insert(key, new_value),
{
}

pub proof fn map_union_remove_right_domain_disjoint_lemma<K, V>(left: Map<K, V>, right: Map<K, V>)
    requires
        left.dom().disjoint(right.dom()),
    ensures
        left.union_prefer_right(right).remove_keys(right.dom()) == left,
{
}

pub proof fn seq_push_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A, x: A| s.contains(x) ==> s.push(v).contains(v) && s.push(v).contains(x),
        forall|s: Seq<A>, v: A| #![auto] s.push(v).contains(v),
        forall|s: Seq<A>, v: A, x: A| !s.contains(x) && v != x ==> !s.push(v).contains(x),
{
    broadcast use vstd::seq_lib::lemma_seq_contains_after_push;
}

pub proof fn seq_push_head_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A, x: A| s.contains(x) ==> s.insert(0, v).contains(v) && s.insert(0, v).contains(x),
        forall|s: Seq<A>, v: A| #![auto] s.insert(0, v).contains(v),
        forall|s: Seq<A>, v: A, x: A| !s.contains(x) && v != x ==> !s.insert(0, v).contains(x),
{
    assert forall|s: Seq<A>, v: A, x: A| s.contains(x) implies #[trigger] s.insert(0, v).contains(v) && #[trigger] s.insert(0, v).contains(x) by { s.insert_ensures(0, v); }
    assert forall|s: Seq<A>, v: A| #[trigger] s.insert(0, v).contains(v) by { s.insert_ensures(0, v); }
}

pub proof fn seq_skip_index_of_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A,| #![auto] s.len() != 0 && s.no_duplicates() && s.contains(v) && s.spec_index(0) != v ==> s.skip(1).index_of(v) == s.index_of(v) - 1,
{
    assert forall|s: Seq<A>, v: A| s.len() != 0 && s.no_duplicates() && #[trigger] s.contains(v) && s.spec_index(0) != v implies s.skip(1).index_of(v) == s.index_of(v) - 1 by {
        assert(s.skip(1).spec_index(s.index_of(v) - 1) == v) by { vstd::seq_lib::lemma_seq_skip_index2(s, 1, s.index_of(v)); };
    }
}

pub proof fn seq_skip_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A| s.len() > 0 && s.spec_index(0) != v ==> (s.skip(1).contains(v) == s.contains(v)),
        forall|s: Seq<A>| #![trigger s.spec_index(0)] s.len() > 0 ==> s.contains(s.spec_index(0)),
        forall|s: Seq<A>| #![trigger s.spec_index(0)] s.len() > 0 && s.no_duplicates() ==> !s.skip(1).contains(s.spec_index(0)),
        forall|s: Seq<A>, v: A| s.len() > 0 && s.spec_index(0) == v && s.no_duplicates() ==> s.skip(1) =~= s.remove_value(v),
        forall|s: Seq<A>, i: int| 0 <= i < s.len() - 1 ==> s.skip(1).spec_index(i) == s.spec_index(i + 1),
{
    assert forall|s: Seq<A>, v: A| s.len() > 0 && s.spec_index(0) != v implies (s.skip(1).contains(v) == s.contains(v)) by {
        if s.contains(v) {
            assert(s.skip(1).contains(v)) by { vstd::seq_lib::lemma_seq_skip_index2(s, 1, s.index_of(v)); };
        }
    }

    assert forall|s: Seq<A>, v: A| s.len() > 0 && s.spec_index(0) == v && s.no_duplicates() implies s.skip(1) =~= s.remove_value(v) by { s.index_of_first_ensures(v); }
}

pub proof fn seq_remove_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A, i: int| #![trigger s.subrange(0, i), s.contains(v)] 0 <= i < s.len() && s.contains(v) && s.spec_index(i) != v && s.no_duplicates() ==> s.subrange(0, i).add(s.subrange(i + 1, s.len() as int)).contains(v),
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.subrange(0, i), s.contains(v)]
            0 <= i < s.len() && s.contains(v) && s.spec_index(i) == v && s.no_duplicates() ==> s.subrange(0, i).add(s.subrange(i + 1, s.len() as int)).contains(v) == false,
        forall|s: Seq<A>, i: int, j: int| #![trigger s.subrange(0, i), s.spec_index(j)] 0 <= j < i <= s.len() ==> s.subrange(0, i).add(s.subrange(i + 1, s.len() as int)).spec_index(j) == s.spec_index(j),
        forall|s: Seq<A>, i: int, j: int| #![trigger s.subrange(0, i), s.spec_index(j + 1)] 0 <= i <= j < s.len() - 1 ==> s.subrange(0, i).add(s.subrange(i + 1, s.len() as int)).spec_index(j) == s.spec_index(j + 1),
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.remove_value(v), s.subrange(0, i)]
            0 <= i < s.len() && s.contains(v) && s.spec_index(i) == v && s.no_duplicates() ==> s.subrange(0, i).add(s.subrange(i + 1, s.len() as int)) == s.remove_value(v),
{
    assert forall|s: Seq<A>, v: A, i: int| 0 <= i < s.len() && s.contains(v) && s.spec_index(i) != v && s.no_duplicates() implies #[trigger] s.subrange(0, i).add(s.subrange(i + 1, s.len() as int)).contains(v) by {
        let s2 = s.subrange(0, i).add(s.subrange(i + 1, s.len() as int));
        let k = s.index_of(v);
        if k < i {
            assert(0 <= k < s2.len() && s2.spec_index(k) == v) by { s.remove_ensures(i); };
        } else {
            assert(0 <= k - 1 < s2.len() && s2.spec_index(k - 1) == v) by { s.remove_ensures(i); };
        }
    }

    assert forall|s: Seq<A>, v: A, i: int| 0 <= i < s.len() && s.contains(v) && s.spec_index(i) == v && s.no_duplicates() implies #[trigger] s.subrange(0, i).add(s.subrange(i + 1, s.len() as int)) == #[trigger] s.remove_value(v) by {
        s.index_of_first_ensures(v);
    }
}

pub proof fn seq_push_unique_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A| #![auto] s.no_duplicates() && s.contains(v) == false ==> s.push(v).no_duplicates() && s.push(v).index_of(v) == s.push(v).len() - 1,
        forall|s: Seq<A>, v: A, y: A| #![auto] s.no_duplicates() && s.contains(v) && s.contains(y) == false ==> s.push(y).index_of(v) == s.index_of(v),
{
    assert forall|s: Seq<A>, v: A| s.no_duplicates() && !#[trigger] s.contains(v) implies s.push(v).no_duplicates() && s.push(v).index_of(v) == s.push(v).len() - 1 by {
        let s2 = s.push(v);
        assert(s2.index_of(v) == s.len()) by { vstd::seq::lemma_seq_push_index_same(s, v, s.len() as int); };
    }

    assert forall|s: Seq<A>, v: A, y: A| s.no_duplicates() && s.contains(v) && !s.contains(y) implies s.push(y).index_of(v) == s.index_of(v) by {
        let s2 = s.push(y);
        let i = s.index_of(v);
        assert(s2.index_of(v) == i) by {
            vstd::seq::lemma_seq_push_index_different(s, y, i);
            let k = s2.index_of(v);
            if k != i { if k == s.len() { } else { vstd::seq::lemma_seq_push_index_different(s, y, k); } }
        };
    }
}

pub proof fn seq_push_head_unique_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A| #![auto] s.no_duplicates() && s.contains(v) == false ==> s.insert(0, v).no_duplicates() && s.insert(0, v).index_of(v) == 0,
{
    assert forall|s: Seq<A>, v: A| s.no_duplicates() && !#[trigger] s.contains(v) implies s.insert(0, v).no_duplicates() && s.insert(0, v).index_of(v) == 0 by {
        s.insert_ensures(0, v);
    }
}

pub proof fn lemma_seq_remove_value_membership<A>()
    ensures
        forall|s: Seq<A>, v: A, x: A| x != v && s.no_duplicates() ==> s.remove_value(x).contains(v) == s.contains(v),
        forall|s: Seq<A>, v: A| #![auto] s.no_duplicates() ==> s.remove_value(v).contains(v) == false,
{
    assert forall|s: Seq<A>, v: A, x: A| x != v && s.no_duplicates() implies s.remove_value(x).contains(v) == s.contains(v) by {
        s.index_of_first_ensures(x);
        match s.index_of_first(x) {
            Some(i) => {
                let s2 = s.remove(i);
                s.remove_ensures(i);
                if s2.contains(v) {
                    s2.index_of_first_ensures(v);
                    let j = s2.index_of_first(v).unwrap();
                    assert(s.contains(v)) by { s.remove_ensures(i); };
                }
                if s.contains(v) {
                    s.index_of_first_ensures(v);
                    let j = s.index_of_first(v).unwrap();
                    if j < i {
                        assert(0 <= j < s2.len() && s2.spec_index(j) == v) by { s.remove_ensures(i); };
                    } else {
                        assert(0 <= j - 1 < s2.len() && s2.spec_index(j - 1) == v) by { s.remove_ensures(i); };
                    }
                }
            }
            None => {}
        }
    }

    assert forall|s: Seq<A>, v: A| s.no_duplicates() implies #[trigger] s.remove_value(v).contains(v) == false by {
        s.index_of_first_ensures(v);
        match s.index_of_first(v) {
            Some(i) => {
                let s2 = s.remove(i);
                s.remove_ensures(i);
                if s2.contains(v) {
                    s2.index_of_first_ensures(v);
                    let j = s2.index_of_first(v).unwrap();
                    let original_j = if j < i { j } else { j + 1 };
                    assert({
                        &&& 0 <= original_j < s.len()
                        &&& original_j != i
                        &&& s.spec_index(original_j) == v
                    }) by { s.remove_ensures(i); };
                }
            }
            None => {}
        }
    }
}

pub proof fn seq_index_lemma<A>()
    ensures
        forall|s: Seq<A>, i: int| #![trigger s.spec_index(i)] 0 <= i < s.len() && s.no_duplicates() ==> s.index_of(s.spec_index(i)) == i,
{
}

pub proof fn seq_fold_upper_bound<A>(s: Seq<A>, f: spec_fn(int, A) -> int, upper: int)
    requires
        forall|i: int, sum: int| #![trigger f(sum, s.spec_index(i))] 0 <= i < s.len() ==> f(sum, s.spec_index(i)) <= sum + upper,
    ensures
        s.fold_left(0int, f) <= s.len() * upper,
    decreases s.len(),
{
    if s.len() != 0 {
        assert(s.drop_last().fold_left(0int, f) <= (s.len() - 1) * upper) by { seq_fold_upper_bound(s.drop_last(), f, upper); };
        assert((s.len() - 1) * upper + upper == s.len() * upper) by { vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(upper, s.len() - 1, 1); };
    }
}

pub proof fn seq_unique_bounded_usize_len(s: Seq<usize>, bound: usize)
    requires
        s.no_duplicates(),
        forall|value: usize| #![trigger s.contains(value)] s.contains(value) ==> value < bound,
    ensures
        s.len() <= bound,
{
    let range = <usize as vstd::set_lib::FiniteRange>::range_set(0usize, bound);
    assert(s.to_set().subset_of(range) && range.len() == bound) by { <usize as vstd::set_lib::FiniteRange>::range_properties(0usize, bound); s.to_set_ensures(); };
    assert(s.len() == s.to_set().len() && s.to_set().len() <= range.len()) by { s.unique_seq_to_set(); vstd::set_lib::lemma_len_subset(s.to_set(), range); };
}
} // verus!
