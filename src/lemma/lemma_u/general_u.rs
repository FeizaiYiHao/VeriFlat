use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_sets_equal};
verus! {

pub broadcast proof fn map_equal_implies_submap_each_other<K, V>(a: Map<K, V>, b: Map<K, V>)
    requires
        a =~= b,
    ensures
        #[trigger] a.submap_of(b),
        b.submap_of(a),
{
    assert(a == b);
}

pub broadcast proof fn submap_by_transitivity<K, V>(a: Map<K, V>, b: Map<K, V>, c: Map<K, V>)
    requires
        #[trigger] a.submap_of(b),
        #[trigger] b.submap_of(c),
    ensures
        a.submap_of(c),
{
    assert(forall|k: K|
        #![trigger a.dom().contains(k)]
        #![trigger b.dom().contains(k)]
        a.dom().contains(k) ==> b.dom().contains(k) && a.spec_index(k) == b.spec_index(k));
}
pub proof fn set_insert_remove_absent_lemma<A>(s: Set<A>, a: A)
    requires
        !s.contains(a),
    ensures
        s.insert(a).remove(a) == s,
{
    assert_sets_equal!(
        s.insert(a).remove(a) == s,
        x => {
            if x == a {
                vstd::set::lemma_set_remove_same(s.insert(a), a);
            } else {
                vstd::set::lemma_set_insert_different(s, x, a);
                vstd::set::lemma_set_remove_different(
                    s.insert(a), x, a,
                );
            }
        }
    );
}

pub proof fn map_insert_remove_absent_lemma<K, V>(m: Map<K, V>, key: K, value: V)
    requires
        !m.dom().contains(key),
    ensures
        m.insert(key, value).remove(key) == m,
{
    assert_maps_equal!(m.insert(key, value).remove(key), m);
}

pub proof fn map_insert_overwrite_lemma<K, V>(
    m: Map<K, V>,
    key: K,
    old_value: V,
    new_value: V,
)
    ensures
        m.insert(key, old_value).insert(key, new_value)
            == m.insert(key, new_value),
{
    assert_maps_equal!(
        m.insert(key, old_value).insert(key, new_value),
        m.insert(key, new_value),
    );
}

pub proof fn map_union_remove_right_domain_disjoint_lemma<K, V>(
    left: Map<K, V>,
    right: Map<K, V>,
)
    requires
        left.dom().disjoint(right.dom()),
    ensures
        left.union_prefer_right(right).remove_keys(right.dom()) == left,
{
    assert_maps_equal!(
        left.union_prefer_right(right).remove_keys(right.dom()),
        left,
    );
}

pub broadcast proof fn seq_drop_first_contains_iff<A>(s: Seq<A>, a: A)
    requires
        s.len() > 0,
    ensures
        #[trigger] s.contains(a)
            == (a == s.spec_index(0) || #[trigger] s.drop_first().contains(a)),
{
    broadcast use vstd::seq_lib::lemma_seq_contains;
    vstd::seq_lib::lemma_seq_skip_contains(s, 1, a);
}

pub proof fn seq_drop_first_contains_iff_forall<A>(s: Seq<A>)
    requires
        s.len() > 0,
    ensures
        forall|a: A|
            #![trigger s.contains(a)]
            s.contains(a)
                == (a == s.spec_index(0) || s.drop_first().contains(a)),
        forall|a: A|
            #![trigger s.drop_first().contains(a)]
            s.drop_first().contains(a) ==> s.contains(a),
{
    broadcast use seq_drop_first_contains_iff;
}


pub proof fn seq_push_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A, x: A|
            s.contains(x) ==> s.push(v).contains(v) && s.push(v).contains(x),
        forall|s: Seq<A>, v: A| #![auto] s.push(v).contains(v),
        forall|s: Seq<A>, v: A, x: A| !s.contains(x) && v != x ==> !s.push(v).contains(x),
{
    broadcast use vstd::seq_lib::lemma_seq_contains_after_push;
}

pub proof fn seq_push_head_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A, x: A|
            s.contains(x) ==> s.insert(0, v).contains(v) && s.insert(0, v).contains(x),
        forall|s: Seq<A>, v: A| #![auto] s.insert(0, v).contains(v),
        forall|s: Seq<A>, v: A, x: A| !s.contains(x) && v != x ==> !s.insert(0, v).contains(x),
{
    assert forall|s: Seq<A>, v: A, x: A|
        s.contains(x) implies #[trigger] s.insert(0, v).contains(v) && #[trigger] s.insert(0, v).contains(x) by {
        s.insert_ensures(0, v);
        let s2 = s.insert(0, v);
        let i = choose|i: int| 0 <= i < s.len() && s.spec_index(i) == x;
        assert(s2.spec_index(i + 1) == x);
        assert(s2.spec_index(0) == v);
    }
    assert forall|s: Seq<A>, v: A| #[trigger] s.insert(0, v).contains(v) by {
        s.insert_ensures(0, v);
        let s2 = s.insert(0, v);
        assert(s2.spec_index(0) == v);
    }
    assert forall|s: Seq<A>, v: A, x: A|
        !s.contains(x) && v != x implies !#[trigger] s.insert(0, v).contains(x) by {
        s.insert_ensures(0, v);
        let s2 = s.insert(0, v);
        if s2.contains(x) {
            let i = choose|i: int| 0 <= i < s2.len() && s2.spec_index(i) == x;
            if i == 0 {
                assert(s2.spec_index(0) == v);
            } else {
                assert(0 <= i - 1 < s.len());
                assert(s.spec_index(i - 1) == s2.spec_index(i));
                assert(s.contains(x));
            }
        }
    }
}

pub proof fn seq_push_index_of_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A, x: A|
            s.no_duplicates() && s.contains(v) && v != x
            ==> 
            s.push(x).index_of(v) == s.index_of(v),
{
    assert forall|s: Seq<A>, v: A, x: A|
        s.no_duplicates() && s.contains(v) && v != x implies
        s.push(x).index_of(v) == s.index_of(v) by
    {
        let i = s.index_of(v);
        let s2 = s.push(x);
        assert(0 <= i < s.len()) by {
            let j = choose|j: int| 0 <= j < s.len() && s.spec_index(j) == v;
            assert(s.spec_index(j) == v);
        }
        assert(s.spec_index(i) == v);
        assert(s2.spec_index(i) == v);
        assert(s2.len() == s.len() + 1);
        assert(s2.spec_index(s.len() as int) == x);
        // s2.no_duplicates because s has no dup and x not in s (since v != x and s.contains(v))
        // Actually we don't know x not in s; but we don't need s2.no_duplicates. We need to show
        // the chosen index i is unique in s2 for value v.
        let j = s2.index_of(v);
        assert(0 <= j < s2.len() && s2.spec_index(j) == v) by {
            let k = choose|k: int| 0 <= k < s2.len() && s2.spec_index(k) == v;
            assert(s2.spec_index(k) == v);
        }
        if j != i {
            if j == s.len() {
                assert(s2.spec_index(j) == x);
                assert(x == v);
            } else {
                assert(0 <= j < s.len());
                assert(s.spec_index(j) == v);
                assert(s.spec_index(i) == v);
                // contradicts no_duplicates
                assert(s.no_duplicates());
            }
        }
    }
}

pub proof fn seq_skip_index_of_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A,|
            #![auto]
            s.len() != 0 && s.no_duplicates() && s.contains(v) && s.spec_index(0) != v
            ==> 
            s.skip(1).index_of(v) == s.index_of(v) - 1,
{
    assert forall|s: Seq<A>, v: A|
        s.len() != 0 && s.no_duplicates() && #[trigger] s.contains(v) && s.spec_index(0) != v implies
        s.skip(1).index_of(v) == s.index_of(v) - 1 by
    {
        let s2 = s.skip(1);
        assert(s2.len() == s.len() - 1);
        let i = s.index_of(v);
        assert(0 <= i < s.len() && s.spec_index(i) == v) by {
            let j = choose|j: int| 0 <= j < s.len() && s.spec_index(j) == v;
            assert(s.spec_index(j) == v);
        }
        // i != 0 because s[0] != v
        assert(i != 0);
        // s2[i-1] == s[i] == v
        assert(s2.spec_index(i - 1) == s.spec_index((i - 1) + 1));
        assert(s2.spec_index(i - 1) == v);
        // The chosen index of v in s2:
        let k = s2.index_of(v);
        assert(0 <= k < s2.len() && s2.spec_index(k) == v) by {
            let j = choose|j: int| 0 <= j < s2.len() && s2.spec_index(j) == v;
            assert(s2.spec_index(j) == v);
        }
        if k != i - 1 {
            // s[k+1] == s2[k] == v, and s[i] == v, with k+1 != i, contradicting no_duplicates
            assert(s2.spec_index(k) == s.spec_index(k + 1));
            assert(s.spec_index(k + 1) == v);
            assert(s.spec_index(i) == v);
            assert(s.no_duplicates());
        }
    }
}
pub proof fn seq_to_set_lemma<A>()
    ensures
        forall|s: Seq<A>, a: A|
            #![trigger s.contains(a)]
            #![trigger s.to_set().contains(a)]
            s.contains(a) == s.to_set().contains(a),
{
    assert forall|s: Seq<A>, a: A|
        #![trigger s.contains(a)]
        #![trigger s.to_set().contains(a)]
        s.contains(a) == s.to_set().contains(a) by {
    }
}

// SPEC FIX: 1st conjunct claimed s.drop_last().contains(s[s.len()-1]) which contradicts
// no_duplicates. Fixed to !s.drop_last().contains(s[s.len()-1]).
pub proof fn seq_pop_unique_lemma<A>()
    ensures
        forall|s: Seq<A>, i: int|
            s.no_duplicates() && 0 <= i < s.len() - 1 ==> !s.drop_last().contains(s.spec_index(s.len() - 1))
                && s.drop_last().spec_index(i) == s.spec_index(i),
        forall|s: Seq<A>, v: A|
            s.no_duplicates() && s.len() > 0 && s.spec_index(s.len() - 1) == v ==> s.drop_last().to_set().contains(v)
                == false,
        forall|s: Seq<A>, v: A|
            s.no_duplicates() && s.len() > 0 && s.spec_index(s.len() - 1) != v ==> s.drop_last().to_set().contains(v)
                == s.to_set().contains(v),
{
    assert forall|s: Seq<A>, i: int|
        s.no_duplicates() && 0 <= i < s.len() - 1 implies !s.drop_last().contains(s.spec_index(s.len() - 1))
        && s.drop_last().spec_index(i) == s.spec_index(i) by {
        // s.drop_last()[i] == s[i] for 0 <= i < len-1
        assert(s.drop_last().spec_index(i) == s.spec_index(i));
        // !s.drop_last().contains(s[len-1])
        if s.drop_last().contains(s.spec_index(s.len() - 1)) {
            let j = choose|j: int| 0 <= j < s.drop_last().len() && s.drop_last().spec_index(j) == s.spec_index(s.len() - 1);
            assert(s.drop_last().spec_index(j) == s.spec_index(j));
            assert(s.spec_index(j) == s.spec_index(s.len() - 1));
            assert(j != s.len() - 1);
            assert(s.no_duplicates());
        }
    }

    assert forall|s: Seq<A>, v: A|
        s.no_duplicates() && s.len() > 0 && s.spec_index(s.len() - 1) == v implies
        #[trigger] s.drop_last().to_set().contains(v) == false by {
        if s.drop_last().to_set().contains(v) {
            assert(s.drop_last().contains(v));
            let j = choose|j: int| 0 <= j < s.drop_last().len() && s.drop_last().spec_index(j) == v;
            assert(s.drop_last().spec_index(j) == s.spec_index(j));
            assert(s.spec_index(j) == v);
            assert(s.spec_index(s.len() - 1) == v);
            assert(j != s.len() - 1);
            assert(s.no_duplicates());
        }
    }

    assert forall|s: Seq<A>, v: A|
        s.no_duplicates() && s.len() > 0 && s.spec_index(s.len() - 1) != v implies
        #[trigger] s.drop_last().to_set().contains(v) == s.to_set().contains(v) by {
        if s.drop_last().contains(v) {
            let j = choose|j: int| 0 <= j < s.drop_last().len() && s.drop_last().spec_index(j) == v;
            assert(s.drop_last().spec_index(j) == s.spec_index(j));
            assert(s.contains(v));
        }
        if s.contains(v) {
            let j = choose|j: int| 0 <= j < s.len() && s.spec_index(j) == v;
            assert(j != s.len() - 1);
            assert(s.drop_last().spec_index(j) == s.spec_index(j));
        }
    }
}

pub proof fn seq_update_lemma<A>()
    ensures
        forall|s: Seq<A>, i: int, j: int, v: A|
            0 <= i < s.len() && 0 <= j < s.len() && i != j ==> s.update(j, v).spec_index(i) == s.spec_index(i)
                && s.update(j, v).spec_index(j) == v,
        forall|s: Seq<A>, i: int, v: A|
            #![trigger s.update(i,v).spec_index(i)]
            0 <= i < s.len() ==> s.update(i, v).spec_index(i) == v
                // && s.len() == s.update(i, v).len()
            ,
{
    broadcast use vstd::seq::axiom_seq_update_same;
    broadcast use vstd::seq::axiom_seq_update_different;
}

pub proof fn map_insert_lemma<A, B>()
    ensures
        forall|m: Map<A, B>, x: A, y: A, v: B| x != y ==> m.insert(x, v).spec_index(y) == m.spec_index(y),
        // forall|m: Map<A, B>, x: A, y: A, v: B| x != y ==> m.insert(x, v).contains_key(y) == m.contains_key(y),
        // forall|m: Map<A, B>, x: A, v: B| m.insert(x, v).contains_key(x),
        // forall|m: Map<A, B>, x: A, v: B| #![trigger m.insert(x, v)] m.insert(x, v).dom() == m.dom().insert(x),
        // forall|m: Map<A, B>, x: A, y: A, v: B| #![trigger m.insert(x, v), m.dom().contains(y)] #![trigger m.insert(x, v).dom().contains(y)] x != y ==> m.insert(x, v).dom().contains(y) == m.dom().contains(y),
        // forall|m: Map<A, B>, x: A, v: B| #![trigger m.insert(x, v)] m.insert(x, v).dom().contains(x),
{
    broadcast use vstd::map::axiom_map_insert_different;
}

// SPEC FIX: 1st conjunct now requires s.len() > 0 (s[0] is uninterp when len == 0).
// 3rd conjunct now requires s.no_duplicates() (was false for s = [a, a]).
// 4th conjunct now requires s.len() > 0 (s[0] is uninterp when len == 0).
pub proof fn seq_skip_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A|
            s.len() > 0 && s.spec_index(0) != v && s.no_duplicates() ==> (s.skip(1).contains(v) == s.contains(v)),
        forall|s: Seq<A>| #![trigger s.spec_index(0)] s.len() > 0 ==> s.contains(s.spec_index(0)),
        forall|s: Seq<A>| #![trigger s.spec_index(0)] s.len() > 0 && s.no_duplicates() ==> !s.skip(1).contains(s.spec_index(0)),
        forall|s: Seq<A>, v: A| s.len() > 0 && s.spec_index(0) == v && s.no_duplicates() ==> s.skip(1) =~= s.remove_value(v),
        forall|s: Seq<A>, i: int| 0 <= i < s.len() - 1 ==> s.skip(1).spec_index(i) == s.spec_index(i + 1),
{
    broadcast use vstd::seq_lib::lemma_seq_skip_index;
    broadcast use vstd::seq_lib::lemma_seq_skip_len;

    assert forall|s: Seq<A>, v: A|
        s.len() > 0 && s.spec_index(0) != v && s.no_duplicates() implies
        (s.skip(1).contains(v) == s.contains(v)) by {
        if s.skip(1).contains(v) {
            let i = choose|i: int| 0 <= i < s.skip(1).len() && s.skip(1).spec_index(i) == v;
            assert(s.spec_index(i + 1) == v);
        }
        if s.contains(v) {
            let i = choose|i: int| 0 <= i < s.len() && s.spec_index(i) == v;
            assert(i != 0);
            assert(s.skip(1).spec_index(i - 1) == s.spec_index(i));
        }
    }

    assert forall|s: Seq<A>| s.len() > 0 implies s.contains(#[trigger] s.spec_index(0)) by {
    }

    assert forall|s: Seq<A>|
        s.len() > 0 && s.no_duplicates() implies !s.skip(1).contains(#[trigger] s.spec_index(0)) by {
        if s.skip(1).contains(s.spec_index(0)) {
            let i = choose|i: int| 0 <= i < s.skip(1).len() && s.skip(1).spec_index(i) == s.spec_index(0);
            assert(s.spec_index(i + 1) == s.spec_index(0));
            assert(i + 1 != 0);
        }
    }

    assert forall|s: Seq<A>, v: A|
        s.len() > 0 && s.spec_index(0) == v && s.no_duplicates() implies s.skip(1) =~= s.remove_value(v) by {
        s.index_of_first_ensures(v);
        match s.index_of_first(v) {
            Some(idx) => {
                if idx != 0 {
                    assert(s.spec_index(0) != v);
                }
                s.remove_ensures(0);
                let s1 = s.skip(1);
                let s2 = s.remove(0);
                assert(s1.len() == s2.len());
                assert forall|k: int| 0 <= k < s1.len() implies s1.spec_index(k) == s2.spec_index(k) by {
                    assert(s1.spec_index(k) == s.spec_index(k + 1));
                    assert(s2.spec_index(k) == s.spec_index(k + 1));
                }
            }
            None => {
                assert(s.contains(v));
            }
        }
    }
}

// Split facts for breaking a seq at index `i` into a prefix `subrange(0, i)`
// and a suffix `subrange(i, len)` (the batch-pop / `pop_head_batch` idiom).
// Bundles the length, indexing, no-duplicates, and to_set-partition facts the
// two-list `wf()` re-establishment needs.
pub proof fn seq_subrange_split_lemma<A>()
    ensures
        forall|s: Seq<A>, i: int|
            #![trigger s.subrange(0, i)]
            0 <= i <= s.len()
            ==>
            s.subrange(0, i).len() == i,
        forall|s: Seq<A>, i: int|
            #![trigger s.subrange(i, s.len() as int)]
            0 <= i <= s.len()
            ==>
            s.subrange(i, s.len() as int).len() == s.len() - i,
        forall|s: Seq<A>, i: int, k: int|
            #![trigger s.subrange(0, i).spec_index(k)]
            0 <= i <= s.len() && 0 <= k < i
            ==>
            s.subrange(0, i).spec_index(k) == s.spec_index(k),
        forall|s: Seq<A>, i: int, k: int|
            #![trigger s.subrange(i, s.len() as int).spec_index(k)]
            0 <= i <= s.len() && 0 <= k < s.len() - i
            ==>
            s.subrange(i, s.len() as int).spec_index(k) == s.spec_index(i + k),
        forall|s: Seq<A>, i: int|
            #![trigger s.subrange(0, i).no_duplicates()]
            0 <= i <= s.len() && s.no_duplicates()
            ==>
            s.subrange(0, i).no_duplicates(),
        forall|s: Seq<A>, i: int|
            #![trigger s.subrange(i, s.len() as int).no_duplicates()]
            0 <= i <= s.len() && s.no_duplicates()
            ==>
            s.subrange(i, s.len() as int).no_duplicates(),
        forall|s: Seq<A>, i: int, a: A|
            #![trigger s.subrange(0, i).contains(a)]
            0 <= i <= s.len() && s.no_duplicates() && s.subrange(0, i).contains(a)
            ==>
            !s.subrange(i, s.len() as int).contains(a),
        forall|s: Seq<A>, i: int, a: A|
            #![trigger s.subrange(i, s.len() as int).contains(a)]
            0 <= i <= s.len() && s.no_duplicates() && s.subrange(i, s.len() as int).contains(a)
            ==>
            !s.subrange(0, i).contains(a),
        forall|s: Seq<A>, i: int, a: A|
            #![trigger s.subrange(0, i).contains(a)]
            #![trigger s.subrange(i, s.len() as int).contains(a)]
            0 <= i <= s.len()
            ==>
            (s.contains(a) == (s.subrange(0, i).contains(a) || s.subrange(i, s.len() as int).contains(a))),
{
    assert forall|s: Seq<A>, i: int|
        0 <= i <= s.len() && s.no_duplicates() implies
        #[trigger] s.subrange(0, i).no_duplicates() by {
        let p = s.subrange(0, i);
        assert forall|j: int, k: int| 0 <= j < p.len() && 0 <= k < p.len() && j != k implies p.spec_index(j) != p.spec_index(k) by {
            assert(p.spec_index(j) == s.spec_index(j));
            assert(p.spec_index(k) == s.spec_index(k));
        }
    }

    assert forall|s: Seq<A>, i: int|
        0 <= i <= s.len() && s.no_duplicates() implies
        #[trigger] s.subrange(i, s.len() as int).no_duplicates() by {
        let q = s.subrange(i, s.len() as int);
        assert forall|j: int, k: int| 0 <= j < q.len() && 0 <= k < q.len() && j != k implies q.spec_index(j) != q.spec_index(k) by {
            assert(q.spec_index(j) == s.spec_index(i + j));
            assert(q.spec_index(k) == s.spec_index(i + k));
        }
    }

    broadcast use vstd::seq_lib::lemma_seq_subrange_elements;

    assert forall|s: Seq<A>, i: int, a: A|
        0 <= i <= s.len() && s.no_duplicates() && #[trigger] s.subrange(0, i).contains(a) implies
        !s.subrange(i, s.len() as int).contains(a) by {
        if s.subrange(i, s.len() as int).contains(a) {
            let j = choose|j: int| 0 <= j < i && s.spec_index(j) == a;
            let k = choose|k: int| i <= k < s.len() && s.spec_index(k) == a;
            assert(j != k);
        }
    }

    assert forall|s: Seq<A>, i: int, a: A|
        0 <= i <= s.len() && s.no_duplicates() && #[trigger] s.subrange(i, s.len() as int).contains(a) implies
        !s.subrange(0, i).contains(a) by {
        if s.subrange(0, i).contains(a) {
            let j = choose|j: int| 0 <= j < i && s.spec_index(j) == a;
            let k = choose|k: int| i <= k < s.len() && s.spec_index(k) == a;
            assert(j != k);
        }
    }

    assert forall|s: Seq<A>, i: int, a: A|
        0 <= i <= s.len() implies
        (s.contains(a) == (#[trigger] s.subrange(0, i).contains(a) || #[trigger] s.subrange(i, s.len() as int).contains(a))) by {
        if s.contains(a) {
            let j = choose|j: int| 0 <= j < s.len() && s.spec_index(j) == a;
        }
    }
}

// SPEC FIX: bounded i to [0, s.len()) so subrange(0,i) and subrange(i+1, len) are well-defined.
// PERF: ~13 ms / ~137k rlimit. Heavy due to multiple choose-based case analyses over subrange.
pub proof fn seq_remove_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.subrange(0,i), s.contains(v)]
            0 <= i < s.len()
            && s.contains(v) 
            && s.spec_index(i) != v
            && s.no_duplicates() 
            ==> 
            s.subrange(0, i).add(s.subrange(i + 1, s.len() as int)).contains(v),
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.subrange(0,i), s.contains(v)]
            0 <= i < s.len()
            && s.contains(v) 
            && s.spec_index(i) == v
            && s.no_duplicates() 
            ==> 
            s.subrange(0, i).add(s.subrange(i + 1, s.len() as int)).contains(v) == false,
        forall|s: Seq<A>, i: int, j: int|
            #![trigger s.subrange(0,i), s.spec_index(j)]
            0 <= j < i <= s.len()
            ==> 
            s.subrange(0, i).add(s.subrange(i + 1, s.len() as int)).spec_index(j) == s.spec_index(j),
        forall|s: Seq<A>, i: int, j: int|
            #![trigger s.subrange(0,i), s.spec_index(j+1)]
            0 <= i <= j < s.len() - 1 
            ==> 
            s.subrange(0, i).add(s.subrange(i + 1, s.len() as int)).spec_index(j) == s.spec_index(j + 1),
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.remove_value(v), s.subrange(0,i)]
            0 <= i < s.len()
            && s.contains(v) 
            && s.spec_index(i) == v
            && s.no_duplicates() 
            ==> s.subrange(0, i).add(s.subrange(i + 1, s.len() as int)) == s.remove_value(v),
{
    assert forall|s: Seq<A>, v: A, i: int|
        0 <= i < s.len() && s.contains(v) && s.spec_index(i) != v && s.no_duplicates() implies
        #[trigger] s.subrange(0, i).add(s.subrange(i + 1, s.len() as int)).contains(v) by {
        let s2 = s.subrange(0, i).add(s.subrange(i + 1, s.len() as int));
        let k = choose|k: int| 0 <= k < s.len() && s.spec_index(k) == v;
        assert(k != i);
        if k < i {
            assert(s.subrange(0, i).spec_index(k) == s.spec_index(k));
            assert(s2.spec_index(k) == s.subrange(0, i).spec_index(k));
        } else {
            assert(s.subrange(i + 1, s.len() as int).spec_index(k - i - 1) == s.spec_index(k));
            assert(s2.spec_index(k - 1) == s.spec_index(k));
        }
    }

    assert forall|s: Seq<A>, v: A, i: int|
        0 <= i < s.len() && s.contains(v) && s.spec_index(i) == v && s.no_duplicates() implies
        #[trigger] s.subrange(0, i).add(s.subrange(i + 1, s.len() as int)).contains(v) == false by {
        let s2 = s.subrange(0, i).add(s.subrange(i + 1, s.len() as int));
        if s2.contains(v) {
            let j = choose|j: int| 0 <= j < s2.len() && s2.spec_index(j) == v;
            if j < i {
                assert(s2.spec_index(j) == s.subrange(0, i).spec_index(j));
                assert(s.subrange(0, i).spec_index(j) == s.spec_index(j));
                assert(s.spec_index(j) == v);
                assert(j != i);
                assert(s.no_duplicates());
            } else {
                assert(s2.spec_index(j) == s.subrange(i + 1, s.len() as int).spec_index(j - i));
                assert(s.subrange(i + 1, s.len() as int).spec_index(j - i) == s.spec_index(j + 1));
                assert(s.spec_index(j + 1) == v);
                assert(j + 1 != i);
                assert(s.no_duplicates());
            }
        }
    }

    assert forall|s: Seq<A>, i: int, j: int|
        0 <= j < i <= s.len() implies
        #[trigger] s.subrange(0, i).add(s.subrange(i + 1, s.len() as int)).spec_index(j) == s.spec_index(j) by {
        if i < s.len() {
            assert(s.subrange(0, i).spec_index(j) == s.spec_index(j));
        } else {
            assert(s.subrange(0, i).spec_index(j) == s.spec_index(j));
        }
    }

    assert forall|s: Seq<A>, i: int, j: int|
        0 <= i <= j < s.len() - 1 implies
        #[trigger] s.subrange(0, i).add(s.subrange(i + 1, s.len() as int)).spec_index(j) == s.spec_index(j + 1) by {
        assert(s.subrange(i + 1, s.len() as int).spec_index(j - i) == s.spec_index(j + 1));
    }

    assert forall|s: Seq<A>, v: A, i: int|
        0 <= i < s.len() && s.contains(v) && s.spec_index(i) == v && s.no_duplicates() implies
        #[trigger] s.subrange(0, i).add(s.subrange(i + 1, s.len() as int)) == #[trigger] s.remove_value(v) by {
        s.index_of_first_ensures(v);
        match s.index_of_first(v) {
            Some(idx) => {
                if idx < i {
                    assert(s.spec_index(idx) == v);
                    assert(s.spec_index(i) == v);
                    assert(s.no_duplicates());
                }
                if idx > i {
                    assert(s.spec_index(i) == v);
                    // index_of_first means smallest idx; idx > i and s[i] == v contradicts smallest
                }
                s.remove_ensures(idx);
                let lhs = s.subrange(0, i).add(s.subrange(i + 1, s.len() as int));
                let rhs = s.remove(idx);
                assert(rhs == s.subrange(0, idx).add(s.subrange(idx + 1, s.len() as int)));
                assert(lhs =~= rhs);
            }
            None => {
                assert(s.contains(v));
            }
        }
    }
}

// SPEC FIX: bounded i to [0, s.len()).
// PERF: ~17 ms / ~190k rlimit. Heaviest in this file: 4 large assert-forall blocks, each
// with nested choose + branch on i vs index-of(v).
pub proof fn seq_remove_index_of_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.index_of(v), s.spec_index(i)]
            0 <= i < s.len() && s.contains(v) && s.spec_index(i) != v && s.no_duplicates() && s.subrange(0, i).contains(v) ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ).index_of(v) == s.index_of(v),
        forall|s: Seq<A>, v: A, i: int|
        #![trigger s.index_of(v), s.spec_index(i)]
            0 <= i < s.len() && s.contains(v) && s.spec_index(i) != v && s.no_duplicates() && s.index_of(v) < i ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ).index_of(v) == s.index_of(v),
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.index_of(v), s.spec_index(i)]
            0 <= i < s.len() && s.contains(v) && s.spec_index(i) != v && s.no_duplicates() && s.subrange(i + 1, s.len() as int).contains(v) ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ).index_of(v) == s.index_of(v) - 1,
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.index_of(v), s.spec_index(i)]
            0 <= i < s.len() && s.contains(v) && s.spec_index(i) != v && s.no_duplicates() && s.index_of(v) > i ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ).index_of(v) == s.index_of(v) - 1,
{
    // Establish: in s, with no_duplicates, index_of(v) is the unique k with 0<=k<s.len(), s[k]==v.
    // Combined seq s2 = subrange(0,i).add(subrange(i+1, len)) has length len-1.
    // For 0 <= j < i: s2[j] == s[j].  For i <= j < len-1: s2[j] == s[j+1].
    // So index_of(v) in s2 is i_orig if i_orig < i, else i_orig - 1 if i_orig > i.

    assert forall|s: Seq<A>, v: A, i: int|
        0 <= i < s.len() && s.contains(v) && s.spec_index(i) != v && s.no_duplicates()
        && s.subrange(0, i).contains(v) implies
        #[trigger] s.subrange(0, i).add(s.subrange(i + 1, s.len() as int)).index_of(v) == s.index_of(v) by {
        let s2 = s.subrange(0, i).add(s.subrange(i + 1, s.len() as int));
        let k_orig = s.index_of(v);
        // s.contains(v), so k_orig is the chosen index in s.
        assert(0 <= k_orig < s.len() && s.spec_index(k_orig) == v) by {
            let kk = choose|kk: int| 0 <= kk < s.len() && s.spec_index(kk) == v;
            assert(s.spec_index(kk) == v);
        }
        // subrange(0, i).contains(v) ==> exists j: 0 <= j < i, s.subrange(0,i)[j] == v ==> s[j] == v
        let j = choose|j: int| 0 <= j < s.subrange(0, i).len() && s.subrange(0, i).spec_index(j) == v;
        assert(s.spec_index(j) == v);
        // s.no_duplicates ==> j == k_orig
        if j != k_orig {
            assert(s.no_duplicates());
        }
        assert(k_orig == j);
        assert(k_orig < i);
        // s2[k_orig] == s[k_orig] == v
        assert(s2.spec_index(k_orig) == s.subrange(0, i).spec_index(k_orig));
        assert(s.subrange(0, i).spec_index(k_orig) == s.spec_index(k_orig));
        // index_of(v) in s2:
        let k2 = s2.index_of(v);
        assert(0 <= k2 < s2.len() && s2.spec_index(k2) == v) by {
            let kk = choose|kk: int| 0 <= kk < s2.len() && s2.spec_index(kk) == v;
            assert(s2.spec_index(kk) == v);
        }
        if k2 != k_orig {
            // s2[k2] == v
            if k2 < i {
                assert(s2.spec_index(k2) == s.subrange(0, i).spec_index(k2));
                assert(s.subrange(0, i).spec_index(k2) == s.spec_index(k2));
                assert(s.spec_index(k2) == v);
                assert(k2 != k_orig);
                assert(s.no_duplicates());
            } else {
                // k2 >= i
                assert(s2.spec_index(k2) == s.subrange(i + 1, s.len() as int).spec_index(k2 - i));
                assert(s.subrange(i + 1, s.len() as int).spec_index(k2 - i) == s.spec_index(k2 + 1));
                assert(s.spec_index(k2 + 1) == v);
                assert(k2 + 1 != k_orig);  // k_orig < i < k2+1 already
                assert(s.no_duplicates());
            }
        }
    }

    assert forall|s: Seq<A>, v: A, i: int|
        0 <= i < s.len() && s.contains(v) && s.spec_index(i) != v && s.no_duplicates()
        && s.index_of(v) < i implies
        #[trigger] s.subrange(0, i).add(s.subrange(i + 1, s.len() as int)).index_of(v) == s.index_of(v) by {
        let s2 = s.subrange(0, i).add(s.subrange(i + 1, s.len() as int));
        let k_orig = s.index_of(v);
        assert(0 <= k_orig < s.len() && s.spec_index(k_orig) == v) by {
            let kk = choose|kk: int| 0 <= kk < s.len() && s.spec_index(kk) == v;
            assert(s.spec_index(kk) == v);
        }
        // k_orig < i
        assert(s2.spec_index(k_orig) == s.subrange(0, i).spec_index(k_orig));
        assert(s.subrange(0, i).spec_index(k_orig) == s.spec_index(k_orig));
        let k2 = s2.index_of(v);
        assert(0 <= k2 < s2.len() && s2.spec_index(k2) == v) by {
            let kk = choose|kk: int| 0 <= kk < s2.len() && s2.spec_index(kk) == v;
            assert(s2.spec_index(kk) == v);
        }
        if k2 != k_orig {
            if k2 < i {
                assert(s2.spec_index(k2) == s.subrange(0, i).spec_index(k2));
                assert(s.subrange(0, i).spec_index(k2) == s.spec_index(k2));
                assert(s.spec_index(k2) == v);
                assert(s.no_duplicates());
            } else {
                assert(s2.spec_index(k2) == s.subrange(i + 1, s.len() as int).spec_index(k2 - i));
                assert(s.subrange(i + 1, s.len() as int).spec_index(k2 - i) == s.spec_index(k2 + 1));
                assert(s.spec_index(k2 + 1) == v);
                assert(s.no_duplicates());
            }
        }
    }

    assert forall|s: Seq<A>, v: A, i: int|
        0 <= i < s.len() && s.contains(v) && s.spec_index(i) != v && s.no_duplicates()
        && s.subrange(i + 1, s.len() as int).contains(v) implies
        #[trigger] s.subrange(0, i).add(s.subrange(i + 1, s.len() as int)).index_of(v) == s.index_of(v) - 1 by {
        let s2 = s.subrange(0, i).add(s.subrange(i + 1, s.len() as int));
        let k_orig = s.index_of(v);
        assert(0 <= k_orig < s.len() && s.spec_index(k_orig) == v) by {
            let kk = choose|kk: int| 0 <= kk < s.len() && s.spec_index(kk) == v;
            assert(s.spec_index(kk) == v);
        }
        // subrange(i+1, len).contains(v): exists j: 0 <= j < len-i-1, s[j+i+1] == v
        let j = choose|j: int| 0 <= j < s.subrange(i + 1, s.len() as int).len() && #[trigger] s.subrange(i + 1, s.len() as int).spec_index(j) == v;
        assert(s.spec_index(j + i + 1) == v);
        if j + i + 1 != k_orig {
            assert(s.no_duplicates());
        }
        assert(k_orig == j + i + 1);
        assert(k_orig > i);
        // s2[k_orig - 1] when k_orig - 1 >= i: s2[k_orig - 1] == s[k_orig]
        assert(s2.spec_index(k_orig - 1) == s.subrange(i + 1, s.len() as int).spec_index(k_orig - 1 - i));
        assert(s.subrange(i + 1, s.len() as int).spec_index(k_orig - 1 - i) == s.spec_index(k_orig));
        let k2 = s2.index_of(v);
        assert(0 <= k2 < s2.len() && s2.spec_index(k2) == v) by {
            let kk = choose|kk: int| 0 <= kk < s2.len() && s2.spec_index(kk) == v;
            assert(s2.spec_index(kk) == v);
        }
        if k2 != k_orig - 1 {
            if k2 < i {
                assert(s2.spec_index(k2) == s.subrange(0, i).spec_index(k2));
                assert(s.subrange(0, i).spec_index(k2) == s.spec_index(k2));
                assert(s.spec_index(k2) == v);
                assert(s.no_duplicates());
            } else {
                assert(s2.spec_index(k2) == s.subrange(i + 1, s.len() as int).spec_index(k2 - i));
                assert(s.subrange(i + 1, s.len() as int).spec_index(k2 - i) == s.spec_index(k2 + 1));
                assert(s.spec_index(k2 + 1) == v);
                assert(s.no_duplicates());
            }
        }
    }

    assert forall|s: Seq<A>, v: A, i: int|
        0 <= i < s.len() && s.contains(v) && s.spec_index(i) != v && s.no_duplicates()
        && s.index_of(v) > i implies
        #[trigger] s.subrange(0, i).add(s.subrange(i + 1, s.len() as int)).index_of(v) == s.index_of(v) - 1 by {
        let s2 = s.subrange(0, i).add(s.subrange(i + 1, s.len() as int));
        let k_orig = s.index_of(v);
        assert(0 <= k_orig < s.len() && s.spec_index(k_orig) == v) by {
            let kk = choose|kk: int| 0 <= kk < s.len() && s.spec_index(kk) == v;
            assert(s.spec_index(kk) == v);
        }
        assert(s2.spec_index(k_orig - 1) == s.subrange(i + 1, s.len() as int).spec_index(k_orig - 1 - i));
        assert(s.subrange(i + 1, s.len() as int).spec_index(k_orig - 1 - i) == s.spec_index(k_orig));
        let k2 = s2.index_of(v);
        assert(0 <= k2 < s2.len() && s2.spec_index(k2) == v) by {
            let kk = choose|kk: int| 0 <= kk < s2.len() && s2.spec_index(kk) == v;
            assert(s2.spec_index(kk) == v);
        }
        if k2 != k_orig - 1 {
            if k2 < i {
                assert(s2.spec_index(k2) == s.subrange(0, i).spec_index(k2));
                assert(s.subrange(0, i).spec_index(k2) == s.spec_index(k2));
                assert(s.spec_index(k2) == v);
                assert(s.no_duplicates());
            } else {
                assert(s2.spec_index(k2) == s.subrange(i + 1, s.len() as int).spec_index(k2 - i));
                assert(s.subrange(i + 1, s.len() as int).spec_index(k2 - i) == s.spec_index(k2 + 1));
                assert(s.spec_index(k2 + 1) == v);
                assert(s.no_duplicates());
            }
        }
    }
}

pub proof fn seq_push_unique_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A|
            #![auto]
            s.no_duplicates() && s.contains(v) == false ==> s.push(v).no_duplicates() && s.push(
                v,
            ).index_of(v) == s.push(v).len() - 1,
        forall|s: Seq<A>, v: A, y: A|
            #![auto]
            s.no_duplicates() && s.contains(v) && s.contains(y) == false ==> s.push(y).index_of(v)
                == s.index_of(v),
{
    broadcast use vstd::seq_lib::lemma_seq_contains_after_push;

    assert forall|s: Seq<A>, v: A|
        s.no_duplicates() && !#[trigger] s.contains(v) implies s.push(v).no_duplicates()
        && s.push(v).index_of(v) == s.push(v).len() - 1 by {
        let s2 = s.push(v);
        // s2[s.len()] == v
        assert(s2.spec_index(s.len() as int) == v);
        // s2 has no_duplicates: any two distinct indices i,j in [0, s2.len()) — if both < s.len(), no_dup of s; if one == s.len(), value v differs from anything in s
        assert(s2.no_duplicates()) by {
            assert forall|i: int, j: int|
                0 <= i < s2.len() && 0 <= j < s2.len() && i != j implies s2.spec_index(i) != s2.spec_index(j) by {
                if i < s.len() && j < s.len() {
                    assert(s.no_duplicates());
                } else if i == s.len() {
                    // s2[i] == v, s2[j] == s[j], v not in s
                } else {
                    // j == s.len()
                }
            }
        }
        // s2.index_of(v): chose any k with s2[k] == v. Since s2 has no_duplicates, k must be unique == s.len()
        let k = s2.index_of(v);
        assert(0 <= k < s2.len() && s2.spec_index(k) == v) by {
            let kk = choose|kk: int| 0 <= kk < s2.len() && s2.spec_index(kk) == v;
            assert(s2.spec_index(kk) == v);
        }
        if k != s.len() {
            assert(0 <= k < s.len());
            assert(s2.spec_index(k) == s.spec_index(k));
            assert(s.contains(v));
        }
    }

    assert forall|s: Seq<A>, v: A, y: A|
        s.no_duplicates() && s.contains(v) && !s.contains(y) implies s.push(y).index_of(v)
        == s.index_of(v) by {
        let s2 = s.push(y);
        let i = s.index_of(v);
        assert(0 <= i < s.len() && s.spec_index(i) == v) by {
            let j = choose|j: int| 0 <= j < s.len() && s.spec_index(j) == v;
            assert(s.spec_index(j) == v);
        }
        assert(s2.spec_index(i) == s.spec_index(i));
        assert(s2.spec_index(i) == v);
        let k = s2.index_of(v);
        assert(0 <= k < s2.len() && s2.spec_index(k) == v) by {
            let j = choose|j: int| 0 <= j < s2.len() && s2.spec_index(j) == v;
            assert(s2.spec_index(j) == v);
        }
        if k != i {
            if k == s.len() {
                assert(s2.spec_index(k) == y);
                assert(y == v);
                // y == v but s.contains(v), so s.contains(y) — contradicts hypothesis
                assert(s.contains(y));
            } else {
                // k < s.len(), s[k] == v, s[i] == v, k != i, contradicts no_dup
                assert(s2.spec_index(k) == s.spec_index(k));
                assert(s.spec_index(k) == v);
                assert(s.no_duplicates());
            }
        }
    }
}

pub proof fn seq_push_head_unique_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A|
            #![auto]
            s.no_duplicates() && s.contains(v) == false ==> s.insert(0,v).no_duplicates() && s.insert(0,v).index_of(v) == 0,
        // forall|s: Seq<A>, v: A, y: A|
        //     #![auto]
        //     s.no_duplicates() && s.contains(v) && s.contains(y) == false ==> s.insert(0,y).index_of(v)
        //         == s.index_of(v),
{
    assert forall|s: Seq<A>, v: A|
        s.no_duplicates() && !#[trigger] s.contains(v) implies s.insert(0, v).no_duplicates()
        && s.insert(0, v).index_of(v) == 0 by {
        s.insert_ensures(0, v);
        let s2 = s.insert(0, v);
        // s2[0] == v, s2[i+1] == s[i] for 0 <= i < s.len()
        assert(s2.no_duplicates()) by {
            assert forall|i: int, j: int|
                0 <= i < s2.len() && 0 <= j < s2.len() && i != j implies s2.spec_index(i) != s2.spec_index(j) by {
                if i == 0 {
                    // s2[0] = v, s2[j] = s[j-1], v not in s
                    assert(s2.spec_index(j) == s.spec_index(j - 1));
                } else if j == 0 {
                    assert(s2.spec_index(i) == s.spec_index(i - 1));
                } else {
                    // both > 0
                    assert(s2.spec_index(i) == s.spec_index(i - 1));
                    assert(s2.spec_index(j) == s.spec_index(j - 1));
                    assert(s.no_duplicates());
                }
            }
        }
        // index_of: chosen index k with s2[k] == v. k must be 0 because v not in s.
        let k = s2.index_of(v);
        assert(0 <= k < s2.len() && s2.spec_index(k) == v) by {
            let kk = choose|kk: int| 0 <= kk < s2.len() && s2.spec_index(kk) == v;
            assert(s2.spec_index(kk) == v);
        }
        if k != 0 {
            assert(s2.spec_index(k) == s.spec_index(k - 1));
            assert(s.contains(v));
        }
    }
}

// PERF: ~16 ms / ~240k rlimit. Two large assert-forall blocks dispatching on
// index_of_first(x) being Some/None and then doing position arithmetic in remove(i).
pub proof fn seq_remove_lemma_2<A>()
    ensures
        forall|s: Seq<A>, v: A, x: A|
            x != v && s.no_duplicates() ==> s.remove_value(x).contains(v) == s.contains(v),
        forall|s: Seq<A>, v: A|
            #![auto]
            s.no_duplicates() ==> s.remove_value(v).contains(v) == false,
{
    assert forall|s: Seq<A>, v: A, x: A|
        x != v && s.no_duplicates() implies s.remove_value(x).contains(v) == s.contains(v) by {
        s.index_of_first_ensures(x);
        match s.index_of_first(x) {
            Some(i) => {
                let s2 = s.remove(i);
                s.remove_ensures(i);
                if s2.contains(v) {
                    let j = choose|j: int| 0 <= j < s2.len() && s2.spec_index(j) == v;
                    if j < i {
                        assert(s2.spec_index(j) == s.spec_index(j));
                        assert(s.contains(v));
                    } else {
                        assert(s2.spec_index(j) == s.spec_index(j + 1));
                        assert(s.contains(v));
                    }
                }
                if s.contains(v) {
                    let j = choose|j: int| 0 <= j < s.len() && s.spec_index(j) == v;
                    assert(s.spec_index(i) == x);
                    assert(j != i);
                    if j < i {
                        assert(s2.spec_index(j) == s.spec_index(j));
                        assert(s2.contains(v));
                    } else {
                        // j > i
                        assert(s2.spec_index(j - 1) == s.spec_index(j));
                        assert(s2.contains(v));
                    }
                }
            }
            None => {
                // s does not contain x (by index_of_first_ensures)
                // s.remove_value(x) = s
            }
        }
    }

    assert forall|s: Seq<A>, v: A|
        s.no_duplicates() implies #[trigger] s.remove_value(v).contains(v) == false by {
        s.index_of_first_ensures(v);
        match s.index_of_first(v) {
            Some(i) => {
                let s2 = s.remove(i);
                s.remove_ensures(i);
                if s2.contains(v) {
                    let j = choose|j: int| 0 <= j < s2.len() && s2.spec_index(j) == v;
                    if j < i {
                        assert(s2.spec_index(j) == s.spec_index(j));
                        assert(s.spec_index(j) == v);
                        assert(s.spec_index(i) == v);
                        // j != i, contradicts no_duplicates
                        assert(s.no_duplicates());
                    } else {
                        assert(s2.spec_index(j) == s.spec_index(j + 1));
                        assert(s.spec_index(j + 1) == v);
                        assert(s.spec_index(i) == v);
                        assert(j + 1 != i);
                        assert(s.no_duplicates());
                    }
                }
            }
            None => {
                // s does not contain v
            }
        }
    }
}

// SPEC FIX: i now bounded to [0, s.len()).
pub proof fn seq_index_lemma<A>()
    ensures
        forall|s: Seq<A>, i: int|
            #![trigger s.spec_index(i)]
            0 <= i < s.len() && s.no_duplicates() ==> s.index_of(s.spec_index(i)) == i,
{
    assert forall|s: Seq<A>, i: int|
        0 <= i < s.len() && s.no_duplicates() implies s.index_of(#[trigger] s.spec_index(i)) == i by {
        let v = s.spec_index(i);
        let k = s.index_of(v);
        assert(0 <= k < s.len() && s.spec_index(k) == v) by {
            let kk = choose|kk: int| 0 <= kk < s.len() && s.spec_index(kk) == v;
            assert(s.spec_index(kk) == v);
        }
        if k != i {
            assert(s.no_duplicates());
        }
    }
}

spec fn sum_fn(s: int, i: int) -> int {
    s + i
}

proof fn sum_fold_drop_last(s: Seq<int>)
    requires
        s.len() > 0,
    ensures
        s.fold_left(0int, |sum: int, i: int| sum + i)
            == s.drop_last().fold_left(0int, |sum: int, i: int| sum + i) + s.last(),
{
    let f = |sum: int, i: int| sum + i;
    // by definition: s.fold_left(0, f) = f(s.drop_last().fold_left(0, f), s.last())
    //                                  = s.drop_last().fold_left(0, f) + s.last()
    assert(s.fold_left(0int, f) == f(s.drop_last().fold_left(0int, f), s.last()));
}

proof fn sum_fold_update_helper(s: Seq<int>, i: int, v: int)
    requires
        0 <= i < s.len(),
    ensures
        s.fold_left(0int, |sum: int, i: int| sum + i) - s.spec_index(i) + v
            == s.update(i, v).fold_left(0int, |sum: int, i: int| sum + i),
    decreases s.len(),
{
    let f = |sum: int, i: int| sum + i;
    let s2 = s.update(i, v);
    if i == s.len() - 1 {
        // s2.drop_last() == s.drop_last(); s2.last() == v; s.last() == s[i]
        assert(s2.drop_last() =~= s.drop_last());
        assert(s2.last() == v);
        assert(s.last() == s.spec_index(i));
    } else {
        // 0 <= i < s.len() - 1
        assert(s2.last() == s.last()) by {
            assert(s2.spec_index((s.len() - 1) as int) == s.spec_index((s.len() - 1) as int));
        }
        // s2.drop_last() == s.drop_last().update(i, v)
        assert(s2.drop_last() =~= s.drop_last().update(i, v));
        sum_fold_update_helper(s.drop_last(), i, v);
        // s.fold_left(0, f) = s.drop_last().fold_left(0, f) + s.last()
        // s2.fold_left(0, f) = s2.drop_last().fold_left(0, f) + s2.last()
        //                    = s.drop_last().update(i, v).fold_left(0, f) + s.last()
        //                    = (s.drop_last().fold_left(0, f) - s.drop_last()[i] + v) + s.last()
        //                    = (s.drop_last().fold_left(0, f) + s.last()) - s[i] + v
        //                    = s.fold_left(0, f) - s[i] + v
        assert(s.drop_last().spec_index(i) == s.spec_index(i));
    }
}

pub proof fn seq_fold_update_lemma()
    ensures
        forall|old: Seq<int>, i: int, v: int|
            0 <= i < old.len()
            ==>
            old.fold_left(0int, |sum: int, i: int| {sum + i}) - old.spec_index(i) + v ==  old.update(i, v).fold_left(0int, |sum: int, i: int| {sum + i})
{
    assert forall|old: Seq<int>, i: int, v: int|
        0 <= i < old.len() implies
        old.fold_left(0int, |sum: int, i: int| {sum + i}) - old.spec_index(i) + v
        == old.update(i, v).fold_left(0int, |sum: int, i: int| {sum + i}) by {
        sum_fold_update_helper(old, i, v);
    }
}

} // verus!
