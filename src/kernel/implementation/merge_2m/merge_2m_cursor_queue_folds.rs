use vstd::prelude::*;

verus! {
pub proof fn sequence_swap_implies_same_multiset<A>(values: Seq<A>, left: int, right: int)
    requires
        0 <= left < values.len(),
        0 <= right < values.len(),
        left != right,
    ensures
        values.update(left, values.spec_index(right)).update(right, values.spec_index(left)).to_multiset() == values.to_multiset(),
{
    assert(values.update(left, values.spec_index(right)).update(right, values.spec_index(left)).to_multiset() =~= values.to_multiset()) by {
        values.lemma_index_contains(left); values.lemma_index_contains(right);
        vstd::seq_lib::to_multiset_contains(values, values.spec_index(left));
        vstd::seq_lib::to_multiset_contains(values, values.spec_index(right));
        broadcast use { vstd::seq_lib::to_multiset_update, vstd::multiset::axiom_multiset_add, vstd::multiset::axiom_multiset_sub,
            vstd::multiset::axiom_multiset_singleton, vstd::multiset::axiom_multiset_singleton_different, vstd::multiset::axiom_multiset_ext_equal };
    };
}

}
