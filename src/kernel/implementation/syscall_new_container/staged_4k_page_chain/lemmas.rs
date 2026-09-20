use vstd::assert_sets_equal;
use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
pub(in super::super) proof fn page_ptr_sets_disjoint_from_index_disjoint(
    left: Seq<PagePtr>,
    right: Seq<PagePtr>,
)
    requires
        page_ptrs_to_indices(left).disjoint(
            page_ptrs_to_indices(right),
        ),
    ensures
        left.to_set().disjoint(right.to_set()),
{
    reveal(page_ptrs_to_indices);
    broadcast use Seq::lemma_to_set_map_commutes;
    let left_set = left.to_set();
    let right_set = right.to_set();
    assert(left_set.intersect(right_set) =~= Set::<PagePtr>::empty()) by {
        assert_sets_equal!(
            left_set.intersect(right_set) == Set::<PagePtr>::empty(),
            page_ptr => {
                if left_set.contains(page_ptr)
                    && right_set.contains(page_ptr)
                {
                    assert(left.to_set().map(
                        |p: PagePtr| page_ptr2page_index(p),
                    ).contains(page_ptr2page_index(page_ptr))) by {
                        left.to_set().lemma_map_contains(
                            |p: PagePtr| page_ptr2page_index(p),
                            page_ptr2page_index(page_ptr),
                        );
                    };
                    assert(right.to_set().map(
                        |p: PagePtr| page_ptr2page_index(p),
                    ).contains(page_ptr2page_index(page_ptr))) by {
                        right.to_set().lemma_map_contains(
                            |p: PagePtr| page_ptr2page_index(p),
                            page_ptr2page_index(page_ptr),
                        );
                    };
                    reveal(Set::disjoint);
                }
            }
        );
    };
    vstd::set_lib::lemma_set_disjoint_iff_empty_intersection(
        left_set,
        right_set,
    );
}

#[verifier::spinoff_prover]
pub(in super::super) proof fn page_ptrs_to_indices_excludes_distinct_valid_page(
    pages: Seq<PagePtr>,
    excluded_page: PagePtr,
)
    requires
        page_ptr_valid(excluded_page),
        forall|i: int|
            #![trigger page_ptr_valid(pages.spec_index(i))]
            0 <= i < pages.len()
                ==> page_ptr_valid(pages.spec_index(i)),
        !pages.to_set().contains(excluded_page),
    ensures
        !page_ptrs_to_indices(pages).contains(
            page_ptr2page_index(excluded_page),
        ),
{
    page_ptr_seq_indices_excludes_page(pages, excluded_page);
    reveal(page_ptrs_to_indices);
}

pub(in super::super) proof fn set_disjoint_from_right_subset<A>(
    left: Set<A>,
    right: Set<A>,
    subset: Set<A>,
)
    requires
        left.disjoint(right),
        subset.subset_of(right),
    ensures
        left.disjoint(subset),
{
    reveal(Set::disjoint);
    reveal(Set::subset_of);
}

pub(in super::super) proof fn set_union_subset_of<A>(
    left: Set<A>,
    right: Set<A>,
    superset: Set<A>,
)
    requires
        left.subset_of(superset),
        right.subset_of(superset),
    ensures
        left.union(right).subset_of(superset),
{
    reveal(Set::subset_of);
}


}
