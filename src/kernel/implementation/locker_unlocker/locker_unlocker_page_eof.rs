use vstd::prelude::*;
use crate::*;

verus! {
/// Closes `inv()` after a page write lock or unlock: only the target slot's lock state moved.
pub(super) proof fn page_lock_op_eof(pre: KernelK, post: KernelK, page_index: PageIndex)
    requires
        pre.inv(),
        index_valid(NUM_PAGES, page_index),
        post == (KernelK { pg_arr: post.pg_arr, ..pre }),
        post.pg_arr.inv(),
        post.pg_arr.unchanged_except(&pre.pg_arr, page_index),
        post.pg_arr.spec_index(page_index).view().inv(),
    ensures
        post.inv(),
{
    assert(page_array_wf(post.pg_arr)) by { lemma_page_array_wf_preserved_for_lock_op_forall(); };
    assert(page_invariant_fields_unchanged(pre.pg_arr, post.pg_arr)) by { page_lock_op_preserves_invariant_fields(pre.pg_arr, post.pg_arr, page_index); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by { lemma_memory_management_inv_preserved_for_page_invariant_fields_forall(); };
}
} // verus!
