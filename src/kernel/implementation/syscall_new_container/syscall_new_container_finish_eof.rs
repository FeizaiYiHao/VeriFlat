use vstd::prelude::*;
use crate::*;

verus! {
/// Releasing the staged backing-page and tail locks: only page lock states change.
#[verifier::opaque]
pub(super) open spec fn finish_staged_container_publish_eof_transition_framing(pre: KernelK, post: KernelK) -> bool {
    &&& post == (KernelK { pg_arr: post.pg_arr, ..pre })
    &&& page_invariant_fields_unchanged(pre.pg_arr, post.pg_arr)
}

/// Closes every kernel invariant after the page-lock releases from the entry invariants, the summary, and the
/// page-array representation `release_container_backing_page_locks` guarantees.
pub(super) proof fn finish_staged_container_publish_eof(pre: KernelK, post: KernelK)
    requires
        pre.inv(),
        finish_staged_container_publish_eof_transition_framing(pre, post),
        page_array_wf(post.pg_arr),
    ensures post.inv(),
{
    reveal(finish_staged_container_publish_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_page_invariant_fields(pre, post); };
}

/// Releasing five staged backing-page locks: only those entries' lock states change.
#[verifier::opaque]
pub(super) open spec fn release_backing_page_lock_group_eof_transition_framing(pre: PageLockedArray, post: PageLockedArray, indices: (PageIndex, PageIndex, PageIndex, PageIndex, PageIndex)) -> bool {
    &&& post.inv()
    &&& page_invariant_fields_unchanged(pre, post)
    &&& forall|index: PageIndex| #![trigger post.spec_index(index)] index_valid(NUM_PAGES, index) && !set![indices.0, indices.1, indices.2, indices.3, indices.4].contains(index)
        ==> post.spec_index(index) == pre.spec_index(index)
    &&& post.spec_index(indices.0).view().inv() && post.spec_index(indices.1).view().inv() && post.spec_index(indices.2).view().inv()
    &&& post.spec_index(indices.3).view().inv() && post.spec_index(indices.4).view().inv()
}

/// Closes the page-array representation after five backing-page unlocks from the entry representation and the summary.
pub(super) proof fn release_backing_page_lock_group_eof(pre: PageLockedArray, post: PageLockedArray, indices: (PageIndex, PageIndex, PageIndex, PageIndex, PageIndex))
    requires
        page_array_wf(pre),
        release_backing_page_lock_group_eof_transition_framing(pre, post, indices),
    ensures page_array_wf(post),
{ reveal(release_backing_page_lock_group_eof_transition_framing); reveal(page_array_wf); }
} // verus!
