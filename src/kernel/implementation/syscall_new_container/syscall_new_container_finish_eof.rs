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
} // verus!
