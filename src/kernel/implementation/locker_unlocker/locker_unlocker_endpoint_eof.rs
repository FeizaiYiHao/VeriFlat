use vstd::prelude::*;
use crate::*;

verus! {
/// Closes `inv()` after an endpoint write lock or unlock: only the target entry's lock state moved.
pub(super) proof fn endpoint_lock_op_eof(pre: KernelK, post: KernelK, endpoint_ptr: RwLockEndpointPtr)
    requires
        pre.inv(),
        pre.ep_mp.dom().contains(endpoint_ptr),
        post == (KernelK { ep_mp: post.ep_mp, ..pre }),
        post.ep_mp.perms_wf(),
        post.ep_mp.unchanged_except(&pre.ep_mp, endpoint_ptr),
        post.ep_mp.spec_index(endpoint_ptr).inv(),
        post.ep_mp.spec_index(endpoint_ptr).view() == pre.ep_mp.spec_index(endpoint_ptr).view(),
    ensures
        post.inv(),
{
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); lemma_endpoint_perms_wf_preserved_for_lock_op_forall(); };
    assert(post.memory_management_inv()) by { lemma_endpoint_pages_wf_preserved_for_endpoint_invariant_fields_forall(); };
    assert(post.process_management_inv()) by {
        lemma_container_endpoint_wf_preserved_for_endpoint_invariant_fields_forall();
        lemma_thread_endpoint_ref_counter_wf_preserved_for_endpoint_invariant_fields_forall();
        lemma_thread_endpoint_queue_wf_preserved_for_endpoint_invariant_fields_forall();
        lemma_container_thread_endpoint_wf_preserved_for_endpoint_invariant_fields_forall();
    };
}
} // verus!
