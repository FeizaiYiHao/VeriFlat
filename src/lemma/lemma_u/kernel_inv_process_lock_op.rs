use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {

/// Kernel invariants read process payloads and read-only data, but never the
/// current process lock owner.
#[verifier::opaque]
pub open spec fn process_invariant_fields_unchanged(
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|p_ptr: RwLockProcessPtr|
        #![trigger post.spec_index(p_ptr)]
        pre.dom().contains(p_ptr) ==>
        {
            &&& post.spec_index(p_ptr).view()
                == pre.spec_index(p_ptr).view()
            &&& post.spec_index(p_ptr).view_rodata()
                == pre.spec_index(p_ptr).view_rodata()
        }
}

pub proof fn process_lock_op_preserves_invariant_fields(
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
    changed: RwLockProcessPtr,
)
    requires
        post.unchanged_except(&pre, changed),
        post.spec_index(changed).view()
            == pre.spec_index(changed).view(),
        post.spec_index(changed).view_rodata()
            == pre.spec_index(changed).view_rodata(),
    ensures
        process_invariant_fields_unchanged(pre, post),
{
    reveal(process_invariant_fields_unchanged);
}

}
