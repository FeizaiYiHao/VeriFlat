use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {

/// The kernel invariants never read a container lock's current owner.  They
/// only read the map domain and these four non-lock projections.
#[verifier::opaque]
pub open spec fn container_invariant_fields_unchanged(
    pre: ContainerLockedMap,
    post: ContainerLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|c_ptr: RwLockContainerPtr|
        #![trigger post.spec_index(c_ptr)]
        pre.dom().contains(c_ptr) ==>
        {
            &&& post.spec_index(c_ptr).view()
                == pre.spec_index(c_ptr).view()
            &&& post.spec_index(c_ptr).view_rodata()
                == pre.spec_index(c_ptr).view_rodata()
            &&& post.spec_index(c_ptr).view_kernel_ghost()
                == pre.spec_index(c_ptr).view_kernel_ghost()
            &&& post.spec_index(c_ptr).view_user_ghost()
                == pre.spec_index(c_ptr).view_user_ghost()
        }
}

/// Turn the pointwise postcondition of a container lock operation into the
/// projection used by invariant framing.
pub proof fn container_lock_op_preserves_invariant_fields(
    pre: ContainerLockedMap,
    post: ContainerLockedMap,
    changed: RwLockContainerPtr,
)
    requires
        post.unchanged_except(&pre, changed),
        post.spec_index(changed).view()
            == pre.spec_index(changed).view(),
        post.spec_index(changed).view_rodata()
            == pre.spec_index(changed).view_rodata(),
        post.spec_index(changed).view_kernel_ghost()
            == pre.spec_index(changed).view_kernel_ghost(),
        post.spec_index(changed).view_user_ghost()
            == pre.spec_index(changed).view_user_ghost(),
    ensures
        container_invariant_fields_unchanged(pre, post),
{
    reveal(container_invariant_fields_unchanged);
}

}
