use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {

pub open spec fn scheduler_invariant_fields_unchanged(
    pre: SchedulerLockedMap,
    post: SchedulerLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|s_ptr: RwLockSchedulerPtr|
        #![trigger pre.spec_index(s_ptr)]
        #![trigger post.spec_index(s_ptr)]
        pre.dom().contains(s_ptr) ==>
            post.spec_index(s_ptr).view()
                == pre.spec_index(s_ptr).view()
}

pub proof fn scheduler_lock_op_preserves_invariant_fields(
    pre: SchedulerLockedMap,
    post: SchedulerLockedMap,
    changed: RwLockSchedulerPtr,
)
    requires
        post.unchanged_except(&pre, changed),
        post.spec_index(changed).view()
            == pre.spec_index(changed).view(),
    ensures
        scheduler_invariant_fields_unchanged(pre, post),
{
}

}
