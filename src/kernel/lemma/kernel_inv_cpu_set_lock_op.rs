use vstd::prelude::*;
use crate::*;

verus! {
pub open spec fn cpu_set_invariant_fields_unchanged(pre: CpuSetLockedMap, post: CpuSetLockedMap) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|s_ptr: RwLockCpuSetPtr|
        #![trigger pre.spec_index(s_ptr).view()]
        #![trigger post.spec_index(s_ptr).view()]
        pre.dom().contains(s_ptr) ==> post.spec_index(s_ptr).view() == pre.spec_index(s_ptr).view()
}

pub proof fn cpu_set_lock_op_preserves_invariant_fields(pre: CpuSetLockedMap, post: CpuSetLockedMap, changed: RwLockCpuSetPtr)
    requires
        post.unchanged_except(&pre, changed),
        post.spec_index(changed).view() == pre.spec_index(changed).view(),
    ensures
        cpu_set_invariant_fields_unchanged(pre, post),
{
}
}
