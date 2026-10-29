use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {
pub open spec fn cpu_offline_flags_invariant_fields_unchanged(pre: CpuOfflineFlagsUnLockedMap, post: CpuOfflineFlagsUnLockedMap) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|f_ptr: RwLockCpuOfflineFlagsPtr| #![trigger pre.spec_index(f_ptr)] #![trigger post.spec_index(f_ptr)] pre.dom().contains(f_ptr) ==> post.spec_index(f_ptr).owning_container == pre.spec_index(f_ptr).owning_container
    &&& forall|f_ptr: RwLockCpuOfflineFlagsPtr, cpu_id: CpuId|
        #![trigger pre.spec_index(f_ptr).flags.spec_index(cpu_id)]
        #![trigger post.spec_index(f_ptr).flags.spec_index(cpu_id)]
        pre.dom().contains(f_ptr) && index_valid(NUM_CPUS, cpu_id) ==> post.spec_index(f_ptr).flags.spec_index(cpu_id).view().view() == pre.spec_index(f_ptr).flags.spec_index(cpu_id).view().view()
}

pub proof fn cpu_offline_flags_lock_op_preserves_invariant_fields(pre: CpuOfflineFlagsUnLockedMap, post: CpuOfflineFlagsUnLockedMap, changed: RwLockCpuOfflineFlagsPtr, cpu_id: CpuId)
    requires
        post.unchanged_except(&pre, changed),
        post.spec_index(changed).owning_container == pre.spec_index(changed).owning_container,
        post.spec_index(changed).flags.unchanged_except(&pre.spec_index(changed).flags, cpu_id),
    ensures
        cpu_offline_flags_invariant_fields_unchanged(pre, post),
{
}
}
