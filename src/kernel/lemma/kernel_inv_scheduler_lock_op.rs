use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {
pub open spec fn scheduler_invariant_fields_unchanged(pre: SchedulerUnLockedMap, post: SchedulerUnLockedMap) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|s_ptr: RwLockSchedulerPtr|
        #![trigger pre.spec_index(s_ptr)]
        #![trigger post.spec_index(s_ptr)]
        pre.dom().contains(s_ptr) ==> post.spec_index(s_ptr).owning_container == pre.spec_index(s_ptr).owning_container
    &&& forall|s_ptr: RwLockSchedulerPtr, cpu_id: CpuId|
        #![trigger pre.spec_index(s_ptr).shards.spec_index(cpu_id)]
        #![trigger post.spec_index(s_ptr).shards.spec_index(cpu_id)]
        pre.dom().contains(s_ptr) && index_valid(NUM_CPUS, cpu_id) ==> post.spec_index(s_ptr).shard(cpu_id) == pre.spec_index(s_ptr).shard(cpu_id)
}

pub proof fn scheduler_lock_op_preserves_invariant_fields(pre: SchedulerUnLockedMap, post: SchedulerUnLockedMap, changed: RwLockSchedulerPtr, cpu_id: CpuId)
    requires
        post.unchanged_except(&pre, changed),
        post.spec_index(changed).owning_container == pre.spec_index(changed).owning_container,
        post.spec_index(changed).shards.unchanged_except(&pre.spec_index(changed).shards, cpu_id),
    ensures
        scheduler_invariant_fields_unchanged(pre, post),
{
}
}
