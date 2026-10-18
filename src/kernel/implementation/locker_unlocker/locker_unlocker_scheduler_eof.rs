use vstd::prelude::*;
use crate::*;

verus! {
/// Closes `inv()` after a scheduler-shard write lock or unlock: only the shard's lock state moved.
pub(super) proof fn scheduler_shard_lock_op_eof(pre: KernelK, post: KernelK, scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId)
    requires
        pre.inv(),
        pre.sched_mp.dom().contains(scheduler_ptr),
        index_valid(NUM_CPUS, cpu_id),
        post == (KernelK { sched_mp: post.sched_mp, ..pre }),
        post.sched_mp.perms_wf(),
        post.sched_mp.unchanged_except(&pre.sched_mp, scheduler_ptr),
        post.sched_mp.spec_index(scheduler_ptr).inv(),
        post.sched_mp.spec_index(scheduler_ptr).owning_container == pre.sched_mp.spec_index(scheduler_ptr).owning_container,
        post.sched_mp.spec_index(scheduler_ptr).shards.unchanged_except(&pre.sched_mp.spec_index(scheduler_ptr).shards, cpu_id),
        post.sched_mp.spec_index(scheduler_ptr).shards.lock_id_by_index(cpu_id) == pre.sched_mp.spec_index(scheduler_ptr).shards.lock_id_by_index(cpu_id),
        post.sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().inv(),
        post.sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().view() == pre.sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().view(),
        post.sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().being_killed() == pre.sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().being_killed(),
        scheduler_shards_of(post.sched_mp.spec_index(scheduler_ptr)) == scheduler_shards_of(pre.sched_mp.spec_index(scheduler_ptr)),
    ensures
        post.inv(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
{
    assert(scheduler_perms_wf(post.sched_mp)) by { reveal(scheduler_perms_wf); };
    assert(scheduler_invariant_fields_unchanged(pre.sched_mp, post.sched_mp)) by { scheduler_lock_op_preserves_invariant_fields(pre.sched_mp, post.sched_mp, scheduler_ptr, cpu_id); };
    assert(post.memory_management_inv()) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.process_management_inv()) by { reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_scheduler_wf); };
}
} // verus!
