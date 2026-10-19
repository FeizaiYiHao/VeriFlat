use vstd::prelude::*;
use crate::*;

verus! {
/// Closes `inv()` after a cpu-offline-flag write lock or unlock: only the flag's lock state moved.
pub(super) proof fn cpu_offline_flag_lock_op_eof(pre: KernelK, post: KernelK, flags_ptr: RwLockCpuOfflineFlagsPtr, cpu_id: CpuId)
    requires
        pre.inv(),
        pre.cpu_offline_mp.dom().contains(flags_ptr),
        index_valid(NUM_CPUS, cpu_id),
        post == (KernelK { cpu_offline_mp: post.cpu_offline_mp, ..pre }),
        post.cpu_offline_mp.perms_wf(),
        post.cpu_offline_mp.unchanged_except(&pre.cpu_offline_mp, flags_ptr),
        post.cpu_offline_mp.spec_index(flags_ptr).inv(),
        post.cpu_offline_mp.spec_index(flags_ptr).owning_container == pre.cpu_offline_mp.spec_index(flags_ptr).owning_container,
        post.cpu_offline_mp.spec_index(flags_ptr).container_depth == pre.cpu_offline_mp.spec_index(flags_ptr).container_depth,
        post.cpu_offline_mp.spec_index(flags_ptr).flags.unchanged_except(&pre.cpu_offline_mp.spec_index(flags_ptr).flags, cpu_id),
        post.cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().inv(),
        post.cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().view() == pre.cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().view(),
        cpu_offline_requests_of(post.cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(pre.cpu_offline_mp.spec_index(flags_ptr)),
    ensures
        post.inv(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
{
    assert(cpu_offline_flags_invariant_fields_unchanged(pre.cpu_offline_mp, post.cpu_offline_mp)) by { cpu_offline_flags_lock_op_preserves_invariant_fields(pre.cpu_offline_mp, post.cpu_offline_mp, flags_ptr, cpu_id); };
    assert(cpu_offline_flags_wf(post.cpu_offline_mp, post.cpu_arr)) by { reveal(cpu_offline_flags_wf); };
    assert(container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp)) by { reveal(container_cpu_offline_flags_wf); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_cpu_offline_flags_wf); };
}
} // verus!
