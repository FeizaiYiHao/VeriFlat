use vstd::prelude::*;
use crate::*;

verus! {
/// Closes `inv()` after a cpu-set write lock or unlock: only the target entry's lock state moved.
pub(super) proof fn cpu_set_lock_op_eof(pre: KernelK, post: KernelK, cpu_set_ptr: RwLockCpuSetPtr)
    requires
        pre.inv(),
        pre.cpu_set_mp.dom().contains(cpu_set_ptr),
        post == (KernelK { cpu_set_mp: post.cpu_set_mp, ..pre }),
        post.cpu_set_mp.perms_wf(),
        post.cpu_set_mp.unchanged_except(&pre.cpu_set_mp, cpu_set_ptr),
        post.cpu_set_mp.spec_index(cpu_set_ptr).inv(),
        post.cpu_set_mp.spec_index(cpu_set_ptr).view() == pre.cpu_set_mp.spec_index(cpu_set_ptr).view(),
        post.cpu_set_mp.spec_index(cpu_set_ptr).view_rodata() == pre.cpu_set_mp.spec_index(cpu_set_ptr).view_rodata(),
        post.cpu_set_mp.spec_index(cpu_set_ptr).view_ghost() == pre.cpu_set_mp.spec_index(cpu_set_ptr).view_ghost(),
        post.cpu_set_mp.spec_index(cpu_set_ptr).being_killed() == pre.cpu_set_mp.spec_index(cpu_set_ptr).being_killed(),
    ensures
        post.inv(),
        forall|c: RwLockContainerPtr| #![trigger post.cpu_set_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().cpu_set)]
            pre.ctn_mp.dom().contains(c) && pre.ctn_mp.spec_index(c).view_rodata().view().cpu_set != cpu_set_ptr
                ==> post.cpu_set_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().cpu_set) == pre.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().cpu_set),
{
    assert(cpu_set_perms_wf(post.cpu_set_mp)) by { reveal(cpu_set_perms_wf); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by { cpu_set_pages_wf_preserved_for_page_state_eq(pre.cpu_set_mp, post.cpu_set_mp, pre.pg_arr, post.pg_arr); };
    assert(cpu_set_invariant_fields_unchanged(pre.cpu_set_mp, post.cpu_set_mp)) by { cpu_set_lock_op_preserves_invariant_fields(pre.cpu_set_mp, post.cpu_set_mp, cpu_set_ptr); };
    assert(post.process_management_inv()) by { reveal(container_cpu_wf); reveal(container_cpu_set_wf); };
    assert(post.inv()) by { reveal(cpu_dirty_map_contains_container_processes); };
    reveal(container_cpu_set_wf);
}

/// Relocking one cpu set back to its original lock mode keeps every container field, quota, and cpu-set lock mode.
pub proof fn container_nonlock_fields_and_quotas_unchanged_for_cpu_set_relock(pre: &KernelK, post: &KernelK, cpu_set_ptr: RwLockCpuSetPtr)
    requires
        container_cpu_set_wf(pre.ctn_mp, pre.cpu_set_mp),
        *post == (KernelK { cpu_set_mp: post.cpu_set_mp, ..*pre }),
        post.cpu_set_mp.unchanged_except(&pre.cpu_set_mp, cpu_set_ptr),
        post.cpu_set_mp.spec_index(cpu_set_ptr).lock_state_u() == pre.cpu_set_mp.spec_index(cpu_set_ptr).lock_state_u(),
    ensures kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
{ reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_cpu_set_wf); }
} // verus!
