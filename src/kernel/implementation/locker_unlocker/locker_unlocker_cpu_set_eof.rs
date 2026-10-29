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
        !pre.cpu_set_mp.spec_index(cpu_set_ptr).being_killed() || post.cpu_set_mp.spec_index(cpu_set_ptr) == pre.cpu_set_mp.spec_index(cpu_set_ptr),
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
    assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
    assert(post.process_management_inv()) by { reveal(container_cpu_wf); reveal(container_cpu_set_wf); };
    assert(post.inv()) by { reveal(cpu_dirty_map_contains_container_processes); };
    reveal(container_cpu_set_wf);
}

/// Closes `inv()` after `wlock_cpu_set_and_mark_kill`: the cpu set of the marked container `container_ptr`, which owns no
/// process or thread, is write-locked by the thread that write-holds the killer's process and marked for that killer.
pub(super) proof fn mark_kill_cpu_set_eof(pre: KernelK, post: KernelK, pre_lctx: LocalContext, container_ptr: RwLockContainerPtr, cpu_set_ptr: RwLockCpuSetPtr, killer_info: KillerInfo)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set == cpu_set_ptr,
        pre.ctn_mp.spec_index(container_ptr).killer_info() == Some(killer_info),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().is_empty(),
        typed_lock_map_contains_mode(pre_lctx.process_lock_map(), killer_info.process, TypedLockMode::Write),
        typed_lock_maps_aligned(&pre, &pre_lctx),
        post == (KernelK { cpu_set_mp: post.cpu_set_mp, ..pre }),
        post.cpu_set_mp.perms_wf(),
        post.cpu_set_mp.unchanged_except(&pre.cpu_set_mp, cpu_set_ptr),
        post.cpu_set_mp.spec_index(cpu_set_ptr).inv(),
        post.cpu_set_mp.spec_index(cpu_set_ptr).view() == pre.cpu_set_mp.spec_index(cpu_set_ptr).view(),
        post.cpu_set_mp.spec_index(cpu_set_ptr).view_rodata() == pre.cpu_set_mp.spec_index(cpu_set_ptr).view_rodata(),
        post.cpu_set_mp.spec_index(cpu_set_ptr).view_ghost() == pre.cpu_set_mp.spec_index(cpu_set_ptr).view_ghost(),
        post.cpu_set_mp.spec_index(cpu_set_ptr).killer_info() == Some(killer_info),
        post.cpu_set_mp.spec_index(cpu_set_ptr).wlocked_by_thread(pre_lctx.thread_id()),
    ensures
        post.inv(),
{
    assert(cpu_set_perms_wf(post.cpu_set_mp)) by { reveal(cpu_set_perms_wf); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by { cpu_set_pages_wf_preserved_for_page_state_eq(pre.cpu_set_mp, post.cpu_set_mp, pre.pg_arr, post.pg_arr); };
    assert(cpu_set_invariant_fields_unchanged(pre.cpu_set_mp, post.cpu_set_mp)) by { cpu_set_lock_op_preserves_invariant_fields(pre.cpu_set_mp, post.cpu_set_mp, cpu_set_ptr); };
    assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by {
        container_cpu_set_wf_container_at(pre.ctn_mp, pre.cpu_set_mp, container_ptr); pre.prc_mp.typed_lock_map_aligned_write_at(pre_lctx.process_lock_map(), pre_lctx.thread_id(), killer_info.process);
        reveal(cpu_set_kill_mark_wf);
    };
    assert(post.process_management_inv()) by { reveal(container_cpu_wf); reveal(container_cpu_set_wf); };
    assert(post.inv()) by { reveal(cpu_dirty_map_contains_container_processes); };
}

/// Relocking one cpu set back to its original lock mode keeps every container field, quota, and cpu-set lock mode.
pub proof fn container_nonlock_fields_and_quotas_unchanged_for_cpu_set_relock(pre: &KernelK, post: &KernelK, cpu_set_ptr: RwLockCpuSetPtr)
    requires
        container_cpu_set_wf(pre.ctn_mp, pre.cpu_set_mp),
        *post == (KernelK { cpu_set_mp: post.cpu_set_mp, ..*pre }),
        post.cpu_set_mp.unchanged_except(&pre.cpu_set_mp, cpu_set_ptr),
        post.cpu_set_mp.spec_index(cpu_set_ptr).lock_state_u() == pre.cpu_set_mp.spec_index(cpu_set_ptr).lock_state_u(),
        post.cpu_set_mp.spec_index(cpu_set_ptr).being_killed() == pre.cpu_set_mp.spec_index(cpu_set_ptr).being_killed(),
    ensures kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
{ reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_cpu_set_wf); }
} // verus!
