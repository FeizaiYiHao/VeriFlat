use vstd::prelude::*;
use crate::*;

verus! {
/// The offline request: the child's request cell for `target` turns on; nothing else changes.
#[verifier::opaque]
pub(super) open spec fn cpu_offline_request_child_transition_framing(pre: KernelK, post: KernelK, flags_ptr: RwLockCpuOfflineFlagsPtr, target: CpuId, child_ptr: RwLockContainerPtr) -> bool {
    let old_table = pre.cpu_offline_mp.spec_index(flags_ptr);
    let new_table = post.cpu_offline_mp.spec_index(flags_ptr);
    let old_cell = old_table.flags.spec_index(target).view();
    let new_cell = new_table.flags.spec_index(target).view();
    &&& index_valid(NUM_CPUS, target)
    &&& pre.ctn_mp.dom().contains(child_ptr)
    &&& flags_ptr == cpu_offline_flags_ptr(child_ptr)
    &&& pre.cpu_offline_mp.dom().contains(flags_ptr)
    &&& old_table.owning_container.view() == child_ptr
    &&& pre.cpu_arr.spec_index(target).view().view().view().owning_container == child_ptr
    &&& !(pre.cpu_arr.spec_index(target).view().view().view().state is Off)
    &&& post == (KernelK { cpu_offline_mp: post.cpu_offline_mp, ..pre })
    &&& post.cpu_offline_mp.unchanged_except(&pre.cpu_offline_mp, flags_ptr)
    &&& new_table.owning_container == old_table.owning_container
    &&& new_table.flags.entries_unchanged_except(&old_table.flags, target)
    &&& new_cell.view().requested
    &&& new_cell.view().index() == old_cell.view().index()
    &&& new_cell.is_init()
    &&& new_cell.view_rodata() == old_cell.view_rodata()
    &&& new_cell.view_ghost() == old_cell.view_ghost()
    &&& new_cell.locking_thread() == old_cell.locking_thread()
    &&& new_cell.being_killed() == old_cell.being_killed()
    &&& new_table.flags.lock_id_by_index(target) == old_table.flags.lock_id_by_index(target)
    &&& cpu_offline_requests_of(new_table) == cpu_offline_requests_of(old_table).update(target as int, true)
}

/// Closes every kernel invariant after the offline request from the entry invariants, the summary, and the
/// representation facts `set_flag` guarantees.
pub(super) proof fn cpu_offline_request_child_eof(pre: KernelK, post: KernelK, flags_ptr: RwLockCpuOfflineFlagsPtr, target: CpuId, child_ptr: RwLockContainerPtr)
    requires
        pre.inv(),
        cpu_offline_request_child_transition_framing(pre, post, flags_ptr, target, child_ptr),
        post.cpu_offline_mp.perms_wf(),
        post.cpu_offline_mp.spec_index(flags_ptr).inv(),
    ensures post.inv(),
{
    reveal(cpu_offline_request_child_transition_framing);
    assert(cpu_offline_flags_wf(post.cpu_offline_mp, post.cpu_arr)) by { reveal(cpu_offline_flags_wf); };
    assert(container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp)) by { reveal(container_cpu_offline_flags_wf); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
}
} // verus!
