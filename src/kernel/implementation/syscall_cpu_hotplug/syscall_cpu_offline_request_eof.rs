use vstd::prelude::*;
use crate::*;

verus! {
/// The offline request: the request cell of `container_ptr` for `target` turns on; nothing else changes.
#[verifier::opaque]
pub(super) open spec fn cpu_offline_request_eof_transition_framing(pre: KernelK, post: KernelK, flags_ptr: RwLockCpuOfflineFlagsPtr, target: CpuId, container_ptr: RwLockContainerPtr) -> bool {
    let old_table = pre.cpu_offline_mp.spec_index(flags_ptr);
    let new_table = post.cpu_offline_mp.spec_index(flags_ptr);
    let old_cell = old_table.flags.spec_index(target).view();
    let new_cell = new_table.flags.spec_index(target).view();
    &&& post == (KernelK { cpu_offline_mp: post.cpu_offline_mp, ..pre })
    &&& post.cpu_offline_mp.unchanged_except(&pre.cpu_offline_mp, flags_ptr)
    &&& new_table.owning_container == old_table.owning_container
    &&& new_table.container_depth == old_table.container_depth
    &&& new_table.flags.entries_unchanged_except(&old_table.flags, target)
    &&& forall|fp: RwLockCpuOfflineFlagsPtr, c: CpuId| #![trigger post.cpu_offline_mp.spec_index(fp).flags.spec_index(c)]
        pre.cpu_offline_mp.dom().contains(fp) && index_valid(NUM_CPUS, c) && (fp != flags_ptr || c != target) ==> post.cpu_offline_mp.spec_index(fp).flags.spec_index(c).view().view() == pre.cpu_offline_mp.spec_index(fp).flags.spec_index(c).view().view()
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
pub(super) proof fn cpu_offline_request_eof(pre: KernelK, post: KernelK, flags_ptr: RwLockCpuOfflineFlagsPtr, target: CpuId, container_ptr: RwLockContainerPtr)
    requires
        pre.inv(),
        cpu_offline_request_eof_transition_framing(pre, post, flags_ptr, target, container_ptr),
        index_valid(NUM_CPUS, target),
        flags_ptr == cpu_offline_flags_ptr(container_ptr),
        pre.cpu_offline_mp.dom().contains(flags_ptr),
        pre.cpu_offline_mp.spec_index(flags_ptr).owning_container.view() == container_ptr,
        pre.cpu_arr.spec_index(target).view().view().view().owning_container == container_ptr,
        !(pre.cpu_arr.spec_index(target).view().view().view().state is Off),
        post.cpu_offline_mp.perms_wf(),
        post.cpu_offline_mp.spec_index(flags_ptr).inv(),
    ensures post.inv(),
{
    reveal(cpu_offline_request_eof_transition_framing);
    assert(cpu_offline_flags_wf(post.cpu_offline_mp, post.cpu_arr)) by { reveal(cpu_offline_flags_wf); };
    assert(container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp)) by { reveal(container_cpu_offline_flags_wf); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
}
} // verus!
