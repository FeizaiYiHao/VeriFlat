use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_new_container_cpu_spec::new_container_cpu_transfer_eof_transition_framing;

verus! {
pub(super) proof fn new_container_cpu_transfer_eof(pre: KernelK, post: KernelK, parent_container: RwLockContainerPtr, child_container: RwLockContainerPtr, parent_cpu_set: RwLockCpuSetPtr, child_cpu_set: RwLockCpuSetPtr, transfer_cpu_id: CpuId, thread_id: LockThreadId)
    requires
        pre.inv(),
        new_container_cpu_transfer_eof_transition_framing(pre, post, parent_container, child_container, parent_cpu_set, child_cpu_set, transfer_cpu_id, thread_id),
        index_valid(NUM_CPUS, transfer_cpu_id),
        parent_cpu_set != child_cpu_set,
        pre.ctn_mp.dom().contains(parent_container),
        pre.ctn_mp.dom().contains(child_container),
        pre.cpu_set_mp.dom().contains(parent_cpu_set),
        pre.cpu_set_mp.dom().contains(child_cpu_set),
        pre.ctn_mp.spec_index(parent_container).view_rodata().view().cpu_set == parent_cpu_set,
        pre.ctn_mp.spec_index(child_container).view_rodata().view().cpu_set == child_cpu_set,
        pre.cpu_set_mp.spec_index(parent_cpu_set).view().owned_cpus.closed_view().contains(transfer_cpu_id),
        !pre.cpu_set_mp.spec_index(child_cpu_set).view().owned_cpus.view().contains(transfer_cpu_id),
        !pre.cpu_set_mp.spec_index(parent_cpu_set).being_killed() && !pre.cpu_set_mp.spec_index(child_cpu_set).being_killed(),
        pre.cpu_arr.spec_index(transfer_cpu_id).view().view().view().state is Off,
        pre.cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container == parent_container,
        post.cpu_arr.inv(),
        post.cpu_set_mp.perms_wf(),
        post.cpu_set_mp.spec_index(parent_cpu_set).view().owned_cpus.wf(),
        post.cpu_set_mp.spec_index(child_cpu_set).view().owned_cpus.wf(),
    ensures
        post.inv(),
{
    reveal(new_container_cpu_transfer_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(cpu_set_perms_wf); reveal(cpu_array_wf); reveal(cpu_hw_cr3_pcid_wf); reveal(cpu_offline_flags_wf); reveal(KernelK::default_pagetable_wf); reveal(cpu_op_wf); };
    assert(post.memory_management_inv()) by { assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); }; };
    assert(post.process_management_inv()) by {
        assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
        assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
        assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); reveal(container_cpu_set_wf); };
        assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { reveal(thread_cpu_wf); };
    };
    assert(post.inv()) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(tlb_wf_spec); };
}
}
