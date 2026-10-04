use vstd::prelude::*;
use crate::*;
use super::syscall_new_container_cpu_spec::new_container_cpu_transfer_transition;

verus! {
#[verifier::spinoff_prover]
pub(super) proof fn new_container_cpu_transfer_eof(
    pre: KernelK, post: KernelK, parent_container: RwLockContainerPtr, child_container: RwLockContainerPtr,
    parent_cpu_set: RwLockCpuSetPtr, child_cpu_set: RwLockCpuSetPtr, transfer_cpu_id: CpuId, thread_id: LockThreadId,
)
    requires
        pre.inv(),
        new_container_cpu_transfer_transition(pre, post, parent_container, child_container, parent_cpu_set, child_cpu_set, transfer_cpu_id, thread_id),
        post.cpu_arr.inv(),
        post.cpu_set_mp.spec_index(parent_cpu_set).view().owned_cpus.wf(),
        post.cpu_set_mp.spec_index(child_cpu_set).view().owned_cpus.wf(),
    ensures
        post.inv(),
{
    reveal(new_container_cpu_transfer_transition);
    assert(post.subsystems_inv()) by { reveal(cpu_set_perms_wf); reveal(cpu_array_wf); reveal(cpu_published_wf); reveal(cpu_offline_flags_wf); reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by { assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); }; };
    assert(post.process_management_inv()) by {
        assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
        assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); reveal(container_cpu_set_wf); reveal(cpu_array_wf); };
        assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); reveal(cpu_array_wf); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { reveal(thread_cpu_wf); };
    };
    assert(post.inv()) by { reveal(cpu_array_wf); reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(tlb_wf_spec); };
}
}
