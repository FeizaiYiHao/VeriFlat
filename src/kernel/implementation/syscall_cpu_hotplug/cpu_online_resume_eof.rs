use vstd::prelude::*;
use crate::*;

verus! {
/// The resume: the cpu records that its hardware runs again; nothing else changes.
#[verifier::opaque]
pub(super) open spec fn cpu_online_resume_eof_transition_framing(pre: KernelK, post: KernelK, cpu_id: CpuId) -> bool {
    let old_cpu = pre.cpu_arr.spec_index(cpu_id).view();
    let new_cpu = post.cpu_arr.spec_index(cpu_id).view();
    &&& post == (KernelK { cpu_arr: post.cpu_arr, ..pre })
    &&& post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, cpu_id)
    &&& new_cpu.is_init() == old_cpu.is_init()
    &&& new_cpu.view_rodata() == old_cpu.view_rodata()
    &&& new_cpu.view_ghost() == old_cpu.view_ghost()
    &&& new_cpu.locking_thread() == old_cpu.locking_thread()
    &&& new_cpu.being_killed() == old_cpu.being_killed()
    &&& new_cpu.killer_info() == old_cpu.killer_info()
    &&& new_cpu.view().kernel_call_perm() == old_cpu.view().kernel_call_perm()
    &&& new_cpu.view().view() == (CpuView { hw_halted: false, ..old_cpu.view().view() })
}

/// Closes every kernel invariant after the resume from the entry invariants, the summary, and the representation
/// facts `clear_hw_halted` guarantees.
pub(super) proof fn cpu_online_resume_eof(pre: KernelK, post: KernelK, cpu_id: CpuId)
    requires
        pre.inv(),
        cpu_online_resume_eof_transition_framing(pre, post, cpu_id),
        index_valid(NUM_CPUS, cpu_id),
        post.cpu_arr.inv(),
        post.cpu_arr.spec_index(cpu_id).view().view().wf(),
    ensures post.inv(),
{
    reveal(cpu_online_resume_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(cpu_array_wf); reveal(cpu_hw_cr3_pcid_wf); reveal(cpu_offline_flags_wf); reveal(KernelK::default_pagetable_wf); reveal(cpu_op_wf); };
    assert(post.process_management_inv()) by { reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match);
    };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}
} // verus!
