use vstd::prelude::*;
use crate::*;

verus! {
/// Closes `inv()` after `wlock_own_cpu`, `wlock_cpu`, or `wlock_off_cpu`: only the target slot's lock state and holder
/// moved, and when the own cpu `entered` its kernel step, its kernel-call permission left the cpu object and its running
/// state became InStep.
pub(super) proof fn wlock_cpu_eof(pre: KernelK, post: KernelK, cpu_id: CpuId, holder: CpuId, entered: bool)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        post == (KernelK { cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, ..pre }),
        post.cpu_arr.inv(),
        post.cpu_arr.view().len() == pre.cpu_arr.view().len(),
        post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, cpu_id),
        entered ==> holder == cpu_id,
        post.cpu_op.view().view() == if entered { pre.cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep) } else { pre.cpu_op.view().view() },
        ({
            let pre_lock = pre.cpu_arr.spec_index(cpu_id).view();
            let post_lock = post.cpu_arr.spec_index(cpu_id).view();
            &&& !pre_lock.locked()
            &&& post_lock.wlocked()
            &&& post_lock.inv()
            &&& post_lock.view().view() == pre_lock.view().view()
            &&& post_lock.view().kernel_call_perm() == if entered { None } else { pre_lock.view().kernel_call_perm() }
            &&& post_lock.view_rodata() == pre_lock.view_rodata()
            &&& post_lock.view_ghost() == Some(holder)
            &&& post_lock.being_killed() == pre_lock.being_killed()
            &&& post_lock.killer_info() == pre_lock.killer_info()
            &&& post_lock.control() == pre_lock.control()
        }),
    ensures
        post.inv(),
        post.cpu_hw_cr3_pcid[cpu_id as int].view() == (post.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, post.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
{
    assert(post.cpu_hw_cr3_pcid[cpu_id as int].view() == (post.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, post.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid)) by { reveal(cpu_hw_cr3_pcid_wf); };
    assert(cpu_array_wf(post.cpu_arr, post.dflt_pt.view())) by { reveal(cpu_array_wf); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(cpu_hw_cr3_pcid_wf); reveal(cpu_offline_flags_wf); reveal(cpu_op_wf); };
    assert(post.process_management_inv()) by { reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match);
        reveal(cpu_dirty_map_contains_pagetable_pcid_match);
    };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}

/// Closes `inv()` after `wunlock_cpu`: the released remote slot was outside a kernel step, and its hardware cr3/pcid
/// word matches its view.
pub(super) proof fn wunlock_cpu_eof(pre: KernelK, post: KernelK, cpu_id: CpuId)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        pre.cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        !(pre.cpu_op.view().view()[cpu_id as int] is InStep),
        pre.cpu_hw_cr3_pcid[cpu_id as int].view() == (pre.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, pre.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        post == (KernelK { cpu_arr: post.cpu_arr, ..pre }),
        post.cpu_arr.inv(),
        post.cpu_arr.view().len() == pre.cpu_arr.view().len(),
        post.cpu_arr.unchanged_except(&pre.cpu_arr, cpu_id),
        ({
            let pre_lock = pre.cpu_arr.spec_index(cpu_id).view();
            let post_lock = post.cpu_arr.spec_index(cpu_id).view();
            &&& post_lock.locking_thread() == RwLockState::None
            &&& post_lock.inv()
            &&& post_lock.view() == pre_lock.view()
            &&& post_lock.view_rodata() == pre_lock.view_rodata()
            &&& post_lock.view_ghost() is None
            &&& post_lock.control() == pre_lock.control()
        }),
    ensures
        post.inv(),
{
    assert(cpu_array_wf(post.cpu_arr, post.dflt_pt.view())) by { reveal(cpu_array_wf); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(cpu_hw_cr3_pcid_wf); reveal(cpu_offline_flags_wf); reveal(cpu_op_wf); };
    assert(post.process_management_inv()) by { reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match);
        reveal(cpu_dirty_map_contains_pagetable_pcid_match);
    };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}

/// Closes `inv()` after `wunlock_own_cpu`: the own cpu left its kernel step, so its running state is the resting state of
/// its scheduling state, its kernel-call permission is back in its released cpu object, and its hardware cr3/pcid word
/// matches its view.
pub(super) proof fn wunlock_own_cpu_eof(pre: KernelK, post: KernelK, cpu_id: CpuId)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        pre.cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        pre.cpu_op.view().view()[cpu_id as int] is InStep,
        pre.cpu_hw_cr3_pcid[cpu_id as int].view() == (pre.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, pre.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        post == (KernelK { cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, ..pre }),
        post.cpu_op.view().view() == pre.cpu_op.view().view().update(cpu_id as int, cpu_op_after_step(pre.cpu_arr.spec_index(cpu_id).view().view().view().state)),
        post.cpu_arr.inv(),
        post.cpu_arr.view().len() == pre.cpu_arr.view().len(),
        post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, cpu_id),
        ({
            let pre_lock = pre.cpu_arr.spec_index(cpu_id).view();
            let post_lock = post.cpu_arr.spec_index(cpu_id).view();
            &&& post_lock.locking_thread() == RwLockState::None
            &&& post_lock.inv()
            &&& post_lock.view().view() == pre_lock.view().view()
            &&& post_lock.view().kernel_call_perm() == Some(cpu_id)
            &&& post_lock.view_rodata() == pre_lock.view_rodata()
            &&& post_lock.view_ghost() is None
            &&& post_lock.control() == pre_lock.control()
        }),
    ensures
        post.inv(),
{
    assert(cpu_array_wf(post.cpu_arr, post.dflt_pt.view())) by { reveal(cpu_array_wf); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(cpu_hw_cr3_pcid_wf); reveal(cpu_offline_flags_wf); reveal(cpu_op_wf); };
    assert(post.process_management_inv()) by { reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match);
        reveal(cpu_dirty_map_contains_pagetable_pcid_match);
    };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}
} // verus!
