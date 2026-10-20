use vstd::prelude::*;
use crate::*;

verus! {
/// Closes `inv()` after `wlock_cpu` or `wlock_off_cpu`: only the target slot's lock state moved.
pub(super) proof fn wlock_cpu_eof(pre: KernelK, post: KernelK, cpu_id: CpuId, lctx: LocalContext, ret: Option<Tracked<LockPerm>>)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        post == (KernelK { cpu_arr: post.cpu_arr, ..pre }),
        post.cpu_arr.inv(),
        post.cpu_arr.view().len() == pre.cpu_arr.view().len(),
        post.cpu_arr.unchanged_except(&pre.cpu_arr, cpu_id),
        ret is None ==> post.cpu_arr == pre.cpu_arr,
        ret is Some ==> wlock_ensures(pre.cpu_arr.spec_index(cpu_id).view(), post.cpu_arr.spec_index(cpu_id).view(), pre.cpu_arr.lock_id_by_index(cpu_id), &lctx, ret->Some_0.view()),
    ensures
        post.inv(),
        ret is Some ==> post.cpu_published[cpu_id as int].view() == (post.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, post.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
{
    assert(ret is Some ==> post.cpu_published[cpu_id as int].view() == (post.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, post.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid)) by { reveal(cpu_published_wf); };
    assert(cpu_array_wf(post.cpu_arr, post.dflt_pt.view())) by { reveal(cpu_array_wf); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(cpu_published_wf); reveal(cpu_offline_flags_wf); };
    assert(post.process_management_inv()) by { reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match);
        reveal(cpu_dirty_map_contains_pagetable_pcid_match);
    };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}

/// Closes `inv()` after `wunlock_cpu`: the released slot's published CR3 and PCID match its view.
pub(super) proof fn wunlock_cpu_eof(pre: KernelK, post: KernelK, cpu_id: CpuId)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        pre.cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        pre.cpu_published[cpu_id as int].view() == (pre.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, pre.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        post == (KernelK { cpu_arr: post.cpu_arr, ..pre }),
        post.cpu_arr.inv(),
        post.cpu_arr.view().len() == pre.cpu_arr.view().len(),
        post.cpu_arr.unchanged_except(&pre.cpu_arr, cpu_id),
        wunlock_ensures(pre.cpu_arr.spec_index(cpu_id).view(), post.cpu_arr.spec_index(cpu_id).view()),
    ensures
        post.inv(),
{
    assert(cpu_array_wf(post.cpu_arr, post.dflt_pt.view())) by { reveal(cpu_array_wf); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(cpu_published_wf); reveal(cpu_offline_flags_wf); };
    assert(post.process_management_inv()) by { reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match);
        reveal(cpu_dirty_map_contains_pagetable_pcid_match);
    };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}
} // verus!
