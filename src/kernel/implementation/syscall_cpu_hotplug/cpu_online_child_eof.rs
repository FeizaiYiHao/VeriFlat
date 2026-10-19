use vstd::prelude::*;
use crate::*;

verus! {
/// The online commit: the target cpu turns from Off to Idle and leaves its cpu set's closed set; nothing else changes.
#[verifier::opaque]
pub(super) open spec fn cpu_online_child_eof_transition_framing(pre: KernelK, post: KernelK, cpu_set_ptr: RwLockCpuSetPtr, target: CpuId, child_ptr: RwLockContainerPtr) -> bool {
    let old_set = pre.cpu_set_mp.spec_index(cpu_set_ptr);
    let new_set = post.cpu_set_mp.spec_index(cpu_set_ptr);
    let old_cpu = pre.cpu_arr.spec_index(target).view();
    let new_cpu = post.cpu_arr.spec_index(target).view();
    &&& post == (KernelK { cpu_arr: post.cpu_arr, cpu_set_mp: post.cpu_set_mp, ..pre })
    &&& post.cpu_set_mp.unchanged_except(&pre.cpu_set_mp, cpu_set_ptr)
    &&& new_set.is_init() == old_set.is_init()
    &&& new_set.view_rodata() == old_set.view_rodata()
    &&& new_set.view_ghost() == old_set.view_ghost()
    &&& new_set.locking_thread() == old_set.locking_thread()
    &&& new_set.being_killed() == old_set.being_killed()
    &&& new_set.view() == (CpuSet { owned_cpus: new_set.view().owned_cpus, ..old_set.view() })
    &&& new_set.view().owned_cpus.view() == old_set.view().owned_cpus.view()
    &&& new_set.view().owned_cpus.closed_view() == old_set.view().owned_cpus.closed_view().remove(target)
    &&& post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, target)
    &&& new_cpu.is_init() == old_cpu.is_init()
    &&& new_cpu.view_rodata() == old_cpu.view_rodata()
    &&& new_cpu.view_ghost() == old_cpu.view_ghost()
    &&& new_cpu.locking_thread() == old_cpu.locking_thread()
    &&& new_cpu.being_killed() == old_cpu.being_killed()
    &&& new_cpu.view().view() == (CpuView { state: CpuState::Idle, ..old_cpu.view().view() })
}

proof fn cpu_online_child_eof_process_management_inv(pre: KernelK, post: KernelK, cpu_set_ptr: RwLockCpuSetPtr, target: CpuId, child_ptr: RwLockContainerPtr)
    requires
        pre.inv(),
        cpu_online_child_eof_transition_framing(pre, post, cpu_set_ptr, target, child_ptr),
        index_valid(NUM_CPUS, target),
        pre.ctn_mp.dom().contains(child_ptr),
        pre.ctn_mp.spec_index(child_ptr).view_rodata().view().cpu_set == cpu_set_ptr,
        pre.cpu_set_mp.dom().contains(cpu_set_ptr),
        pre.cpu_set_mp.spec_index(cpu_set_ptr).view().owned_cpus.closed_view().contains(target),
        !pre.cpu_set_mp.spec_index(cpu_set_ptr).being_killed(),
        pre.cpu_arr.spec_index(target).view().view().view().state is Off,
        pre.cpu_arr.spec_index(target).view().view().view().owning_container == child_ptr,
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(cpu_online_child_eof_transition_framing);
    assert(post.process_management_inv()) by { reveal(container_cpu_wf); reveal(container_cpu_set_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf); reveal(cpu_array_wf); reveal(cpu_set_kill_mark_wf); };
}

/// Closes every kernel invariant after the online commit from the entry invariants, the summary, and the
/// representation facts its callees guarantee.
pub(super) proof fn cpu_online_child_eof(pre: KernelK, post: KernelK, cpu_set_ptr: RwLockCpuSetPtr, target: CpuId, child_ptr: RwLockContainerPtr)
    requires
        pre.inv(),
        cpu_online_child_eof_transition_framing(pre, post, cpu_set_ptr, target, child_ptr),
        index_valid(NUM_CPUS, target),
        pre.ctn_mp.dom().contains(child_ptr),
        pre.ctn_mp.spec_index(child_ptr).view_rodata().view().cpu_set == cpu_set_ptr,
        pre.cpu_set_mp.dom().contains(cpu_set_ptr),
        pre.cpu_set_mp.spec_index(cpu_set_ptr).view().owned_cpus.closed_view().contains(target),
        !pre.cpu_set_mp.spec_index(cpu_set_ptr).being_killed(),
        pre.cpu_arr.spec_index(target).view().view().view().state is Off,
        pre.cpu_arr.spec_index(target).view().view().view().owning_container == child_ptr,
        post.cpu_arr.inv(),
        post.cpu_arr.spec_index(target).view().view().wf(),
        post.cpu_set_mp.perms_wf(),
        post.cpu_set_mp.spec_index(cpu_set_ptr).view().owned_cpus.wf(),
    ensures post.inv(),
{
    reveal(cpu_online_child_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(cpu_array_wf); reveal(cpu_published_wf); reveal(cpu_offline_flags_wf); reveal(cpu_set_perms_wf); reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by { reveal(cpu_set_pages_wf); };
    cpu_online_child_eof_process_management_inv(pre, post, cpu_set_ptr, target, child_ptr);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match);
    };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}
}
