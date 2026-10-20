use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_retire_eof::kill_container_retire_eof_transition_framing;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_retire_eof_entry::*;

verus! {
/// Retiring the childless container keeps every remaining container's lock invariant and tree fields.
pub(crate) proof fn kill_container_retire_eof_container_perms(
    pre: KernelK, post: KernelK, container_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, container_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, container_ptr, parent_ptr, owner_ptr),
        post.ctn_mp.spec_index(parent_ptr).view().inv(),
        post.ctn_mp.spec_index(parent_ptr).view().children.view().no_duplicates(),
    ensures container_perms_wf(post.ctn_mp),
{
    reveal(kill_container_retire_eof_transition_framing); reveal(container_perms_wf); reveal(container_tree_fields_wf); lemma_seq_remove_value_membership::<RwLockContainerPtr>();
}

/// Retiring the childless container, a leaf below `parent_ptr` with an empty subtree, keeps the container tree well
/// formed.
pub(crate) proof fn kill_container_retire_eof_container_tree(
    pre: KernelK, post: KernelK, container_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, container_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, container_ptr, parent_ptr, owner_ptr),
    ensures container_tree_wf(post.rt_ctn, post.ctn_mp),
{
    reveal(kill_container_retire_eof_transition_framing);
    let target = pre.ctn_mp.spec_index(container_ptr);
    container_perms_wf_at(pre.ctn_mp, container_ptr);
    assert(target.view_ghost().uppertree_seq.view().len() > 0);
    container_root_wf_at(pre.rt_ctn, pre.ctn_mp, pre.rt_ctn);
    assert(container_ptr != pre.rt_ctn && pre.ctn_mp.dom().contains(pre.rt_ctn)) by { reveal(container_root_wf); };
    containers_linkedlist_wf_at(pre.rt_ctn, pre.ctn_mp, container_ptr); container_perms_wf_at(pre.ctn_mp, parent_ptr);
    assert(container_root_wf(post.rt_ctn, post.ctn_mp)) by { reveal(container_root_wf); };
    assert(container_children_parent_wf(post.rt_ctn, post.ctn_mp)) by { reveal(container_children_parent_wf); lemma_seq_remove_value_membership::<RwLockContainerPtr>(); };
    assert(containers_linkedlist_wf(post.rt_ctn, post.ctn_mp)) by {
        reveal(containers_linkedlist_wf); reveal(container_children_parent_wf); lemma_seq_remove_value_membership::<RwLockContainerPtr>();
    };
    assert(container_children_depth_wf(post.rt_ctn, post.ctn_mp)) by { reveal(container_children_depth_wf); };
    assert(container_subtree_set_wf(post.rt_ctn, post.ctn_mp)) by { reveal(container_subtree_set_wf); };
    assert(container_uppertree_seq_wf(post.rt_ctn, post.ctn_mp)) by { reveal(container_uppertree_seq_wf); broadcast use kill_container_retire_eof_subtree_empty; };
    assert(container_subtree_set_exclusive(post.rt_ctn, post.ctn_mp)) by { reveal(container_subtree_set_exclusive); };
}

/// Retiring the container together with its scheduler, cpu set, offline request table, and PCID allocator keeps the
/// container-object maps and their links to containers well formed; no cpu belongs to the retired container.
pub(crate) proof fn kill_container_retire_eof_container_objects(
    pre: KernelK, post: KernelK, container_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, container_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, container_ptr, parent_ptr, owner_ptr),
    ensures
        scheduler_perms_wf(post.sched_mp),
        cpu_set_perms_wf(post.cpu_set_mp),
        pcid_allocator_perms_wf(post.pcid_allc_mp),
        cpu_offline_flags_wf(post.cpu_offline_mp, post.cpu_arr),
        container_scheduler_wf(post.ctn_mp, post.sched_mp),
        container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp),
        container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp),
        container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp),
        process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp),
        container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr),
{
    reveal(kill_container_retire_eof_transition_framing);
    let ro = pre.ctn_mp.spec_index(container_ptr).view_rodata().view();
    container_scheduler_wf_at(pre.ctn_mp, pre.sched_mp, container_ptr); container_cpu_set_wf_container_at(pre.ctn_mp, pre.cpu_set_mp, container_ptr);
    container_cpu_offline_flags_wf_container_at(pre.ctn_mp, pre.cpu_offline_mp, container_ptr); container_pcid_allocator_wf_container_at(pre.ctn_mp, pre.pcid_allc_mp, container_ptr);
    assert(scheduler_perms_wf(post.sched_mp)) by { reveal(scheduler_perms_wf); };
    assert(cpu_set_perms_wf(post.cpu_set_mp)) by { reveal(cpu_set_perms_wf); };
    assert(pcid_allocator_perms_wf(post.pcid_allc_mp)) by { reveal(pcid_allocator_perms_wf); };
    assert(cpu_offline_flags_wf(post.cpu_offline_mp, post.cpu_arr)) by { reveal(cpu_offline_flags_wf); };
    assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { reveal(container_scheduler_wf); };
    assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
    assert(container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp)) by { reveal(container_cpu_offline_flags_wf); };
    assert(container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
    assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by {
        reveal(process_pcid_allocator_wf); reveal(container_process_wf); reveal(container_pcid_allocator_wf);
    };
    assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); reveal(container_cpu_set_wf); };
}

/// Retiring the container, which owns no thread, endpoint, or indirect thread, keeps the thread and endpoint links to
/// containers well formed.
pub(crate) proof fn kill_container_retire_eof_container_threads(
    pre: KernelK, post: KernelK, container_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, container_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, container_ptr, parent_ptr, owner_ptr),
    ensures
        container_endpoint_wf(post.ctn_mp, post.ep_mp),
        container_thread_wf(post.ctn_mp, post.thr_mp),
        container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp),
        container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp),
{
    reveal(kill_container_retire_eof_transition_framing);
    let ro = pre.ctn_mp.spec_index(container_ptr).view_rodata().view();
    container_scheduler_wf_at(pre.ctn_mp, pre.sched_mp, container_ptr);
    assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { reveal(container_endpoint_wf); broadcast use kill_container_retire_eof_no_endpoint; };
    assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { reveal(container_thread_wf); };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by {
        reveal(container_thread_endpoint_wf); reveal(container_thread_wf); reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
        broadcast use kill_container_retire_eof_no_endpoint;
    };
    assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by {
        reveal(container_thread_scheduler_wf); reveal(container_thread_wf); reveal(container_scheduler_wf);
    };
}

/// Retiring the container, which owns no process and holds no kill mark of a remaining container, process, or cpu set,
/// keeps the process links to containers and every kill mark well formed.
pub(crate) proof fn kill_container_retire_eof_container_processes(
    pre: KernelK, post: KernelK, container_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, container_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, container_ptr, parent_ptr, owner_ptr),
    ensures
        container_process_wf(post.ctn_mp, post.prc_mp),
        per_container_process_tree_wf(post.ctn_mp, post.prc_mp),
        process_kill_mark_wf(post.ctn_mp, post.prc_mp),
        container_kill_mark_wf(post.ctn_mp, post.prc_mp),
        cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp),
        post.ctn_mp.spec_index(post.rt_ctn).view_ghost().owned_processes.view().contains(post.ctn_mp.spec_index(post.rt_ctn).view().root_process),
{
    reveal(kill_container_retire_eof_transition_framing);
    let ro = pre.ctn_mp.spec_index(container_ptr).view_rodata().view();
    container_perms_wf_at(pre.ctn_mp, container_ptr);
    assert(container_ptr != pre.rt_ctn && pre.ctn_mp.dom().contains(pre.rt_ctn)) by { reveal(container_root_wf); };
    container_cpu_set_wf_container_at(pre.ctn_mp, pre.cpu_set_mp, container_ptr);
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { reveal(per_container_process_tree_wf); };
    assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); reveal(container_process_wf); };
    assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); reveal(container_children_parent_wf); };
    assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); reveal(container_cpu_set_wf); };
}

/// Retiring the container, which owns no cpu, keeps every cpu's dirty map and TLB well formed.
pub(crate) proof fn kill_container_retire_eof_tlb(
    pre: KernelK, post: KernelK, container_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, container_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, container_ptr, parent_ptr, owner_ptr),
    ensures
        cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush),
        tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    reveal(kill_container_retire_eof_transition_framing);
    assert(cpu_dirty_map_contains_container_processes(post.ctn_mp, post.cpu_set_mp, post.cpu_arr, post.pcid_needflush, post.cpu_tlb)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(container_cpu_wf); container_cpu_set_wf_container_at(pre.ctn_mp, pre.cpu_set_mp, container_ptr);
    };
}
} // verus!
