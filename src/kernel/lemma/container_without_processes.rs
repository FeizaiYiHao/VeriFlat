use vstd::prelude::*;
use crate::*;

verus! {
/// A live thread `t_ptr`, or one a killer holds, lies in a process its container owns.
proof fn container_thread_own_process_at(k: KernelK, t_ptr: RwLockThreadPtr)
    requires
        k.inv(),
        k.thr_mp.dom().contains(t_ptr),
        !thread_is_dangling(k.thr_mp.spec_index(t_ptr)) || k.thr_mp.spec_index(t_ptr).being_killed(),
    ensures
        k.ctn_mp.spec_index(k.thr_mp.spec_index(t_ptr).view().owning_container).view_ghost().owned_processes.view().contains(k.thr_mp.spec_index(t_ptr).view().owning_proc),
{
    let p_ptr = k.thr_mp.spec_index(t_ptr).view().owning_proc;
    if thread_is_dangling(k.thr_mp.spec_index(t_ptr)) {
        process_thread_wf_killed_thread_at(k.prc_mp, k.thr_mp, t_ptr);
    } else {
        process_thread_wf_at(k.prc_mp, k.thr_mp, t_ptr);
        process_thread_wf_process_at(k.prc_mp, k.thr_mp, p_ptr, t_ptr);
    }
    container_process_wf_process_at(k.ctn_mp, k.prc_mp, p_ptr);
}

/// Thread `t_ptr` of container `c_ptr` lies in a process `c_ptr` owns, or ends a call chain in one when it is dangling and no
/// killer holds it.
proof fn container_thread_anchor_process_at(k: KernelK, c_ptr: RwLockContainerPtr, t_ptr: RwLockThreadPtr)
    requires
        k.inv(),
        k.ctn_mp.dom().contains(c_ptr),
        k.ctn_mp.spec_index(c_ptr).view_ghost().owned_threads.view().contains(t_ptr),
    ensures
        ({
            let thread = k.thr_mp.spec_index(t_ptr);
            let anchor = if thread_is_dangling(thread) && !thread.being_killed() { thread.view_ghost().chain_end.unwrap() } else { t_ptr };
            k.ctn_mp.spec_index(c_ptr).view_ghost().owned_processes.view().contains(k.thr_mp.spec_index(anchor).view().owning_proc)
        }),
{
    container_thread_wf_owned_thread_at(k.ctn_mp, k.thr_mp, c_ptr, t_ptr);
    if thread_is_dangling(k.thr_mp.spec_index(t_ptr)) && !k.thr_mp.spec_index(t_ptr).being_killed() {
        thread_dangling_chain_end_wf_at(k.thr_mp, t_ptr);
        container_thread_own_process_at(k, k.thr_mp.spec_index(t_ptr).view_ghost().chain_end.unwrap());
    } else {
        container_thread_own_process_at(k, t_ptr);
    }
}

/// Every indirect thread `t_ptr` of container `c_ptr` lives in a container below one of `c_ptr`'s children.
proof fn container_indirect_thread_child_at(k: KernelK, c_ptr: RwLockContainerPtr, t_ptr: RwLockThreadPtr)
    requires
        k.inv(),
        k.ctn_mp.dom().contains(c_ptr),
        k.ctn_mp.spec_index(c_ptr).view_ghost().owned_indirect_threads.view().contains(t_ptr),
    ensures
        0 < k.ctn_mp.spec_index(c_ptr).view().children.view().len(),
{
    container_thread_wf_indirect_thread_at(k.ctn_mp, k.thr_mp, c_ptr, t_ptr);
    container_thread_wf_uppertree_at(k.ctn_mp, k.thr_mp, t_ptr);
    let owner = k.thr_mp.spec_index(t_ptr).view().owning_container;
    let uppers = k.ctn_mp.spec_index(owner).view_ghost().uppertree_seq.view();
    let depth = k.ctn_mp.spec_index(c_ptr).view_rodata().view().depth;
    container_uppertree_seq_wf_at(k.rt_ctn, k.ctn_mp, owner, c_ptr);
    container_perms_wf_at(k.ctn_mp, owner);
    container_perms_wf_at(k.ctn_mp, c_ptr);
    let child = if depth + 1 == uppers.len() { owner } else { uppers[depth + 1] };
    if depth + 1 < uppers.len() {
        container_uppertree_seq_wf_at(k.rt_ctn, k.ctn_mp, owner, child);
        container_perms_wf_at(k.ctn_mp, child);
    }
    assert(k.ctn_mp.dom().contains(child) && k.ctn_mp.spec_index(child).view_rodata().view().depth == depth + 1
        && k.ctn_mp.spec_index(child).view_ghost().uppertree_seq.view()[depth as int] == c_ptr);
    container_root_wf_at(k.rt_ctn, k.ctn_mp, child);
    container_children_depth_wf_at(k.rt_ctn, k.ctn_mp, child);
    containers_linkedlist_wf_at(k.rt_ctn, k.ctn_mp, child);
}

/// A container without children and processes owns no threads, directly or below it, and its scheduler queues no thread.
pub proof fn container_without_children_and_processes_owns_no_threads(k: KernelK, c: RwLockContainerPtr)
    requires
        k.inv(),
        k.ctn_mp.dom().contains(c),
        k.ctn_mp.spec_index(c).view().children.view().len() == 0,
        k.ctn_mp.spec_index(c).view_ghost().owned_processes.view().is_empty(),
    ensures
        k.ctn_mp.spec_index(c).view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty(),
        k.ctn_mp.spec_index(c).view_ghost().owned_indirect_threads.view() == Set::<RwLockThreadPtr>::empty(),
        forall|i: CpuId| #![trigger k.sched_mp.spec_index(k.ctn_mp.spec_index(c).view_rodata().view().scheduler).shards.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> k.sched_mp.spec_index(k.ctn_mp.spec_index(c).view_rodata().view().scheduler).shards.spec_index(i).view().view().queue.view().len() == 0,
{
    let container = k.ctn_mp.spec_index(c);
    assert forall|t: RwLockThreadPtr| !container.view_ghost().owned_threads.view().contains(t) by {
        if container.view_ghost().owned_threads.view().contains(t) {
            container_thread_anchor_process_at(k, c, t);
        }
    };
    assert(container.view_ghost().owned_threads.view() =~= Set::<RwLockThreadPtr>::empty());
    assert forall|t: RwLockThreadPtr| !container.view_ghost().owned_indirect_threads.view().contains(t) by {
        if container.view_ghost().owned_indirect_threads.view().contains(t) {
            container_indirect_thread_child_at(k, c, t);
        }
    };
    assert(container.view_ghost().owned_indirect_threads.view() =~= Set::<RwLockThreadPtr>::empty());
    let s_ptr = container.view_rodata().view().scheduler;
    container_scheduler_wf_at(k.ctn_mp, k.sched_mp, c);
    assert forall|i: CpuId| #![trigger k.sched_mp.spec_index(s_ptr).shards.spec_index(i)]
        index_valid(NUM_CPUS, i) implies k.sched_mp.spec_index(s_ptr).shards.spec_index(i).view().view().queue.view().len() == 0 by {
        let queue = k.sched_mp.spec_index(s_ptr).shards.spec_index(i).view().view().queue.view();
        if queue.len() > 0 {
            let t = queue[0];
            assert(queue.contains(t));
            container_thread_scheduler_wf_at(k.ctn_mp, k.thr_mp, k.sched_mp, s_ptr, i, t);
            container_thread_wf_at(k.ctn_mp, k.thr_mp, t);
        }
    };
}
} // verus!
