use vstd::prelude::*;
use crate::*;

verus! {
/// The write-held thread `victim_ptr`, waiting for a reply or killed, leaves the write-held marked process `process_ptr`,
/// which absorbs its quota, and takes back its process node; a thread waiting for a reply becomes a dangling thread, and it
/// and its dangling callers `callers` record the end of its call chain.
#[verifier::opaque]
pub open spec fn kill_leave_process_eof_transition_framing(
    pre: KernelK, post: KernelK, process_ptr: RwLockProcessPtr, victim_ptr: RwLockThreadPtr, callers: Set<RwLockThreadPtr>,
) -> bool {
    let process = pre.prc_mp.spec_index(process_ptr);
    let victim = pre.thr_mp.spec_index(victim_ptr);
    let callee = pre.thr_mp.spec_index(victim.view().callee.unwrap());
    let end = if thread_is_dangling(callee) && !callee.being_killed() { callee.view_ghost().chain_end.unwrap() } else { victim.view().callee.unwrap() };
    let node_addr = victim.view().proc_linkedlist_node.addr();
    let after_process = post.prc_mp.spec_index(process_ptr);
    let after_victim = post.thr_mp.spec_index(victim_ptr);
    &&& post == (KernelK { prc_mp: post.prc_mp, thr_mp: post.thr_mp, ..pre })
    &&& post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr)
    &&& forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p).view().owned_threads.view()]
        pre.prc_mp.dom().contains(p) && p != process_ptr ==> post.prc_mp.spec_index(p).view().owned_threads.view() == pre.prc_mp.spec_index(p).view().owned_threads.view()
    &&& after_process.is_init() == process.is_init()
    &&& after_process.view_rodata() == process.view_rodata()
    &&& after_process.view_ghost() == process.view_ghost()
    &&& after_process.being_killed() == process.being_killed()
    &&& after_process.killer_info() == process.killer_info()
    &&& after_process.locking_thread() == process.locking_thread()
    &&& after_process.view() == (Process {
        quota_4k: (process.view().quota_4k + victim.view().quota_4k) as usize, quota_2m: (process.view().quota_2m + victim.view().quota_2m) as usize,
        quota_1g: (process.view().quota_1g + victim.view().quota_1g) as usize, owned_threads: after_process.view().owned_threads, ..process.view()
    })
    &&& after_process.view().owned_threads.view() == process.view().owned_threads.view().remove_value(victim_ptr)
    &&& after_process.view().owned_threads.dom() == process.view().owned_threads.dom().remove(node_addr)
    &&& after_process.view().owned_threads.map() == process.view().owned_threads.map().remove(node_addr)
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)]
        pre.thr_mp.dom().contains(t) && t != victim_ptr && !callers.contains(t) ==> post.thr_mp.spec_index(t) == pre.thr_mp.spec_index(t)
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)]
        callers.contains(t) && t != victim_ptr ==> {
            &&& update_ghost_ensures(pre.thr_mp.spec_index(t), post.thr_mp.spec_index(t), ThreadGhost { chain_end: Some(end), ..pre.thr_mp.spec_index(t).view_ghost() })
            &&& post.thr_mp.spec_index(t).being_killed() == pre.thr_mp.spec_index(t).being_killed()
        }
    &&& victim.view().state is KILLED ==> callers == Set::<RwLockThreadPtr>::empty()
    &&& after_victim.is_init() == victim.is_init()
    &&& after_victim.view_rodata() == victim.view_rodata()
    &&& after_victim.view_ghost() == if callers.contains(victim_ptr) { ThreadGhost { chain_end: Some(end), ..victim.view_ghost() } } else { victim.view_ghost() }
    &&& after_victim.being_killed() == victim.being_killed()
    &&& after_victim.killer_info() == victim.killer_info()
    &&& after_victim.locking_thread() == victim.locking_thread()
    &&& after_victim.view() == (Thread {
        state: if victim.view().state is WAITING_REPLY { ThreadState::DANGLING } else { victim.view().state }, quota_4k: 0, quota_2m: 0, quota_1g: 0,
        proc_linkedlist_node: after_victim.view().proc_linkedlist_node, ..victim.view()
    })
    &&& after_victim.view().proc_linkedlist_node.is_init()
    &&& after_victim.view().proc_linkedlist_node.addr() == node_addr
}

/// The write-held marked thread `victim_ptr` scheduled on shard `shard` of `scheduler_ptr` leaves the shard and becomes
/// killed.
#[verifier::opaque]
pub open spec fn kill_dequeue_scheduled_eof_transition_framing(pre: KernelK, post: KernelK, victim_ptr: RwLockThreadPtr, scheduler_ptr: RwLockSchedulerPtr, shard: CpuId) -> bool {
    let victim = pre.thr_mp.spec_index(victim_ptr);
    let after_victim = post.thr_mp.spec_index(victim_ptr);
    let node_addr = victim.view().scheduler_linkedlist_node.addr();
    let before = pre.sched_mp.spec_index(scheduler_ptr);
    let after = post.sched_mp.spec_index(scheduler_ptr);
    &&& post == (KernelK { sched_mp: post.sched_mp, thr_mp: post.thr_mp, ..pre })
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, victim_ptr)
    &&& after_victim.is_init() == victim.is_init()
    &&& after_victim.view_rodata() == victim.view_rodata()
    &&& after_victim.view_ghost() == victim.view_ghost()
    &&& after_victim.being_killed() == victim.being_killed()
    &&& after_victim.killer_info() == victim.killer_info()
    &&& after_victim.locking_thread() == victim.locking_thread()
    &&& after_victim.view() == (Thread { state: ThreadState::KILLED, error_code: None, scheduler_linkedlist_node: after_victim.view().scheduler_linkedlist_node, ..victim.view() })
    &&& after_victim.view().scheduler_linkedlist_node.is_init()
    &&& after_victim.view().scheduler_linkedlist_node.addr() == node_addr
    &&& post.sched_mp.unchanged_except(&pre.sched_mp, scheduler_ptr)
    &&& after.owning_container == before.owning_container
    &&& after.shards.entries_unchanged_except(&before.shards, shard)
    &&& after.shards.spec_index(shard).view().locking_thread() == before.shards.spec_index(shard).view().locking_thread()
    &&& after.shards.spec_index(shard).view().being_killed() == before.shards.spec_index(shard).view().being_killed()
    &&& after.shard(shard).queue.view() == before.shard(shard).queue.view().remove_value(victim_ptr)
    &&& after.shard(shard).queue.map() == before.shard(shard).queue.map().remove(node_addr)
    &&& after.shard(shard).queue.dom() == before.shard(shard).queue.dom().remove(node_addr)
    &&& scheduler_shards_of(after) == scheduler_shards_of(before).update(shard as int, scheduler_shards_of(before)[shard as int].remove_value(victim_ptr))
}

/// The write-held marked thread `victim_ptr` waiting in the queue of the write-held endpoint `endpoint_ptr` leaves the
/// queue and becomes killed.
#[verifier::opaque]
pub open spec fn kill_dequeue_endpoint_eof_transition_framing(pre: KernelK, post: KernelK, victim_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr) -> bool {
    let victim = pre.thr_mp.spec_index(victim_ptr);
    let after_victim = post.thr_mp.spec_index(victim_ptr);
    let node_addr = victim.view().endpoint_linkedlist_node.addr();
    let before = pre.ep_mp.spec_index(endpoint_ptr);
    let after = post.ep_mp.spec_index(endpoint_ptr);
    &&& post == (KernelK { ep_mp: post.ep_mp, thr_mp: post.thr_mp, ..pre })
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, victim_ptr)
    &&& after_victim.is_init() == victim.is_init()
    &&& after_victim.view_rodata() == victim.view_rodata()
    &&& after_victim.view_ghost() == victim.view_ghost()
    &&& after_victim.being_killed() == victim.being_killed()
    &&& after_victim.killer_info() == victim.killer_info()
    &&& after_victim.locking_thread() == victim.locking_thread()
    &&& after_victim.view() == (Thread {
        state: ThreadState::KILLED, blocking_endpoint_ptr: None, blocking_endpoint_index: None, endpoint_linkedlist_node: after_victim.view().endpoint_linkedlist_node, ..victim.view()
    })
    &&& after_victim.view().endpoint_linkedlist_node.is_init()
    &&& after_victim.view().endpoint_linkedlist_node.addr() == node_addr
    &&& post.ep_mp.unchanged_except(&pre.ep_mp, endpoint_ptr)
    &&& after.is_init() == before.is_init()
    &&& after.view_rodata() == before.view_rodata()
    &&& after.view_ghost() == before.view_ghost()
    &&& after.being_killed() == before.being_killed()
    &&& after.locking_thread() == before.locking_thread()
    &&& after.view().queue.view() == before.view().queue.view().remove_value(victim_ptr)
    &&& after.view().queue.map() == before.view().queue.map().remove(node_addr)
    &&& after.view().queue.dom() == before.view().queue.dom().remove(node_addr)
    &&& after.view().queue.container_depth == before.view().queue.container_depth
    &&& after.view().queue.lock_minor() == before.view().queue.lock_minor()
    &&& after.view() == (Endpoint { queue: after.view().queue, ..before.view() })
}

/// The write-held remote cpu `remote` running the write-held marked thread `victim_ptr` is forced from running to idle:
/// the cpu loads the default page table with the default PCID and goes idle, its running state becomes Idle, and the
/// thread becomes killed.
#[verifier::opaque]
pub open spec fn kill_cpu_to_idle_eof_transition_framing(pre: KernelK, post: KernelK, victim_ptr: RwLockThreadPtr, remote: CpuId, default_cr3: PageTableRoot) -> bool {
    let victim = pre.thr_mp.spec_index(victim_ptr);
    let after_victim = post.thr_mp.spec_index(victim_ptr);
    let before = pre.cpu_arr.spec_index(remote).view();
    let after = post.cpu_arr.spec_index(remote).view();
    &&& post == (KernelK { cpu_arr: post.cpu_arr, cpu_hw_cr3_pcid: post.cpu_hw_cr3_pcid, cpu_op: post.cpu_op, thr_mp: post.thr_mp, ..pre })
    &&& post.cpu_op.view().view() == pre.cpu_op.view().view().update(remote as int, CpuOpState::Idle)
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, victim_ptr)
    &&& after_victim.is_init() == victim.is_init()
    &&& after_victim.view_rodata() == victim.view_rodata()
    &&& after_victim.view_ghost() == victim.view_ghost()
    &&& after_victim.being_killed() == victim.being_killed()
    &&& after_victim.killer_info() == victim.killer_info()
    &&& after_victim.locking_thread() == victim.locking_thread()
    &&& after_victim.view() == (Thread { state: ThreadState::KILLED, ..victim.view() })
    &&& post.cpu_arr.inv()
    &&& post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, remote)
    &&& after.is_init()
    &&& after.view().wf()
    &&& after.locking_thread() == before.locking_thread()
    &&& after.killer_info() == before.killer_info()
    &&& after.view_rodata() == before.view_rodata()
    &&& after.view_ghost() == before.view_ghost()
    &&& after.view().kernel_call_perm() == before.view().kernel_call_perm()
    &&& after.view().view() == (CpuView {
        state: CpuState::Idle, current_process: None, current_thread: None, current_pagetable: None, current_cr3: default_cr3, current_pcid: KERNEL_DEFAULT_PCID,
        ..before.view().view()
    })
    &&& post.cpu_hw_cr3_pcid[remote as int].inv()
    &&& post.cpu_hw_cr3_pcid[remote as int].view() == (default_cr3, KERNEL_DEFAULT_PCID)
    &&& post.cpu_hw_cr3_pcid[remote as int].owner_cpu() == pre.cpu_hw_cr3_pcid[remote as int].owner_cpu()
    &&& forall|c: CpuId| #![trigger post.cpu_hw_cr3_pcid[c as int]] index_valid(NUM_CPUS, c) && c != remote ==> post.cpu_hw_cr3_pcid[c as int] == pre.cpu_hw_cr3_pcid[c as int]
}
} // verus!
