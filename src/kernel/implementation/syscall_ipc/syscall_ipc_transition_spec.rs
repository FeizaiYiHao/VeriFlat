use vstd::prelude::*;
use crate::*;

verus! {
/// Blocks the running caller on the write-held endpoint and idles its cpu on the default page table; no other object
/// changes.
#[verifier::opaque]
pub open spec fn ipc_block_current_eof_transition_framing(
    pre: KernelK, post: KernelK, cpu_id: CpuId, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    waiting_state: ThreadState, payload: IPCPayLoad, default_cr3: PageTableRoot,
) -> bool {
    let thread_before = pre.thr_mp.spec_index(current_thread_ptr);
    let thread_after = post.thr_mp.spec_index(current_thread_ptr);
    let endpoint_before = pre.ep_mp.spec_index(endpoint_ptr);
    let endpoint_after = post.ep_mp.spec_index(endpoint_ptr);
    let node = thread_after.view().endpoint_linkedlist_node.addr();
    let cpu_before = pre.cpu_arr.spec_index(cpu_id).view();
    let cpu_after = post.cpu_arr.spec_index(cpu_id).view();
    let flush_before = pre.pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID);
    let flush_after = post.pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID);
    &&& post == (KernelK { cpu_arr: post.cpu_arr, thr_mp: post.thr_mp, ep_mp: post.ep_mp, cpu_tlb: post.cpu_tlb, pcid_needflush: post.pcid_needflush, cpu_published: post.cpu_published, ..pre })
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, current_thread_ptr)
    &&& thread_after.locking_thread() == thread_before.locking_thread()
    &&& thread_after.being_killed() == thread_before.being_killed()
    &&& thread_after.view_ghost() == thread_before.view_ghost()
    &&& thread_after.view().non_ipc_fields_unchanged(&thread_before.view())
    &&& thread_after.view().caller == thread_before.view().caller
    &&& thread_after.view().syscall_progress == thread_before.view().syscall_progress
    &&& thread_after.view().callee == thread_before.view().callee
    &&& thread_after.view().error_code == thread_before.view().error_code
    &&& thread_after.view().state == waiting_state
    &&& thread_after.view().blocking_endpoint_ptr == Some(endpoint_ptr)
    &&& thread_after.view().blocking_endpoint_index == Some(endpoint_index)
    &&& thread_after.view().ipc_payload == payload
    &&& thread_after.view().trap_frame.is_some()
    &&& post.ep_mp.unchanged_except(&pre.ep_mp, endpoint_ptr)
    &&& endpoint_after.is_init() == endpoint_before.is_init()
    &&& endpoint_after.view_rodata() == endpoint_before.view_rodata()
    &&& endpoint_after.view_ghost() == endpoint_before.view_ghost()
    &&& endpoint_after.locking_thread() == endpoint_before.locking_thread()
    &&& endpoint_after.being_killed() == endpoint_before.being_killed()
    &&& endpoint_after.view().queue.wf()
    &&& endpoint_after.view().queue.container_depth == endpoint_before.view().queue.container_depth
    &&& endpoint_after.view().queue.lock_minor() == endpoint_before.view().queue.lock_minor()
    &&& endpoint_after.view().queue.length as int == endpoint_before.view().queue.length as int + 1
    &&& endpoint_after.view().queue.dom() == endpoint_before.view().queue.dom().insert(node)
    &&& endpoint_after.view().rf_counter == endpoint_before.view().rf_counter
    &&& endpoint_after.view().owning_threads == endpoint_before.view().owning_threads
    &&& endpoint_after.view().owning_container == endpoint_before.view().owning_container
    &&& endpoint_after.view().queue.view() == endpoint_before.view().queue.view().push(current_thread_ptr)
    &&& endpoint_after.view().queue.map() == endpoint_before.view().queue.map().insert(node, current_thread_ptr)
    &&& !endpoint_before.view().queue.map().dom().contains(node)
    &&& endpoint_after.view().queue_state == if endpoint_before.view().queue.length == 0 {
        match waiting_state { ThreadState::SENDING | ThreadState::CALLING => EndpointState::SEND, _ => EndpointState::RECEIVE }
    } else {
        endpoint_before.view().queue_state
    }
    &&& post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, cpu_id)
    &&& cpu_after.is_init()
    &&& cpu_after.view().wf()
    &&& cpu_after.locking_thread() == cpu_before.locking_thread()
    &&& cpu_after.being_killed() == cpu_before.being_killed()
    &&& cpu_after.killer_info() == cpu_before.killer_info()
    &&& cpu_after.view_rodata() == cpu_before.view_rodata()
    &&& cpu_after.view_ghost() == cpu_before.view_ghost()
    &&& cpu_after.view().view() == (CpuView { state: CpuState::Idle, current_process: None, current_thread: None, current_pagetable: None, current_cr3: default_cr3, current_pcid: KERNEL_DEFAULT_PCID, ..cpu_before.view().view() })
    &&& post.cpu_tlb.view() == if flush_before.view().needflush { pre.cpu_tlb.view().insert((cpu_id, KERNEL_DEFAULT_PCID), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }) } else { pre.cpu_tlb.view() }
    &&& forall|c: CpuId, p: Pcid| #![trigger post.cpu_tlb.spec_index((c, p))] #![trigger pre.cpu_tlb.spec_index((c, p))]
        index_valid(NUM_CPUS, c) && pcid_valid(p) ==> post.cpu_tlb.spec_index((c, p)) == if flush_before.view().needflush && c == cpu_id && p == KERNEL_DEFAULT_PCID {
            SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }
        } else { pre.cpu_tlb.spec_index((c, p)) }
    &&& flush_after.view() == (PcidNeedFlush { needflush: false, ..flush_before.view() })
    &&& flush_after.is_init()
    &&& flush_after.locking_thread() == flush_before.locking_thread()
    &&& flush_after.view_ghost() == flush_before.view_ghost()
    &&& flush_after.view_rodata() == flush_before.view_rodata()
    &&& flush_after.being_killed() == flush_before.being_killed()
    &&& forall|c: CpuId, p: Pcid| #![trigger post.pcid_needflush.spec_index(c, p)] #![trigger pre.pcid_needflush.spec_index(c, p)]
        index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != KERNEL_DEFAULT_PCID) ==> post.pcid_needflush.spec_index(c, p) == pre.pcid_needflush.spec_index(c, p)
    &&& post.cpu_published[cpu_id as int].view() == (default_cr3, KERNEL_DEFAULT_PCID)
    &&& post.cpu_published[cpu_id as int].owner_cpu() == pre.cpu_published[cpu_id as int].owner_cpu()
    &&& forall|c: CpuId| #![trigger post.cpu_published[c as int]] #![trigger pre.cpu_published[c as int]]
        index_valid(NUM_CPUS, c) && c != cpu_id ==> post.cpu_published[c as int] == pre.cpu_published[c as int]
}

/// Dequeues the endpoint waiter and schedules it on `wake_cpu`; no other object changes.
#[verifier::opaque]
pub open spec fn ipc_schedule_waiting_peer_eof_transition_framing(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, peer_result: RetValueType, thread_id: LockThreadId,
) -> bool {
    &&& post.pt_mp == pre.pt_mp
    &&& post.it_mp == pre.it_mp
    &&& post.irt == pre.irt
    &&& post.pg_arr == pre.pg_arr
    &&& post.ctn_mp == pre.ctn_mp
    &&& post.prc_mp == pre.prc_mp
    &&& post.cpu_arr == pre.cpu_arr
    &&& post.cpu_set_mp == pre.cpu_set_mp
    &&& post.pcid_needflush == pre.pcid_needflush
    &&& post.cpu_published == pre.cpu_published
    &&& post.pcid_allc_mp == pre.pcid_allc_mp
    &&& post.allc_4k_mp == pre.allc_4k_mp
    &&& post.allc_2m_mp == pre.allc_2m_mp
    &&& post.allc_1g_mp == pre.allc_1g_mp
    &&& post.cpu_offline_mp == pre.cpu_offline_mp
    &&& post.cpu_tlb == pre.cpu_tlb
    &&& post.iommu_tlb == pre.iommu_tlb
    &&& post.rt_ctn == pre.rt_ctn
    &&& post.dflt_pt == pre.dflt_pt
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& forall|key: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(key)] #![trigger post.thr_mp.spec_index(key)]
        #![trigger pre.thr_mp.spec_index(key).view().temp_alloc_cache_2m] #![trigger post.thr_mp.spec_index(key).view().temp_alloc_cache_2m]
        #![trigger pre.thr_mp.spec_index(key).view().temp_alloc_cache_1g] #![trigger post.thr_mp.spec_index(key).view().temp_alloc_cache_1g]
        pre.thr_mp.dom().contains(key) ==> {
            let before = pre.thr_mp.spec_index(key);
            let after = post.thr_mp.spec_index(key);
            &&& post.thr_mp.view().spec_index(key).is_init() == pre.thr_mp.view().spec_index(key).is_init()
            &&& post.thr_mp.view().spec_index(key).addr() == pre.thr_mp.view().spec_index(key).addr()
            &&& after.view().temp_alloc_cache_2m == before.view().temp_alloc_cache_2m
            &&& after.view().temp_alloc_cache_1g == before.view().temp_alloc_cache_1g
            &&& !(key == peer_thread_ptr) ==> after == before
        }
    &&& {
        let before = pre.thr_mp.spec_index(peer_thread_ptr);
        let after = post.thr_mp.spec_index(peer_thread_ptr);
        &&& after.is_init() == before.is_init()
        &&& after.view_rodata() == before.view_rodata()
        &&& after.view_ghost() == before.view_ghost()
        &&& after.being_killed() == before.being_killed()
        &&& after.locking_thread() == before.locking_thread()
        &&& after.view() == Thread { state: ThreadState::SCHEDULED { cpu_id: wake_cpu }, blocking_endpoint_ptr: None, blocking_endpoint_index: None, ipc_payload: IPCPayLoad::Empty, error_code: Some(peer_result),
            endpoint_linkedlist_node: after.view().endpoint_linkedlist_node, scheduler_linkedlist_node: after.view().scheduler_linkedlist_node, ..before.view() }
        &&& after.view().endpoint_linkedlist_node.addr() == before.view().endpoint_linkedlist_node.addr()
        &&& after.view().scheduler_linkedlist_node.addr() == before.view().scheduler_linkedlist_node.addr()
        &&& after.view().endpoint_linkedlist_node.is_init()
        &&& !after.view().scheduler_linkedlist_node.is_init()
    }
    &&& post.ep_mp.dom() == pre.ep_mp.dom()
    &&& forall|key: RwLockEndpointPtr| #![trigger pre.ep_mp.spec_index(key)] #![trigger post.ep_mp.spec_index(key)] pre.ep_mp.dom().contains(key) ==> {
        let before = pre.ep_mp.spec_index(key);
        let after = post.ep_mp.spec_index(key);
        &&& post.ep_mp.view().spec_index(key).is_init() == pre.ep_mp.view().spec_index(key).is_init()
        &&& post.ep_mp.view().spec_index(key).addr() == pre.ep_mp.view().spec_index(key).addr()
        &&& !(key == endpoint_ptr) ==> after == before
    }
    &&& {
        let before = pre.ep_mp.spec_index(endpoint_ptr);
        let after = post.ep_mp.spec_index(endpoint_ptr);
        &&& after.is_init() == before.is_init()
        &&& after.view_rodata() == before.view_rodata()
        &&& after.view_ghost() == before.view_ghost()
        &&& after.being_killed() == before.being_killed()
        &&& after.locking_thread() == before.locking_thread()
        &&& after.view() == Endpoint { queue: after.view().queue, ..before.view() }
        &&& after.view().queue.container_depth == before.view().queue.container_depth
        &&& after.view().queue.lock_minor() == before.view().queue.lock_minor()
        &&& after.view().queue.view() == before.view().queue.view().skip(1)
        &&& after.view().queue.length as int == before.view().queue.length as int - 1
        &&& after.view().queue.map() == before.view().queue.map().remove(pre.thr_mp.spec_index(peer_thread_ptr).view().endpoint_linkedlist_node.addr())
        &&& after.view().queue.dom() == before.view().queue.dom().remove(pre.thr_mp.spec_index(peer_thread_ptr).view().endpoint_linkedlist_node.addr())
    }
    &&& post.sched_mp.dom() == pre.sched_mp.dom()
    &&& forall|key: RwLockSchedulerPtr| #![trigger pre.sched_mp.spec_index(key)] #![trigger post.sched_mp.spec_index(key)] pre.sched_mp.dom().contains(key) ==> {
        let before = pre.sched_mp.spec_index(key);
        let after = post.sched_mp.spec_index(key);
        &&& post.sched_mp.view().spec_index(key).is_init() == pre.sched_mp.view().spec_index(key).is_init()
        &&& post.sched_mp.view().spec_index(key).addr() == pre.sched_mp.view().spec_index(key).addr()
        &&& !(key == peer_scheduler_ptr) ==> after == before
    }
    &&& {
        let before = pre.sched_mp.spec_index(peer_scheduler_ptr);
        let after = post.sched_mp.spec_index(peer_scheduler_ptr);
        let shard_before = before.shards.spec_index(wake_cpu).view();
        let shard_after = after.shards.spec_index(wake_cpu).view();
        &&& after.owning_container == before.owning_container
        &&& after.shards.entries_unchanged_except(&before.shards, wake_cpu)
        &&& shard_after.is_init() == shard_before.is_init()
        &&& shard_after.view_rodata() == shard_before.view_rodata()
        &&& shard_after.view_ghost() == shard_before.view_ghost()
        &&& shard_after.being_killed() == shard_before.being_killed()
        &&& shard_after.locking_thread() is Write
        &&& shard_after.locking_thread()->Write_thread_id == thread_id
        &&& shard_after.view().queue.view() == shard_before.view().queue.view().push(peer_thread_ptr)
        &&& shard_after.view().queue.length as int == shard_before.view().queue.length as int + 1
        &&& shard_after.view().queue.map() == shard_before.view().queue.map().insert(pre.thr_mp.spec_index(peer_thread_ptr).view().scheduler_linkedlist_node.addr(), peer_thread_ptr)
        &&& shard_after.view().queue.dom() == shard_before.view().queue.dom().insert(pre.thr_mp.spec_index(peer_thread_ptr).view().scheduler_linkedlist_node.addr())
        &&& scheduler_shards_of(after) == scheduler_shards_of(before).update(wake_cpu as int, scheduler_shards_of(before)[wake_cpu as int].push(peer_thread_ptr))
    }
}
} // verus!
