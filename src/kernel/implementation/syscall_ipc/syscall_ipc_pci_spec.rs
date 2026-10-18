use vstd::prelude::*;
use crate::*;

verus! {
/// Dequeues and schedules the endpoint waiter with `peer_result`; when `transferred`, also hands the PCI function
/// `bdf` from the sender to the receiver process, detaches it, and flushes its IOTLB domain.
#[verifier::opaque]
pub open spec fn ipc_pci_rendezvous_transition(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr, peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId,
    sender_proc: RwLockProcessPtr, receiver_proc: RwLockProcessPtr, bdf: PciBdf, transferred: bool, peer_result: RetValueType, thread_id: LockThreadId,
) -> bool {
    &&& pre.inv()
    &&& current_thread_ptr != peer_thread_ptr
    &&& index_valid(NUM_CPUS, wake_cpu)
    &&& pre.thr_mp.dom().contains(current_thread_ptr)
    &&& pre.thr_mp.dom().contains(peer_thread_ptr)
    &&& pre.ep_mp.dom().contains(endpoint_ptr)
    &&& pre.sched_mp.dom().contains(peer_scheduler_ptr)
    &&& pre.ctn_mp.spec_index(pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container).view_rodata().view().scheduler == peer_scheduler_ptr
    &&& pre.thr_mp.spec_index(peer_thread_ptr).view().state.is_endpoint_waiting()
    &&& pre.thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr)
    &&& pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() > 0
    &&& pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr
    &&& pci_bdf_valid(bdf.0, bdf.1, bdf.2)
    &&& pre.prc_mp.dom().contains(sender_proc)
    &&& pre.prc_mp.dom().contains(receiver_proc)
    &&& sender_proc != receiver_proc
    &&& !pre.prc_mp.spec_index(sender_proc).view().zombie
    &&& !pre.prc_mp.spec_index(receiver_proc).view().zombie
    &&& transferred ==> pre.irt.view().spec_index_owner(bdf.0, bdf.1, bdf.2) == sender_proc
    &&& post.pt_mp == pre.pt_mp
    &&& post.it_mp == pre.it_mp
    &&& post.pg_arr == pre.pg_arr
    &&& post.ctn_mp == pre.ctn_mp
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
    &&& post.rt_ctn == pre.rt_ctn
    &&& post.dflt_pt == pre.dflt_pt
    &&& !transferred ==> post.irt.view() == pre.irt.view() && post.iommu_tlb.view() == pre.iommu_tlb.view() && post.prc_mp == pre.prc_mp
    &&& transferred ==> {
        &&& post.irt.view().owners() == seq3_update(pre.irt.view().owners(), bdf.0 as int, bdf.1 as int, bdf.2 as int, receiver_proc)
        &&& post.irt.view().iommu_roots() == seq3_update(pre.irt.view().iommu_roots(), bdf.0 as int, bdf.1 as int, bdf.2 as int, None)
        &&& forall|bus: usize, device: usize, function: usize| #![trigger post.irt.view().spec_index_owner(bus, device, function)] #![trigger post.irt.view().spec_index_iommu_root(bus, device, function)]
            pci_bdf_valid(bus, device, function) ==> {
                &&& post.irt.view().spec_index_owner(bus, device, function) == if (bus, device, function) == bdf { receiver_proc } else { pre.irt.view().spec_index_owner(bus, device, function) }
                &&& post.irt.view().spec_index_iommu_root(bus, device, function) == if (bus, device, function) == bdf { None } else { pre.irt.view().spec_index_iommu_root(bus, device, function) }
            }
        &&& post.iommu_tlb.view() == pre.iommu_tlb.view().insert(pci_bdf_did(bdf.0, bdf.1, bdf.2), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
    }
    &&& post.prc_mp.dom() == pre.prc_mp.dom()
    &&& forall|key: RwLockProcessPtr| #![trigger pre.prc_mp.spec_index(key)] #![trigger post.prc_mp.spec_index(key)] pre.prc_mp.dom().contains(key) ==> {
        let before = pre.prc_mp.spec_index(key);
        let after = post.prc_mp.spec_index(key);
        let pci = before.view_ghost().owned_pci_functions.view();
        &&& after.is_init() == before.is_init()
        &&& after.view() == before.view()
        &&& after.view_rodata() == before.view_rodata()
        &&& after.locking_thread() == before.locking_thread()
        &&& after.killer_info() == before.killer_info()
        &&& after.view_ghost().uppertree_seq == before.view_ghost().uppertree_seq
        &&& after.view_ghost().subtree_set == before.view_ghost().subtree_set
        &&& after.view_ghost().owned_pci_functions.view() == if transferred && key == sender_proc { pci.remove(bdf) } else if transferred && key == receiver_proc { pci.insert(bdf) } else { pci }
    }
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
        &&& !shard_before.view().queue.dom().contains(pre.thr_mp.spec_index(peer_thread_ptr).view().scheduler_linkedlist_node.addr())
    }
}
}
