use vstd::prelude::*;
use crate::*;

verus! {
/// Dequeues and schedules the endpoint waiter with `peer_result`; when `transferred`, also hands the PCI function
/// `bdf` from the sender to the receiver process. An attached `bdf` is detached under the write lock of the sender's
/// IOMMU table `iommu_table` (read from the sender's read-only mirror), which re-anchors at `anchor` or loses its DID
/// when `bdf` was its anchor, and the old DID domain is invalidated; an absent `bdf` only changes owner.
#[verifier::opaque]
pub open spec fn ipc_pci_rendezvous_eof_transition_framing(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr, peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId,
    sender_proc: RwLockProcessPtr, receiver_proc: RwLockProcessPtr, bdf: PciBdf, transferred: bool, peer_result: RetValueType, thread_id: LockThreadId,
    iommu_table: Option<RwLockPageTableRoot>, anchor: Option<PciBdf>,
) -> bool {
    &&& post.pt_mp == pre.pt_mp
    &&& post.pt_lower == pre.pt_lower
    &&& post.pg_arr == pre.pg_arr
    &&& post.ctn_mp == pre.ctn_mp
    &&& post.cpu_arr == pre.cpu_arr
    &&& post.cpu_set_mp == pre.cpu_set_mp
    &&& post.pcid_needflush == pre.pcid_needflush
    &&& post.cpu_hw_cr3_pcid == pre.cpu_hw_cr3_pcid
    &&& post.pcid_allc_mp == pre.pcid_allc_mp
    &&& post.allc_4k_mp == pre.allc_4k_mp
    &&& post.allc_2m_mp == pre.allc_2m_mp
    &&& post.allc_1g_mp == pre.allc_1g_mp
    &&& post.cpu_offline_mp == pre.cpu_offline_mp
    &&& post.cpu_op == pre.cpu_op
    &&& post.cpu_tlb == pre.cpu_tlb
    &&& post.rt_ctn == pre.rt_ctn
    &&& post.dflt_pt == pre.dflt_pt
    &&& !transferred ==> post.irt.view() == pre.irt.view() && post.iommu_tlb == pre.iommu_tlb && post.prc_mp == pre.prc_mp
    &&& iommu_table == if transferred && pre.irt.view().spec_index_iommu_root(bdf.0, bdf.1, bdf.2) is Some {
        pre.prc_mp.spec_index(sender_proc).view_rodata().view().iommu_table_ptr
    } else { None }
    &&& iommu_table is None ==> post.it_mp == pre.it_mp && anchor is None
    &&& transferred ==> post.irt.view().owners() == seq3_update(pre.irt.view().owners(), bdf.0 as int, bdf.1 as int, bdf.2 as int, receiver_proc)
    &&& transferred && iommu_table is None ==> {
        &&& post.iommu_tlb == pre.iommu_tlb
        &&& forall|b: usize, d: usize, f: usize| #![trigger post.irt.view().spec_index_owner(b, d, f)] #![trigger post.irt.view().spec_index_iommu_root(b, d, f)]
            #![trigger post.irt.view().spec_index_iommu_did(b, d, f)] pci_bdf_valid(b, d, f) ==> {
            &&& post.irt.view().spec_index_owner(b, d, f) == if (b, d, f) == bdf { receiver_proc } else { pre.irt.view().spec_index_owner(b, d, f) }
            &&& post.irt.view().spec_index_iommu_root(b, d, f) == pre.irt.view().spec_index_iommu_root(b, d, f)
            &&& post.irt.view().spec_index_iommu_did(b, d, f) == pre.irt.view().spec_index_iommu_did(b, d, f)
        }
    }
    &&& iommu_table matches Some(t) ==> {
        let table = pre.it_mp.spec_index(t);
        let old_did = pre.irt.view().spec_index_iommu_did(bdf.0, bdf.1, bdf.2);
        let anchored = old_did == Some(pci_bdf_did(bdf.0, bdf.1, bdf.2));
        &&& transferred
        &&& pre.it_mp.dom().contains(t)
        &&& forall|b: usize, d: usize, f: usize| #![trigger post.irt.view().spec_index_owner(b, d, f)] #![trigger post.irt.view().spec_index_iommu_root(b, d, f)]
            #![trigger post.irt.view().spec_index_iommu_did(b, d, f)] pci_bdf_valid(b, d, f) ==> {
            let moved = anchor is Some && (b, d, f) != bdf && pre.irt.view().spec_index_owner(b, d, f) == table.view().proc_ptr && pre.irt.view().spec_index_iommu_did(b, d, f) == old_did;
            &&& post.irt.view().spec_index_owner(b, d, f) == if (b, d, f) == bdf { receiver_proc } else { pre.irt.view().spec_index_owner(b, d, f) }
            &&& post.irt.view().spec_index_iommu_root(b, d, f) == if (b, d, f) == bdf { None } else if moved { Some(table.view().cr3) } else { pre.irt.view().spec_index_iommu_root(b, d, f) }
            &&& post.irt.view().spec_index_iommu_did(b, d, f) == if (b, d, f) == bdf { None }
                else if moved { Some(pci_bdf_did(anchor.unwrap().0, anchor.unwrap().1, anchor.unwrap().2)) } else { pre.irt.view().spec_index_iommu_did(b, d, f) }
        }
        &&& anchor matches Some(a) ==> {
            &&& anchored
            &&& pci_bdf_valid(a.0, a.1, a.2)
            &&& a != bdf
            &&& pre.irt.view().spec_index_owner(a.0, a.1, a.2) == table.view().proc_ptr
            &&& pre.irt.view().spec_index_iommu_did(a.0, a.1, a.2) == old_did
            &&& forall|b: usize, d: usize, f: usize| #![trigger pre.irt.view().spec_index_iommu_did(b, d, f)]
                pci_bdf_valid(b, d, f) ==> (pre.irt.view().spec_index_iommu_did(b, d, f) is Some) == (pre.irt.view().spec_index_iommu_root(b, d, f) is Some)
        }
        &&& anchored ==> forall|b: usize, d: usize, f: usize| #![trigger pre.irt.view().owners()[b as int][d as int][f as int]] #![trigger pre.irt.view().spec_index_iommu_did(b, d, f)]
            pci_bdf_valid(b, d, f) && (anchor is None || pci_bdf_lt((b, d, f), anchor.unwrap())) && (b, d, f) != bdf && pre.irt.view().owners()[b as int][d as int][f as int] == table.view().proc_ptr
                && pre.irt.view().spec_index_iommu_root(b, d, f) is Some ==> pre.irt.view().spec_index_iommu_did(b, d, f) != old_did
        &&& post.it_mp.unchanged_except(&pre.it_mp, t)
        &&& post.it_mp.spec_index(t).being_killed() == table.being_killed()
        &&& post.it_mp.spec_index(t).locking_thread() is Write
        &&& post.it_mp.spec_index(t).locking_thread()->Write_thread_id == thread_id
        &&& post.it_mp.spec_index(t).view() == (PageTable { did: post.it_mp.spec_index(t).view().did, ..table.view() })
        &&& post.it_mp.spec_index(t).view().page_closure() == table.view().page_closure()
        &&& post.it_mp.spec_index(t).view().mapping_4k() == table.view().mapping_4k()
        &&& post.it_mp.spec_index(t).view().mapping_2m() == table.view().mapping_2m()
        &&& post.it_mp.spec_index(t).view().mapping_1g() == table.view().mapping_1g()
        &&& post.it_mp.spec_index(t).view().did == if anchor is Some { Some(pci_bdf_did(anchor.unwrap().0, anchor.unwrap().1, anchor.unwrap().2)) }
            else if anchored { None } else { table.view().did }
        &&& old_did matches Some(did) ==> {
            &&& post.iommu_tlb.view() == pre.iommu_tlb.view().insert(did, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
            &&& forall|x: VtdDomainId| #![trigger post.iommu_tlb.spec_index(x)] x != did ==> post.iommu_tlb.spec_index(x) == pre.iommu_tlb.spec_index(x)
            &&& post.iommu_tlb.context_cache() == Map::new(pre.iommu_tlb.context_cache().dom().filter(|x: PciBdf| pre.iommu_tlb.context_cache()[x].1 != did), |x: PciBdf| pre.iommu_tlb.context_cache()[x])
        }
        &&& old_did is None ==> post.iommu_tlb.view() == pre.iommu_tlb.view() && post.iommu_tlb.context_cache() == pre.iommu_tlb.context_cache()
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
    }
}
}
