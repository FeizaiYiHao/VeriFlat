use vstd::prelude::*;
use crate::*;

verus! {
/// The page tables in the PCI part of the rendezvous: only the sender's and the receiver's page tables `sender_pt` and
/// `receiver_pt` change, in their PCI function arrays alone; when `transferred`, `bdf` leaves the sender's array and enters the
/// receiver's with no BAR mapping.
#[verifier::opaque]
pub(super) open spec fn ipc_pci_rendezvous_eof_pagetable_frame(
    pre: KernelK, mid: KernelK, sender_pt: RwLockPageTableRoot, receiver_pt: RwLockPageTableRoot, bdf: PciBdf, transferred: bool,
) -> bool {
    &&& mid.pt_mp.dom() == pre.pt_mp.dom()
    &&& forall|p: RwLockPageTableRoot| #![trigger mid.pt_mp.spec_index(p)] pre.pt_mp.dom().contains(p) && p != sender_pt && p != receiver_pt ==> mid.pt_mp.spec_index(p) == pre.pt_mp.spec_index(p)
    &&& mid.pt_mp.spec_index(sender_pt).view().higher == (PageTableHigher { pci: mid.pt_mp.spec_index(sender_pt).view().higher.pci, ..pre.pt_mp.spec_index(sender_pt).view().higher })
    &&& mid.pt_mp.spec_index(receiver_pt).view().higher == (PageTableHigher { pci: mid.pt_mp.spec_index(receiver_pt).view().higher.pci, ..pre.pt_mp.spec_index(receiver_pt).view().higher })
    &&& mid.pt_mp.spec_index(sender_pt).view().higher.pci.view() == if transferred { pre.pt_mp.spec_index(sender_pt).view().higher.pci.view().remove(bdf) }
        else { pre.pt_mp.spec_index(sender_pt).view().higher.pci.view() }
    &&& mid.pt_mp.spec_index(receiver_pt).view().higher.pci.view() == if transferred { pre.pt_mp.spec_index(receiver_pt).view().higher.pci.view().insert(bdf, Set::<PciBarMapping>::empty()) }
        else { pre.pt_mp.spec_index(receiver_pt).view().higher.pci.view() }
    &&& forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(mid.pt_mp, mid.pt_lower.view(), p)] pre.pt_mp.dom().contains(p) ==> {
        let before = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p);
        let after = whole_pagetable(mid.pt_mp, mid.pt_lower.view(), p);
        &&& after.mapping_4k() == before.mapping_4k()
        &&& after.mapping_2m() == before.mapping_2m()
        &&& after.mapping_1g() == before.mapping_1g()
        &&& after.lower.pagetable_window_locks == before.lower.pagetable_window_locks
    }
    &&& mid.pt_mp.spec_index(sender_pt).being_killed() == pre.pt_mp.spec_index(sender_pt).being_killed()
    &&& mid.pt_mp.spec_index(receiver_pt).being_killed() == pre.pt_mp.spec_index(receiver_pt).being_killed()
}

/// The PCI part of the rendezvous, from `pre`, with the sender's and the receiver's page tables `sender_pt` and `receiver_pt`
/// write-held, to `mid`. When `transferred`, an attached `bdf` is first detached under the write lock of the sender's IOMMU
/// table `iommu_table` (read from the sender's read-only mirror), which re-anchors at `anchor` or loses its DID when `bdf` was
/// its anchor, and the old DID domain is invalidated down to what the IOMMU may cache in the detached root table; then `bdf`
/// leaves the sender's PCI function array, unowned, and enters the receiver's, owned by the receiver. Otherwise only the
/// page-table locks were taken.
#[verifier::opaque]
pub(super) open spec fn ipc_pci_rendezvous_eof_pci_handoff(
    pre: KernelK, mid: KernelK, sender_proc: RwLockProcessPtr, receiver_proc: RwLockProcessPtr, sender_pt: RwLockPageTableRoot, receiver_pt: RwLockPageTableRoot,
    bdf: PciBdf, transferred: bool, thread_id: LockThreadId, iommu_table: Option<RwLockPageTableRoot>, anchor: Option<PciBdf>,
) -> bool {
    &&& mid == (KernelK { pt_mp: mid.pt_mp, irt: mid.irt, iommu_tlb: mid.iommu_tlb, it_mp: mid.it_mp, ..pre })
    &&& ipc_pci_rendezvous_eof_pagetable_frame(pre, mid, sender_pt, receiver_pt, bdf, transferred)
    &&& !transferred ==> mid.irt.view() == pre.irt.view() && mid.iommu_tlb == pre.iommu_tlb && mid.it_mp == pre.it_mp
    &&& transferred ==> mid.irt.view().owners() == seq3_update(pre.irt.view().owners(), bdf.0 as int, bdf.1 as int, bdf.2 as int, Some(receiver_proc))
    &&& iommu_table == if transferred && pre.irt.view().spec_index_iommu_root(bdf.0, bdf.1, bdf.2) is Some {
        pre.prc_mp.spec_index(sender_proc).view_rodata().view().iommu_table_ptr
    } else { None }
    &&& iommu_table is None ==> mid.it_mp == pre.it_mp && mid.iommu_tlb == pre.iommu_tlb && anchor is None
    &&& transferred && iommu_table is None ==> forall|b: usize, d: usize, f: usize| #![trigger mid.irt.view().spec_index_iommu_root(b, d, f)]
        #![trigger mid.irt.view().spec_index_iommu_did(b, d, f)] pci_bdf_valid(b, d, f) ==> {
        &&& mid.irt.view().spec_index_iommu_root(b, d, f) == pre.irt.view().spec_index_iommu_root(b, d, f)
        &&& mid.irt.view().spec_index_iommu_did(b, d, f) == pre.irt.view().spec_index_iommu_did(b, d, f)
    }
    &&& iommu_table matches Some(t) ==> {
        let table = pre.it_mp.spec_index(t);
        let pci = pre.pt_mp.spec_index(sender_pt).view().higher.pci;
        let old_did = pre.irt.view().spec_index_iommu_did(bdf.0, bdf.1, bdf.2);
        let anchored = old_did == Some(pci_bdf_did(bdf.0, bdf.1, bdf.2));
        &&& transferred
        &&& pre.it_mp.dom().contains(t)
        &&& forall|b: usize, d: usize, f: usize| #![trigger mid.irt.view().spec_index_iommu_root(b, d, f)] #![trigger mid.irt.view().spec_index_iommu_did(b, d, f)]
            pci_bdf_valid(b, d, f) ==> {
            let moved = anchor is Some && (b, d, f) != bdf && pci.view().dom().contains((b, d, f)) && pre.irt.view().spec_index_iommu_did(b, d, f) == old_did;
            &&& mid.irt.view().spec_index_iommu_root(b, d, f) == if (b, d, f) == bdf { None } else if moved { Some(table.view().cr3) } else { pre.irt.view().spec_index_iommu_root(b, d, f) }
            &&& mid.irt.view().spec_index_iommu_did(b, d, f) == if (b, d, f) == bdf { None }
                else if moved { Some(pci_bdf_did(anchor.unwrap().0, anchor.unwrap().1, anchor.unwrap().2)) } else { pre.irt.view().spec_index_iommu_did(b, d, f) }
        }
        &&& anchor matches Some(a) ==> {
            &&& anchored
            &&& pci_bdf_valid(a.0, a.1, a.2)
            &&& a != bdf
            &&& pci.view().dom().contains(a)
            &&& pre.irt.view().spec_index_iommu_did(a.0, a.1, a.2) == old_did
            &&& forall|b: usize, d: usize, f: usize| #![trigger pre.irt.view().spec_index_iommu_did(b, d, f)]
                pci_bdf_valid(b, d, f) && (b, d, f) != bdf && pci.view().dom().contains((b, d, f)) && pre.irt.view().spec_index_iommu_did(b, d, f) == old_did ==> !pci_bdf_lt((b, d, f), a)
            &&& forall|b: usize, d: usize, f: usize| #![trigger pre.irt.view().spec_index_iommu_did(b, d, f)]
                pci_bdf_valid(b, d, f) ==> (pre.irt.view().spec_index_iommu_did(b, d, f) is Some) == (pre.irt.view().spec_index_iommu_root(b, d, f) is Some)
        }
        &&& anchor is None && anchored ==> forall|b: usize, d: usize, f: usize| #![trigger pre.irt.view().spec_index_iommu_did(b, d, f)]
            pci_bdf_valid(b, d, f) && (b, d, f) != bdf && pci.view().dom().contains((b, d, f)) ==> pre.irt.view().spec_index_iommu_did(b, d, f) != old_did
        &&& mid.it_mp.unchanged_except(&pre.it_mp, t)
        &&& mid.it_mp.spec_index(t).being_killed() == table.being_killed()
        &&& mid.it_mp.spec_index(t).locking_thread() is Write
        &&& mid.it_mp.spec_index(t).locking_thread()->Write_thread_id == thread_id
        &&& mid.it_mp.spec_index(t).view() == (IommuTable { did: mid.it_mp.spec_index(t).view().did, ..table.view() })
        &&& mid.it_mp.spec_index(t).view().did == if anchor is Some { Some(pci_bdf_did(anchor.unwrap().0, anchor.unwrap().1, anchor.unwrap().2)) }
            else if anchored { None } else { table.view().did }
        &&& old_did matches Some(did) ==> {
            &&& mid.iommu_tlb.view() == pre.iommu_tlb.view().insert(did, mid.iommu_tlb.spec_index(did))
            &&& iommu_tlb_within_may_cache(KernelK { irt: mid.irt, ..pre }, did, mid.iommu_tlb.spec_index(did))
        }
        &&& old_did is None ==> mid.iommu_tlb.view() == pre.iommu_tlb.view()
    }
}

/// The PCI-payload rendezvous from `pre` through `mid`, after the PCI part `ipc_pci_rendezvous_eof_pci_handoff`, to `post`,
/// which dequeues and schedules the endpoint waiter with `peer_result`.
#[verifier::opaque]
pub(super) open spec fn ipc_pci_rendezvous_eof_transition_framing(
    pre: KernelK, mid: KernelK, post: KernelK, peer_thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr, peer_sched_ptr: RwLockSchedulerPtr,
    wake_cpu: CpuId, sender_proc: RwLockProcessPtr, receiver_proc: RwLockProcessPtr, sender_pt: RwLockPageTableRoot, receiver_pt: RwLockPageTableRoot,
    bdf: PciBdf, transferred: bool, peer_result: RetValueType, thread_id: LockThreadId, iommu_table: Option<RwLockPageTableRoot>, anchor: Option<PciBdf>,
) -> bool {
    &&& ipc_pci_rendezvous_eof_pci_handoff(pre, mid, sender_proc, receiver_proc, sender_pt, receiver_pt, bdf, transferred, thread_id, iommu_table, anchor)
    &&& post == (KernelK { thrd_mp: post.thrd_mp, ep_mp: post.ep_mp, sched_mp: post.sched_mp, ..mid })
    &&& post.thrd_mp.dom() == mid.thrd_mp.dom()
    &&& forall|key: RwLockThreadPtr| #![trigger mid.thrd_mp.spec_index(key)] #![trigger post.thrd_mp.spec_index(key)]
        #![trigger mid.thrd_mp.spec_index(key).view().temp_alloc_cache_2m] #![trigger post.thrd_mp.spec_index(key).view().temp_alloc_cache_2m]
        #![trigger mid.thrd_mp.spec_index(key).view().temp_alloc_cache_1g] #![trigger post.thrd_mp.spec_index(key).view().temp_alloc_cache_1g]
        mid.thrd_mp.dom().contains(key) ==> {
            let before = mid.thrd_mp.spec_index(key);
            let after = post.thrd_mp.spec_index(key);
            &&& post.thrd_mp.view().spec_index(key).is_init() == mid.thrd_mp.view().spec_index(key).is_init()
            &&& post.thrd_mp.view().spec_index(key).addr() == mid.thrd_mp.view().spec_index(key).addr()
            &&& after.view().temp_alloc_cache_2m == before.view().temp_alloc_cache_2m
            &&& after.view().temp_alloc_cache_1g == before.view().temp_alloc_cache_1g
            &&& !(key == peer_thrd_ptr) ==> after == before
        }
    &&& {
        let before = mid.thrd_mp.spec_index(peer_thrd_ptr);
        let after = post.thrd_mp.spec_index(peer_thrd_ptr);
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
    &&& post.ep_mp.dom() == mid.ep_mp.dom()
    &&& forall|key: RwLockEndpointPtr| #![trigger mid.ep_mp.spec_index(key)] #![trigger post.ep_mp.spec_index(key)] mid.ep_mp.dom().contains(key) ==> {
        let before = mid.ep_mp.spec_index(key);
        let after = post.ep_mp.spec_index(key);
        &&& post.ep_mp.view().spec_index(key).is_init() == mid.ep_mp.view().spec_index(key).is_init()
        &&& post.ep_mp.view().spec_index(key).addr() == mid.ep_mp.view().spec_index(key).addr()
        &&& !(key == ep_ptr) ==> after == before
    }
    &&& {
        let before = mid.ep_mp.spec_index(ep_ptr);
        let after = post.ep_mp.spec_index(ep_ptr);
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
        &&& after.view().queue.map() == before.view().queue.map().remove(mid.thrd_mp.spec_index(peer_thrd_ptr).view().endpoint_linkedlist_node.addr())
        &&& after.view().queue.dom() == before.view().queue.dom().remove(mid.thrd_mp.spec_index(peer_thrd_ptr).view().endpoint_linkedlist_node.addr())
    }
    &&& post.sched_mp.dom() == mid.sched_mp.dom()
    &&& forall|key: RwLockSchedulerPtr| #![trigger mid.sched_mp.spec_index(key)] #![trigger post.sched_mp.spec_index(key)] mid.sched_mp.dom().contains(key) ==> {
        let before = mid.sched_mp.spec_index(key);
        let after = post.sched_mp.spec_index(key);
        &&& post.sched_mp.view().spec_index(key).is_init() == mid.sched_mp.view().spec_index(key).is_init()
        &&& post.sched_mp.view().spec_index(key).addr() == mid.sched_mp.view().spec_index(key).addr()
        &&& !(key == peer_sched_ptr) ==> after == before
    }
    &&& {
        let before = mid.sched_mp.spec_index(peer_sched_ptr);
        let after = post.sched_mp.spec_index(peer_sched_ptr);
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
        &&& shard_after.view().queue.view() == shard_before.view().queue.view().push(peer_thrd_ptr)
        &&& shard_after.view().queue.length as int == shard_before.view().queue.length as int + 1
        &&& shard_after.view().queue.map() == shard_before.view().queue.map().insert(mid.thrd_mp.spec_index(peer_thrd_ptr).view().scheduler_linkedlist_node.addr(), peer_thrd_ptr)
        &&& shard_after.view().queue.dom() == shard_before.view().queue.dom().insert(mid.thrd_mp.spec_index(peer_thrd_ptr).view().scheduler_linkedlist_node.addr())
    }
}
}
