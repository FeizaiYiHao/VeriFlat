use vstd::prelude::*;
use crate::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal};
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_pci_spec::{ipc_pci_rendezvous_eof_pagetable_frame, ipc_pci_rendezvous_eof_pci_handoff, ipc_pci_rendezvous_eof_transition_framing};
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_dispatch::running_thread_not_in_endpoint_queue;

verus! {

/// Detaching `bdf` changes only the root table, the IOTLB, and the IOMMU table `table`: the function loses its context entry,
/// `table` re-anchors at `anchor` or loses its DID when `bdf` was its anchor, the other functions of the PCI function array of
/// `sender_pt` that carried the old DID move with it, the old DID domain is invalidated, and owners are as before.
pub(super) open spec fn ipc_pci_detach_eof_transition_framing(pre: KernelK, post: KernelK, sender_pt: RwLockPageTableRoot, table: RwLockPageTableRoot, bdf: PciBdf, anchor: Option<PciBdf>) -> bool {
    let pci = pre.pt_mp.spec_index(sender_pt).view().higher.pci;
    let old_did = pre.irt.view().spec_index_iommu_did(bdf.0, bdf.1, bdf.2);
    let anchored = old_did == Some(pci_bdf_did(bdf.0, bdf.1, bdf.2));
    &&& post == (KernelK { irt: post.irt, iommu_tlb: post.iommu_tlb, it_mp: post.it_mp, ..pre })
    &&& post.irt.view().owners() == pre.irt.view().owners()
    &&& forall|b: usize, d: usize, f: usize| #![trigger post.irt.view().spec_index_owner(b, d, f)] #![trigger post.irt.view().spec_index_iommu_root(b, d, f)]
        #![trigger post.irt.view().spec_index_iommu_did(b, d, f)] pci_bdf_valid(b, d, f) ==> {
        let moved = anchor is Some && (b, d, f) != bdf && pci.view().dom().contains((b, d, f)) && pre.irt.view().spec_index_iommu_did(b, d, f) == old_did;
        &&& post.irt.view().spec_index_owner(b, d, f) == pre.irt.view().spec_index_owner(b, d, f)
        &&& post.irt.view().spec_index_iommu_root(b, d, f) == if (b, d, f) == bdf { None } else if moved { Some(pre.it_mp.spec_index(table).view().cr3) }
            else { pre.irt.view().spec_index_iommu_root(b, d, f) }
        &&& post.irt.view().spec_index_iommu_did(b, d, f) == if (b, d, f) == bdf { None } else if moved { Some(pci_bdf_did(anchor.unwrap().0, anchor.unwrap().1, anchor.unwrap().2)) }
            else { pre.irt.view().spec_index_iommu_did(b, d, f) }
    }
    &&& anchor matches Some(a) ==> {
        &&& anchored
        &&& pci_bdf_valid(a.0, a.1, a.2)
        &&& a != bdf
        &&& pci.view().dom().contains(a)
        &&& pre.irt.view().spec_index_iommu_did(a.0, a.1, a.2) == old_did
    }
    &&& anchor is None && anchored ==> forall|b: usize, d: usize, f: usize| #![trigger pre.irt.view().spec_index_iommu_did(b, d, f)]
        pci_bdf_valid(b, d, f) && (b, d, f) != bdf && pci.view().dom().contains((b, d, f)) ==> pre.irt.view().spec_index_iommu_did(b, d, f) != old_did
    &&& post.it_mp.unchanged_except(&pre.it_mp, table)
    &&& post.it_mp.spec_index(table).locking_thread() == pre.it_mp.spec_index(table).locking_thread()
    &&& post.it_mp.spec_index(table).being_killed() == pre.it_mp.spec_index(table).being_killed()
    &&& post.it_mp.spec_index(table).view() == (IommuTable { did: post.it_mp.spec_index(table).view().did, ..pre.it_mp.spec_index(table).view() })
    &&& post.it_mp.spec_index(table).view().did == if anchor is Some { Some(pci_bdf_did(anchor.unwrap().0, anchor.unwrap().1, anchor.unwrap().2)) }
        else if anchored { None } else { pre.it_mp.spec_index(table).view().did }
    &&& old_did matches Some(did) ==> {
        &&& post.iommu_tlb.view() == pre.iommu_tlb.view().insert(did, post.iommu_tlb.spec_index(did))
        &&& forall|x: VtdDomainId| #![trigger post.iommu_tlb.spec_index(x)] x != did ==> post.iommu_tlb.spec_index(x) == pre.iommu_tlb.spec_index(x)
        &&& iommu_tlb_within_may_cache(KernelK { irt: post.irt, ..pre }, did, post.iommu_tlb.spec_index(did))
        &&& Map::new(post.iommu_tlb.context_cache().dom().filter(|bdf: PciBdf| post.iommu_tlb.context_cache()[bdf].1 != did), |bdf: PciBdf| post.iommu_tlb.context_cache()[bdf])
            == Map::new(pre.iommu_tlb.context_cache().dom().filter(|bdf: PciBdf| pre.iommu_tlb.context_cache()[bdf].1 != did), |bdf: PciBdf| pre.iommu_tlb.context_cache()[bdf])
        &&& forall|bdf: PciBdf| #![trigger post.iommu_tlb.context_cache().dom().contains(bdf)] post.iommu_tlb.context_cache().dom().contains(bdf) && post.iommu_tlb.context_cache()[bdf].1 == did
            ==> iommu_context_cache_entry_present(KernelK { irt: post.irt, ..pre }, bdf, post.iommu_tlb.context_cache()[bdf])
    }
    &&& old_did is None ==> post.iommu_tlb.view() == pre.iommu_tlb.view() && post.iommu_tlb.context_cache() == pre.iommu_tlb.context_cache()
}

/// The root table still names, for every attached function, the IOMMU table of the function's owner.
proof fn ipc_pci_detach_eof_root_table(
    pre: KernelK, post: KernelK, sender_proc: RwLockProcessPtr, sender_pt: RwLockPageTableRoot, table: RwLockPageTableRoot, bdf: PciBdf, anchor: Option<PciBdf>,
)
    requires
        pre.inv(),
        ipc_pci_detach_eof_transition_framing(pre, post, sender_pt, table, bdf, anchor),
        pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        pre.prc_mp.dom().contains(sender_proc),
        pre.pt_mp.dom().contains(sender_pt),
        pre.pt_mp.spec_index(sender_pt).view().higher.proc_ptr == sender_proc,
        pre.prc_mp.spec_index(sender_proc).view().pagetable == sender_pt,
        pre.prc_mp.spec_index(sender_proc).view().iommu_table == Some(table),
        pre.it_mp.dom().contains(table),
        pre.it_mp.spec_index(table).locking_thread() is Write,
        pre.it_mp.spec_index(table).view().leaves_present(),
        pre.irt.view().spec_index_iommu_root(bdf.0, bdf.1, bdf.2) is Some,
        pre.pt_mp.spec_index(sender_pt).view().higher.pci.view().dom().contains(bdf),
        pre.it_mp.spec_index(table).view().proc_ptr == sender_proc,
        pre.irt.view().spec_index_owner(bdf.0, bdf.1, bdf.2) == Some(sender_proc),
        pre.irt.view().spec_index_iommu_root(bdf.0, bdf.1, bdf.2) == Some(pre.it_mp.spec_index(table).view().cr3),
        pre.irt.view().spec_index_iommu_did(bdf.0, bdf.1, bdf.2) == pre.it_mp.spec_index(table).view().did,
        pre.it_mp.spec_index(table).view().did is Some,
        vtd_domain_id_valid(pre.it_mp.spec_index(table).view().did->Some_0),
        post.irt.inv(),
        post.iommu_tlb.inv(),
        iommu_table_perms_wf(post.it_mp),
    ensures iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp),
{
    let t = pre.it_mp.spec_index(table).view();
    let old_did = pre.irt.view().spec_index_iommu_did(bdf.0, bdf.1, bdf.2);
    assert(pci_bdf_of_did(pci_bdf_did(bdf.0, bdf.1, bdf.2)) == bdf) by (nonlinear_arith) requires pci_bdf_valid(bdf.0, bdf.1, bdf.2);
    assert(pci_bdf_valid(pci_bdf_of_did(t.did->Some_0).0, pci_bdf_of_did(t.did->Some_0).1, pci_bdf_of_did(t.did->Some_0).2)
        && pci_bdf_did(pci_bdf_of_did(t.did->Some_0).0, pci_bdf_of_did(t.did->Some_0).1, pci_bdf_of_did(t.did->Some_0).2) == t.did->Some_0) by (nonlinear_arith)
        requires vtd_domain_id_valid(t.did->Some_0);
    if let Some(a) = anchor {
        assert(pci_bdf_of_did(pci_bdf_did(a.0, a.1, a.2)) == a && vtd_domain_id_valid(pci_bdf_did(a.0, a.1, a.2))) by (nonlinear_arith) requires pci_bdf_valid(a.0, a.1, a.2);
    }
    assert({
        &&& post.it_mp.spec_index(table).view().page_closure() == t.page_closure()
        &&& post.it_mp.spec_index(table).view().mapping_4k() == t.mapping_4k()
        &&& post.it_mp.spec_index(table).view().mapping_2m() == t.mapping_2m()
        &&& post.it_mp.spec_index(table).view().mapping_1g() == t.mapping_1g()
    });
    reveal(iommu_root_table_process_wf); reveal(process_iommu_table_wf); reveal(pci_function_ownership_wf);
}

/// The IOTLB and the context cache keep only what the detached root table may still cache.
proof fn ipc_pci_detach_eof_iotlb(
    pre: KernelK, post: KernelK, sender_proc: RwLockProcessPtr, sender_pt: RwLockPageTableRoot, table: RwLockPageTableRoot, bdf: PciBdf, anchor: Option<PciBdf>,
)
    requires
        pre.inv(),
        ipc_pci_detach_eof_transition_framing(pre, post, sender_pt, table, bdf, anchor),
        pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        pre.prc_mp.dom().contains(sender_proc),
        pre.pt_mp.dom().contains(sender_pt),
        pre.pt_mp.spec_index(sender_pt).view().higher.proc_ptr == sender_proc,
        pre.prc_mp.spec_index(sender_proc).view().pagetable == sender_pt,
        pre.prc_mp.spec_index(sender_proc).view().iommu_table == Some(table),
        pre.it_mp.dom().contains(table),
        pre.it_mp.spec_index(table).locking_thread() is Write,
        pre.it_mp.spec_index(table).view().leaves_present(),
        pre.irt.view().spec_index_iommu_root(bdf.0, bdf.1, bdf.2) is Some,
        pre.pt_mp.spec_index(sender_pt).view().higher.pci.view().dom().contains(bdf),
        post.irt.inv(),
        post.iommu_tlb.inv(),
        iommu_table_perms_wf(post.it_mp),
        pre.it_mp.spec_index(table).view().proc_ptr == sender_proc,
        pre.irt.view().spec_index_owner(bdf.0, bdf.1, bdf.2) == Some(sender_proc),
        pre.irt.view().spec_index_iommu_root(bdf.0, bdf.1, bdf.2) == Some(pre.it_mp.spec_index(table).view().cr3),
        pre.irt.view().spec_index_iommu_did(bdf.0, bdf.1, bdf.2) == pre.it_mp.spec_index(table).view().did,
        pre.it_mp.spec_index(table).view().did is Some,
        vtd_domain_id_valid(pre.it_mp.spec_index(table).view().did->Some_0),
        iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp),
    ensures iommu_tlb_wf(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp),
{
    let t = pre.it_mp.spec_index(table).view();
    let old_did = pre.irt.view().spec_index_iommu_did(bdf.0, bdf.1, bdf.2);
    assert(pci_bdf_of_did(pci_bdf_did(bdf.0, bdf.1, bdf.2)) == bdf) by (nonlinear_arith) requires pci_bdf_valid(bdf.0, bdf.1, bdf.2);
    assert(pci_bdf_valid(pci_bdf_of_did(t.did->Some_0).0, pci_bdf_of_did(t.did->Some_0).1, pci_bdf_of_did(t.did->Some_0).2)
        && pci_bdf_did(pci_bdf_of_did(t.did->Some_0).0, pci_bdf_of_did(t.did->Some_0).1, pci_bdf_of_did(t.did->Some_0).2) == t.did->Some_0) by (nonlinear_arith)
        requires vtd_domain_id_valid(t.did->Some_0);
    if let Some(a) = anchor {
        assert(pci_bdf_of_did(pci_bdf_did(a.0, a.1, a.2)) == a && vtd_domain_id_valid(pci_bdf_did(a.0, a.1, a.2))) by (nonlinear_arith) requires pci_bdf_valid(a.0, a.1, a.2);
    }
    assert({
        &&& post.it_mp.spec_index(table).view().page_closure() == t.page_closure()
        &&& post.it_mp.spec_index(table).view().mapping_4k() == t.mapping_4k()
        &&& post.it_mp.spec_index(table).view().mapping_2m() == t.mapping_2m()
        &&& post.it_mp.spec_index(table).view().mapping_1g() == t.mapping_1g()
    });
    if old_did is Some {
        let did = old_did->Some_0;
        assert(post.iommu_tlb.context_cache() =~= Map::new(pre.iommu_tlb.context_cache().dom().filter(|bdf: PciBdf| pre.iommu_tlb.context_cache()[bdf].1 != did), |bdf: PciBdf| pre.iommu_tlb.context_cache()[bdf])
            .union_prefer_right(Map::new(post.iommu_tlb.context_cache().dom().filter(|bdf: PciBdf| post.iommu_tlb.context_cache()[bdf].1 == did), |bdf: PciBdf| post.iommu_tlb.context_cache()[bdf])));
    }
    reveal(iommu_tlb_wf); reveal(iommu_root_table_process_wf); reveal(IommuTLB::inv); reveal(process_iommu_table_wf);
}

/// Detaching the attached function `bdf` of the live process `sender_proc` from its write-held IOMMU table `table` under the
/// held root-table lock: the function loses its context entry, `table` re-anchors at `anchor` or loses its DID when `bdf` was its
/// anchor, the other functions of the sender's PCI function array that carried the old DID move with it, and the old DID domain
/// is invalidated. Owners and every other object are as before.
pub(super) proof fn ipc_pci_detach_eof(
    pre: KernelK, post: KernelK, sender_proc: RwLockProcessPtr, sender_pt: RwLockPageTableRoot, table: RwLockPageTableRoot, bdf: PciBdf, anchor: Option<PciBdf>,
)
    requires
        pre.inv(),
        ipc_pci_detach_eof_transition_framing(pre, post, sender_pt, table, bdf, anchor),
        pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        pre.prc_mp.dom().contains(sender_proc),
        pre.pt_mp.dom().contains(sender_pt),
        pre.pt_mp.spec_index(sender_pt).view().higher.proc_ptr == sender_proc,
        pre.prc_mp.spec_index(sender_proc).view().pagetable == sender_pt,
        pre.prc_mp.spec_index(sender_proc).view().iommu_table == Some(table),
        pre.it_mp.dom().contains(table),
        pre.it_mp.spec_index(table).locking_thread() is Write,
        pre.it_mp.spec_index(table).view().leaves_present(),
        pre.irt.view().spec_index_iommu_root(bdf.0, bdf.1, bdf.2) is Some,
        pre.pt_mp.spec_index(sender_pt).view().higher.pci.view().dom().contains(bdf),
        post.irt.inv(),
        post.iommu_tlb.inv(),
        iommu_table_perms_wf(post.it_mp),
    ensures
        post.inv(),
{
    let t = pre.it_mp.spec_index(table).view();
    let old_did = pre.irt.view().spec_index_iommu_did(bdf.0, bdf.1, bdf.2);
    assert({
        &&& t.proc_ptr == sender_proc
        &&& pre.irt.view().spec_index_owner(bdf.0, bdf.1, bdf.2) == Some(sender_proc)
        &&& pre.irt.view().spec_index_iommu_root(bdf.0, bdf.1, bdf.2) == Some(t.cr3)
        &&& old_did == t.did
        &&& t.did is Some
        &&& vtd_domain_id_valid(t.did->Some_0)
    }) by {
        process_iommu_table_wf_process_at(pre.prc_mp, pre.it_mp, sender_proc); pci_function_ownership_wf_pagetable_at(pre.irt.view(), pre.prc_mp, pre.pt_mp, sender_pt, bdf);
        reveal(iommu_root_table_process_wf);
    };
    assert({
        &&& post.it_mp.spec_index(table).view().page_closure() == t.page_closure()
        &&& post.it_mp.spec_index(table).view().mapping_4k() == t.mapping_4k()
        &&& post.it_mp.spec_index(table).view().mapping_2m() == t.mapping_2m()
        &&& post.it_mp.spec_index(table).view().mapping_1g() == t.mapping_1g()
    });
    assert(process_iommu_table_wf(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_iommu_table_wf); };
    assert(pci_function_ownership_wf(post.irt.view(), post.prc_mp, post.pt_mp)) by { reveal(pci_function_ownership_wf); };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { ipc_pci_detach_eof_root_table(pre, post, sender_proc, sender_pt, table, bdf, anchor); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { reveal(iommu_table_pages_wf); };
    assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { reveal(process_object_pages_owner_wf); reveal(iommu_table_pages_wf); };
    assert(iommu_tlb_wf(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { ipc_pci_detach_eof_iotlb(pre, post, sender_proc, sender_pt, table, bdf, anchor); };
    assert(post.inv()) by { reveal(KernelK::default_pagetable_wf); };
}

/// The endpoint queue, descriptor, reference-counter, and call-link relations close after the transition.
proof fn ipc_pci_rendezvous_eof_endpoint_wf(
    pre: KernelK, mid: KernelK, post: KernelK, current_thrd_ptr: RwLockThreadPtr, peer_thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr,
    peer_sched_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, sender_proc: RwLockProcessPtr, receiver_proc: RwLockProcessPtr, sender_pt: RwLockPageTableRoot,
    receiver_pt: RwLockPageTableRoot, bdf: PciBdf, transferred: bool, peer_result: RetValueType, thread_id: LockThreadId, iommu_table: Option<RwLockPageTableRoot>,
    anchor: Option<PciBdf>,
)
    requires
        mid.inv(),
        index_valid(NUM_CPUS, wake_cpu),
        mid.thrd_mp.dom().contains(peer_thrd_ptr),
        mid.ep_mp.dom().contains(ep_ptr),
        mid.sched_mp.dom().contains(peer_sched_ptr),
        mid.ctn_mp.spec_index(mid.thrd_mp.spec_index(peer_thrd_ptr).view().owning_container).view_rodata().view().scheduler == peer_sched_ptr,
        mid.thrd_mp.spec_index(peer_thrd_ptr).view().state.is_endpoint_waiting(),
        mid.thrd_mp.spec_index(peer_thrd_ptr).view().blocking_endpoint_ptr == Some(ep_ptr),
        mid.ep_mp.spec_index(ep_ptr).view().queue.view().len() > 0,
        mid.ep_mp.spec_index(ep_ptr).view().queue.view().spec_index(0) == peer_thrd_ptr,
        !mid.sched_mp.spec_index(peer_sched_ptr).shards.spec_index(wake_cpu).view().view().queue.dom().contains(mid.thrd_mp.spec_index(peer_thrd_ptr).view().scheduler_linkedlist_node.addr()),
        ipc_pci_rendezvous_eof_transition_framing(pre, mid, post, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, sender_proc, receiver_proc, sender_pt, receiver_pt, bdf, transferred, peer_result, thread_id, iommu_table, anchor),
        post.subsystems_inv(),
    ensures
        thread_endpoint_ref_counter_wf(post.thrd_mp, post.ep_mp),
        container_endpoint_wf(post.ctn_mp, post.ep_mp),
        thread_caller_callee_wf(post.thrd_mp),
        thread_endpoint_queue_wf(post.thrd_mp, post.ep_mp),
        container_thread_endpoint_wf(post.ctn_mp, post.thrd_mp, post.ep_mp),
{
    reveal(ipc_pci_rendezvous_eof_transition_framing);
    assert(thread_endpoint_ref_counter_wf(post.thrd_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_descriptor_eq(mid.thrd_mp, post.thrd_mp, mid.ep_mp, post.ep_mp); };
    assert({
        &&& container_endpoint_wf(post.ctn_mp, post.ep_mp)
        &&& thread_caller_callee_wf(post.thrd_mp)
    }) by { container_endpoint_wf_preserved_for_endpoint_owner_eq(mid.ctn_mp, post.ctn_mp, mid.ep_mp, post.ep_mp); thread_caller_callee_wf_preserved_for_call_link_eq(mid.thrd_mp, post.thrd_mp); };
    assert(thread_endpoint_queue_wf(post.thrd_mp, post.ep_mp)) by { seq_skip_one_implies_contains_and_index_shift::<RwLockThreadPtr>(); reveal(endpoint_perms_wf); reveal(LinkedList::wf_value_list); reveal(LinkedList::value_list_unique); reveal(thread_endpoint_queue_wf); };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thrd_mp, post.ep_mp)) by {
        reveal(thread_endpoint_ref_counter_wf); container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(mid.ctn_mp, post.ctn_mp, mid.thrd_mp, post.thrd_mp, mid.ep_mp, post.ep_mp);
    };
}

proof fn ipc_pci_rendezvous_eof_process_management_inv(
    pre: KernelK, mid: KernelK, post: KernelK, current_thrd_ptr: RwLockThreadPtr, peer_thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr,
    peer_sched_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, sender_proc: RwLockProcessPtr, receiver_proc: RwLockProcessPtr, sender_pt: RwLockPageTableRoot,
    receiver_pt: RwLockPageTableRoot, bdf: PciBdf, transferred: bool, peer_result: RetValueType, thread_id: LockThreadId, iommu_table: Option<RwLockPageTableRoot>,
    anchor: Option<PciBdf>,
)
    requires
        mid.inv(),
        index_valid(NUM_CPUS, wake_cpu),
        mid.thrd_mp.dom().contains(peer_thrd_ptr),
        mid.ep_mp.dom().contains(ep_ptr),
        mid.sched_mp.dom().contains(peer_sched_ptr),
        mid.ctn_mp.spec_index(mid.thrd_mp.spec_index(peer_thrd_ptr).view().owning_container).view_rodata().view().scheduler == peer_sched_ptr,
        mid.thrd_mp.spec_index(peer_thrd_ptr).view().state.is_endpoint_waiting(),
        mid.thrd_mp.spec_index(peer_thrd_ptr).view().blocking_endpoint_ptr == Some(ep_ptr),
        mid.ep_mp.spec_index(ep_ptr).view().queue.view().len() > 0,
        mid.ep_mp.spec_index(ep_ptr).view().queue.view().spec_index(0) == peer_thrd_ptr,
        !mid.sched_mp.spec_index(peer_sched_ptr).shards.spec_index(wake_cpu).view().view().queue.dom().contains(mid.thrd_mp.spec_index(peer_thrd_ptr).view().scheduler_linkedlist_node.addr()),
        ipc_pci_rendezvous_eof_transition_framing(pre, mid, post, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, sender_proc, receiver_proc, sender_pt, receiver_pt, bdf, transferred, peer_result, thread_id, iommu_table, anchor),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(ipc_pci_rendezvous_eof_transition_framing);
    ipc_pci_rendezvous_eof_endpoint_wf(pre, mid, post, current_thrd_ptr, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, sender_proc, receiver_proc, sender_pt, receiver_pt, bdf, transferred, peer_result, thread_id, iommu_table, anchor);
    assert(post.process_management_inv()) by {
        assert(thread_dangling_chain_end_wf(post.thrd_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(mid.thrd_mp, post.thrd_mp); };
        assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
        assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { process_rodata_unchanged_implies_container_process_wf_preserved_forall(); };
        assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { per_container_process_tree_wf_preserved_for_tree_fields_eq(post.ctn_mp, mid.prc_mp, post.prc_mp); };
        assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
        assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
        assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
        assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); };
        assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { process_pagetable_fields_unchanged_implies_process_cpu_wf_preserved_forall(); };
        assert({
            &&& container_scheduler_wf(post.ctn_mp, post.sched_mp)
            &&& container_thread_wf(post.ctn_mp, post.thrd_mp)
            &&& process_thread_wf(post.prc_mp, post.thrd_mp)
        }) by { reveal(container_scheduler_wf); reveal(container_thread_wf); reveal(process_thread_wf); };
        assert(thread_cpu_wf(post.thrd_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_running_thread_eq(mid.thrd_mp, post.thrd_mp, mid.cpu_arr, post.cpu_arr); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thrd_mp, post.sched_mp)) by {
            seq_push_implies_contains::<RwLockThreadPtr>();
            reveal(scheduler_perms_wf); reveal(LinkedList::wf_map); reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
        };
    };
}

/// The container, process, and thread quota folds close after the transition.
proof fn ipc_pci_rendezvous_eof_quota_wf(
    pre: KernelK, mid: KernelK, post: KernelK, current_thrd_ptr: RwLockThreadPtr, peer_thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr,
    peer_sched_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, sender_proc: RwLockProcessPtr, receiver_proc: RwLockProcessPtr, sender_pt: RwLockPageTableRoot,
    receiver_pt: RwLockPageTableRoot, bdf: PciBdf, transferred: bool, peer_result: RetValueType, thread_id: LockThreadId, iommu_table: Option<RwLockPageTableRoot>,
    anchor: Option<PciBdf>,
)
    requires
        mid.inv(),
        ipc_pci_rendezvous_eof_transition_framing(pre, mid, post, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, sender_proc, receiver_proc, sender_pt, receiver_pt, bdf, transferred, peer_result, thread_id, iommu_table, anchor),
        post.subsystems_inv(),
    ensures
        container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp),
        container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_2m_mp),
        container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_1g_mp),
{
    reveal(ipc_pci_rendezvous_eof_transition_framing);
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp)) by {
        container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(post.ctn_mp, mid.prc_mp, mid.thrd_mp, post.thrd_mp, post.allc_4k_mp);
        container_process_allocator_quota_4k_wf_preserved_for_process_4k_fields(post.ctn_mp, post.thrd_mp, post.allc_4k_mp, mid.prc_mp, post.prc_mp);
        reveal(container_thread_wf); reveal(container_process_wf);
        unchanged_members_implies_process_effective_quota_4k_fold_sum_eq_forall();
        unchanged_members_implies_thread_effective_quota_4k_fold_sum_eq_forall();
        unchanged_thread_pending_4k_implies_per_container_pending_4k_fold_sums_eq_forall(post.ctn_mp, mid.thrd_mp, post.thrd_mp);
    };
    assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_2m_mp)) by {
        container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, mid.prc_mp, mid.thrd_mp, post.thrd_mp, post.allc_2m_mp);
        container_process_allocator_quota_2m_wf_preserved_for_process_2m_fields(post.ctn_mp, post.thrd_mp, post.allc_2m_mp, mid.prc_mp, post.prc_mp);
        reveal(container_thread_wf); reveal(container_process_wf);
        unchanged_members_implies_process_effective_quota_2m_fold_sum_eq_forall();
        unchanged_members_implies_thread_effective_quota_2m_fold_sum_eq_forall();
        unchanged_thread_pending_2m_implies_per_container_pending_2m_fold_sums_eq_forall(post.ctn_mp, mid.thrd_mp, post.thrd_mp);
    };
    assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_1g_mp)) by {
        reveal(container_process_allocator_quota_1g_wf); reveal(container_thread_wf); reveal(container_process_wf);
        unchanged_members_implies_process_effective_quota_1g_fold_sum_eq_forall();
        unchanged_members_implies_thread_effective_quota_1g_fold_sum_eq_forall();
        unchanged_thread_pending_1g_implies_per_container_pending_1g_fold_sums_eq_forall(post.ctn_mp, mid.thrd_mp, post.thrd_mp);
    };
}

/// The page records of schedulers, threads, endpoints, and staged pages close after the transfer.
proof fn ipc_pci_rendezvous_eof_object_pages_wf(
    pre: KernelK, mid: KernelK, post: KernelK, current_thrd_ptr: RwLockThreadPtr, peer_thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr,
    peer_sched_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, sender_proc: RwLockProcessPtr, receiver_proc: RwLockProcessPtr, sender_pt: RwLockPageTableRoot,
    receiver_pt: RwLockPageTableRoot, bdf: PciBdf, transferred: bool, peer_result: RetValueType, thread_id: LockThreadId, iommu_table: Option<RwLockPageTableRoot>,
    anchor: Option<PciBdf>,
)
    requires
        mid.inv(),
        ipc_pci_rendezvous_eof_transition_framing(pre, mid, post, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, sender_proc, receiver_proc, sender_pt, receiver_pt, bdf, transferred, peer_result, thread_id, iommu_table, anchor),
        post.subsystems_inv(),
        iommu_table_perms_wf(post.it_mp),
    ensures
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        thread_pages_wf(post.thrd_mp, post.pg_arr),
        page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
        thread_staged_4k_pages_wf(post.thrd_mp, post.pg_arr),
        thread_staged_2m_pages_wf(post.thrd_mp, post.pg_arr),
        thread_staged_1g_pages_wf(post.thrd_mp, post.pg_arr),
{
    reveal(ipc_pci_rendezvous_eof_transition_framing);
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(mid.sched_mp, post.sched_mp, mid.pg_arr, post.pg_arr); };
    assert(thread_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(mid.thrd_mp, post.thrd_mp, mid.pg_arr, post.pg_arr); };
    assert(page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr)) by { reveal(page_object_owner_wf); reveal(container_owned_pages_wf); };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(mid.ep_mp, post.ep_mp, mid.pg_arr, post.pg_arr); };
    assert(thread_staged_4k_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_staged_4k_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(mid.thrd_mp, post.thrd_mp, mid.pg_arr, post.pg_arr); };
    assert(thread_staged_2m_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_staged_2m_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(mid.thrd_mp, post.thrd_mp, mid.pg_arr, post.pg_arr); };
    assert(thread_staged_1g_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_staged_1g_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(mid.thrd_mp, post.thrd_mp, mid.pg_arr, post.pg_arr); };
}

proof fn ipc_pci_rendezvous_eof_memory_management_inv(
    pre: KernelK, mid: KernelK, post: KernelK, current_thrd_ptr: RwLockThreadPtr, peer_thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr,
    peer_sched_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, sender_proc: RwLockProcessPtr, receiver_proc: RwLockProcessPtr, sender_pt: RwLockPageTableRoot,
    receiver_pt: RwLockPageTableRoot, bdf: PciBdf, transferred: bool, peer_result: RetValueType, thread_id: LockThreadId, iommu_table: Option<RwLockPageTableRoot>,
    anchor: Option<PciBdf>,
)
    requires
        mid.inv(),
        ipc_pci_rendezvous_eof_transition_framing(pre, mid, post, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, sender_proc, receiver_proc, sender_pt, receiver_pt, bdf, transferred, peer_result, thread_id, iommu_table, anchor),
        post.subsystems_inv(),
        iommu_table_perms_wf(post.it_mp),
    ensures post.memory_management_inv(),
{
    reveal(ipc_pci_rendezvous_eof_transition_framing);
    ipc_pci_rendezvous_eof_quota_wf(pre, mid, post, current_thrd_ptr, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, sender_proc, receiver_proc, sender_pt, receiver_pt, bdf, transferred, peer_result, thread_id, iommu_table, anchor);
    ipc_pci_rendezvous_eof_object_pages_wf(pre, mid, post, current_thrd_ptr, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, sender_proc, receiver_proc, sender_pt, receiver_pt, bdf,
        transferred, peer_result, thread_id, iommu_table, anchor);
    assert(post.memory_management_inv()) by {
        assert(pagetable_pci_mappings_wf(post.pci_bars.view(), post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_pci_mappings_wf); };
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); };
        assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { reveal(iommu_table_pages_wf); };
        assert(process_pages_wf(post.prc_mp, post.pg_arr)) by { process_domain_unchanged_implies_process_pages_wf_preserved_forall(); };
        assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(mid, post); };
        assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { process_pagetable_fields_unchanged_implies_process_pagetable_wf_preserved_forall(); };
        assert(process_iommu_table_wf(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_wf); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_iommu_table_wf); };
        assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); reveal(process_pagetable_wf); };
    };
}

/// The rendezvous closes every invariant: the PCI part already kept them at `mid`, and `mid` to `post` only dequeues and
/// schedules the endpoint waiter.
pub(super) proof fn ipc_pci_rendezvous_eof(
    pre: KernelK, mid: KernelK, post: KernelK, current_thrd_ptr: RwLockThreadPtr, peer_thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr,
    peer_sched_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, sender_proc: RwLockProcessPtr, receiver_proc: RwLockProcessPtr, sender_pt: RwLockPageTableRoot,
    receiver_pt: RwLockPageTableRoot, bdf: PciBdf, transferred: bool, peer_result: RetValueType, thread_id: LockThreadId, iommu_table: Option<RwLockPageTableRoot>,
    anchor: Option<PciBdf>,
)
    requires
        mid.inv(),
        current_thrd_ptr != peer_thrd_ptr,
        index_valid(NUM_CPUS, wake_cpu),
        mid.thrd_mp.dom().contains(current_thrd_ptr),
        mid.thrd_mp.dom().contains(peer_thrd_ptr),
        !thread_is_dangling(mid.thrd_mp.spec_index(current_thrd_ptr)),
        !thread_is_dangling(mid.thrd_mp.spec_index(peer_thrd_ptr)),
        mid.ep_mp.dom().contains(ep_ptr),
        mid.sched_mp.dom().contains(peer_sched_ptr),
        mid.ctn_mp.spec_index(mid.thrd_mp.spec_index(peer_thrd_ptr).view().owning_container).view_rodata().view().scheduler == peer_sched_ptr,
        mid.thrd_mp.spec_index(peer_thrd_ptr).view().state.is_endpoint_waiting(),
        mid.thrd_mp.spec_index(peer_thrd_ptr).view().blocking_endpoint_ptr == Some(ep_ptr),
        mid.ep_mp.spec_index(ep_ptr).view().queue.view().len() > 0,
        mid.ep_mp.spec_index(ep_ptr).view().queue.view().spec_index(0) == peer_thrd_ptr,
        !mid.sched_mp.spec_index(peer_sched_ptr).shards.spec_index(wake_cpu).view().view().queue.dom().contains(mid.thrd_mp.spec_index(peer_thrd_ptr).view().scheduler_linkedlist_node.addr()),
        ipc_pci_rendezvous_eof_transition_framing(pre, mid, post, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, sender_proc, receiver_proc, sender_pt, receiver_pt, bdf, transferred, peer_result, thread_id, iommu_table, anchor),
        post.ep_mp.spec_index(ep_ptr).view().queue.wf(),
        post.sched_mp.perms_wf(),
        post.sched_mp.spec_index(peer_sched_ptr).shards.inv(),
        post.sched_mp.spec_index(peer_sched_ptr).shard(wake_cpu).queue.wf(),
    ensures
        post.inv(),
{
    reveal(ipc_pci_rendezvous_eof_transition_framing);
    assert(post.subsystems_inv()) by {
        assert({
            &&& process_perms_wf(post.prc_mp)
            &&& thread_perms_wf(post.thrd_mp)
            &&& endpoint_perms_wf(post.ep_mp)
            &&& scheduler_perms_wf(post.sched_mp)
        }) by {
            process_thread_wf_thread_at(mid.prc_mp, mid.thrd_mp, current_thrd_ptr); process_thread_wf_thread_at(mid.prc_mp, mid.thrd_mp, peer_thrd_ptr);
            reveal(process_perms_wf); reveal(thread_perms_wf); reveal(endpoint_perms_wf); reveal(scheduler_perms_wf);
            reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
        };
        reveal(KernelK::default_pagetable_wf);
    };
    ipc_pci_rendezvous_eof_memory_management_inv(pre, mid, post, current_thrd_ptr, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, sender_proc, receiver_proc, sender_pt, receiver_pt, bdf,
        transferred, peer_result, thread_id, iommu_table, anchor);
    ipc_pci_rendezvous_eof_process_management_inv(pre, mid, post, current_thrd_ptr, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, sender_proc, receiver_proc, sender_pt, receiver_pt, bdf,
        transferred, peer_result, thread_id, iommu_table, anchor);
    assert(post.inv()) by { reveal(cpu_dirty_map_proc_pcid_match); };
}

/// Every function the sender owns sits in its page table's PCI function array, and an attached one carries the DID of the
/// sender's IOMMU table `table`.
proof fn ipc_pci_rendezvous_eof_sender_functions(pre: KernelK, sender_proc: RwLockProcessPtr, sender_pt: RwLockPageTableRoot, table: RwLockPageTableRoot)
    requires
        pre.inv(),
        pre.prc_mp.dom().contains(sender_proc),
        pre.prc_mp.spec_index(sender_proc).view().pagetable == sender_pt,
        pre.prc_mp.spec_index(sender_proc).view().iommu_table == Some(table),
    ensures
        forall|b: usize, d: usize, f: usize| #![trigger pre.irt.view().owners()[b as int][d as int][f as int]]
            pci_bdf_valid(b, d, f) && pre.irt.view().spec_index_owner(b, d, f) == Some(sender_proc) ==> {
                &&& pre.pt_mp.spec_index(sender_pt).view().higher.pci.view().dom().contains((b, d, f))
                &&& pre.irt.view().spec_index_iommu_root(b, d, f) is Some ==> pre.irt.view().spec_index_iommu_did(b, d, f) == pre.it_mp.spec_index(table).view().did
            },
{ reveal(pci_function_ownership_wf); reveal(iommu_root_table_process_wf); }

/// The PCI part's root-table, IOTLB, and IOMMU-table effects in the form of `kernel_ipc_rendezvous_fields`: the old DID domain is
/// invalidated exactly when `bdf` was attached, the sender table's DID follows `pci_handoff_table_did`, and every table keeps its
/// mappings; an anchor that still carries the sender table's old DID is the sender's.
proof fn ipc_pci_rendezvous_eof_handoff(
    pre: KernelK, mid: KernelK, sender_proc: RwLockProcessPtr, receiver_proc: RwLockProcessPtr, sender_pt: RwLockPageTableRoot, receiver_pt: RwLockPageTableRoot,
    bdf: PciBdf, transferred: bool, thread_id: LockThreadId, iommu_table: Option<RwLockPageTableRoot>, anchor: Option<PciBdf>,
)
    requires
        pre.inv(),
        pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        pre.prc_mp.dom().contains(sender_proc),
        pre.prc_mp.spec_index(sender_proc).view().pagetable == sender_pt,
        transferred ==> pre.pt_mp.spec_index(sender_pt).view().higher.pci.view().dom().contains(bdf),
        ipc_pci_rendezvous_eof_pci_handoff(pre, mid, sender_proc, receiver_proc, sender_pt, receiver_pt, bdf, transferred, thread_id, iommu_table, anchor),
        forall|b: usize, d: usize, f: usize| #![trigger pre.irt.view().spec_index_iommu_did(b, d, f)]
            pci_bdf_valid(b, d, f) ==> (pre.irt.view().spec_index_iommu_did(b, d, f) is Some) == (pre.irt.view().spec_index_iommu_root(b, d, f) is Some),
    ensures
        !transferred ==> mid.it_mp == pre.it_mp && mid.irt.view() == pre.irt.view() && mid.iommu_tlb == pre.iommu_tlb,
        transferred ==> {
            let sender_table = pre.prc_mp.spec_index(sender_proc).view().iommu_table;
            let attached = iommu_roots_attached(pre.irt.view().iommu_roots());
            let old_did = match sender_table { Some(t) => pre.it_mp.spec_index(t).view().did, None => None };
            &&& mid.iommu_tlb.view() == if attached[bdf.0 as int][bdf.1 as int][bdf.2 as int] && old_did is Some { pre.iommu_tlb.view().insert(old_did->Some_0, mid.iommu_tlb.spec_index(old_did->Some_0)) }
                else { pre.iommu_tlb.view() }
            &&& attached[bdf.0 as int][bdf.1 as int][bdf.2 as int] && old_did is Some ==> iommu_tlb_within_may_cache(KernelK { irt: mid.irt, ..pre }, old_did->Some_0, mid.iommu_tlb.spec_index(old_did->Some_0))
            &&& sender_table matches Some(t) ==> pci_handoff_table_did(pre.irt.view().owners(), attached, sender_proc, bdf, old_did, mid.it_mp.spec_index(t).view().did)
            &&& mid.it_mp.dom() == pre.it_mp.dom()
            &&& forall|p: RwLockPageTableRoot| #![trigger mid.it_mp.spec_index(p)] pre.it_mp.dom().contains(p) ==> {
                let before = pre.it_mp.spec_index(p).view();
                let after = mid.it_mp.spec_index(p).view();
                &&& sender_table != Some(p) ==> after.did == before.did
                &&& after.mapping_4k() == before.mapping_4k()
                &&& after.mapping_2m() == before.mapping_2m()
                &&& after.mapping_1g() == before.mapping_1g()
            }
            &&& forall|b: usize, d: usize, f: usize| #![trigger mid.irt.view().spec_index_iommu_root(b, d, f)] pci_bdf_valid(b, d, f)
                ==> (mid.irt.view().spec_index_iommu_root(b, d, f) is Some) == ((b, d, f) != bdf && pre.irt.view().spec_index_iommu_root(b, d, f) is Some)
        },
        iommu_table matches Some(t) ==> {
            let did = pre.it_mp.spec_index(t).view().did;
            let anchor = pci_bdf_of_did(did->Some_0);
            did is Some && mid.irt.view().spec_index_iommu_did(anchor.0, anchor.1, anchor.2) == did ==> mid.irt.view().spec_index_owner(anchor.0, anchor.1, anchor.2) == Some(sender_proc)
        },
{
    reveal(ipc_pci_rendezvous_eof_pci_handoff);
    assert(pci_bdf_of_did(pci_bdf_did(bdf.0, bdf.1, bdf.2)) == bdf) by (nonlinear_arith) requires pci_bdf_valid(bdf.0, bdf.1, bdf.2);
    process_iommu_table_wf_process_at(pre.prc_mp, pre.it_mp, sender_proc);
    process_pagetable_wf_process_at(pre.prc_mp, pre.pt_mp, sender_proc);
    if let Some(t) = iommu_table {
        let od = pre.it_mp.spec_index(t).view().did;
        assert({
            &&& pre.prc_mp.spec_index(sender_proc).view().iommu_table == Some(t)
            &&& pre.it_mp.spec_index(t).view().proc_ptr == sender_proc
            &&& pre.irt.view().spec_index_iommu_did(bdf.0, bdf.1, bdf.2) == od
            &&& od is Some
            &&& vtd_domain_id_valid(od->Some_0)
        }) by {
            pci_function_ownership_wf_pagetable_at(pre.irt.view(), pre.prc_mp, pre.pt_mp, sender_pt, bdf);
            reveal(iommu_root_table_process_wf);
        };
        assert(pci_bdf_valid(pci_bdf_of_did(od->Some_0).0, pci_bdf_of_did(od->Some_0).1, pci_bdf_of_did(od->Some_0).2)
            && pci_bdf_did(pci_bdf_of_did(od->Some_0).0, pci_bdf_of_did(od->Some_0).1, pci_bdf_of_did(od->Some_0).2) == od->Some_0) by (nonlinear_arith) requires vtd_domain_id_valid(od->Some_0);
        iommu_root_table_process_wf_table_at(pre.irt.view(), pre.prc_mp, pre.it_mp, t);
        ipc_pci_rendezvous_eof_sender_functions(pre, sender_proc, sender_pt, t);
        if let Some(a) = anchor {
            assert(pci_bdf_of_did(pci_bdf_did(a.0, a.1, a.2)) == a && vtd_domain_id_valid(pci_bdf_did(a.0, a.1, a.2))) by (nonlinear_arith) requires pci_bdf_valid(a.0, a.1, a.2);
            assert(pre.irt.view().spec_index_owner(a.0, a.1, a.2) == Some(sender_proc)) by { pci_function_ownership_wf_pagetable_at(pre.irt.view(), pre.prc_mp, pre.pt_mp, sender_pt, a); };
            assert(pre.irt.view().spec_index_iommu_root(a.0, a.1, a.2) is Some) by { pre.irt.view().wf_context_entry_at(a.0, a.1, a.2); };
        }
        assert(pci_handoff_table_did(pre.irt.view().owners(), iommu_roots_attached(pre.irt.view().iommu_roots()), sender_proc, bdf, od, mid.it_mp.spec_index(t).view().did));
    } else if transferred {
        assert(pre.irt.view().spec_index_iommu_root(bdf.0, bdf.1, bdf.2) is None) by {
            pci_function_ownership_wf_pagetable_at(pre.irt.view(), pre.prc_mp, pre.pt_mp, sender_pt, bdf);
            reveal(iommu_root_table_process_wf);
        };
    }
}

/// The rendezvous fields of the step, the scheduler-shard push, and the sender-table anchor close for the state `post` reached
/// from `scheduled` by unlocking the two page tables.
pub(super) proof fn ipc_pci_rendezvous_eof_rendezvous_fields(
    pre: KernelK, mid: KernelK, scheduled: KernelK, post: KernelK, current_thrd_ptr: RwLockThreadPtr, peer_thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr,
    peer_sched_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, sender_proc: RwLockProcessPtr, receiver_proc: RwLockProcessPtr, sender_pt: RwLockPageTableRoot,
    receiver_pt: RwLockPageTableRoot, bdf: PciBdf, transferred: bool, peer_result: RetValueType, thread_id: LockThreadId, iommu_table: Option<RwLockPageTableRoot>,
    anchor: Option<PciBdf>, snapshot: KernelK, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, ep_idx: EndpointIdx, waiting_state: ThreadState,
)
    requires
        pre.inv(),
        current_thrd_ptr != peer_thrd_ptr,
        index_valid(NUM_CPUS, wake_cpu),
        pre.thrd_mp.dom().contains(current_thrd_ptr),
        pre.thrd_mp.dom().contains(peer_thrd_ptr),
        pre.ep_mp.dom().contains(ep_ptr),
        pre.sched_mp.dom().contains(peer_sched_ptr),
        pre.ctn_mp.spec_index(pre.thrd_mp.spec_index(peer_thrd_ptr).view().owning_container).view_rodata().view().scheduler == peer_sched_ptr,
        pre.thrd_mp.spec_index(peer_thrd_ptr).view().state.is_endpoint_waiting(),
        pre.thrd_mp.spec_index(peer_thrd_ptr).view().blocking_endpoint_ptr == Some(ep_ptr),
        pre.ep_mp.spec_index(ep_ptr).view().queue.view().len() > 0,
        pre.ep_mp.spec_index(ep_ptr).view().queue.view().spec_index(0) == peer_thrd_ptr,
        pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        pre.prc_mp.dom().contains(sender_proc),
        pre.prc_mp.dom().contains(receiver_proc),
        sender_proc != receiver_proc,
        !pre.prc_mp.spec_index(sender_proc).view().zombie,
        !pre.prc_mp.spec_index(receiver_proc).view().zombie,
        pre.prc_mp.spec_index(sender_proc).view().pagetable == sender_pt,
        pre.prc_mp.spec_index(receiver_proc).view().pagetable == receiver_pt,
        sender_pt != receiver_pt,
        pre.pt_mp.dom().contains(sender_pt),
        pre.pt_mp.dom().contains(receiver_pt),
        pre.pt_mp.spec_index(sender_pt).locking_thread() is None,
        pre.pt_mp.spec_index(receiver_pt).locking_thread() is None,
        transferred ==> pre.pt_mp.spec_index(sender_pt).view().higher.pci.view().dom().contains(bdf),
        !pre.sched_mp.spec_index(peer_sched_ptr).shards.spec_index(wake_cpu).view().view().queue.dom().contains(pre.thrd_mp.spec_index(peer_thrd_ptr).view().scheduler_linkedlist_node.addr()),
        ipc_pci_rendezvous_eof_transition_framing(pre, mid, scheduled, peer_thrd_ptr, ep_ptr, peer_sched_ptr, wake_cpu, sender_proc, receiver_proc, sender_pt, receiver_pt, bdf, transferred, peer_result, thread_id, iommu_table, anchor),
        forall|b: usize, d: usize, f: usize| #![trigger pre.irt.view().spec_index_iommu_did(b, d, f)]
            pci_bdf_valid(b, d, f) ==> (pre.irt.view().spec_index_iommu_did(b, d, f) is Some) == (pre.irt.view().spec_index_iommu_root(b, d, f) is Some),
        scheduled.sched_mp.spec_index(peer_sched_ptr).shards.inv(),
        scheduled.sched_mp.spec_index(peer_sched_ptr).shard(wake_cpu).queue.wf(),
        post == (KernelK { pt_mp: post.pt_mp, ..scheduled }),
        post.pt_mp.dom() == scheduled.pt_mp.dom(),
        forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), p)] scheduled.pt_mp.dom().contains(p)
            ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(scheduled.pt_mp, scheduled.pt_lower.view(), p),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&snapshot, &pre),
        kernel_endpoint_nonlock_fields_unchanged(snapshot.ep_mp, pre.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&snapshot, &pre),
        pre.irt.view().owners() == snapshot.irt.view().owners(),
        pre.irt.view().iommu_roots() == snapshot.irt.view().iommu_roots(),
        pre.cpu_tlb.view() == snapshot.cpu_tlb.view(),
        pre.cpu_tlb.structure_caches() == snapshot.cpu_tlb.structure_caches(),
        pre.iommu_tlb.view() == snapshot.iommu_tlb.view(),
        snapshot.cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        snapshot.thrd_mp.dom().contains(current_thrd_ptr) ==> snapshot.thrd_mp.spec_index(current_thrd_ptr).locking_thread() is None,
        snapshot.ep_mp.dom().contains(ep_ptr) ==> snapshot.ep_mp.spec_index(ep_ptr).locking_thread() is None,
        snapshot.thrd_mp.dom().contains(peer_thrd_ptr) ==> snapshot.thrd_mp.spec_index(peer_thrd_ptr).locking_thread() is None,
        snapshot.pt_mp.dom().contains(sender_pt) ==> snapshot.pt_mp.spec_index(sender_pt).locking_thread() == pre.pt_mp.spec_index(sender_pt).locking_thread(),
        snapshot.pt_mp.dom().contains(receiver_pt) ==> snapshot.pt_mp.spec_index(receiver_pt).locking_thread() == pre.pt_mp.spec_index(receiver_pt).locking_thread(),
        iommu_table matches Some(t) ==> snapshot.it_mp.dom().contains(t) && pre.it_mp.dom().contains(t) ==> snapshot.it_mp.spec_index(t).locking_thread() is None,
        pre.thrd_mp.spec_index(current_thrd_ptr).view().syscall_progress.view() is None,
        index_valid(NUM_CPUS, cpu_id),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thrd_ptr),
        pre.prc_mp.dom().contains(prc_ptr),
        pre.thrd_mp.spec_index(current_thrd_ptr).being_killed() == false,
        pre.thrd_mp.spec_index(current_thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thrd_mp.spec_index(current_thrd_ptr).view().owning_proc == prc_ptr,
        pre.thrd_mp.spec_index(peer_thrd_ptr).being_killed() == false,
        pre.ctn_mp.dom().contains(pre.thrd_mp.spec_index(current_thrd_ptr).view().owning_container),
        pre.ctn_mp.dom().contains(pre.thrd_mp.spec_index(peer_thrd_ptr).view().owning_container),
        wake_cpu == if pre.thrd_mp.spec_index(peer_thrd_ptr).view().owning_container == pre.thrd_mp.spec_index(current_thrd_ptr).view().owning_container { cpu_id }
            else { pre.thrd_mp.spec_index(peer_thrd_ptr).view().last_cpu },
        edp_idx_valid(ep_idx),
        pre.thrd_mp.spec_index(current_thrd_ptr).view().endpoint_descriptors.view()[ep_idx as int] == Some(ep_ptr),
        waiting_state is SENDING || waiting_state is RECEIVING,
        (pre.ep_mp.spec_index(ep_ptr).view().queue_state is SEND) != (waiting_state is SENDING),
    ensures
        kernel_ipc_rendezvous_fields(&snapshot, &post, cpu_id, current_thrd_ptr, ep_ptr, ep_idx, waiting_state, peer_thrd_ptr, peer_result, None, if transferred { Some((bdf, sender_proc, receiver_proc)) } else { None }),
        iommu_table matches Some(t) ==> {
            let did = snapshot.it_mp.spec_index(t).view().did;
            let anchor = pci_bdf_of_did(did->Some_0);
            did is Some && post.irt.view().spec_index_iommu_did(anchor.0, anchor.1, anchor.2) == did ==> post.irt.view().spec_index_owner(anchor.0, anchor.1, anchor.2) == Some(sender_proc)
        },
{
    reveal(ipc_pci_rendezvous_eof_transition_framing); reveal(ipc_pci_rendezvous_eof_pci_handoff); reveal(ipc_pci_rendezvous_eof_pagetable_frame);
    assert(scheduler_shards_of(scheduled.sched_mp.spec_index(peer_sched_ptr))
        =~= scheduler_shards_of(pre.sched_mp.spec_index(peer_sched_ptr)).update(wake_cpu as int, scheduler_shards_of(pre.sched_mp.spec_index(peer_sched_ptr))[wake_cpu as int].push(peer_thrd_ptr))) by {
        reveal(scheduler_shards_of);
    };
    ipc_pci_rendezvous_eof_handoff(pre, mid, sender_proc, receiver_proc, sender_pt, receiver_pt, bdf, transferred, thread_id, iommu_table, anchor);
    if transferred {
        assert_maps_equal!(mid.pt_mp.spec_index(sender_pt).view().higher.pci.mapping_counts(), pre.pt_mp.spec_index(sender_pt).view().higher.pci.mapping_counts().remove(bdf));
        assert_maps_equal!(mid.pt_mp.spec_index(receiver_pt).view().higher.pci.mapping_counts(), pre.pt_mp.spec_index(receiver_pt).view().higher.pci.mapping_counts().insert(bdf, 0));
    }
    assert(transferred ==> {
        let sender_table = snapshot.prc_mp.spec_index(sender_proc).view().iommu_table;
        &&& sender_table == pre.prc_mp.spec_index(sender_proc).view().iommu_table
        &&& (match sender_table { Some(t) => snapshot.it_mp.spec_index(t).view().did, None => None }) == match sender_table { Some(t) => pre.it_mp.spec_index(t).view().did, None => None }
        &&& snapshot.it_mp.dom() == pre.it_mp.dom()
        &&& iommu_table matches Some(t) ==> snapshot.it_mp.spec_index(t).view().did == pre.it_mp.spec_index(t).view().did
    }) by {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
        process_iommu_table_wf_process_at(pre.prc_mp, pre.it_mp, sender_proc);
    };
    assert(snapshot.prc_mp.spec_index(sender_proc).view().pagetable == sender_pt && snapshot.prc_mp.spec_index(receiver_proc).view().pagetable == receiver_pt) by {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
    };
    assert(kernel_ipc_rendezvous_fields(&snapshot, &post, cpu_id, current_thrd_ptr, ep_ptr, ep_idx, waiting_state, peer_thrd_ptr, peer_result, None, if transferred { Some((bdf, sender_proc, receiver_proc)) } else { None })) by {
        running_thread_not_in_endpoint_queue(&pre, ep_ptr, current_thrd_ptr); process_iommu_table_wf_process_at(pre.prc_mp, pre.it_mp, sender_proc);
        reveal(kernel_ipc_rendezvous_fields); reveal(container_scheduler_wf);
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged);
        reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
        reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged);
    };
}

/// The old DID domain that the detach invalidated stays within what the IOMMU may cache after the function is handed over:
/// the hand-over changes only the owner of the detached function, whose context entry carries no DID.
pub(super) proof fn ipc_pci_transfer_eof_within_may_cache(pre: KernelK, locked: KernelK, detached: KernelK, post: KernelK, bdf: PciBdf, table: RwLockPageTableRoot, did: VtdDomainId, tlb: SingleTLB)
    requires
        pre.inv(),
        pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        pre.irt.view().spec_index_iommu_root(bdf.0, bdf.1, bdf.2) is Some,
        pre.irt.view().spec_index_iommu_did(bdf.0, bdf.1, bdf.2) == Some(did),
        locked.prc_mp == pre.prc_mp,
        locked.it_mp.unchanged_except(&pre.it_mp, table),
        locked.it_mp.spec_index(table).view() == pre.it_mp.spec_index(table).view(),
        detached.inv(),
        detached.prc_mp == locked.prc_mp,
        detached.it_mp.dom() == locked.it_mp.dom(),
        iommu_tlb_within_may_cache(KernelK { irt: detached.irt, ..locked }, did, tlb),
        detached.irt.view().spec_index_iommu_did(bdf.0, bdf.1, bdf.2) is None,
        forall|b: usize, d: usize, f: usize| #![trigger post.irt.view().spec_index_iommu_did(b, d, f)] #![trigger post.irt.view().spec_index_owner(b, d, f)]
            pci_bdf_valid(b, d, f) ==> post.irt.view().spec_index_iommu_did(b, d, f) == detached.irt.view().spec_index_iommu_did(b, d, f)
                && ((b, d, f) != bdf ==> post.irt.view().spec_index_owner(b, d, f) == detached.irt.view().spec_index_owner(b, d, f)),
    ensures
        iommu_tlb_within_may_cache(KernelK { irt: post.irt, ..pre }, did, tlb),
{
    assert(vtd_domain_id_valid(did)) by { pre.irt.view().wf_context_entry_at(bdf.0, bdf.1, bdf.2); };
    let a = pci_bdf_of_did(did);
    assert(pci_bdf_valid(a.0, a.1, a.2)) by (nonlinear_arith) requires vtd_domain_id_valid(did), a == pci_bdf_of_did(did);
    if detached.irt.view().spec_index_iommu_did(a.0, a.1, a.2) == Some(did) {
        let owner = detached.irt.view().spec_index_owner(a.0, a.1, a.2)->Some_0;
        let it = pre.prc_mp.spec_index(owner).view().iommu_table->Some_0;
        assert(pre.it_mp.dom().contains(it)) by { detached.irt.view().wf_context_entry_at(a.0, a.1, a.2); reveal(iommu_root_table_process_wf); };
    }
}

/// The hand-over changed only the PCI function arrays of the sender's and the receiver's page tables: `bdf` left the sender's
/// and entered the receiver's with no BAR mapping.
pub(super) proof fn ipc_pci_transfer_eof_pagetable_frame(pre: KernelK, post: KernelK, sender_pt: RwLockPageTableRoot, receiver_pt: RwLockPageTableRoot, bdf: PciBdf)
    requires
        post.pt_lower == pre.pt_lower,
        post.pt_mp.dom() == pre.pt_mp.dom(),
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)] pre.pt_mp.dom().contains(p) && p != sender_pt && p != receiver_pt ==> post.pt_mp.spec_index(p) == pre.pt_mp.spec_index(p),
        post.pt_mp.spec_index(sender_pt).view().higher == (PageTableHigher { pci: post.pt_mp.spec_index(sender_pt).view().higher.pci, ..pre.pt_mp.spec_index(sender_pt).view().higher }),
        post.pt_mp.spec_index(receiver_pt).view().higher == (PageTableHigher { pci: post.pt_mp.spec_index(receiver_pt).view().higher.pci, ..pre.pt_mp.spec_index(receiver_pt).view().higher }),
        post.pt_mp.spec_index(sender_pt).view().higher.pci.view() == pre.pt_mp.spec_index(sender_pt).view().higher.pci.view().remove(bdf),
        post.pt_mp.spec_index(receiver_pt).view().higher.pci.view() == pre.pt_mp.spec_index(receiver_pt).view().higher.pci.view().insert(bdf, Set::<PciBarMapping>::empty()),
        post.pt_mp.spec_index(sender_pt).being_killed() == pre.pt_mp.spec_index(sender_pt).being_killed(),
        post.pt_mp.spec_index(receiver_pt).being_killed() == pre.pt_mp.spec_index(receiver_pt).being_killed(),
    ensures
        ipc_pci_rendezvous_eof_pagetable_frame(pre, post, sender_pt, receiver_pt, bdf, true),
{
    reveal(ipc_pci_rendezvous_eof_pagetable_frame);
}
}
