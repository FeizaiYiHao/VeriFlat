use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_pci_spec::ipc_pci_rendezvous_eof_transition_framing;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_dispatch::running_thread_not_in_endpoint_queue;

verus! {

#[verifier::spinoff_prover]
proof fn ipc_pci_rendezvous_eof_process_management_inv(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, sender_proc: RwLockProcessPtr, receiver_proc: RwLockProcessPtr, bdf: PciBdf,
    transferred: bool, peer_result: RetValueType, thread_id: LockThreadId, iommu_table: Option<RwLockPageTableRoot>, anchor: Option<PciBdf>,
)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, wake_cpu),
        pre.thr_mp.dom().contains(peer_thread_ptr),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.sched_mp.dom().contains(peer_scheduler_ptr),
        pre.ctn_mp.spec_index(pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container).view_rodata().view().scheduler == peer_scheduler_ptr,
        pre.thr_mp.spec_index(peer_thread_ptr).view().state.is_endpoint_waiting(),
        pre.thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() > 0,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr,
        pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        pre.prc_mp.dom().contains(sender_proc),
        pre.prc_mp.dom().contains(receiver_proc),
        sender_proc != receiver_proc,
        !pre.prc_mp.spec_index(sender_proc).view().zombie,
        !pre.prc_mp.spec_index(receiver_proc).view().zombie,
        transferred ==> pre.irt.view().spec_index_owner(bdf.0, bdf.1, bdf.2) == sender_proc,
        !pre.sched_mp.spec_index(peer_scheduler_ptr).shards.spec_index(wake_cpu).view().view().queue.dom().contains(pre.thr_mp.spec_index(peer_thread_ptr).view().scheduler_linkedlist_node.addr()),
        ipc_pci_rendezvous_eof_transition_framing(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred, peer_result, thread_id, iommu_table, anchor),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(ipc_pci_rendezvous_eof_transition_framing);
    assert(post.process_management_inv()) by {
        assert(thread_dangling_chain_end_wf(post.thr_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thr_mp, post.thr_mp); };
        assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
        assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { lemma_container_process_wf_preserved_for_process_rodata_forall(); };
        assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { per_container_process_tree_wf_preserved_for_tree_fields_eq(post.ctn_mp, pre.prc_mp, post.prc_mp); };
        assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
        assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
        assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
        assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); };
        assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { lemma_process_cpu_wf_preserved_for_process_pagetable_fields_forall(); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_descriptor_eq(pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
        assert({
            &&& container_endpoint_wf(post.ctn_mp, post.ep_mp)
            &&& thread_caller_callee_wf(post.thr_mp)
        }) by { container_endpoint_wf_preserved_for_endpoint_owner_eq(pre.ctn_mp, post.ctn_mp, pre.ep_mp, post.ep_mp); thread_caller_callee_wf_preserved_for_call_link_eq(pre.thr_mp, post.thr_mp); };
        assert({
            &&& container_scheduler_wf(post.ctn_mp, post.sched_mp)
            &&& container_thread_wf(post.ctn_mp, post.thr_mp)
            &&& process_thread_wf(post.prc_mp, post.thr_mp)
        }) by { reveal(container_scheduler_wf); reveal(container_thread_wf); reveal(process_thread_wf); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_running_thread_eq(pre.thr_mp, post.thr_mp, pre.cpu_arr, post.cpu_arr); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { seq_skip_lemma::<RwLockThreadPtr>(); reveal(endpoint_perms_wf); reveal(LinkedList::wf_value_list); reveal(LinkedList::value_list_unique); reveal(thread_endpoint_queue_wf); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by {
            seq_push_lemma::<RwLockThreadPtr>();
            reveal(scheduler_perms_wf); reveal(LinkedList::wf_map); reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
        };
    };
}

proof fn ipc_pci_rendezvous_eof_memory_management_inv(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, sender_proc: RwLockProcessPtr, receiver_proc: RwLockProcessPtr, bdf: PciBdf,
    transferred: bool, peer_result: RetValueType, thread_id: LockThreadId, iommu_table: Option<RwLockPageTableRoot>, anchor: Option<PciBdf>,
)
    requires
        pre.inv(),
        ipc_pci_rendezvous_eof_transition_framing(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred, peer_result, thread_id, iommu_table, anchor),
        post.subsystems_inv(),
        iommu_table_perms_wf(post.it_mp),
    ensures post.memory_management_inv(),
{
    reveal(ipc_pci_rendezvous_eof_transition_framing);
    assert(post.memory_management_inv()) by {
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); };
        assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { reveal(iommu_table_pages_wf); };
        assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
        assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { lemma_process_pages_wf_preserved_for_process_domain_eq_forall(); };
        assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
        assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { lemma_process_pagetable_match_preserved_for_process_pagetable_fields_forall(); };
        assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_match); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); reveal(process_iommu_table_match); };
        assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
        assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp)) by { reveal(page_object_owner_wf); reveal(container_page_owner_wf); };
        assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
        assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by {
            container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(post.ctn_mp, pre.prc_mp, pre.thr_mp, post.thr_mp, post.allc_4k_mp);
            container_process_allocator_quota_4k_wf_preserved_for_process_4k_fields(post.ctn_mp, post.thr_mp, post.allc_4k_mp, pre.prc_mp, post.prc_mp);
            reveal(container_thread_wf); reveal(container_process_wf);
            lemma_process_effective_quota_4k_fold_sum_eq_forall();
            lemma_thread_effective_quota_4k_fold_sum_eq_forall();
            lemma_thread_pending_4k_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp);
        };
        assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp)) by {
            container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, pre.prc_mp, pre.thr_mp, post.thr_mp, post.allc_2m_mp);
            container_process_allocator_quota_2m_wf_preserved_for_process_2m_fields(post.ctn_mp, post.thr_mp, post.allc_2m_mp, pre.prc_mp, post.prc_mp);
            reveal(container_thread_wf); reveal(container_process_wf);
            lemma_process_effective_quota_2m_fold_sum_eq_forall();
            lemma_thread_effective_quota_2m_fold_sum_eq_forall();
            lemma_thread_pending_2m_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp);
        };
        assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp)) by {
            reveal(container_process_allocator_quota_1g_wf); reveal(container_thread_wf); reveal(container_process_wf);
            lemma_process_effective_quota_1g_fold_sum_eq_forall();
            lemma_thread_effective_quota_1g_fold_sum_eq_forall();
            lemma_thread_pending_1g_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp);
        };
    };
}

/// The sender's write-locked table `iommu_table` is the sender's IOMMU table, and the attached `bdf` carries its DID; an
/// unlocked transfer leaves an absent `bdf`. The candidate DIDs of `bdf`, of the old DID's anchor, and of `anchor` invert.
proof fn ipc_pci_rendezvous_eof_sender_table(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, sender_proc: RwLockProcessPtr, receiver_proc: RwLockProcessPtr, bdf: PciBdf,
    transferred: bool, peer_result: RetValueType, thread_id: LockThreadId, iommu_table: Option<RwLockPageTableRoot>, anchor: Option<PciBdf>,
)
    requires
        pre.inv(),
        pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        pre.prc_mp.dom().contains(sender_proc),
        transferred ==> pre.irt.view().spec_index_owner(bdf.0, bdf.1, bdf.2) == sender_proc,
        ipc_pci_rendezvous_eof_transition_framing(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred, peer_result, thread_id, iommu_table, anchor),
    ensures
        pci_bdf_of_did(pci_bdf_did(bdf.0, bdf.1, bdf.2)) == bdf,
        transferred && iommu_table is None ==> pre.irt.view().spec_index_iommu_root(bdf.0, bdf.1, bdf.2) is None,
        iommu_table matches Some(t) ==> {
            let old_did = pre.irt.view().spec_index_iommu_did(bdf.0, bdf.1, bdf.2);
            &&& transferred
            &&& pre.prc_mp.spec_index(sender_proc).view().iommu_table == Some(t)
            &&& pre.it_mp.dom().contains(t)
            &&& pre.it_mp.spec_index(t).view().proc_ptr == sender_proc
            &&& pre.irt.view().spec_index_iommu_root(bdf.0, bdf.1, bdf.2) == Some(pre.it_mp.spec_index(t).view().cr3)
            &&& old_did is Some
            &&& old_did == pre.it_mp.spec_index(t).view().did
            &&& vtd_domain_id_valid(old_did->Some_0)
            &&& pci_bdf_valid(pci_bdf_of_did(old_did->Some_0).0, pci_bdf_of_did(old_did->Some_0).1, pci_bdf_of_did(old_did->Some_0).2)
            &&& pci_bdf_did(pci_bdf_of_did(old_did->Some_0).0, pci_bdf_of_did(old_did->Some_0).1, pci_bdf_of_did(old_did->Some_0).2) == old_did->Some_0
        },
        anchor matches Some(a) ==> {
            &&& pci_bdf_of_did(pci_bdf_did(a.0, a.1, a.2)) == a
            &&& vtd_domain_id_valid(pci_bdf_did(a.0, a.1, a.2))
            &&& pre.irt.view().spec_index_iommu_root(a.0, a.1, a.2) is Some
        },
{
    reveal(ipc_pci_rendezvous_eof_transition_framing);
    assert(pci_bdf_of_did(pci_bdf_did(bdf.0, bdf.1, bdf.2)) == bdf) by (nonlinear_arith) requires pci_bdf_valid(bdf.0, bdf.1, bdf.2);
    assert(transferred && pre.irt.view().spec_index_iommu_root(bdf.0, bdf.1, bdf.2) is Some ==> pre.prc_mp.spec_index(sender_proc).view_rodata().view().iommu_table_ptr is Some) by {
        process_iommu_table_match_process_at(pre.prc_mp, pre.it_mp, sender_proc); reveal(iommu_root_table_process_wf);
    };
    if let Some(t) = iommu_table {
        assert({
            &&& pre.prc_mp.spec_index(sender_proc).view().iommu_table == Some(t)
            &&& pre.it_mp.dom().contains(t)
            &&& pre.it_mp.spec_index(t).view().proc_ptr == sender_proc
            &&& pre.irt.view().spec_index_iommu_root(bdf.0, bdf.1, bdf.2) == Some(pre.it_mp.spec_index(t).view().cr3)
            &&& pre.irt.view().spec_index_iommu_did(bdf.0, bdf.1, bdf.2) == pre.it_mp.spec_index(t).view().did
            &&& pre.it_mp.spec_index(t).view().did is Some
            &&& vtd_domain_id_valid(pre.it_mp.spec_index(t).view().did->Some_0)
        }) by { process_iommu_table_match_process_at(pre.prc_mp, pre.it_mp, sender_proc); reveal(iommu_root_table_process_wf); };
        let od = pre.it_mp.spec_index(t).view().did->Some_0;
        assert(pci_bdf_valid(pci_bdf_of_did(od).0, pci_bdf_of_did(od).1, pci_bdf_of_did(od).2) && pci_bdf_did(pci_bdf_of_did(od).0, pci_bdf_of_did(od).1, pci_bdf_of_did(od).2) == od)
            by (nonlinear_arith) requires vtd_domain_id_valid(od);
    }
    if let Some(a) = anchor {
        assert(pci_bdf_of_did(pci_bdf_did(a.0, a.1, a.2)) == a && vtd_domain_id_valid(pci_bdf_did(a.0, a.1, a.2))) by (nonlinear_arith) requires pci_bdf_valid(a.0, a.1, a.2);
        assert(pre.irt.view().spec_index_iommu_root(a.0, a.1, a.2) is Some) by { pre.irt.view().context_wf_at(a.0, a.1, a.2); };
    }
}

/// A handed-over function keeps a unique owner in the receiver's reverse set and has no translation; a re-anchored table
/// carries the candidate DID of `anchor`, whose functions now carry it; every other slot is unchanged.
proof fn ipc_pci_rendezvous_eof_iommu_inv(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, sender_proc: RwLockProcessPtr, receiver_proc: RwLockProcessPtr, bdf: PciBdf,
    transferred: bool, peer_result: RetValueType, thread_id: LockThreadId, iommu_table: Option<RwLockPageTableRoot>, anchor: Option<PciBdf>,
)
    requires
        pre.inv(),
        pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        pre.prc_mp.dom().contains(sender_proc),
        pre.prc_mp.dom().contains(receiver_proc),
        sender_proc != receiver_proc,
        !pre.prc_mp.spec_index(sender_proc).view().zombie,
        !pre.prc_mp.spec_index(receiver_proc).view().zombie,
        transferred ==> pre.irt.view().spec_index_owner(bdf.0, bdf.1, bdf.2) == sender_proc,
        ipc_pci_rendezvous_eof_transition_framing(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred, peer_result, thread_id, iommu_table, anchor),
        post.irt.view().wf(),
    ensures
        iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp),
        process_pci_function_ownership_wf(post.irt.view(), post.prc_mp),
{
    reveal(ipc_pci_rendezvous_eof_transition_framing);
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); reveal(process_iommu_table_match); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
}

/// Detaching an attached function empties its old DID domain and drops the context-cache entries of that DID; a re-anchored
/// table moves its remaining functions to the previously inactive, hence empty, candidate domain of `anchor`.
proof fn ipc_pci_rendezvous_eof_iotlb(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, sender_proc: RwLockProcessPtr, receiver_proc: RwLockProcessPtr, bdf: PciBdf,
    transferred: bool, peer_result: RetValueType, thread_id: LockThreadId, iommu_table: Option<RwLockPageTableRoot>, anchor: Option<PciBdf>,
)
    requires
        pre.inv(),
        pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        pre.prc_mp.dom().contains(sender_proc),
        transferred ==> pre.irt.view().spec_index_owner(bdf.0, bdf.1, bdf.2) == sender_proc,
        ipc_pci_rendezvous_eof_transition_framing(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred, peer_result, thread_id, iommu_table, anchor),
        post.iommu_tlb.inv(),
    ensures iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp),
{
    ipc_pci_rendezvous_eof_sender_table(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred, peer_result, thread_id, iommu_table, anchor);
    reveal(ipc_pci_rendezvous_eof_transition_framing);
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf_spec); reveal(iommu_root_table_process_wf); reveal(IommuTLB::inv); };
}

/// The transfer's root-table, IOTLB, and IOMMU-table effects in the form of `kernel_ipc_rendezvous_fields`: the old DID domain
/// is emptied exactly when `bdf` was attached, the sender table's DID follows `pci_handoff_table_did`, and every table keeps its
/// mappings.
proof fn ipc_pci_rendezvous_eof_handoff(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, sender_proc: RwLockProcessPtr, receiver_proc: RwLockProcessPtr, bdf: PciBdf,
    transferred: bool, peer_result: RetValueType, thread_id: LockThreadId, iommu_table: Option<RwLockPageTableRoot>, anchor: Option<PciBdf>,
)
    requires
        pre.inv(),
        pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        pre.prc_mp.dom().contains(sender_proc),
        transferred ==> pre.irt.view().spec_index_owner(bdf.0, bdf.1, bdf.2) == sender_proc,
        ipc_pci_rendezvous_eof_transition_framing(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred, peer_result, thread_id, iommu_table, anchor),
    ensures
        !transferred ==> post.it_mp == pre.it_mp,
        transferred ==> {
            let sender_table = pre.prc_mp.spec_index(sender_proc).view().iommu_table;
            let attached = iommu_roots_attached(pre.irt.view().iommu_roots());
            let old_did = match sender_table { Some(t) => pre.it_mp.spec_index(t).view().did, None => None };
            &&& post.iommu_tlb.view() == if attached[bdf.0 as int][bdf.1 as int][bdf.2 as int] && old_did is Some {
                pre.iommu_tlb.view().insert(old_did->Some_0, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
            } else { pre.iommu_tlb.view() }
            &&& sender_table matches Some(t) ==> pci_handoff_table_did(pre.irt.view().owners(), attached, sender_proc, bdf, old_did, post.it_mp.spec_index(t).view().did)
            &&& post.it_mp.dom() == pre.it_mp.dom()
            &&& forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)] pre.it_mp.dom().contains(p) ==> {
                let before = pre.it_mp.spec_index(p).view();
                let after = post.it_mp.spec_index(p).view();
                &&& sender_table != Some(p) ==> after.did == before.did
                &&& after.mapping_4k() == before.mapping_4k()
                &&& after.mapping_2m() == before.mapping_2m()
                &&& after.mapping_1g() == before.mapping_1g()
            }
        },
        transferred ==> forall|b: usize, d: usize, f: usize| #![trigger post.irt.view().spec_index_iommu_root(b, d, f)] pci_bdf_valid(b, d, f)
            ==> (post.irt.view().spec_index_iommu_root(b, d, f) is Some) == ((b, d, f) != bdf && pre.irt.view().spec_index_iommu_root(b, d, f) is Some),
{
    ipc_pci_rendezvous_eof_sender_table(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred, peer_result, thread_id, iommu_table, anchor);
    reveal(ipc_pci_rendezvous_eof_transition_framing);
    assert(transferred ==> (pre.prc_mp.spec_index(sender_proc).view().iommu_table matches Some(t) ==> pci_handoff_table_did(pre.irt.view().owners(),
        iommu_roots_attached(pre.irt.view().iommu_roots()), sender_proc, bdf, pre.it_mp.spec_index(t).view().did, post.it_mp.spec_index(t).view().did))) by {
        reveal(iommu_root_table_process_wf);
    };
}

pub(super) proof fn ipc_pci_rendezvous_eof(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, sender_proc: RwLockProcessPtr, receiver_proc: RwLockProcessPtr, bdf: PciBdf,
    transferred: bool, peer_result: RetValueType, thread_id: LockThreadId, iommu_table: Option<RwLockPageTableRoot>, anchor: Option<PciBdf>, snapshot: KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, endpoint_index: EndpointIdx,
    waiting_state: ThreadState,
)
    requires
        pre.inv(),
        current_thread_ptr != peer_thread_ptr,
        index_valid(NUM_CPUS, wake_cpu),
        pre.thr_mp.dom().contains(current_thread_ptr),
        pre.thr_mp.dom().contains(peer_thread_ptr),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.sched_mp.dom().contains(peer_scheduler_ptr),
        pre.ctn_mp.spec_index(pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container).view_rodata().view().scheduler == peer_scheduler_ptr,
        pre.thr_mp.spec_index(peer_thread_ptr).view().state.is_endpoint_waiting(),
        pre.thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() > 0,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr,
        pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        pre.prc_mp.dom().contains(sender_proc),
        pre.prc_mp.dom().contains(receiver_proc),
        sender_proc != receiver_proc,
        !pre.prc_mp.spec_index(sender_proc).view().zombie,
        !pre.prc_mp.spec_index(receiver_proc).view().zombie,
        transferred ==> pre.irt.view().spec_index_owner(bdf.0, bdf.1, bdf.2) == sender_proc,
        !pre.sched_mp.spec_index(peer_scheduler_ptr).shards.spec_index(wake_cpu).view().view().queue.dom().contains(pre.thr_mp.spec_index(peer_thread_ptr).view().scheduler_linkedlist_node.addr()),
        ipc_pci_rendezvous_eof_transition_framing(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred, peer_result, thread_id, iommu_table, anchor),
        post.irt.inv(),
        post.iommu_tlb.inv(),
        iommu_table_perms_wf(post.it_mp),
        post.prc_mp.perms_wf(),
        post.ep_mp.spec_index(endpoint_ptr).view().queue.wf(),
        post.sched_mp.perms_wf(),
        post.sched_mp.spec_index(peer_scheduler_ptr).shards.inv(),
        post.sched_mp.spec_index(peer_scheduler_ptr).shard(wake_cpu).queue.wf(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&snapshot, &pre),
        kernel_endpoint_nonlock_fields_unchanged(snapshot.ep_mp, pre.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&snapshot, &pre),
        pre.irt.view().owners() == snapshot.irt.view().owners(),
        pre.irt.view().iommu_roots() == snapshot.irt.view().iommu_roots(),
        pre.cpu_tlb.view() == snapshot.cpu_tlb.view(),
        pre.iommu_tlb.view() == snapshot.iommu_tlb.view(),
        snapshot.cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        snapshot.thr_mp.dom().contains(current_thread_ptr) ==> snapshot.thr_mp.spec_index(current_thread_ptr).locking_thread() is None,
        snapshot.ep_mp.dom().contains(endpoint_ptr) ==> snapshot.ep_mp.spec_index(endpoint_ptr).locking_thread() is None,
        snapshot.thr_mp.dom().contains(peer_thread_ptr) ==> snapshot.thr_mp.spec_index(peer_thread_ptr).locking_thread() is None,
        iommu_table matches Some(t) ==> snapshot.it_mp.dom().contains(t) && pre.it_mp.dom().contains(t) ==> snapshot.it_mp.spec_index(t).locking_thread() is None,
        pre.thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
        index_valid(NUM_CPUS, cpu_id),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        pre.prc_mp.dom().contains(process_ptr),
        pre.thr_mp.spec_index(current_thread_ptr).being_killed() == false,
        pre.thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
        pre.thr_mp.spec_index(peer_thread_ptr).being_killed() == false,
        pre.ctn_mp.dom().contains(pre.thr_mp.spec_index(current_thread_ptr).view().owning_container),
        pre.ctn_mp.dom().contains(pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container),
        wake_cpu == if pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container == pre.thr_mp.spec_index(current_thread_ptr).view().owning_container { cpu_id }
            else { pre.thr_mp.spec_index(peer_thread_ptr).view().last_cpu },
        edp_idx_valid(endpoint_index),
        pre.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int] == Some(endpoint_ptr),
        waiting_state is SENDING || waiting_state is RECEIVING,
        (pre.ep_mp.spec_index(endpoint_ptr).view().queue_state is SEND) != (waiting_state is SENDING),
    ensures
        post.inv(),
        kernel_ipc_rendezvous_fields(&snapshot, &post, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, None, if transferred { Some((bdf, sender_proc, receiver_proc)) } else { None }),
{
    reveal(ipc_pci_rendezvous_eof_transition_framing);
    assert(post.subsystems_inv()) by {
        assert({
            &&& process_perms_wf(post.prc_mp)
            &&& thread_perms_wf(post.thr_mp)
            &&& endpoint_perms_wf(post.ep_mp)
            &&& scheduler_perms_wf(post.sched_mp)
        }) by {
            reveal(process_perms_wf); reveal(thread_perms_wf); reveal(endpoint_perms_wf); reveal(scheduler_perms_wf);
            reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
        };
        reveal(KernelK::default_pagetable_wf);
    };
    ipc_pci_rendezvous_eof_memory_management_inv(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred, peer_result, thread_id, iommu_table, anchor);
    ipc_pci_rendezvous_eof_process_management_inv(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred, peer_result, thread_id, iommu_table, anchor);
    ipc_pci_rendezvous_eof_iommu_inv(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred, peer_result, thread_id, iommu_table, anchor);
    ipc_pci_rendezvous_eof_iotlb(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred, peer_result, thread_id, iommu_table, anchor);
    assert(post.inv()) by { reveal(cpu_dirty_map_proc_pcid_match); };
    assert(scheduler_shards_of(post.sched_mp.spec_index(peer_scheduler_ptr)) =~= scheduler_shards_of(pre.sched_mp.spec_index(peer_scheduler_ptr)).update(wake_cpu as int, scheduler_shards_of(pre.sched_mp.spec_index(peer_scheduler_ptr))[wake_cpu as int].push(peer_thread_ptr))) by {
        reveal(scheduler_shards_of);
    };
    ipc_pci_rendezvous_eof_handoff(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred, peer_result, thread_id, iommu_table, anchor);
    assert(transferred ==> {
        let sender_table = snapshot.prc_mp.spec_index(sender_proc).view().iommu_table;
        &&& sender_table == pre.prc_mp.spec_index(sender_proc).view().iommu_table
        &&& (match sender_table { Some(t) => snapshot.it_mp.spec_index(t).view().did, None => None }) == match sender_table { Some(t) => pre.it_mp.spec_index(t).view().did, None => None }
        &&& snapshot.it_mp.dom() == pre.it_mp.dom()
    }) by {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
        process_iommu_table_match_process_at(pre.prc_mp, pre.it_mp, sender_proc);
    };
    assert(kernel_ipc_rendezvous_fields(&snapshot, &post, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, None, if transferred { Some((bdf, sender_proc, receiver_proc)) } else { None })) by {
        running_thread_not_in_endpoint_queue(&pre, endpoint_ptr, current_thread_ptr); process_iommu_table_match_process_at(pre.prc_mp, pre.it_mp, sender_proc);
        reveal(kernel_ipc_rendezvous_fields); reveal(container_scheduler_wf);
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
        reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
        reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged);
    };
}
}
