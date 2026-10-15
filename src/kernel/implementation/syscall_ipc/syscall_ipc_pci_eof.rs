use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_pci_spec::ipc_pci_rendezvous_transition;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_dispatch::running_thread_not_in_endpoint_queue;

verus! {
#[verifier::spinoff_prover]
proof fn ipc_pci_rendezvous_eof_process_management_inv(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, sender_proc: RwLockProcessPtr, receiver_proc: RwLockProcessPtr, bdf: PciBdf,
    transferred: bool, peer_result: RetValueType, thread_id: LockThreadId,
)
    requires
        ipc_pci_rendezvous_transition(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred, peer_result, thread_id),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(ipc_pci_rendezvous_transition);
    assert(post.process_management_inv()) by {
        assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { lemma_container_process_wf_preserved_for_process_rodata_forall(); };
        assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { per_container_process_tree_wf_preserved_for_tree_fields_eq(post.ctn_mp, pre.prc_mp, post.prc_mp); };
        assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); };
        assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { lemma_process_cpu_wf_preserved_for_process_pagetable_fields_forall(); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_descriptor_eq(pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
        assert({
            &&& container_endpoint_wf(post.ctn_mp, post.ep_mp)
            &&& thread_caller_callee_wf(post.thr_mp)
        }) by { reveal(container_endpoint_wf); reveal(thread_caller_callee_wf); };
        assert({
            &&& container_scheduler_wf(post.ctn_mp, post.sched_mp)
            &&& container_thread_wf(post.ctn_mp, post.thr_mp)
            &&& process_thread_wf(post.prc_mp, post.thr_mp)
        }) by { reveal(container_scheduler_wf); reveal(container_thread_wf); reveal(process_thread_wf); reveal(process_empty_lists_wlocked); };
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
    transferred: bool, peer_result: RetValueType, thread_id: LockThreadId,
)
    requires
        ipc_pci_rendezvous_transition(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred, peer_result, thread_id),
        post.subsystems_inv(),
    ensures post.memory_management_inv(),
{
    reveal(ipc_pci_rendezvous_transition);
    assert(post.memory_management_inv()) by {
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); };
        assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { lemma_process_pages_wf_preserved_for_process_domain_eq_forall(); };
        assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { lemma_process_pagetable_match_preserved_for_process_pagetable_fields_forall(); };
        assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { lemma_process_iommu_table_match_preserved_for_process_iommu_table_fields_forall(); };
        assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
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

/// A handed-over function keeps a unique owner in the receiver's reverse set,
/// has no translation, and has an empty IOTLB domain; every other slot is unchanged.
proof fn ipc_pci_rendezvous_eof_iommu_inv(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, sender_proc: RwLockProcessPtr, receiver_proc: RwLockProcessPtr, bdf: PciBdf,
    transferred: bool, peer_result: RetValueType, thread_id: LockThreadId,
)
    requires
        ipc_pci_rendezvous_transition(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred, peer_result, thread_id),
        post.irt.view().wf(),
        post.iommu_tlb.inv(),
    ensures
        iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp),
        process_pci_function_ownership_wf(post.irt.view(), post.prc_mp),
        iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp),
        iommu_table_lock_wf(post.irt.view(), post.prc_mp, post.it_mp),
{
    reveal(ipc_pci_rendezvous_transition);
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf_spec); reveal(iommu_root_table_process_wf); };
    assert(iommu_table_lock_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_table_lock_wf); };
}

pub(super) proof fn ipc_pci_rendezvous_eof(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, sender_proc: RwLockProcessPtr, receiver_proc: RwLockProcessPtr, bdf: PciBdf,
    transferred: bool, peer_result: RetValueType, thread_id: LockThreadId, snapshot: KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, endpoint_index: EndpointIdx,
    waiting_state: ThreadState,
)
    requires
        ipc_pci_rendezvous_transition(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred, peer_result, thread_id),
        post.irt.inv(),
        post.iommu_tlb.inv(),
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
    reveal(ipc_pci_rendezvous_transition);
    assert(post.subsystems_inv()) by {
        assert({
            &&& process_perms_wf(post.prc_mp)
            &&& thread_perms_wf(post.thr_mp)
            &&& endpoint_perms_wf(post.ep_mp)
            &&& scheduler_perms_wf(post.sched_mp)
        }) by {
            reveal(process_perms_wf); reveal(thread_perms_wf); reveal(endpoint_perms_wf); reveal(scheduler_perms_wf);
            reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
        };
        reveal(KernelK::default_pagetable_wf);
    };
    ipc_pci_rendezvous_eof_memory_management_inv(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred, peer_result, thread_id);
    ipc_pci_rendezvous_eof_process_management_inv(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred, peer_result, thread_id);
    ipc_pci_rendezvous_eof_iommu_inv(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, sender_proc, receiver_proc, bdf, transferred, peer_result, thread_id);
    assert(post.inv()) by { reveal(cpu_dirty_map_proc_pcid_match); };
    assert(scheduler_shards_of(post.sched_mp.spec_index(peer_scheduler_ptr)) =~= scheduler_shards_of(pre.sched_mp.spec_index(peer_scheduler_ptr)).update(wake_cpu as int, scheduler_shards_of(pre.sched_mp.spec_index(peer_scheduler_ptr))[wake_cpu as int].push(peer_thread_ptr))) by {
        reveal(scheduler_shards_of);
    };
    assert(kernel_ipc_rendezvous_fields(&snapshot, &post, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, None, if transferred { Some((bdf, sender_proc, receiver_proc)) } else { None })) by {
        running_thread_not_in_endpoint_queue(&pre, endpoint_ptr, current_thread_ptr);
        reveal(kernel_ipc_rendezvous_fields); reveal(container_scheduler_wf);
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
        reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
        reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged);
    };
}
}
