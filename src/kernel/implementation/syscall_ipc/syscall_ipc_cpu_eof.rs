use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_cpu_spec::ipc_cpu_rendezvous_transition;
use super::syscall_ipc_dispatch::running_thread_not_in_endpoint_queue;

verus! {
#[verifier::spinoff_prover]
proof fn ipc_cpu_rendezvous_eof_process_management_inv(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr, peer_scheduler_ptr: RwLockSchedulerPtr,
    source_container: RwLockContainerPtr, target_container: RwLockContainerPtr,
    source_cpu_set: RwLockCpuSetPtr, target_cpu_set: RwLockCpuSetPtr,
    transfer_cpu_id: CpuId, transferred: bool, peer_result: RetValueType, thread_id: LockThreadId,
)
    requires
        ipc_cpu_rendezvous_transition(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, source_container, target_container, source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(ipc_cpu_rendezvous_transition);
    assert(post.process_management_inv()) by {
        assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
        assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); reveal(container_cpu_set_wf); reveal(cpu_array_wf); };
        assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); reveal(cpu_array_wf); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); };
        assert({
            &&& container_endpoint_wf(post.ctn_mp, post.ep_mp)
            &&& thread_caller_callee_wf(post.thr_mp)
        }) by { reveal(container_endpoint_wf); reveal(thread_caller_callee_wf); };
        assert({
            &&& container_scheduler_wf(post.ctn_mp, post.sched_mp)
            &&& container_thread_wf(post.ctn_mp, post.thr_mp)
            &&& process_thread_wf(post.prc_mp, post.thr_mp)
        }) by { reveal(container_scheduler_wf); reveal(container_thread_wf); reveal(process_thread_wf); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { reveal(thread_cpu_wf); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { seq_skip_lemma::<RwLockThreadPtr>(); reveal(endpoint_perms_wf); reveal(LinkedList::wf_value_list); reveal(LinkedList::value_list_unique); reveal(thread_endpoint_queue_wf); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); reveal(container_thread_endpoint_wf); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by {
            seq_push_lemma::<RwLockThreadPtr>();
            reveal(scheduler_perms_wf); reveal(LinkedList::wf_map); reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
        };
    };
}

proof fn ipc_cpu_rendezvous_eof_memory_management_inv(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr, peer_scheduler_ptr: RwLockSchedulerPtr,
    source_container: RwLockContainerPtr, target_container: RwLockContainerPtr,
    source_cpu_set: RwLockCpuSetPtr, target_cpu_set: RwLockCpuSetPtr,
    transfer_cpu_id: CpuId, transferred: bool, peer_result: RetValueType, thread_id: LockThreadId,
)
    requires
        ipc_cpu_rendezvous_transition(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, source_container, target_container, source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id),
        post.subsystems_inv(),
    ensures post.memory_management_inv(),
{
    reveal(ipc_cpu_rendezvous_transition);
    assert(post.memory_management_inv()) by {
        assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
        assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { reveal(scheduler_pages_wf); };
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_pages_wf); };
        assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { reveal(endpoint_pages_wf); };
        assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_4k_wf); };
        assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_2m_wf); };
        assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_1g_wf); };
        assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by {
            reveal(container_process_allocator_quota_4k_wf); reveal(container_thread_wf);
            lemma_thread_effective_quota_4k_fold_sum_eq_forall();
            lemma_thread_pending_4k_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp);
        };
        assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp)) by {
            reveal(container_process_allocator_quota_2m_wf); reveal(container_thread_wf);
            lemma_thread_effective_quota_2m_fold_sum_eq_forall();
            lemma_thread_pending_2m_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp);
        };
        assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp)) by {
            reveal(container_process_allocator_quota_1g_wf); reveal(container_thread_wf);
            lemma_thread_effective_quota_1g_fold_sum_eq_forall();
            lemma_thread_pending_1g_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp);
        };
    };
}

pub(super) proof fn ipc_cpu_rendezvous_eof(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr, peer_scheduler_ptr: RwLockSchedulerPtr,
    source_container: RwLockContainerPtr, target_container: RwLockContainerPtr,
    source_cpu_set: RwLockCpuSetPtr, target_cpu_set: RwLockCpuSetPtr,
    transfer_cpu_id: CpuId, transferred: bool, peer_result: RetValueType, thread_id: LockThreadId, snapshot: KernelK, cpu_id: CpuId,
    process_ptr: RwLockProcessPtr, endpoint_index: EndpointIdx, waiting_state: ThreadState, cpu_transfer: Option<(CpuId, RwLockThreadPtr)>,
)
    requires
        ipc_cpu_rendezvous_transition(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, source_container, target_container, source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id),
        post.cpu_arr.inv(),
        post.cpu_set_mp.spec_index(source_cpu_set).view().owned_cpus.wf(),
        post.cpu_set_mp.spec_index(target_cpu_set).view().owned_cpus.wf(),
        post.ep_mp.spec_index(endpoint_ptr).view().queue.wf(),
        post.sched_mp.spec_index(peer_scheduler_ptr).view().queue.wf(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&snapshot, &pre),
        kernel_endpoint_nonlock_fields_unchanged(snapshot.ep_mp, pre.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&snapshot, &pre),
        pre.irt.owners() == snapshot.irt.owners(),
        pre.irt.iommu_roots() == snapshot.irt.iommu_roots(),
        pre.cpu_tlb.view() == snapshot.cpu_tlb.view(),
        pre.iommu_tlb.view() == snapshot.iommu_tlb.view(),
        index_valid(NUM_CPUS, cpu_id),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        pre.prc_mp.dom().contains(process_ptr),
        pre.prc_mp.spec_index(process_ptr).being_killed() == false,
        pre.thr_mp.spec_index(current_thread_ptr).being_killed() == false,
        pre.thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
        pre.thr_mp.spec_index(peer_thread_ptr).being_killed() == false,
        pre.ctn_mp.dom().contains(pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container),
        edp_idx_valid(endpoint_index),
        pre.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int] == Some(endpoint_ptr),
        waiting_state is SENDING || waiting_state is RECEIVING,
        (pre.ep_mp.spec_index(endpoint_ptr).view().queue_state is SEND) != (waiting_state is SENDING),
        (cpu_transfer is Some) == transferred,
        cpu_transfer is Some ==> {
            &&& cpu_transfer.unwrap().0 == transfer_cpu_id
            &&& pre.thr_mp.dom().contains(cpu_transfer.unwrap().1)
            &&& pre.thr_mp.spec_index(cpu_transfer.unwrap().1).view().owning_container == target_container
        },
    ensures
        post.inv(),
        kernel_ipc_rendezvous_fields(
            &snapshot, &post, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer,
        ),
{
    reveal(ipc_cpu_rendezvous_transition);
    assert(post.subsystems_inv()) by {
        assert({
            &&& thread_perms_wf(post.thr_mp)
            &&& endpoint_perms_wf(post.ep_mp)
            &&& scheduler_perms_wf(post.sched_mp)
        }) by { reveal(thread_perms_wf); reveal(endpoint_perms_wf); reveal(scheduler_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); };
        reveal(cpu_set_perms_wf); reveal(cpu_array_wf); reveal(cpu_published_wf); reveal(KernelK::default_pagetable_wf);
    };
    ipc_cpu_rendezvous_eof_memory_management_inv(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, source_container, target_container, source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id);
    ipc_cpu_rendezvous_eof_process_management_inv(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, source_container, target_container, source_cpu_set, target_cpu_set, transfer_cpu_id, transferred, peer_result, thread_id);
    assert(post.inv()) by { reveal(cpu_array_wf); reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(tlb_wf_spec); };
    assert(kernel_ipc_rendezvous_fields(
        &snapshot, &post, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer,
    )) by {
        running_thread_not_in_endpoint_queue(&pre, endpoint_ptr, current_thread_ptr);
        reveal(kernel_ipc_rendezvous_fields); reveal(container_scheduler_wf);
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
        reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
        reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged);
    };
}
}
