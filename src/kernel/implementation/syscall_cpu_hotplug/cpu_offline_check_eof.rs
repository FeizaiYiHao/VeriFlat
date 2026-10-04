use vstd::prelude::*;
use crate::*;
use super::cpu_offline_check_spec::cpu_went_off_transition;

verus! {
proof fn cpu_went_off_eof_container_thread_scheduler(
    pre: KernelK, post: KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr,
    cpu_set_ptr: RwLockCpuSetPtr, flags_ptr: RwLockCpuOfflineFlagsPtr, entry_regs: Registers,
)
    requires
        pre.inv(),
        cpu_went_off_transition(pre, post, cpu_id, container_ptr, scheduler_ptr, cpu_set_ptr, flags_ptr, entry_regs),
        post.subsystems_inv(),
    ensures container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp),
{
    reveal(cpu_went_off_transition);
    assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by {
        let cpu = pre.cpu_arr.spec_index(cpu_id).view().view().view();
        assert(cpu.current_thread is Some ==> pre.thr_mp.spec_index(cpu.current_thread.unwrap()).view().owning_container == cpu.owning_container) by {
            reveal(thread_cpu_wf); reveal(process_thread_wf); reveal(process_cpu_wf);
        };
        assert(pre.sched_mp.spec_index(scheduler_ptr).view().queue.view().no_duplicates()) by { reveal(scheduler_perms_wf); reveal(LinkedList::value_list_unique); reveal(LinkedList::wf_value_list); };
        reveal(container_thread_scheduler_wf); reveal(container_scheduler_wf); reveal(container_thread_wf);
        seq_push_lemma::<RwLockThreadPtr>();
    };
}

#[verifier::spinoff_prover]
proof fn cpu_went_off_eof_process_management_inv(
    pre: KernelK, post: KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr,
    cpu_set_ptr: RwLockCpuSetPtr, flags_ptr: RwLockCpuOfflineFlagsPtr, entry_regs: Registers,
)
    requires
        pre.inv(),
        cpu_went_off_transition(pre, post, cpu_id, container_ptr, scheduler_ptr, cpu_set_ptr, flags_ptr, entry_regs),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(cpu_went_off_transition);
    assert(post.process_management_inv()) by {
        cpu_went_off_eof_container_thread_scheduler(pre, post, cpu_id, container_ptr, scheduler_ptr, cpu_set_ptr, flags_ptr, entry_regs);
        assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); reveal(container_cpu_set_wf); };
        assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { reveal(thread_cpu_wf); };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { reveal(container_thread_wf); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { reveal(process_thread_wf); };
        assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { reveal(container_scheduler_wf); };
        assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
        assert(container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp)) by { reveal(container_cpu_offline_flags_wf); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by {
            assert(forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)] pre.thr_mp.dom().contains(t)
                ==> post.thr_mp.spec_index(t).view().endpoint_descriptors == pre.thr_mp.spec_index(t).view().endpoint_descriptors);
            reveal(thread_endpoint_ref_counter_wf);
        };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_queue_wf); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(container_thread_endpoint_wf); };
        assert(thread_caller_callee_wf(post.thr_mp)) by { reveal(thread_caller_callee_wf); };
    };
}

/// Closes every kernel invariant after the committed offline from the entry invariants, the summary, and
/// the representation facts its callees guarantee.
pub(super) proof fn cpu_went_off_eof(
    pre: KernelK, post: KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr,
    cpu_set_ptr: RwLockCpuSetPtr, flags_ptr: RwLockCpuOfflineFlagsPtr, entry_regs: Registers,
)
    requires
        pre.inv(),
        cpu_went_off_transition(pre, post, cpu_id, container_ptr, scheduler_ptr, cpu_set_ptr, flags_ptr, entry_regs),
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        post.cpu_arr.spec_index(cpu_id).view().view().wf(),
        post.sched_mp.spec_index(scheduler_ptr).view().queue.wf(),
        post.cpu_set_mp.spec_index(cpu_set_ptr).view().owned_cpus.wf(),
        post.cpu_offline_mp.perms_wf(),
        post.cpu_offline_mp.spec_index(flags_ptr).inv(),
    ensures
        post.inv(),
        post.cpu_arr.spec_index(cpu_id).view().view().view().state is Off,
        forall|other_cpu: CpuId| #![trigger post.cpu_arr.spec_index(other_cpu)]
            index_valid(NUM_CPUS, other_cpu) && other_cpu != cpu_id ==> post.cpu_arr.spec_index(other_cpu) == pre.cpu_arr.spec_index(other_cpu),
{
    hide(Seq::contains);
    reveal(cpu_went_off_transition);
    assert(post.subsystems_inv()) by {
        assert(cpu_array_wf(post.cpu_arr, post.dflt_pt.view())) by { reveal(cpu_array_wf); };
        assert(thread_perms_wf(post.thr_mp)) by {
            reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
        };
        assert(scheduler_perms_wf(post.sched_mp)) by { reveal(scheduler_perms_wf); };
        assert(cpu_set_perms_wf(post.cpu_set_mp)) by { reveal(cpu_set_perms_wf); };
        assert(pcid_needflush_wf(post.pcid_needflush)) by { reveal(pcid_needflush_wf); };
        assert(cpu_published_wf(post.cpu_published, post.cpu_arr, post.pcid_needflush)) by { reveal(cpu_published_wf); reveal(KernelK::default_pagetable_wf); reveal(PageTable::table_pages_wf); };
        assert(cpu_offline_flags_wf(post.cpu_offline_mp, post.cpu_arr)) by { reveal(cpu_offline_flags_wf); reveal(container_cpu_offline_flags_wf); };
        reveal(KernelK::default_pagetable_wf);
    };
    assert(post.memory_management_inv()) by {
        assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { reveal(scheduler_pages_wf); };
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_pages_wf); };
        assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
        thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_4k_mp);
        container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_2m_mp);
        container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_1g_mp);
    };
    cpu_went_off_eof_process_management_inv(pre, post, cpu_id, container_ptr, scheduler_ptr, cpu_set_ptr, flags_ptr, entry_regs);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
    };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}
}
