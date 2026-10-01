use vstd::prelude::*;
use crate::*;
use super::syscall_schedule_spec::scheduler_context_switch_transition;

verus! {
proof fn scheduler_context_switch_eof_container_thread_scheduler(
    pre: KernelK, post: KernelK, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr, next_thread: RwLockThreadPtr, entry_regs: Registers,
)
    requires
        pre.inv(),
        scheduler_context_switch_transition(pre, post, cpu_id, scheduler_ptr, next_thread, entry_regs),
        post.subsystems_inv(),
    ensures container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp),
{
    reveal(scheduler_context_switch_transition);
    assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by {
        let cpu = pre.cpu_arr.spec_index(cpu_id).view().view().view();
        assert(cpu.current_thread is Some ==> pre.thr_mp.spec_index(cpu.current_thread.unwrap()).view().owning_container == cpu.owning_container) by { reveal(thread_cpu_wf); reveal(process_thread_wf); reveal(process_cpu_wf); };
        assert(pre.sched_mp.spec_index(scheduler_ptr).view().queue.view().no_duplicates()) by { reveal(scheduler_perms_wf); reveal(LinkedList::value_list_unique); reveal(LinkedList::wf_value_list); };
        reveal(container_thread_scheduler_wf); reveal(container_scheduler_wf); reveal(container_thread_wf);
        seq_push_lemma::<RwLockThreadPtr>(); seq_skip_lemma::<RwLockThreadPtr>();
    };
}

#[verifier::spinoff_prover]
proof fn scheduler_context_switch_eof_process_management_inv(
    pre: KernelK, post: KernelK, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr, next_thread: RwLockThreadPtr, entry_regs: Registers,
)
    requires
        pre.inv(),
        scheduler_context_switch_transition(pre, post, cpu_id, scheduler_ptr, next_thread, entry_regs),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(scheduler_context_switch_transition);
    assert(post.process_management_inv()) by {
        scheduler_context_switch_eof_container_thread_scheduler(pre, post, cpu_id, scheduler_ptr, next_thread, entry_regs);
        assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); reveal(container_thread_wf); reveal(container_process_wf); reveal(process_thread_wf); };
        assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); reveal(process_pagetable_match); reveal(process_thread_wf); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { reveal(thread_cpu_wf); };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { reveal(container_thread_wf); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { reveal(process_thread_wf); };
        assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { reveal(container_scheduler_wf); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_queue_wf); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(container_thread_endpoint_wf); };
        assert(thread_caller_callee_wf(post.thr_mp)) by { reveal(thread_caller_callee_wf); };
    };
}

pub(super) proof fn scheduler_context_switch_eof(pre: KernelK, post: KernelK, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr, next_thread: RwLockThreadPtr, entry_regs: Registers)
    requires
        pre.inv(),
        scheduler_context_switch_transition(pre, post, cpu_id, scheduler_ptr, next_thread, entry_regs),
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        post.cpu_published[cpu_id as int].inv(),
        post.cpu_arr.spec_index(cpu_id).view().view().view().tlb_dirty_bitmap.inv(),
        post.sched_mp.spec_index(scheduler_ptr).view().queue.wf(),
    ensures
        post.inv(),
        post.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        post.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(pre.thr_mp.spec_index(next_thread).view().owning_proc),
        post.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(next_thread),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread != Some(next_thread),
        post.thr_mp.spec_index(next_thread).view().state == (ThreadState::RUNNING { cpu_id }),
        post.thr_mp.spec_index(next_thread).view().error_code is None,
        post.sched_mp.spec_index(scheduler_ptr).view().queue.view() == match pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread {
            Some(previous) => pre.sched_mp.spec_index(scheduler_ptr).view().queue.view().skip(1).push(previous),
            None => pre.sched_mp.spec_index(scheduler_ptr).view().queue.view().skip(1),
        },
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread is Some ==> {
            let previous = pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap();
            &&& post.thr_mp.spec_index(previous).view().state is SCHEDULED
            &&& *post.thr_mp.spec_index(previous).view().trap_frame.get_some_0() == entry_regs
        },
        forall|other_cpu: CpuId| #![trigger post.cpu_arr.spec_index(other_cpu)]
            index_valid(NUM_CPUS, other_cpu) && other_cpu != cpu_id ==> post.cpu_arr.spec_index(other_cpu) == pre.cpu_arr.spec_index(other_cpu),
{
    hide(Seq::contains);
    reveal(scheduler_context_switch_transition);
    assert(post.subsystems_inv()) by {
        assert(cpu_array_wf(post.cpu_arr, post.dflt_pt.view())) by { reveal(cpu_array_wf); };
        assert(thread_perms_wf(post.thr_mp)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); };
        assert(scheduler_perms_wf(post.sched_mp)) by { reveal(scheduler_perms_wf); };
        assert(pcid_needflush_wf(post.pcid_needflush)) by { reveal(pcid_needflush_wf); };
        assert(cpu_published_wf(post.cpu_published, post.cpu_arr, post.pcid_needflush)) by { reveal(process_thread_wf); reveal(process_pagetable_match); reveal(pagetable_perms_wf); reveal(PageTable::table_pages_wf); reveal(cpu_published_wf); };
        reveal(KernelK::default_pagetable_wf);
    };
    assert(post.memory_management_inv()) by {
        assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { reveal(scheduler_pages_wf); };
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_pages_wf); };
        thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_4k_mp);
        container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_2m_mp);
        container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_1g_mp);
    };
    scheduler_context_switch_eof_process_management_inv(pre, post, cpu_id, scheduler_ptr, next_thread, entry_regs);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(process_pagetable_match); reveal(container_process_wf); reveal(process_thread_wf); };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}
}
