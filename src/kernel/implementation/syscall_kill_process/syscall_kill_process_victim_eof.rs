use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_victim_spec::*;

verus! {
proof fn kill_leave_process_eof_memory(pre: KernelK, post: KernelK, process_ptr: RwLockProcessPtr, victim_ptr: RwLockThreadPtr)
    requires
        pre.inv(),
        kill_leave_process_eof_transition_framing(pre, post, process_ptr, victim_ptr),
        pre.prc_mp.dom().contains(process_ptr),
        pre.thr_mp.dom().contains(victim_ptr),
        pre.prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(victim_ptr),
        pre.prc_mp.spec_index(process_ptr).being_killed(),
        pre.prc_mp.spec_index(process_ptr).locking_thread() is Write,
        pre.thr_mp.spec_index(victim_ptr).locking_thread() is Write,
        pre.thr_mp.spec_index(victim_ptr).view().state is WAITING_REPLY || pre.thr_mp.spec_index(victim_ptr).view().state is KILLED,
        pre.thr_mp.spec_index(victim_ptr).view().temp_alloc_clean(),
        post.subsystems_inv(),
    ensures post.memory_management_inv(),
{
    reveal(kill_leave_process_eof_transition_framing);
    let victim = pre.thr_mp.spec_index(victim_ptr).view();
    let container_ptr = victim.owning_container;
    assert(victim.owning_proc == process_ptr && pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr) by { reveal(process_thread_wf); };
    container_thread_wf_at(pre.ctn_mp, pre.thr_mp, victim_ptr); container_process_wf_process_at(pre.ctn_mp, pre.prc_mp, process_ptr);
    let dp4k = victim.quota_4k as int;
    let dp2m = victim.quota_2m as int;
    let dp1g = victim.quota_1g as int;
    container_process_thread_quota_sums_bounded(&pre, container_ptr, process_ptr, victim_ptr);
    assert(post.memory_management_inv()) by {
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); };
        assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { lemma_process_pages_wf_preserved_for_process_domain_eq_forall(); };
        assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_staged_pages_wf(post.thr_mp, post.pg_arr)) by {
            thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
            thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
            thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        };
        assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { process_pagetable_match_preserved_for_process_fields_eq(pre.prc_mp, post.prc_mp, post.pt_mp); };
        assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_match); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.it_mp)) by { reveal(process_emptied_tables_wf); };
        assert({
            &&& container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)
            &&& container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp)
            &&& container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp)
        }) by {
            lemma_container_process_thread_quota_folds_change_forall(pre.ctn_mp, pre.prc_mp, post.prc_mp, pre.thr_mp, post.thr_mp, container_ptr, process_ptr, victim_ptr, dp4k, dp2m, dp1g, -dp4k, -dp2m, -dp1g);
            reveal(container_process_allocator_quota_4k_wf); reveal(container_process_allocator_quota_2m_wf); reveal(container_process_allocator_quota_1g_wf); reveal(container_allocator_wf);
        };
    };
}

proof fn kill_leave_process_eof_process(pre: KernelK, post: KernelK, process_ptr: RwLockProcessPtr, victim_ptr: RwLockThreadPtr)
    requires
        pre.inv(),
        kill_leave_process_eof_transition_framing(pre, post, process_ptr, victim_ptr),
        pre.prc_mp.dom().contains(process_ptr),
        pre.thr_mp.dom().contains(victim_ptr),
        pre.prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(victim_ptr),
        pre.prc_mp.spec_index(process_ptr).being_killed(),
        pre.prc_mp.spec_index(process_ptr).locking_thread() is Write,
        pre.thr_mp.spec_index(victim_ptr).view().state is WAITING_REPLY || pre.thr_mp.spec_index(victim_ptr).view().state is KILLED,
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(kill_leave_process_eof_transition_framing);
    process_perms_wf_at(pre.prc_mp, process_ptr);
    lemma_seq_remove_value_membership::<RwLockThreadPtr>();
    assert(post.process_management_inv()) by {
        assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { lemma_container_process_wf_preserved_for_process_rodata_forall(); };
        assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by {
            per_container_process_tree_wf_preserved_for_tree_fields_eq(pre.ctn_mp, pre.prc_mp, post.prc_mp); reveal(per_container_process_tree_wf);
        };
        assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { lemma_process_cpu_wf_preserved_for_process_pagetable_fields_forall(); };
        assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); };
        assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
        assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
        assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); };
        assert(thread_caller_callee_wf(post.thr_mp)) by { thread_caller_callee_wf_preserved_for_call_link_eq(pre.thr_mp, post.thr_mp); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_descriptor_eq(pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_endpoint_waiting_eq(pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by {
            container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp);
        };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by {
            container_thread_scheduler_wf_preserved_for_scheduled_thread_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp);
        };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { reveal(container_thread_wf); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { reveal(process_thread_wf); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_running_thread_eq(pre.thr_mp, post.thr_mp, pre.cpu_arr, post.cpu_arr); };
    };
}

/// The thread that left its marked process, which absorbed its quota, keeps the kernel invariant.
pub(crate) proof fn kill_leave_process_eof(pre: KernelK, post: KernelK, process_ptr: RwLockProcessPtr, victim_ptr: RwLockThreadPtr)
    requires
        pre.inv(),
        kill_leave_process_eof_transition_framing(pre, post, process_ptr, victim_ptr),
        pre.prc_mp.dom().contains(process_ptr),
        pre.thr_mp.dom().contains(victim_ptr),
        pre.prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(victim_ptr),
        pre.prc_mp.spec_index(process_ptr).being_killed(),
        pre.prc_mp.spec_index(process_ptr).locking_thread() is Write,
        pre.thr_mp.spec_index(victim_ptr).locking_thread() is Write,
        pre.thr_mp.spec_index(victim_ptr).view().state is WAITING_REPLY || pre.thr_mp.spec_index(victim_ptr).view().state is KILLED,
        pre.thr_mp.spec_index(victim_ptr).view().temp_alloc_clean(),
        post.prc_mp.perms_wf(),
        post.prc_mp.spec_index(process_ptr).view().inv(),
        post.thr_mp.perms_wf(),
        post.thr_mp.spec_index(victim_ptr).view().inv(),
    ensures post.inv(),
{
    reveal(kill_leave_process_eof_transition_framing);
    assert(post.subsystems_inv()) by {
        assert(process_perms_wf(post.prc_mp)) by { reveal(process_perms_wf); };
        assert(thread_perms_wf(post.thr_mp)) by {
            reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
        };
        reveal(KernelK::default_pagetable_wf);
    };
    kill_leave_process_eof_memory(pre, post, process_ptr, victim_ptr);
    kill_leave_process_eof_process(pre, post, process_ptr, victim_ptr);
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf_spec); reveal(iommu_root_table_process_wf); };
    assert(iommu_table_lock_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { iommu_table_lock_wf_preserved_for_root_and_process_fields_eq(pre.irt.view(), post.irt.view(), pre.prc_mp, post.prc_mp, post.it_mp); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_proc_pcid_match); };
}

proof fn kill_victim_killed_eof_memory(pre: KernelK, post: KernelK)
    requires
        pre.inv(),
        post.subsystems_inv(),
        post == (KernelK { thr_mp: post.thr_mp, sched_mp: post.sched_mp, ep_mp: post.ep_mp, cpu_arr: post.cpu_arr, cpu_published: post.cpu_published, ..pre }),
        post.ep_mp.dom() == pre.ep_mp.dom(),
        post.sched_mp.dom() == pre.sched_mp.dom(),
        post.thr_mp.dom() == pre.thr_mp.dom(),
        forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)] pre.thr_mp.dom().contains(t) ==> {
            &&& post.thr_mp.spec_index(t).view().quota_4k == pre.thr_mp.spec_index(t).view().quota_4k
            &&& post.thr_mp.spec_index(t).view().quota_2m == pre.thr_mp.spec_index(t).view().quota_2m
            &&& post.thr_mp.spec_index(t).view().quota_1g == pre.thr_mp.spec_index(t).view().quota_1g
            &&& post.thr_mp.spec_index(t).view().temp_alloc_cache_4k == pre.thr_mp.spec_index(t).view().temp_alloc_cache_4k
            &&& post.thr_mp.spec_index(t).view().temp_alloc_cache_2m == pre.thr_mp.spec_index(t).view().temp_alloc_cache_2m
            &&& post.thr_mp.spec_index(t).view().temp_alloc_cache_1g == pre.thr_mp.spec_index(t).view().temp_alloc_cache_1g
            &&& post.thr_mp.spec_index(t).view().owning_container == pre.thr_mp.spec_index(t).view().owning_container
            &&& post.thr_mp.spec_index(t).view().free_quota_pending_fields_unchanged(&pre.thr_mp.spec_index(t).view())
        },
        forall|s: RwLockSchedulerPtr| #![trigger post.sched_mp.spec_index(s)] pre.sched_mp.dom().contains(s) ==> post.sched_mp.spec_index(s).owning_container == pre.sched_mp.spec_index(s).owning_container,
        forall|e: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(e)] pre.ep_mp.dom().contains(e) ==> post.ep_mp.spec_index(e).view().owning_container == pre.ep_mp.spec_index(e).view().owning_container,
    ensures post.memory_management_inv(),
{
    assert(post.memory_management_inv()) by {
        assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { reveal(scheduler_pages_wf); };
        assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { reveal(endpoint_pages_wf); };
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_staged_pages_wf(post.thr_mp, post.pg_arr)) by {
            thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
            thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
            thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        };
        container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_4k_mp);
        container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_2m_mp);
        container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_1g_mp);
    };
}

/// The killed thread taken off its scheduler shard keeps the kernel invariant.
pub(crate) proof fn kill_dequeue_scheduled_eof(pre: KernelK, post: KernelK, victim_ptr: RwLockThreadPtr, scheduler_ptr: RwLockSchedulerPtr, shard: CpuId)
    requires
        pre.inv(),
        kill_dequeue_scheduled_eof_transition_framing(pre, post, victim_ptr, scheduler_ptr, shard),
        index_valid(NUM_CPUS, shard),
        pre.thr_mp.dom().contains(victim_ptr),
        pre.sched_mp.dom().contains(scheduler_ptr),
        pre.thr_mp.spec_index(victim_ptr).locking_thread() is Write,
        pre.thr_mp.spec_index(victim_ptr).view().state == (ThreadState::SCHEDULED { cpu_id: shard }),
        pre.ctn_mp.spec_index(pre.thr_mp.spec_index(victim_ptr).view().owning_container).view_rodata().view().scheduler == scheduler_ptr,
        post.thr_mp.perms_wf(),
        post.thr_mp.spec_index(victim_ptr).view().inv(),
        scheduler_perms_wf(post.sched_mp),
    ensures post.inv(),
{
    reveal(kill_dequeue_scheduled_eof_transition_framing);
    let before = pre.sched_mp.spec_index(scheduler_ptr).shard(shard).queue;
    scheduler_perms_wf_at(pre.sched_mp, scheduler_ptr);
    assert(before.view().no_duplicates()) by { reveal(scheduler_perms_wf); reveal(LinkedList::value_list_unique); reveal(LinkedList::wf_value_list); };
    lemma_seq_remove_value_membership::<RwLockThreadPtr>();
    assert(post.subsystems_inv()) by {
        assert(thread_perms_wf(post.thr_mp)) by {
            reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
        };
        reveal(KernelK::default_pagetable_wf);
    };
    kill_victim_killed_eof_memory(pre, post);
    assert(post.process_management_inv()) by {
        assert(thread_caller_callee_wf(post.thr_mp)) by { thread_caller_callee_wf_preserved_for_call_link_eq(pre.thr_mp, post.thr_mp); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_descriptor_eq(pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_endpoint_waiting_eq(pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by {
            container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp);
        };
        assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { container_scheduler_wf_preserved_for_scheduler_owner_eq(pre.ctn_mp, post.ctn_mp, pre.sched_mp, post.sched_mp); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by {
            reveal(scheduler_perms_wf); reveal(LinkedList::wf_map); reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
        };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { reveal(container_thread_wf); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { reveal(process_thread_wf); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_running_thread_eq(pre.thr_mp, post.thr_mp, pre.cpu_arr, post.cpu_arr); };
    };
}

/// The killed thread taken out of its endpoint's queue keeps the kernel invariant.
pub(crate) proof fn kill_dequeue_endpoint_eof(pre: KernelK, post: KernelK, victim_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr)
    requires
        pre.inv(),
        kill_dequeue_endpoint_eof_transition_framing(pre, post, victim_ptr, endpoint_ptr),
        pre.thr_mp.dom().contains(victim_ptr),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.thr_mp.spec_index(victim_ptr).locking_thread() is Write,
        pre.thr_mp.spec_index(victim_ptr).view().state.is_endpoint_waiting(),
        pre.thr_mp.spec_index(victim_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        post.thr_mp.perms_wf(),
        post.thr_mp.spec_index(victim_ptr).view().inv(),
        post.ep_mp.perms_wf(),
        post.ep_mp.spec_index(endpoint_ptr).view().inv(),
    ensures post.inv(),
{
    reveal(kill_dequeue_endpoint_eof_transition_framing);
    let before = pre.ep_mp.spec_index(endpoint_ptr).view().queue;
    endpoint_perms_wf_at(pre.ep_mp, endpoint_ptr);
    assert(before.view().no_duplicates()) by { reveal(LinkedList::value_list_unique); reveal(LinkedList::wf_value_list); };
    lemma_seq_remove_value_membership::<RwLockThreadPtr>();
    assert(post.subsystems_inv()) by {
        assert(thread_perms_wf(post.thr_mp)) by {
            reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
        };
        assert(endpoint_perms_wf(post.ep_mp)) by { reveal(endpoint_perms_wf); };
        reveal(KernelK::default_pagetable_wf);
    };
    kill_victim_killed_eof_memory(pre, post);
    assert(post.process_management_inv()) by {
        assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { container_endpoint_wf_preserved_for_endpoint_owner_eq(pre.ctn_mp, post.ctn_mp, pre.ep_mp, post.ep_mp); };
        assert(thread_caller_callee_wf(post.thr_mp)) by { thread_caller_callee_wf_preserved_for_call_link_eq(pre.thr_mp, post.thr_mp); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_descriptor_eq(pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_queue_wf); reveal(LinkedList::wf_map); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by {
            container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp);
        };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by {
            container_thread_scheduler_wf_preserved_for_scheduled_thread_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp);
        };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { reveal(container_thread_wf); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { reveal(process_thread_wf); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_running_thread_eq(pre.thr_mp, post.thr_mp, pre.cpu_arr, post.cpu_arr); };
    };
}

proof fn kill_evict_eof_cpu_relations(pre: KernelK, post: KernelK, victim_ptr: RwLockThreadPtr, remote: CpuId, default_cr3: PageTableRoot)
    requires
        pre.inv(),
        kill_evict_eof_transition_framing(pre, post, victim_ptr, remote, default_cr3),
        index_valid(NUM_CPUS, remote),
        pre.thr_mp.dom().contains(victim_ptr),
        pre.thr_mp.spec_index(victim_ptr).locking_thread() is Write,
        pre.thr_mp.spec_index(victim_ptr).view().state == (ThreadState::RUNNING { cpu_id: remote }),
        default_cr3 == pre.dflt_pt.view().cr3,
        !pre.cpu_arr.spec_index(remote).view().being_killed(),
    ensures
        container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr),
        process_cpu_wf(post.prc_mp, post.cpu_arr),
        thread_cpu_wf(post.thr_mp, post.cpu_arr),
{
    reveal(kill_evict_eof_transition_framing);
    reveal(cpu_array_wf); reveal(thread_cpu_wf);
    assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); };
    assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); };
}

/// The killed thread evicted from its remote cpu, which went idle on the default page table, keeps the kernel invariant.
pub(crate) proof fn kill_evict_eof(pre: KernelK, post: KernelK, victim_ptr: RwLockThreadPtr, remote: CpuId, default_cr3: PageTableRoot)
    requires
        pre.inv(),
        kill_evict_eof_transition_framing(pre, post, victim_ptr, remote, default_cr3),
        index_valid(NUM_CPUS, remote),
        pre.thr_mp.dom().contains(victim_ptr),
        pre.thr_mp.spec_index(victim_ptr).locking_thread() is Write,
        pre.thr_mp.spec_index(victim_ptr).view().state == (ThreadState::RUNNING { cpu_id: remote }),
        default_cr3 == pre.dflt_pt.view().cr3,
        !pre.cpu_arr.spec_index(remote).view().being_killed(),
        post.thr_mp.perms_wf(),
        post.thr_mp.spec_index(victim_ptr).view().inv(),
    ensures post.inv(),
{
    reveal(kill_evict_eof_transition_framing);
    assert(post.subsystems_inv()) by {
        assert(cpu_array_wf(post.cpu_arr, post.dflt_pt.view())) by { reveal(cpu_array_wf); reveal(KernelK::default_pagetable_wf); };
        assert(cpu_offline_flags_wf(post.cpu_offline_mp, post.cpu_arr)) by { reveal(cpu_offline_flags_wf); };
        assert(cpu_published_wf(post.cpu_published, post.cpu_arr, post.pcid_needflush)) by { reveal(cpu_published_wf); reveal(KernelK::default_pagetable_wf); reveal(PageTable::table_pages_wf); };
        assert(thread_perms_wf(post.thr_mp)) by {
            reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
        };
        reveal(KernelK::default_pagetable_wf);
    };
    kill_victim_killed_eof_memory(pre, post);
    assert(post.process_management_inv()) by {
        kill_evict_eof_cpu_relations(pre, post, victim_ptr, remote, default_cr3);
        assert(container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp)) by { reveal(container_cpu_offline_flags_wf); };
        assert(thread_caller_callee_wf(post.thr_mp)) by { thread_caller_callee_wf_preserved_for_call_link_eq(pre.thr_mp, post.thr_mp); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_descriptor_eq(pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_endpoint_waiting_eq(pre.thr_mp, post.thr_mp, post.ep_mp); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by {
            container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp);
        };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by {
            container_thread_scheduler_wf_preserved_for_scheduled_thread_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp);
        };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { reveal(container_thread_wf); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { reveal(process_thread_wf); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match);
        reveal(container_cpu_wf);
    };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}
} // verus!
