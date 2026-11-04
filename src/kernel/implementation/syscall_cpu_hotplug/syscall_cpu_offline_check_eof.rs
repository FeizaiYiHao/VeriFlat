use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_cpu_offline_check_spec::{cpu_went_off_eof_transition_framing, cpu_offline_check_flushed_default_pcid};

verus! {
proof fn cpu_went_off_eof_container_thread_scheduler(pre: KernelK, post: KernelK, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, sched_ptr: RwLockSchedulerPtr, cpu_set_ptr: RwLockCpuSetPtr, flags_ptr: RwLockCpuOfflineFlagsPtr, entry_regs: Registers)
    requires
        pre.inv(),
        cpu_went_off_eof_transition_framing(pre, post, cpu_id, ctn_ptr, sched_ptr, cpu_set_ptr, flags_ptr, entry_regs),
        ({
            let old_cpu = pre.cpu_arr.spec_index(cpu_id).view().view().view();
            let queue_before = pre.sched_mp.spec_index(sched_ptr).shards.spec_index(cpu_id).view().view().queue;
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& old_cpu.owning_container == ctn_ptr
            &&& pre.ctn_mp.dom().contains(ctn_ptr)
            &&& pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().scheduler == sched_ptr
            &&& pre.sched_mp.dom().contains(sched_ptr)
            &&& old_cpu.current_process is Some == old_cpu.current_thread is Some
            &&& (old_cpu.current_thread is Some ==> {
                let prev = old_cpu.current_thread.unwrap();
                &&& pre.thrd_mp.dom().contains(prev)
                &&& pre.thrd_mp.spec_index(prev).view().state == (ThreadState::RUNNING { cpu_id })
                &&& pre.thrd_mp.spec_index(prev).view().owning_proc == old_cpu.current_process.unwrap()
                &&& !queue_before.view().contains(prev)
                &&& !queue_before.map().dom().contains(pre.thrd_mp.spec_index(prev).view().scheduler_linkedlist_node.addr())
            })
        }),
        post.subsystems_inv(),
    ensures container_thread_scheduler_wf(post.ctn_mp, post.thrd_mp, post.sched_mp),
{
    reveal(cpu_went_off_eof_transition_framing);
    assert(container_thread_scheduler_wf(post.ctn_mp, post.thrd_mp, post.sched_mp)) by {
        let cpu = pre.cpu_arr.spec_index(cpu_id).view().view().view();
        assert(cpu.current_thread is Some ==> pre.thrd_mp.spec_index(cpu.current_thread.unwrap()).view().owning_container == cpu.owning_container) by { reveal(process_thread_wf); reveal(process_cpu_wf); };
        reveal(container_thread_scheduler_wf); reveal(container_scheduler_wf); reveal(container_thread_wf);
        seq_push_implies_contains::<RwLockThreadPtr>();
    };
}

proof fn cpu_went_off_eof_process_management_inv(pre: KernelK, post: KernelK, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, sched_ptr: RwLockSchedulerPtr, cpu_set_ptr: RwLockCpuSetPtr, flags_ptr: RwLockCpuOfflineFlagsPtr, entry_regs: Registers)
    requires
        pre.inv(),
        cpu_went_off_eof_transition_framing(pre, post, cpu_id, ctn_ptr, sched_ptr, cpu_set_ptr, flags_ptr, entry_regs),
        ({
            let old_cpu = pre.cpu_arr.spec_index(cpu_id).view().view().view();
            let queue_before = pre.sched_mp.spec_index(sched_ptr).shards.spec_index(cpu_id).view().view().queue;
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& !pre.cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& old_cpu.owning_container == ctn_ptr
            &&& pre.ctn_mp.dom().contains(ctn_ptr)
            &&& pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().scheduler == sched_ptr
            &&& pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set == cpu_set_ptr
            &&& pre.sched_mp.dom().contains(sched_ptr)
            &&& pre.cpu_set_mp.dom().contains(cpu_set_ptr)
            &&& !pre.cpu_set_mp.spec_index(cpu_set_ptr).being_killed()
            &&& old_cpu.current_process is Some == old_cpu.current_thread is Some
            &&& (old_cpu.current_thread is Some ==> {
                let prev = old_cpu.current_thread.unwrap();
                &&& pre.thrd_mp.dom().contains(prev)
                &&& pre.thrd_mp.spec_index(prev).view().state == (ThreadState::RUNNING { cpu_id })
                &&& pre.thrd_mp.spec_index(prev).view().owning_proc == old_cpu.current_process.unwrap()
                &&& !queue_before.view().contains(prev)
                &&& !queue_before.map().dom().contains(pre.thrd_mp.spec_index(prev).view().scheduler_linkedlist_node.addr())
            })
        }),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(cpu_went_off_eof_transition_framing);
    assert(post.process_management_inv()) by {
        cpu_went_off_eof_container_thread_scheduler(pre, post, cpu_id, ctn_ptr, sched_ptr, cpu_set_ptr, flags_ptr, entry_regs);
        assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); reveal(container_cpu_set_wf); };
        assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); };
        assert(thread_cpu_wf(post.thrd_mp, post.cpu_arr)) by { reveal(thread_cpu_wf); };
        assert(container_thread_wf(post.ctn_mp, post.thrd_mp)) by { container_thread_wf_preserved_for_container_thread_link_eq(pre.ctn_mp, post.ctn_mp, pre.thrd_mp, post.thrd_mp); };
        assert(process_thread_wf(post.prc_mp, post.thrd_mp)) by { process_thread_wf_preserved_for_process_thread_link_eq(pre.prc_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp); };
        assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { container_scheduler_wf_preserved_for_scheduler_owner_eq(pre.ctn_mp, post.ctn_mp, pre.sched_mp, post.sched_mp); };
        assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
        assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
        assert(container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp)) by { container_cpu_offline_flags_wf_preserved_for_flags_owner_eq(pre.ctn_mp, post.ctn_mp, pre.cpu_offline_mp, post.cpu_offline_mp); };
        assert(thread_endpoint_ref_counter_wf(post.thrd_mp, post.ep_mp)) by {
            thread_endpoint_ref_counter_wf_preserved_for_descriptor_eq(pre.thrd_mp, post.thrd_mp, pre.ep_mp, post.ep_mp);
            assert(forall|t: RwLockThreadPtr| #![trigger post.thrd_mp.spec_index(t)]
                post.thrd_mp.dom().contains(t) ==> post.thrd_mp.spec_index(t).view().endpoint_descriptors == pre.thrd_mp.spec_index(t).view().endpoint_descriptors);
        };
        assert(thread_endpoint_queue_wf(post.thrd_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_endpoint_waiting_eq(pre.thrd_mp, post.thrd_mp, post.ep_mp); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thrd_mp, post.ep_mp)) by { container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(pre.ctn_mp, post.ctn_mp, pre.thrd_mp, post.thrd_mp, pre.ep_mp, post.ep_mp); };
        assert(thread_caller_callee_wf(post.thrd_mp)) by { thread_caller_callee_wf_preserved_for_call_link_eq(pre.thrd_mp, post.thrd_mp); };
        assert(thread_dangling_chain_end_wf(post.thrd_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thrd_mp, post.thrd_mp); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
    };
}

proof fn cpu_went_off_eof_thread_perms(pre: KernelK, post: KernelK, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, sched_ptr: RwLockSchedulerPtr, cpu_set_ptr: RwLockCpuSetPtr, flags_ptr: RwLockCpuOfflineFlagsPtr, entry_regs: Registers)
    requires
        pre.inv(),
        cpu_went_off_eof_transition_framing(pre, post, cpu_id, ctn_ptr, sched_ptr, cpu_set_ptr, flags_ptr, entry_regs),
        ({
            let old_cpu = pre.cpu_arr.spec_index(cpu_id).view().view().view();
            let queue_before = pre.sched_mp.spec_index(sched_ptr).shards.spec_index(cpu_id).view().view().queue;
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& old_cpu.owning_container == ctn_ptr
            &&& pre.ctn_mp.dom().contains(ctn_ptr)
            &&& pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().scheduler == sched_ptr
            &&& pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set == cpu_set_ptr
            &&& flags_ptr == cpu_offline_flags_ptr(ctn_ptr)
            &&& pre.sched_mp.dom().contains(sched_ptr)
            &&& pre.cpu_set_mp.dom().contains(cpu_set_ptr)
            &&& !pre.cpu_set_mp.spec_index(cpu_set_ptr).being_killed()
            &&& pre.cpu_offline_mp.dom().contains(flags_ptr)
            &&& !pre.cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& old_cpu.current_process is Some == old_cpu.current_thread is Some
            &&& (old_cpu.current_thread is Some ==> {
                let prev = old_cpu.current_thread.unwrap();
                &&& pre.thrd_mp.dom().contains(prev)
                &&& pre.thrd_mp.spec_index(prev).view().state == (ThreadState::RUNNING { cpu_id })
                &&& pre.thrd_mp.spec_index(prev).view().syscall_progress.view() is None
                &&& pre.thrd_mp.spec_index(prev).view().owning_proc == old_cpu.current_process.unwrap()
                &&& !queue_before.view().contains(prev)
                &&& !queue_before.map().dom().contains(pre.thrd_mp.spec_index(prev).view().scheduler_linkedlist_node.addr())
            })
        }),
        post.cpu_op.view().view()[cpu_id as int] is InStep,
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        post.cpu_arr.spec_index(cpu_id).view().view().wf(),
        post.sched_mp.perms_wf(),
        post.sched_mp.spec_index(sched_ptr).shards.inv(),
        post.sched_mp.spec_index(sched_ptr).shard(cpu_id).queue.wf(),
        post.cpu_set_mp.perms_wf(),
        post.cpu_set_mp.spec_index(cpu_set_ptr).view().owned_cpus.wf(),
        post.cpu_offline_mp.perms_wf(),
        post.cpu_offline_mp.spec_index(flags_ptr).inv(),
    ensures thread_perms_wf(post.thrd_mp),
{
    hide(Seq::contains);
    reveal(cpu_went_off_eof_transition_framing);
    reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
    reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
}

proof fn cpu_went_off_eof_subsystems_inv(pre: KernelK, post: KernelK, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, sched_ptr: RwLockSchedulerPtr, cpu_set_ptr: RwLockCpuSetPtr, flags_ptr: RwLockCpuOfflineFlagsPtr, entry_regs: Registers)
    requires
        pre.inv(),
        cpu_went_off_eof_transition_framing(pre, post, cpu_id, ctn_ptr, sched_ptr, cpu_set_ptr, flags_ptr, entry_regs),
        ({
            let old_cpu = pre.cpu_arr.spec_index(cpu_id).view().view().view();
            let queue_before = pre.sched_mp.spec_index(sched_ptr).shards.spec_index(cpu_id).view().view().queue;
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& old_cpu.owning_container == ctn_ptr
            &&& pre.ctn_mp.dom().contains(ctn_ptr)
            &&& pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().scheduler == sched_ptr
            &&& pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set == cpu_set_ptr
            &&& flags_ptr == cpu_offline_flags_ptr(ctn_ptr)
            &&& pre.sched_mp.dom().contains(sched_ptr)
            &&& pre.cpu_set_mp.dom().contains(cpu_set_ptr)
            &&& !pre.cpu_set_mp.spec_index(cpu_set_ptr).being_killed()
            &&& pre.cpu_offline_mp.dom().contains(flags_ptr)
            &&& !pre.cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& old_cpu.current_process is Some == old_cpu.current_thread is Some
            &&& (old_cpu.current_thread is Some ==> {
                let prev = old_cpu.current_thread.unwrap();
                &&& pre.thrd_mp.dom().contains(prev)
                &&& pre.thrd_mp.spec_index(prev).view().state == (ThreadState::RUNNING { cpu_id })
                &&& pre.thrd_mp.spec_index(prev).view().syscall_progress.view() is None
                &&& pre.thrd_mp.spec_index(prev).view().owning_proc == old_cpu.current_process.unwrap()
                &&& !queue_before.view().contains(prev)
                &&& !queue_before.map().dom().contains(pre.thrd_mp.spec_index(prev).view().scheduler_linkedlist_node.addr())
            })
        }),
        post.cpu_op.view().view()[cpu_id as int] is InStep,
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        post.pcid_needflush.inv(),
        post.cpu_arr.spec_index(cpu_id).view().view().wf(),
        post.sched_mp.perms_wf(),
        post.sched_mp.spec_index(sched_ptr).shards.inv(),
        post.sched_mp.spec_index(sched_ptr).shard(cpu_id).queue.wf(),
        post.cpu_set_mp.perms_wf(),
        post.cpu_set_mp.spec_index(cpu_set_ptr).view().owned_cpus.wf(),
        post.cpu_offline_mp.perms_wf(),
        post.cpu_offline_mp.spec_index(flags_ptr).inv(),
    ensures post.subsystems_inv(),
{
    hide(Seq::contains);
    reveal(cpu_went_off_eof_transition_framing);
    assert(cpu_array_wf(post.cpu_arr, post.dflt_pt.view())) by { reveal(cpu_array_wf); };
    assert(cpu_op_wf(post.cpu_op.view().view(), post.cpu_arr)) by { reveal(cpu_op_wf); };
    cpu_went_off_eof_thread_perms(pre, post, cpu_id, ctn_ptr, sched_ptr, cpu_set_ptr, flags_ptr, entry_regs);
    assert(scheduler_perms_wf(post.sched_mp)) by { reveal(scheduler_perms_wf); };
    assert(cpu_set_perms_wf(post.cpu_set_mp)) by { reveal(cpu_set_perms_wf); };
    assert(pcid_needflush_wf(post.pcid_needflush)) by { reveal(pcid_needflush_wf); };
    assert(cpu_hw_cr3_pcid_wf(post.cpu_hw_cr3_pcid, post.cpu_arr, post.pcid_needflush)) by { reveal(cpu_hw_cr3_pcid_wf); reveal(KernelK::default_pagetable_wf); reveal(PageTable::table_pages_wf); };
    assert(cpu_offline_flags_wf(post.cpu_offline_mp, post.cpu_arr)) by { reveal(cpu_offline_flags_wf); reveal(container_cpu_offline_flags_wf); };
    reveal(KernelK::default_pagetable_wf);
}

proof fn cpu_went_off_eof_memory_management_inv(pre: KernelK, post: KernelK, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, sched_ptr: RwLockSchedulerPtr, cpu_set_ptr: RwLockCpuSetPtr, flags_ptr: RwLockCpuOfflineFlagsPtr, entry_regs: Registers)
    requires
        pre.inv(),
        cpu_went_off_eof_transition_framing(pre, post, cpu_id, ctn_ptr, sched_ptr, cpu_set_ptr, flags_ptr, entry_regs),
        ({
            let old_cpu = pre.cpu_arr.spec_index(cpu_id).view().view().view();
            let queue_before = pre.sched_mp.spec_index(sched_ptr).shards.spec_index(cpu_id).view().view().queue;
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& old_cpu.owning_container == ctn_ptr
            &&& pre.ctn_mp.dom().contains(ctn_ptr)
            &&& pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().scheduler == sched_ptr
            &&& pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set == cpu_set_ptr
            &&& flags_ptr == cpu_offline_flags_ptr(ctn_ptr)
            &&& pre.sched_mp.dom().contains(sched_ptr)
            &&& pre.cpu_set_mp.dom().contains(cpu_set_ptr)
            &&& !pre.cpu_set_mp.spec_index(cpu_set_ptr).being_killed()
            &&& pre.cpu_offline_mp.dom().contains(flags_ptr)
            &&& !pre.cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& old_cpu.current_process is Some == old_cpu.current_thread is Some
            &&& (old_cpu.current_thread is Some ==> {
                let prev = old_cpu.current_thread.unwrap();
                &&& pre.thrd_mp.dom().contains(prev)
                &&& pre.thrd_mp.spec_index(prev).view().state == (ThreadState::RUNNING { cpu_id })
                &&& pre.thrd_mp.spec_index(prev).view().syscall_progress.view() is None
                &&& pre.thrd_mp.spec_index(prev).view().owning_proc == old_cpu.current_process.unwrap()
                &&& !queue_before.view().contains(prev)
                &&& !queue_before.map().dom().contains(pre.thrd_mp.spec_index(prev).view().scheduler_linkedlist_node.addr())
            })
        }),
        post.cpu_op.view().view()[cpu_id as int] is InStep,
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        post.cpu_arr.spec_index(cpu_id).view().view().wf(),
        post.sched_mp.perms_wf(),
        post.sched_mp.spec_index(sched_ptr).shards.inv(),
        post.sched_mp.spec_index(sched_ptr).shard(cpu_id).queue.wf(),
        post.cpu_set_mp.perms_wf(),
        post.cpu_set_mp.spec_index(cpu_set_ptr).view().owned_cpus.wf(),
        post.cpu_offline_mp.perms_wf(),
        post.cpu_offline_mp.spec_index(flags_ptr).inv(),
        post.subsystems_inv(),
    ensures post.memory_management_inv(),
{
    hide(Seq::contains);
    reveal(cpu_went_off_eof_transition_framing);
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { reveal(scheduler_pages_wf); };
    assert(thread_pages_wf(post.thrd_mp, post.pg_arr)) by { reveal(thread_pages_wf); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
    assert(page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr)) by { reveal(page_object_owner_wf); reveal(container_owned_pages_wf); };
    thread_staged_4k_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
    thread_staged_2m_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
    thread_staged_1g_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
    container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_4k_mp);
    container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_2m_mp);
    container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_1g_mp);
}

proof fn cpu_went_off_eof_tlb(pre: KernelK, post: KernelK, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, sched_ptr: RwLockSchedulerPtr, cpu_set_ptr: RwLockCpuSetPtr, flags_ptr: RwLockCpuOfflineFlagsPtr, entry_regs: Registers)
    requires
        pre.inv(),
        cpu_went_off_eof_transition_framing(pre, post, cpu_id, ctn_ptr, sched_ptr, cpu_set_ptr, flags_ptr, entry_regs),
        ({
            let old_cpu = pre.cpu_arr.spec_index(cpu_id).view().view().view();
            let queue_before = pre.sched_mp.spec_index(sched_ptr).shards.spec_index(cpu_id).view().view().queue;
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& old_cpu.owning_container == ctn_ptr
            &&& pre.ctn_mp.dom().contains(ctn_ptr)
            &&& pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().scheduler == sched_ptr
            &&& pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set == cpu_set_ptr
            &&& flags_ptr == cpu_offline_flags_ptr(ctn_ptr)
            &&& pre.sched_mp.dom().contains(sched_ptr)
            &&& pre.cpu_set_mp.dom().contains(cpu_set_ptr)
            &&& !pre.cpu_set_mp.spec_index(cpu_set_ptr).being_killed()
            &&& pre.cpu_offline_mp.dom().contains(flags_ptr)
            &&& !pre.cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& old_cpu.current_process is Some == old_cpu.current_thread is Some
            &&& (old_cpu.current_thread is Some ==> {
                let prev = old_cpu.current_thread.unwrap();
                &&& pre.thrd_mp.dom().contains(prev)
                &&& pre.thrd_mp.spec_index(prev).view().state == (ThreadState::RUNNING { cpu_id })
                &&& pre.thrd_mp.spec_index(prev).view().syscall_progress.view() is None
                &&& pre.thrd_mp.spec_index(prev).view().owning_proc == old_cpu.current_process.unwrap()
                &&& !queue_before.view().contains(prev)
                &&& !queue_before.map().dom().contains(pre.thrd_mp.spec_index(prev).view().scheduler_linkedlist_node.addr())
            })
        }),
        post.cpu_op.view().view()[cpu_id as int] is InStep,
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        post.cpu_arr.spec_index(cpu_id).view().view().wf(),
        post.sched_mp.perms_wf(),
        post.sched_mp.spec_index(sched_ptr).shards.inv(),
        post.sched_mp.spec_index(sched_ptr).shard(cpu_id).queue.wf(),
        post.cpu_set_mp.perms_wf(),
        post.cpu_set_mp.spec_index(cpu_set_ptr).view().owned_cpus.wf(),
        post.cpu_offline_mp.perms_wf(),
        post.cpu_offline_mp.spec_index(flags_ptr).inv(),
        post.subsystems_inv(),
        post.process_management_inv(),
    ensures
        cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush),
        cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
        structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    hide(Seq::contains);
    reveal(cpu_went_off_eof_transition_framing);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_process_in_cpu_container); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_pagetable_pcid_match); reveal(cpu_dirty_map_covers_nonempty_tlb);
    };
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(cpu_tlb_wf); };
    assert(structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(structure_cache_wf); };
}

/// Closes every kernel invariant after the committed offline from the entry invariants, the summary, and
/// the representation facts its callees guarantee.
pub(super) proof fn cpu_went_off_eof(pre: KernelK, post: KernelK, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, sched_ptr: RwLockSchedulerPtr, cpu_set_ptr: RwLockCpuSetPtr, flags_ptr: RwLockCpuOfflineFlagsPtr, entry_regs: Registers)
    requires
        pre.inv(),
        cpu_went_off_eof_transition_framing(pre, post, cpu_id, ctn_ptr, sched_ptr, cpu_set_ptr, flags_ptr, entry_regs),
        ({
            let old_cpu = pre.cpu_arr.spec_index(cpu_id).view().view().view();
            let queue_before = pre.sched_mp.spec_index(sched_ptr).shards.spec_index(cpu_id).view().view().queue;
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& old_cpu.owning_container == ctn_ptr
            &&& pre.ctn_mp.dom().contains(ctn_ptr)
            &&& pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().scheduler == sched_ptr
            &&& pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set == cpu_set_ptr
            &&& flags_ptr == cpu_offline_flags_ptr(ctn_ptr)
            &&& pre.sched_mp.dom().contains(sched_ptr)
            &&& pre.cpu_set_mp.dom().contains(cpu_set_ptr)
            &&& !pre.cpu_set_mp.spec_index(cpu_set_ptr).being_killed()
            &&& pre.cpu_offline_mp.dom().contains(flags_ptr)
            &&& !pre.cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& old_cpu.current_process is Some == old_cpu.current_thread is Some
            &&& (old_cpu.current_thread is Some ==> {
                let prev = old_cpu.current_thread.unwrap();
                &&& pre.thrd_mp.dom().contains(prev)
                &&& pre.thrd_mp.spec_index(prev).view().state == (ThreadState::RUNNING { cpu_id })
                &&& pre.thrd_mp.spec_index(prev).view().syscall_progress.view() is None
                &&& pre.thrd_mp.spec_index(prev).view().owning_proc == old_cpu.current_process.unwrap()
                &&& !queue_before.view().contains(prev)
                &&& !queue_before.map().dom().contains(pre.thrd_mp.spec_index(prev).view().scheduler_linkedlist_node.addr())
            })
        }),
        post.cpu_op.view().view()[cpu_id as int] is InStep,
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        post.pcid_needflush.inv(),
        post.cpu_arr.spec_index(cpu_id).view().view().wf(),
        post.sched_mp.perms_wf(),
        post.sched_mp.spec_index(sched_ptr).shards.inv(),
        post.sched_mp.spec_index(sched_ptr).shard(cpu_id).queue.wf(),
        post.cpu_set_mp.perms_wf(),
        post.cpu_set_mp.spec_index(cpu_set_ptr).view().owned_cpus.wf(),
        post.cpu_offline_mp.perms_wf(),
        post.cpu_offline_mp.spec_index(flags_ptr).inv(),
    ensures
        post.inv(),
        post.cpu_arr.spec_index(cpu_id).view().view().view().state is Off,
        forall|other_cpu: CpuId| #![trigger post.cpu_arr.spec_index(other_cpu)]
            index_valid(NUM_CPUS, other_cpu) && other_cpu != cpu_id ==> post.cpu_arr.spec_index(other_cpu) == pre.cpu_arr.spec_index(other_cpu),
{
    reveal(cpu_went_off_eof_transition_framing);
    cpu_went_off_eof_subsystems_inv(pre, post, cpu_id, ctn_ptr, sched_ptr, cpu_set_ptr, flags_ptr, entry_regs);
    cpu_went_off_eof_memory_management_inv(pre, post, cpu_id, ctn_ptr, sched_ptr, cpu_set_ptr, flags_ptr, entry_regs);
    cpu_went_off_eof_process_management_inv(pre, post, cpu_id, ctn_ptr, sched_ptr, cpu_set_ptr, flags_ptr, entry_regs);
    cpu_went_off_eof_tlb(pre, post, cpu_id, ctn_ptr, sched_ptr, cpu_set_ptr, flags_ptr, entry_regs);
}

/// The committed offline, between the lock acquisitions that follow the check's start `snapshot` and the releases and the
/// exit from the kernel step as Off that end the step, gives the went-off fields from `snapshot`.
pub(super) proof fn cpu_went_off_eof_fields(
    snapshot: KernelK, entry: KernelK, pre: KernelK, mid: KernelK, post: KernelK, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, sched_ptr: RwLockSchedulerPtr,
    cpu_set_ptr: RwLockCpuSetPtr, flags_ptr: RwLockCpuOfflineFlagsPtr, current_process: Option<RwLockProcessPtr>, current_thread: Option<RwLockThreadPtr>, entry_regs: Registers,
)
    requires
        entry.inv(),
        mid.cpu_tlb.inv(),
        entry == (KernelK {
            cpu_arr: entry.cpu_arr, prc_mp: entry.prc_mp, thrd_mp: entry.thrd_mp, sched_mp: entry.sched_mp, cpu_set_mp: entry.cpu_set_mp, cpu_offline_mp: entry.cpu_offline_mp, ..snapshot
        }),
        entry.cpu_arr.unchanged_except(&snapshot.cpu_arr, cpu_id),
        forall|p: RwLockProcessPtr| #![trigger entry.prc_mp.spec_index(p)]
            snapshot.prc_mp.dom().contains(p) ==> if current_process == Some(p) {
                snapshot.prc_mp.spec_index(p).locking_thread() is None
            } else { entry.prc_mp.spec_index(p).locking_thread() == snapshot.prc_mp.spec_index(p).locking_thread() },
        forall|t: RwLockThreadPtr| #![trigger entry.thrd_mp.spec_index(t)]
            snapshot.thrd_mp.dom().contains(t) ==> if current_thread == Some(t) {
                snapshot.thrd_mp.spec_index(t).locking_thread() is None
            } else { entry.thrd_mp.spec_index(t).locking_thread() == snapshot.thrd_mp.spec_index(t).locking_thread() },
        entry.sched_mp.unchanged_except(&snapshot.sched_mp, sched_ptr),
        entry.cpu_set_mp.unchanged_except(&snapshot.cpu_set_mp, cpu_set_ptr),
        snapshot.cpu_set_mp.spec_index(cpu_set_ptr).locking_thread() is None,
        !snapshot.cpu_set_mp.spec_index(cpu_set_ptr).being_killed() && !entry.cpu_set_mp.spec_index(cpu_set_ptr).being_killed(),
        entry.cpu_offline_mp.unchanged_except(&snapshot.cpu_offline_mp, flags_ptr),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&snapshot, &entry),
        kernel_endpoint_nonlock_fields_unchanged(snapshot.ep_mp, entry.ep_mp),
        entry.irt.view().owners() == snapshot.irt.view().owners(),
        entry.irt.view().iommu_roots() == snapshot.irt.view().iommu_roots(),
        entry.cpu_tlb.view() == snapshot.cpu_tlb.view(),
        entry.iommu_tlb.view() == snapshot.iommu_tlb.view(),
        scheduler_shards_of(entry.sched_mp.spec_index(sched_ptr)) == scheduler_shards_of(snapshot.sched_mp.spec_index(sched_ptr)),
        cpu_offline_requests_of(entry.cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(snapshot.cpu_offline_mp.spec_index(flags_ptr)),
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = entry.cpu_arr.spec_index(cpu_id).view().view().view();
            &&& !(cpu.state is Off)
            &&& cpu.current_process == current_process
            &&& cpu.current_thread == current_thread
            &&& cpu.owning_container == ctn_ptr
            &&& entry.ctn_mp.dom().contains(ctn_ptr)
            &&& entry.ctn_mp.spec_index(ctn_ptr).view_rodata().view().scheduler == sched_ptr
            &&& entry.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set == cpu_set_ptr
            &&& flags_ptr == cpu_offline_flags_ptr(ctn_ptr)
        },
        current_process is Some == current_thread is Some,
        entry.sched_mp.dom().contains(sched_ptr),
        entry.cpu_set_mp.dom().contains(cpu_set_ptr),
        entry.cpu_offline_mp.dom().contains(flags_ptr),
        entry.cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().view().requested,
        current_process is Some ==> entry.prc_mp.dom().contains(current_process.unwrap()) && !entry.prc_mp.spec_index(current_process.unwrap()).being_killed(),
        current_thread is Some ==> {
            let thread = entry.thrd_mp.spec_index(current_thread.unwrap());
            &&& entry.thrd_mp.dom().contains(current_thread.unwrap())
            &&& !thread.being_killed()
            &&& thread.view().state == (ThreadState::RUNNING { cpu_id })
            &&& thread.view().owning_proc == current_process.unwrap()
        },
        pre == (KernelK { pcid_needflush: pre.pcid_needflush, ..entry }),
        pre.pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).view() == entry.pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).view(),
        cpu_went_off_eof_transition_framing(pre, mid, cpu_id, ctn_ptr, sched_ptr, cpu_set_ptr, flags_ptr, entry_regs),
        post == (KernelK {
            cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, prc_mp: post.prc_mp, thrd_mp: post.thrd_mp, sched_mp: post.sched_mp, cpu_set_mp: post.cpu_set_mp,
            cpu_offline_mp: post.cpu_offline_mp, pcid_needflush: post.pcid_needflush, ..mid
        }),
        post.cpu_op.view().view() == mid.cpu_op.view().view().update(cpu_id as int, CpuOpState::Off),
        post.cpu_arr.entries_unchanged_except(&mid.cpu_arr, cpu_id),
        post.cpu_arr.spec_index(cpu_id).view().view().view() == mid.cpu_arr.spec_index(cpu_id).view().view().view(),
        post.cpu_arr.spec_index(cpu_id).view().locking_thread() is None,
        post.cpu_arr.spec_index(cpu_id).view().killer_info() == mid.cpu_arr.spec_index(cpu_id).view().killer_info(),
        current_process is Some ==> post.prc_mp.unchanged_except(&mid.prc_mp, current_process.unwrap()) && wunlock_ensures(mid.prc_mp.spec_index(current_process.unwrap()), post.prc_mp.spec_index(current_process.unwrap())),
        current_process is None ==> post.prc_mp == mid.prc_mp,
        current_thread is Some ==> post.thrd_mp.unchanged_except(&mid.thrd_mp, current_thread.unwrap()) && wunlock_ensures(mid.thrd_mp.spec_index(current_thread.unwrap()), post.thrd_mp.spec_index(current_thread.unwrap())),
        current_thread is None ==> post.thrd_mp == mid.thrd_mp,
        post.sched_mp.unchanged_except(&mid.sched_mp, sched_ptr),
        scheduler_shards_of(post.sched_mp.spec_index(sched_ptr)) == scheduler_shards_of(mid.sched_mp.spec_index(sched_ptr)),
        post.cpu_set_mp.unchanged_except(&mid.cpu_set_mp, cpu_set_ptr),
        wunlock_ensures(mid.cpu_set_mp.spec_index(cpu_set_ptr), post.cpu_set_mp.spec_index(cpu_set_ptr)),
        post.cpu_offline_mp.unchanged_except(&mid.cpu_offline_mp, flags_ptr),
        cpu_offline_requests_of(post.cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(mid.cpu_offline_mp.spec_index(flags_ptr)),
    ensures
        kernel_cpu_went_off_fields(&snapshot, &post, cpu_id, entry_regs, cpu_offline_check_flushed_default_pcid(entry, cpu_id)),
        post.ctn_mp == snapshot.ctn_mp,
{
    reveal(cpu_went_off_eof_transition_framing);
    assert(mid.cpu_tlb.view() == cpu_tlb_after_cpu_went_off(pre.cpu_tlb.view(), cpu_id, cpu_offline_check_flushed_default_pcid(pre, cpu_id))) by {
        reveal(CpuTLB::inv);
        vstd::assert_maps_equal!(mid.cpu_tlb.view(), cpu_tlb_after_cpu_went_off(pre.cpu_tlb.view(), cpu_id, cpu_offline_check_flushed_default_pcid(pre, cpu_id)), key => {
            let tlb = mid.cpu_tlb.spec_index((key.0, key.1));
            if mid.cpu_tlb.view().dom().contains((key.0, key.1)) && key.0 == cpu_id && (key.1 != KERNEL_DEFAULT_PCID || cpu_offline_check_flushed_default_pcid(pre, cpu_id)) {
                assert(tlb.tlb_4k =~= Map::empty() && tlb.tlb_2m =~= Map::empty() && tlb.tlb_1g =~= Map::empty());
            }
        });
    };
    assert(scheduler_shards_of(mid.sched_mp.spec_index(sched_ptr)) =~= match current_thread {
        Some(prev) => scheduler_shards_of(pre.sched_mp.spec_index(sched_ptr)).update(cpu_id as int, scheduler_shards_of(pre.sched_mp.spec_index(sched_ptr))[cpu_id as int].push(prev)),
        None => scheduler_shards_of(pre.sched_mp.spec_index(sched_ptr)),
    }) by { reveal(scheduler_shards_of); };
    reveal(kernel_cpu_went_off_fields); reveal(container_scheduler_wf); reveal(container_cpu_offline_flags_wf); reveal(cpu_offline_requests_of);
    reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
}
}
