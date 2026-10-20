use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_schedule_spec::scheduler_context_switch_eof_transition_framing;

verus! {
proof fn scheduler_context_switch_eof_container_thread_scheduler(pre: KernelK, post: KernelK, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr, next_thread: RwLockThreadPtr, entry_regs: Registers)
    requires
        pre.inv(),
        scheduler_context_switch_eof_transition_framing(pre, post, cpu_id, scheduler_ptr, next_thread, entry_regs),
        ({
            let old_cpu = pre.cpu_arr.spec_index(cpu_id).view().view().view();
            let queue_before = pre.sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().view().queue;
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& pre.thr_mp.dom().contains(next_thread)
            &&& pre.sched_mp.dom().contains(scheduler_ptr)
            &&& pre.ctn_mp.dom().contains(old_cpu.owning_container)
            &&& pre.thr_mp.spec_index(next_thread).view().state is SCHEDULED
            &&& pre.sched_mp.spec_index(scheduler_ptr).owning_container == old_cpu.owning_container
            &&& pre.thr_mp.spec_index(next_thread).view().owning_container == old_cpu.owning_container
            &&& pre.ctn_mp.spec_index(old_cpu.owning_container).view_rodata().view().scheduler == scheduler_ptr
            &&& queue_before.view().len() > 0
            &&& queue_before.view()[0] == next_thread
            &&& (old_cpu.current_thread is Some ==> {
                let prev = old_cpu.current_thread.unwrap();
                &&& prev != next_thread
                &&& pre.thr_mp.dom().contains(prev)
                &&& pre.thr_mp.spec_index(prev).view().state == (ThreadState::RUNNING { cpu_id })
                &&& !queue_before.map().remove(pre.thr_mp.spec_index(next_thread).view().scheduler_linkedlist_node.addr()).dom().contains(pre.thr_mp.spec_index(prev).view().scheduler_linkedlist_node.addr())
            })
        }),
        post.subsystems_inv(),
    ensures container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp),
{
    reveal(scheduler_context_switch_eof_transition_framing);
    assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by {
        let cpu = pre.cpu_arr.spec_index(cpu_id).view().view().view();
        assert(cpu.current_thread is Some ==> pre.thr_mp.spec_index(cpu.current_thread.unwrap()).view().owning_container == cpu.owning_container) by {
            cpu_array_wf_at(pre.cpu_arr, pre.dflt_pt.view(), cpu_id); thread_cpu_wf_cpu_at(pre.thr_mp, pre.cpu_arr, cpu_id); process_cpu_wf_at(pre.prc_mp, pre.cpu_arr, cpu_id);
            if cpu.current_thread is Some { process_thread_wf_at(pre.prc_mp, pre.thr_mp, cpu.current_thread.unwrap()); }
        };
        assert(pre.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view().no_duplicates()) by { scheduler_perms_wf_at(pre.sched_mp, scheduler_ptr); reveal(LinkedList::value_list_unique); reveal(LinkedList::wf_value_list); };
        reveal(container_thread_scheduler_wf); reveal(container_scheduler_wf); reveal(container_thread_wf);
        seq_push_lemma::<RwLockThreadPtr>(); seq_skip_lemma::<RwLockThreadPtr>();
    };
}

/// The cpu relations close after the switch.
proof fn scheduler_context_switch_eof_cpu_wf(pre: KernelK, post: KernelK, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr, next_thread: RwLockThreadPtr, entry_regs: Registers)
    requires
        pre.inv(),
        scheduler_context_switch_eof_transition_framing(pre, post, cpu_id, scheduler_ptr, next_thread, entry_regs),
        ({
            let old_cpu = pre.cpu_arr.spec_index(cpu_id).view().view().view();
            let next_process = pre.thr_mp.spec_index(next_thread).view().owning_proc;
            let queue_before = pre.sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().view().queue;
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& !(old_cpu.state is Off)
            &&& !pre.cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& pre.thr_mp.dom().contains(next_thread)
            &&& pre.prc_mp.dom().contains(next_process)
            &&& pre.sched_mp.dom().contains(scheduler_ptr)
            &&& pre.ctn_mp.dom().contains(old_cpu.owning_container)
            &&& pre.thr_mp.spec_index(next_thread).view().state is SCHEDULED
            &&& pre.sched_mp.spec_index(scheduler_ptr).owning_container == old_cpu.owning_container
            &&& pre.thr_mp.spec_index(next_thread).view().owning_container == old_cpu.owning_container
            &&& pre.ctn_mp.spec_index(old_cpu.owning_container).view_rodata().view().scheduler == scheduler_ptr
            &&& queue_before.view().len() > 0
            &&& queue_before.view()[0] == next_thread
            &&& (old_cpu.current_thread is Some ==> {
                let prev = old_cpu.current_thread.unwrap();
                &&& prev != next_thread
                &&& pre.thr_mp.dom().contains(prev)
                &&& pre.thr_mp.spec_index(prev).view().state == (ThreadState::RUNNING { cpu_id })
                &&& !queue_before.map().remove(pre.thr_mp.spec_index(next_thread).view().scheduler_linkedlist_node.addr()).dom().contains(pre.thr_mp.spec_index(prev).view().scheduler_linkedlist_node.addr())
            })
        }),
        post.subsystems_inv(),
    ensures
        container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr),
        process_cpu_wf(post.prc_mp, post.cpu_arr),
        thread_cpu_wf(post.thr_mp, post.cpu_arr),
{
    reveal(scheduler_context_switch_eof_transition_framing);
    assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); reveal(container_thread_wf); reveal(container_process_wf); reveal(process_thread_wf); };
    assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); reveal(process_pagetable_match); reveal(process_thread_wf); };
    assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { reveal(thread_cpu_wf); };
}

/// The endpoint, call-link, and dangling-chain relations close after the switch.
proof fn scheduler_context_switch_eof_endpoint_wf(pre: KernelK, post: KernelK, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr, next_thread: RwLockThreadPtr, entry_regs: Registers)
    requires
        pre.inv(),
        scheduler_context_switch_eof_transition_framing(pre, post, cpu_id, scheduler_ptr, next_thread, entry_regs),
        ({
            let old_cpu = pre.cpu_arr.spec_index(cpu_id).view().view().view();
            let next_process = pre.thr_mp.spec_index(next_thread).view().owning_proc;
            let queue_before = pre.sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().view().queue;
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& !(old_cpu.state is Off)
            &&& !pre.cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& pre.thr_mp.dom().contains(next_thread)
            &&& pre.prc_mp.dom().contains(next_process)
            &&& pre.sched_mp.dom().contains(scheduler_ptr)
            &&& pre.ctn_mp.dom().contains(old_cpu.owning_container)
            &&& pre.thr_mp.spec_index(next_thread).view().state is SCHEDULED
            &&& pre.sched_mp.spec_index(scheduler_ptr).owning_container == old_cpu.owning_container
            &&& pre.thr_mp.spec_index(next_thread).view().owning_container == old_cpu.owning_container
            &&& pre.ctn_mp.spec_index(old_cpu.owning_container).view_rodata().view().scheduler == scheduler_ptr
            &&& queue_before.view().len() > 0
            &&& queue_before.view()[0] == next_thread
            &&& (old_cpu.current_thread is Some ==> {
                let prev = old_cpu.current_thread.unwrap();
                &&& prev != next_thread
                &&& pre.thr_mp.dom().contains(prev)
                &&& pre.thr_mp.spec_index(prev).view().state == (ThreadState::RUNNING { cpu_id })
                &&& !queue_before.map().remove(pre.thr_mp.spec_index(next_thread).view().scheduler_linkedlist_node.addr()).dom().contains(pre.thr_mp.spec_index(prev).view().scheduler_linkedlist_node.addr())
            })
        }),
        post.subsystems_inv(),
    ensures
        thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp),
        thread_endpoint_queue_wf(post.thr_mp, post.ep_mp),
        container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp),
        thread_caller_callee_wf(post.thr_mp),
        thread_dangling_chain_end_wf(post.thr_mp),
{
    reveal(scheduler_context_switch_eof_transition_framing);
    assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_descriptor_eq(pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
    assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_endpoint_waiting_eq(pre.thr_mp, post.thr_mp, post.ep_mp); };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
    assert(thread_caller_callee_wf(post.thr_mp)) by { thread_caller_callee_wf_preserved_for_call_link_eq(pre.thr_mp, post.thr_mp); };
    assert(thread_dangling_chain_end_wf(post.thr_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thr_mp, post.thr_mp); };
}

#[verifier::spinoff_prover]
proof fn scheduler_context_switch_eof_process_management_inv(pre: KernelK, post: KernelK, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr, next_thread: RwLockThreadPtr, entry_regs: Registers)
    requires
        pre.inv(),
        scheduler_context_switch_eof_transition_framing(pre, post, cpu_id, scheduler_ptr, next_thread, entry_regs),
        ({
            let old_cpu = pre.cpu_arr.spec_index(cpu_id).view().view().view();
            let next_process = pre.thr_mp.spec_index(next_thread).view().owning_proc;
            let queue_before = pre.sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().view().queue;
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& !(old_cpu.state is Off)
            &&& !pre.cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& pre.thr_mp.dom().contains(next_thread)
            &&& pre.prc_mp.dom().contains(next_process)
            &&& pre.sched_mp.dom().contains(scheduler_ptr)
            &&& pre.ctn_mp.dom().contains(old_cpu.owning_container)
            &&& pre.thr_mp.spec_index(next_thread).view().state is SCHEDULED
            &&& pre.sched_mp.spec_index(scheduler_ptr).owning_container == old_cpu.owning_container
            &&& pre.thr_mp.spec_index(next_thread).view().owning_container == old_cpu.owning_container
            &&& pre.ctn_mp.spec_index(old_cpu.owning_container).view_rodata().view().scheduler == scheduler_ptr
            &&& queue_before.view().len() > 0
            &&& queue_before.view()[0] == next_thread
            &&& (old_cpu.current_thread is Some ==> {
                let prev = old_cpu.current_thread.unwrap();
                &&& prev != next_thread
                &&& pre.thr_mp.dom().contains(prev)
                &&& pre.thr_mp.spec_index(prev).view().state == (ThreadState::RUNNING { cpu_id })
                &&& !queue_before.map().remove(pre.thr_mp.spec_index(next_thread).view().scheduler_linkedlist_node.addr()).dom().contains(pre.thr_mp.spec_index(prev).view().scheduler_linkedlist_node.addr())
            })
        }),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(scheduler_context_switch_eof_transition_framing);
    scheduler_context_switch_eof_container_thread_scheduler(pre, post, cpu_id, scheduler_ptr, next_thread, entry_regs);
    scheduler_context_switch_eof_cpu_wf(pre, post, cpu_id, scheduler_ptr, next_thread, entry_regs);
    scheduler_context_switch_eof_endpoint_wf(pre, post, cpu_id, scheduler_ptr, next_thread, entry_regs);
    assert(post.process_management_inv()) by {
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { container_thread_wf_preserved_for_container_thread_link_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { process_thread_wf_preserved_for_process_thread_link_eq(pre.prc_mp, post.prc_mp, pre.thr_mp, post.thr_mp); };
        assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { container_scheduler_wf_preserved_for_scheduler_owner_eq(pre.ctn_mp, post.ctn_mp, pre.sched_mp, post.sched_mp); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
    };
}

pub(super) proof fn scheduler_context_switch_eof_subsystems(pre: KernelK, post: KernelK, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr, next_thread: RwLockThreadPtr, entry_regs: Registers)
    requires
        pre.inv(),
        scheduler_context_switch_eof_transition_framing(pre, post, cpu_id, scheduler_ptr, next_thread, entry_regs),
        ({
            let old_cpu = pre.cpu_arr.spec_index(cpu_id).view().view().view();
            let next_process = pre.thr_mp.spec_index(next_thread).view().owning_proc;
            let queue_before = pre.sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().view().queue;
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& !(old_cpu.state is Off)
            &&& !pre.cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& pre.thr_mp.dom().contains(next_thread)
            &&& pre.prc_mp.dom().contains(next_process)
            &&& pre.sched_mp.dom().contains(scheduler_ptr)
            &&& pcid_valid(pre.prc_mp.spec_index(next_process).view_rodata().view().pcid)
            &&& pre.thr_mp.spec_index(next_thread).view().state is SCHEDULED
            &&& queue_before.view().len() > 0
            &&& queue_before.view()[0] == next_thread
            &&& (old_cpu.current_thread is Some ==> {
                let prev = old_cpu.current_thread.unwrap();
                &&& prev != next_thread
                &&& pre.thr_mp.dom().contains(prev)
                &&& pre.thr_mp.spec_index(prev).view().state == (ThreadState::RUNNING { cpu_id })
                &&& !queue_before.map().remove(pre.thr_mp.spec_index(next_thread).view().scheduler_linkedlist_node.addr()).dom().contains(pre.thr_mp.spec_index(prev).view().scheduler_linkedlist_node.addr())
            })
        }),
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        post.cpu_published[cpu_id as int].inv(),
        post.cpu_arr.spec_index(cpu_id).view().view().view().tlb_dirty_bitmap.inv(),
        post.sched_mp.perms_wf(),
        post.sched_mp.spec_index(scheduler_ptr).shards.inv(),
        post.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.wf(),
    ensures
        post.subsystems_inv(),
{
    hide(Seq::contains);
    reveal(scheduler_context_switch_eof_transition_framing);
    assert(post.subsystems_inv()) by {
        assert(cpu_array_wf(post.cpu_arr, post.dflt_pt.view())) by { reveal(cpu_array_wf); };
        assert(thread_perms_wf(post.thr_mp)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked); };
        assert(scheduler_perms_wf(post.sched_mp)) by { reveal(scheduler_perms_wf); };
        assert(pcid_needflush_wf(post.pcid_needflush)) by { reveal(pcid_needflush_wf); };
        assert(cpu_published_wf(post.cpu_published, post.cpu_arr, post.pcid_needflush)) by { reveal(process_thread_wf); reveal(process_pagetable_match); reveal(pagetable_perms_wf); reveal(PageTable::table_pages_wf); reveal(cpu_published_wf); };
        assert(cpu_offline_flags_wf(post.cpu_offline_mp, post.cpu_arr)) by { cpu_offline_flags_wf_preserved_for_cpu_owner_eq(post.cpu_offline_mp, pre.cpu_arr, post.cpu_arr); };
        reveal(KernelK::default_pagetable_wf);
    };
}

pub(super) proof fn scheduler_context_switch_eof_memory(pre: KernelK, post: KernelK, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr, next_thread: RwLockThreadPtr, entry_regs: Registers)
    requires
        pre.inv(),
        scheduler_context_switch_eof_transition_framing(pre, post, cpu_id, scheduler_ptr, next_thread, entry_regs),
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        post.cpu_published[cpu_id as int].inv(),
        post.cpu_arr.spec_index(cpu_id).view().view().view().tlb_dirty_bitmap.inv(),
        post.sched_mp.perms_wf(),
        post.sched_mp.spec_index(scheduler_ptr).shards.inv(),
        post.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.wf(),
    ensures
        post.memory_management_inv(),
{
    hide(Seq::contains);
    reveal(scheduler_context_switch_eof_transition_framing);
    assert(post.memory_management_inv()) by {
        assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
        assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp)) by { reveal(page_object_owner_wf); reveal(container_page_owner_wf); };
        thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_4k_mp);
        container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_2m_mp);
        container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_1g_mp);
    };
}

pub(super) proof fn scheduler_context_switch_eof(pre: KernelK, post: KernelK, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr, next_thread: RwLockThreadPtr, entry_regs: Registers)
    requires
        pre.inv(),
        scheduler_context_switch_eof_transition_framing(pre, post, cpu_id, scheduler_ptr, next_thread, entry_regs),
        ({
            let old_cpu = pre.cpu_arr.spec_index(cpu_id).view().view().view();
            let next_process = pre.thr_mp.spec_index(next_thread).view().owning_proc;
            let queue_before = pre.sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().view().queue;
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& !(old_cpu.state is Off)
            &&& !pre.cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& pre.thr_mp.dom().contains(next_thread)
            &&& pre.prc_mp.dom().contains(next_process)
            &&& pre.sched_mp.dom().contains(scheduler_ptr)
            &&& pre.ctn_mp.dom().contains(old_cpu.owning_container)
            &&& pcid_valid(pre.prc_mp.spec_index(next_process).view_rodata().view().pcid)
            &&& pre.thr_mp.spec_index(next_thread).view().state is SCHEDULED
            &&& pre.sched_mp.spec_index(scheduler_ptr).owning_container == old_cpu.owning_container
            &&& pre.thr_mp.spec_index(next_thread).view().owning_container == old_cpu.owning_container
            &&& pre.ctn_mp.spec_index(old_cpu.owning_container).view_rodata().view().scheduler == scheduler_ptr
            &&& queue_before.view().len() > 0
            &&& queue_before.view()[0] == next_thread
            &&& (old_cpu.current_thread is Some ==> {
                let prev = old_cpu.current_thread.unwrap();
                &&& prev != next_thread
                &&& pre.thr_mp.dom().contains(prev)
                &&& pre.thr_mp.spec_index(prev).view().state == (ThreadState::RUNNING { cpu_id })
                &&& !queue_before.map().remove(pre.thr_mp.spec_index(next_thread).view().scheduler_linkedlist_node.addr()).dom().contains(pre.thr_mp.spec_index(prev).view().scheduler_linkedlist_node.addr())
            })
        }),
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        post.cpu_published[cpu_id as int].inv(),
        post.cpu_arr.spec_index(cpu_id).view().view().view().tlb_dirty_bitmap.inv(),
        post.sched_mp.perms_wf(),
        post.sched_mp.spec_index(scheduler_ptr).shards.inv(),
        post.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.wf(),
    ensures
        post.inv(),
        post.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        post.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(pre.thr_mp.spec_index(next_thread).view().owning_proc),
        post.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(next_thread),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread != Some(next_thread),
        post.thr_mp.spec_index(next_thread).view().state == (ThreadState::RUNNING { cpu_id }),
        post.thr_mp.spec_index(next_thread).view().error_code is None,
        scheduler_shards_of(post.sched_mp.spec_index(scheduler_ptr)) == scheduler_shards_of(pre.sched_mp.spec_index(scheduler_ptr)).update(cpu_id as int,
            match pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread {
                Some(previous) => pre.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view().skip(1).push(previous),
                None => pre.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view().skip(1),
            }),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread is Some ==> {
            let previous = pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap();
            &&& post.thr_mp.spec_index(previous).view().state == (ThreadState::SCHEDULED { cpu_id })
            &&& *post.thr_mp.spec_index(previous).view().trap_frame.get_some_0() == entry_regs
        },
        forall|other_cpu: CpuId| #![trigger post.cpu_arr.spec_index(other_cpu)]
            index_valid(NUM_CPUS, other_cpu) && other_cpu != cpu_id ==> post.cpu_arr.spec_index(other_cpu) == pre.cpu_arr.spec_index(other_cpu),
{
    hide(Seq::contains);
    reveal(scheduler_context_switch_eof_transition_framing);
    scheduler_context_switch_eof_subsystems(pre, post, cpu_id, scheduler_ptr, next_thread, entry_regs);
    scheduler_context_switch_eof_memory(pre, post, cpu_id, scheduler_ptr, next_thread, entry_regs);
    assert(scheduler_shards_of(post.sched_mp.spec_index(scheduler_ptr)) =~= scheduler_shards_of(pre.sched_mp.spec_index(scheduler_ptr)).update(cpu_id as int,
        match pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread {
            Some(previous) => pre.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view().skip(1).push(previous),
            None => pre.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view().skip(1),
        })) by { reveal(scheduler_shards_of); };
    scheduler_context_switch_eof_process_management_inv(pre, post, cpu_id, scheduler_ptr, next_thread, entry_regs);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
        reveal(process_pagetable_match); reveal(container_process_wf); reveal(process_thread_wf);
    };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}
}
