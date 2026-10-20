use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_call_spec::*;

verus! {
/// The cpu and emptied-thread relations close after the transition.
proof fn ipc_call_handoff_eof_cpu_wf(pre: KernelK, post: KernelK, cpu_id: CpuId, caller_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, callee_ptr: RwLockThreadPtr, entry_regs: Registers)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        caller_ptr != callee_ptr,
        pre.thr_mp.dom().contains(caller_ptr),
        pre.thr_mp.dom().contains(callee_ptr),
        !pre.thr_mp.spec_index(caller_ptr).being_killed(),
        pre.prc_mp.dom().contains(pre.thr_mp.spec_index(callee_ptr).view().owning_proc),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.ctn_mp.dom().contains(pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
        pcid_valid(pre.prc_mp.spec_index(pre.thr_mp.spec_index(callee_ptr).view().owning_proc).view_rodata().view().pcid),
        !pre.cpu_arr.spec_index(cpu_id).view().being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(caller_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(pre.thr_mp.spec_index(caller_ptr).view().owning_proc),
        pre.thr_mp.spec_index(caller_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(caller_ptr).view().callee is None,
        pre.thr_mp.spec_index(caller_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.thr_mp.spec_index(caller_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        pre.thr_mp.spec_index(callee_ptr).view().state is RECEIVING_CALL,
        pre.thr_mp.spec_index(callee_ptr).view().caller is None,
        pre.thr_mp.spec_index(callee_ptr).view().callee is None,
        pre.thr_mp.spec_index(callee_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        pre.thr_mp.spec_index(callee_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() > 0,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view()[0] == callee_ptr,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue_state is RECEIVE,
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(caller_ptr),
        ipc_call_handoff_eof_transition_framing(pre, post, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, entry_regs),
        post.subsystems_inv(),
    ensures
        process_emptied_threads_wf(post.prc_mp, post.thr_mp),
        container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr),
        process_cpu_wf(post.prc_mp, post.cpu_arr),
        thread_cpu_wf(post.thr_mp, post.cpu_arr),
{
    reveal(ipc_call_handoff_eof_transition_framing);
    assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
    assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); reveal(container_thread_wf); reveal(container_process_wf); reveal(process_thread_wf); };
    assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); reveal(process_pagetable_match); reveal(process_thread_wf); };
    assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { reveal(thread_cpu_wf); };
}

/// The endpoint queue, descriptor, reference-counter, and call-link relations close after the transition.
proof fn ipc_call_handoff_eof_endpoint_wf(pre: KernelK, post: KernelK, cpu_id: CpuId, caller_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, callee_ptr: RwLockThreadPtr, entry_regs: Registers)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        caller_ptr != callee_ptr,
        pre.thr_mp.dom().contains(caller_ptr),
        pre.thr_mp.dom().contains(callee_ptr),
        !pre.thr_mp.spec_index(caller_ptr).being_killed(),
        pre.prc_mp.dom().contains(pre.thr_mp.spec_index(callee_ptr).view().owning_proc),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.ctn_mp.dom().contains(pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
        pcid_valid(pre.prc_mp.spec_index(pre.thr_mp.spec_index(callee_ptr).view().owning_proc).view_rodata().view().pcid),
        !pre.cpu_arr.spec_index(cpu_id).view().being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(caller_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(pre.thr_mp.spec_index(caller_ptr).view().owning_proc),
        pre.thr_mp.spec_index(caller_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(caller_ptr).view().callee is None,
        pre.thr_mp.spec_index(caller_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.thr_mp.spec_index(caller_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        pre.thr_mp.spec_index(callee_ptr).view().state is RECEIVING_CALL,
        pre.thr_mp.spec_index(callee_ptr).view().caller is None,
        pre.thr_mp.spec_index(callee_ptr).view().callee is None,
        pre.thr_mp.spec_index(callee_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        pre.thr_mp.spec_index(callee_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() > 0,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view()[0] == callee_ptr,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue_state is RECEIVE,
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(caller_ptr),
        ipc_call_handoff_eof_transition_framing(pre, post, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, entry_regs),
        post.subsystems_inv(),
    ensures
        thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp),
        thread_endpoint_queue_wf(post.thr_mp, post.ep_mp),
        container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp),
        container_endpoint_wf(post.ctn_mp, post.ep_mp),
        thread_caller_callee_wf(post.thr_mp),
{
    reveal(ipc_call_handoff_eof_transition_framing);
    assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_descriptor_eq(pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
    assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { seq_skip_lemma::<RwLockThreadPtr>(); reveal(endpoint_perms_wf); reveal(LinkedList::wf_value_list); reveal(LinkedList::value_list_unique); reveal(thread_endpoint_queue_wf); };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
    assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { container_endpoint_wf_preserved_for_endpoint_owner_eq(pre.ctn_mp, post.ctn_mp, pre.ep_mp, post.ep_mp); };
    assert(thread_caller_callee_wf(post.thr_mp)) by { reveal(thread_caller_callee_wf); };
}

#[verifier::spinoff_prover]
proof fn ipc_call_handoff_eof_process_management_inv(pre: KernelK, post: KernelK, cpu_id: CpuId, caller_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, callee_ptr: RwLockThreadPtr, entry_regs: Registers)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        caller_ptr != callee_ptr,
        pre.thr_mp.dom().contains(caller_ptr),
        pre.thr_mp.dom().contains(callee_ptr),
        !pre.thr_mp.spec_index(caller_ptr).being_killed(),
        pre.prc_mp.dom().contains(pre.thr_mp.spec_index(callee_ptr).view().owning_proc),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.ctn_mp.dom().contains(pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
        pcid_valid(pre.prc_mp.spec_index(pre.thr_mp.spec_index(callee_ptr).view().owning_proc).view_rodata().view().pcid),
        !pre.cpu_arr.spec_index(cpu_id).view().being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(caller_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(pre.thr_mp.spec_index(caller_ptr).view().owning_proc),
        pre.thr_mp.spec_index(caller_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(caller_ptr).view().callee is None,
        pre.thr_mp.spec_index(caller_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.thr_mp.spec_index(caller_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        pre.thr_mp.spec_index(callee_ptr).view().state is RECEIVING_CALL,
        pre.thr_mp.spec_index(callee_ptr).view().caller is None,
        pre.thr_mp.spec_index(callee_ptr).view().callee is None,
        pre.thr_mp.spec_index(callee_ptr).locking_thread() is Write,
        forall|u: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(u).locking_thread()]
            pre.thr_mp.dom().contains(u) && pre.thr_mp.spec_index(u).wlocked_by_thread(pre.thr_mp.spec_index(callee_ptr).locking_thread()->Write_thread_id) ==> u == caller_ptr || u == callee_ptr,
        pre.thr_mp.spec_index(callee_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        pre.thr_mp.spec_index(callee_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() > 0,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view()[0] == callee_ptr,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue_state is RECEIVE,
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(caller_ptr),
        ipc_call_handoff_eof_transition_framing(pre, post, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, entry_regs),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(ipc_call_handoff_eof_transition_framing);
    ipc_call_handoff_eof_cpu_wf(pre, post, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, entry_regs);
    ipc_call_handoff_eof_endpoint_wf(pre, post, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, entry_regs);
    assert(post.process_management_inv()) by {
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { container_thread_wf_preserved_for_container_thread_link_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { process_thread_wf_preserved_for_process_thread_link_eq(pre.prc_mp, post.prc_mp, pre.thr_mp, post.thr_mp); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { container_thread_scheduler_wf_preserved_for_scheduled_thread_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp); reveal(container_scheduler_wf); reveal(container_thread_wf); };
        assert(thread_dangling_chain_end_wf(post.thr_mp)) by {
            thread_dangling_chain_end_on_caller_chain(pre.thr_mp, callee_ptr, Set::<RwLockThreadPtr>::empty(), pre.thr_mp.spec_index(callee_ptr).view().call_depth.view());
            reveal(thread_dangling_chain_end_wf); reveal(thread_caller_callee_wf);
        };
    };
}

/// Closes every invariant after the call handoff from the entry invariants, the summary, and the
/// representation facts produced by the switch and the dequeue.
pub(super) proof fn ipc_call_handoff_eof_subsystems(pre: KernelK, post: KernelK, cpu_id: CpuId, caller_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, callee_ptr: RwLockThreadPtr, entry_regs: Registers)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        caller_ptr != callee_ptr,
        pre.thr_mp.dom().contains(caller_ptr),
        pre.thr_mp.dom().contains(callee_ptr),
        !pre.thr_mp.spec_index(caller_ptr).being_killed(),
        pre.prc_mp.dom().contains(pre.thr_mp.spec_index(callee_ptr).view().owning_proc),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.ctn_mp.dom().contains(pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
        pcid_valid(pre.prc_mp.spec_index(pre.thr_mp.spec_index(callee_ptr).view().owning_proc).view_rodata().view().pcid),
        !pre.cpu_arr.spec_index(cpu_id).view().being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(caller_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(pre.thr_mp.spec_index(caller_ptr).view().owning_proc),
        pre.thr_mp.spec_index(caller_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(caller_ptr).view().callee is None,
        pre.thr_mp.spec_index(caller_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.thr_mp.spec_index(caller_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        pre.thr_mp.spec_index(callee_ptr).view().state is RECEIVING_CALL,
        pre.thr_mp.spec_index(callee_ptr).view().caller is None,
        pre.thr_mp.spec_index(callee_ptr).view().callee is None,
        pre.thr_mp.spec_index(callee_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        pre.thr_mp.spec_index(callee_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() > 0,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view()[0] == callee_ptr,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue_state is RECEIVE,
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(caller_ptr),
        ipc_call_handoff_eof_transition_framing(pre, post, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, entry_regs),
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        post.cpu_published[cpu_id as int].inv(),
        post.cpu_arr.spec_index(cpu_id).view().view().view().tlb_dirty_bitmap.inv(),
        endpoint_perms_wf(post.ep_mp),
    ensures
        post.subsystems_inv(),
{
    hide(Seq::contains);
    reveal(ipc_call_handoff_eof_transition_framing);
    assert(post.subsystems_inv()) by {
        assert(cpu_array_wf(post.cpu_arr, post.dflt_pt.view())) by { reveal(cpu_array_wf); };
        assert(thread_perms_wf(post.thr_mp)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked); };
        assert(pcid_needflush_wf(post.pcid_needflush)) by { reveal(pcid_needflush_wf); };
        assert(cpu_published_wf(post.cpu_published, post.cpu_arr, post.pcid_needflush)) by { reveal(process_thread_wf); reveal(process_pagetable_match); reveal(pagetable_perms_wf); reveal(PageTableHigher::table_pages_wf); reveal(cpu_published_wf); };
        assert(cpu_offline_flags_wf(post.cpu_offline_mp, post.cpu_arr)) by { reveal(cpu_offline_flags_wf); };
        reveal(KernelK::default_pagetable_wf);
    };
}

pub(super) proof fn ipc_call_handoff_eof_memory(pre: KernelK, post: KernelK, cpu_id: CpuId, caller_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, callee_ptr: RwLockThreadPtr, entry_regs: Registers)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        caller_ptr != callee_ptr,
        pre.thr_mp.dom().contains(caller_ptr),
        pre.thr_mp.dom().contains(callee_ptr),
        !pre.thr_mp.spec_index(caller_ptr).being_killed(),
        pre.prc_mp.dom().contains(pre.thr_mp.spec_index(callee_ptr).view().owning_proc),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.ctn_mp.dom().contains(pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
        pcid_valid(pre.prc_mp.spec_index(pre.thr_mp.spec_index(callee_ptr).view().owning_proc).view_rodata().view().pcid),
        !pre.cpu_arr.spec_index(cpu_id).view().being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(caller_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(pre.thr_mp.spec_index(caller_ptr).view().owning_proc),
        pre.thr_mp.spec_index(caller_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(caller_ptr).view().callee is None,
        pre.thr_mp.spec_index(caller_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.thr_mp.spec_index(caller_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        pre.thr_mp.spec_index(callee_ptr).view().state is RECEIVING_CALL,
        pre.thr_mp.spec_index(callee_ptr).view().caller is None,
        pre.thr_mp.spec_index(callee_ptr).view().callee is None,
        pre.thr_mp.spec_index(callee_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        pre.thr_mp.spec_index(callee_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() > 0,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view()[0] == callee_ptr,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue_state is RECEIVE,
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(caller_ptr),
        ipc_call_handoff_eof_transition_framing(pre, post, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, entry_regs),
    ensures
        post.memory_management_inv(),
{
    hide(Seq::contains);
    reveal(ipc_call_handoff_eof_transition_framing);
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_endpoint_memory_fields(pre, post); };
}

pub(super) proof fn ipc_call_handoff_eof(pre: KernelK, post: KernelK, cpu_id: CpuId, caller_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, callee_ptr: RwLockThreadPtr, entry_regs: Registers)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        caller_ptr != callee_ptr,
        pre.thr_mp.dom().contains(caller_ptr),
        pre.thr_mp.dom().contains(callee_ptr),
        !pre.thr_mp.spec_index(caller_ptr).being_killed(),
        pre.prc_mp.dom().contains(pre.thr_mp.spec_index(callee_ptr).view().owning_proc),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.ctn_mp.dom().contains(pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
        pcid_valid(pre.prc_mp.spec_index(pre.thr_mp.spec_index(callee_ptr).view().owning_proc).view_rodata().view().pcid),
        !pre.cpu_arr.spec_index(cpu_id).view().being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(caller_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(pre.thr_mp.spec_index(caller_ptr).view().owning_proc),
        pre.thr_mp.spec_index(caller_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(caller_ptr).view().callee is None,
        pre.thr_mp.spec_index(caller_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.thr_mp.spec_index(caller_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        pre.thr_mp.spec_index(callee_ptr).view().state is RECEIVING_CALL,
        pre.thr_mp.spec_index(callee_ptr).view().caller is None,
        pre.thr_mp.spec_index(callee_ptr).view().callee is None,
        pre.thr_mp.spec_index(callee_ptr).locking_thread() is Write,
        forall|u: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(u).locking_thread()]
            pre.thr_mp.dom().contains(u) && pre.thr_mp.spec_index(u).wlocked_by_thread(pre.thr_mp.spec_index(callee_ptr).locking_thread()->Write_thread_id) ==> u == caller_ptr || u == callee_ptr,
        pre.thr_mp.spec_index(callee_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        pre.thr_mp.spec_index(callee_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() > 0,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view()[0] == callee_ptr,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue_state is RECEIVE,
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(caller_ptr),
        ipc_call_handoff_eof_transition_framing(pre, post, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, entry_regs),
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        post.cpu_published[cpu_id as int].inv(),
        post.cpu_arr.spec_index(cpu_id).view().view().view().tlb_dirty_bitmap.inv(),
        endpoint_perms_wf(post.ep_mp),
    ensures post.inv(),
{
    hide(Seq::contains);
    reveal(ipc_call_handoff_eof_transition_framing);
    ipc_call_handoff_eof_subsystems(pre, post, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, entry_regs);
    ipc_call_handoff_eof_memory(pre, post, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, entry_regs);
    ipc_call_handoff_eof_process_management_inv(pre, post, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, entry_regs);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
        reveal(process_pagetable_match); reveal(container_process_wf); reveal(process_thread_wf);
    };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}

/// The cpu and emptied-thread relations close after the acceptance.
proof fn ipc_accept_call_eof_cpu_wf(pre: KernelK, post: KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, caller_ptr: RwLockThreadPtr)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        caller_ptr != callee_ptr,
        pre.thr_mp.dom().contains(caller_ptr),
        pre.thr_mp.dom().contains(callee_ptr),
        !pre.thr_mp.spec_index(caller_ptr).being_killed(),
        !pre.thr_mp.spec_index(callee_ptr).being_killed(),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(callee_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(pre.thr_mp.spec_index(callee_ptr).view().owning_proc),
        pre.thr_mp.spec_index(callee_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(callee_ptr).view().caller is None,
        pre.thr_mp.spec_index(callee_ptr).view().callee is None,
        pre.thr_mp.spec_index(callee_ptr).locking_thread() is Write,
        pre.thr_mp.spec_index(callee_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().state is CALLING,
        pre.thr_mp.spec_index(caller_ptr).view().callee is None,
        pre.thr_mp.spec_index(caller_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().owning_container == pre.thr_mp.spec_index(callee_ptr).view().owning_container,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() > 0,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view()[0] == caller_ptr,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue_state is SEND,
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(callee_ptr),
        ipc_accept_call_eof_transition_framing(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr),
        post.subsystems_inv(),
    ensures
        process_emptied_threads_wf(post.prc_mp, post.thr_mp),
        container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr),
        thread_cpu_wf(post.thr_mp, post.cpu_arr),
{
    reveal(ipc_accept_call_eof_transition_framing);
    assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
    assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_thread_wf); reveal(process_thread_wf); };
    assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_running_thread_eq(pre.thr_mp, post.thr_mp, pre.cpu_arr, post.cpu_arr); };
}

/// The endpoint queue, descriptor, and reference-counter relations close after the acceptance.
proof fn ipc_accept_call_eof_endpoint_wf(pre: KernelK, post: KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, caller_ptr: RwLockThreadPtr)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        caller_ptr != callee_ptr,
        pre.thr_mp.dom().contains(caller_ptr),
        pre.thr_mp.dom().contains(callee_ptr),
        !pre.thr_mp.spec_index(caller_ptr).being_killed(),
        !pre.thr_mp.spec_index(callee_ptr).being_killed(),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(callee_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(pre.thr_mp.spec_index(callee_ptr).view().owning_proc),
        pre.thr_mp.spec_index(callee_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(callee_ptr).view().caller is None,
        pre.thr_mp.spec_index(callee_ptr).view().callee is None,
        pre.thr_mp.spec_index(callee_ptr).locking_thread() is Write,
        pre.thr_mp.spec_index(callee_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().state is CALLING,
        pre.thr_mp.spec_index(caller_ptr).view().callee is None,
        pre.thr_mp.spec_index(caller_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().owning_container == pre.thr_mp.spec_index(callee_ptr).view().owning_container,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() > 0,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view()[0] == caller_ptr,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue_state is SEND,
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(callee_ptr),
        ipc_accept_call_eof_transition_framing(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr),
        post.subsystems_inv(),
    ensures
        thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp),
        thread_endpoint_queue_wf(post.thr_mp, post.ep_mp),
        container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp),
        container_endpoint_wf(post.ctn_mp, post.ep_mp),
{
    reveal(ipc_accept_call_eof_transition_framing);
    assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_descriptor_eq(pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
    assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { seq_skip_lemma::<RwLockThreadPtr>(); reveal(endpoint_perms_wf); reveal(LinkedList::wf_value_list); reveal(LinkedList::value_list_unique); reveal(thread_endpoint_queue_wf); };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
    assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { container_endpoint_wf_preserved_for_endpoint_owner_eq(pre.ctn_mp, post.ctn_mp, pre.ep_mp, post.ep_mp); };
}

/// The call-link and dangling-chain relations close after the caller is linked to the callee.
proof fn ipc_accept_call_eof_call_chain_wf(pre: KernelK, post: KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, caller_ptr: RwLockThreadPtr)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        caller_ptr != callee_ptr,
        pre.thr_mp.dom().contains(caller_ptr),
        pre.thr_mp.dom().contains(callee_ptr),
        !pre.thr_mp.spec_index(caller_ptr).being_killed(),
        !pre.thr_mp.spec_index(callee_ptr).being_killed(),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(callee_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(pre.thr_mp.spec_index(callee_ptr).view().owning_proc),
        pre.thr_mp.spec_index(callee_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(callee_ptr).view().caller is None,
        pre.thr_mp.spec_index(callee_ptr).view().callee is None,
        pre.thr_mp.spec_index(callee_ptr).locking_thread() is Write,
        forall|u: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(u).locking_thread()]
            pre.thr_mp.dom().contains(u) && pre.thr_mp.spec_index(u).wlocked_by_thread(pre.thr_mp.spec_index(callee_ptr).locking_thread()->Write_thread_id) ==> u == caller_ptr || u == callee_ptr,
        pre.thr_mp.spec_index(callee_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().state is CALLING,
        pre.thr_mp.spec_index(caller_ptr).view().callee is None,
        pre.thr_mp.spec_index(caller_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().owning_container == pre.thr_mp.spec_index(callee_ptr).view().owning_container,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() > 0,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view()[0] == caller_ptr,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue_state is SEND,
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(callee_ptr),
        ipc_accept_call_eof_transition_framing(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr),
        post.subsystems_inv(),
    ensures
        thread_caller_callee_wf(post.thr_mp),
        thread_dangling_chain_end_wf(post.thr_mp),
{
    reveal(ipc_accept_call_eof_transition_framing);
    assert(thread_caller_callee_wf(post.thr_mp)) by { reveal(thread_caller_callee_wf); };
    assert(thread_dangling_chain_end_wf(post.thr_mp)) by {
        thread_dangling_chain_end_on_caller_chain(pre.thr_mp, callee_ptr, Set::<RwLockThreadPtr>::empty(), pre.thr_mp.spec_index(callee_ptr).view().call_depth.view());
        reveal(thread_dangling_chain_end_wf); reveal(thread_caller_callee_wf);
    };
}

#[verifier::spinoff_prover]
proof fn ipc_accept_call_eof_process_management_inv(pre: KernelK, post: KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, caller_ptr: RwLockThreadPtr)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        caller_ptr != callee_ptr,
        pre.thr_mp.dom().contains(caller_ptr),
        pre.thr_mp.dom().contains(callee_ptr),
        !pre.thr_mp.spec_index(caller_ptr).being_killed(),
        !pre.thr_mp.spec_index(callee_ptr).being_killed(),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(callee_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(pre.thr_mp.spec_index(callee_ptr).view().owning_proc),
        pre.thr_mp.spec_index(callee_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(callee_ptr).view().caller is None,
        pre.thr_mp.spec_index(callee_ptr).view().callee is None,
        pre.thr_mp.spec_index(callee_ptr).locking_thread() is Write,
        forall|u: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(u).locking_thread()]
            pre.thr_mp.dom().contains(u) && pre.thr_mp.spec_index(u).wlocked_by_thread(pre.thr_mp.spec_index(callee_ptr).locking_thread()->Write_thread_id) ==> u == caller_ptr || u == callee_ptr,
        pre.thr_mp.spec_index(callee_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().state is CALLING,
        pre.thr_mp.spec_index(caller_ptr).view().callee is None,
        pre.thr_mp.spec_index(caller_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().owning_container == pre.thr_mp.spec_index(callee_ptr).view().owning_container,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() > 0,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view()[0] == caller_ptr,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue_state is SEND,
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(callee_ptr),
        ipc_accept_call_eof_transition_framing(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(ipc_accept_call_eof_transition_framing);
    ipc_accept_call_eof_cpu_wf(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr);
    ipc_accept_call_eof_endpoint_wf(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr);
    ipc_accept_call_eof_call_chain_wf(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr);
    assert(post.process_management_inv()) by {
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { container_thread_wf_preserved_for_container_thread_link_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { process_thread_wf_preserved_for_process_thread_link_eq(pre.prc_mp, post.prc_mp, pre.thr_mp, post.thr_mp); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { container_thread_scheduler_wf_preserved_for_scheduled_thread_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp); reveal(container_thread_wf); };
    };
}

/// Closes every invariant after the call acceptance from the entry invariants, the summary, and the
/// representation facts produced by the dequeue.
pub(super) proof fn ipc_accept_call_eof(pre: KernelK, post: KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, caller_ptr: RwLockThreadPtr)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        caller_ptr != callee_ptr,
        pre.thr_mp.dom().contains(caller_ptr),
        pre.thr_mp.dom().contains(callee_ptr),
        !pre.thr_mp.spec_index(caller_ptr).being_killed(),
        !pre.thr_mp.spec_index(callee_ptr).being_killed(),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(callee_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(pre.thr_mp.spec_index(callee_ptr).view().owning_proc),
        pre.thr_mp.spec_index(callee_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(callee_ptr).view().caller is None,
        pre.thr_mp.spec_index(callee_ptr).view().callee is None,
        pre.thr_mp.spec_index(callee_ptr).locking_thread() is Write,
        forall|u: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(u).locking_thread()]
            pre.thr_mp.dom().contains(u) && pre.thr_mp.spec_index(u).wlocked_by_thread(pre.thr_mp.spec_index(callee_ptr).locking_thread()->Write_thread_id) ==> u == caller_ptr || u == callee_ptr,
        pre.thr_mp.spec_index(callee_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().state is CALLING,
        pre.thr_mp.spec_index(caller_ptr).view().callee is None,
        pre.thr_mp.spec_index(caller_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().owning_container == pre.thr_mp.spec_index(callee_ptr).view().owning_container,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() > 0,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view()[0] == caller_ptr,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue_state is SEND,
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(callee_ptr),
        ipc_accept_call_eof_transition_framing(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr),
        endpoint_perms_wf(post.ep_mp),
    ensures post.inv(),
{
    hide(Seq::contains);
    reveal(ipc_accept_call_eof_transition_framing);
    assert(post.subsystems_inv()) by {
        assert(thread_perms_wf(post.thr_mp)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked); };
        reveal(cpu_array_wf); reveal(cpu_published_wf); reveal(cpu_offline_flags_wf); reveal(KernelK::default_pagetable_wf);
    };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_endpoint_memory_fields(pre, post); };
    ipc_accept_call_eof_process_management_inv(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr);
    assert(post.inv()) by { reveal(cpu_array_wf); reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(tlb_wf_spec); };
}

/// The reply handoff leaves the cpu, caller/callee, and emptied-thread relations closed.
proof fn ipc_reply_handoff_eof_cpu_wf(pre: KernelK, post: KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, caller_ptr: RwLockThreadPtr, entry_regs: Registers)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        caller_ptr != callee_ptr,
        pre.thr_mp.dom().contains(caller_ptr),
        pre.thr_mp.dom().contains(callee_ptr),
        pre.prc_mp.dom().contains(pre.thr_mp.spec_index(caller_ptr).view().owning_proc),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.ctn_mp.dom().contains(pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
        pcid_valid(pre.prc_mp.spec_index(pre.thr_mp.spec_index(caller_ptr).view().owning_proc).view_rodata().view().pcid),
        !pre.cpu_arr.spec_index(cpu_id).view().being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(callee_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(pre.thr_mp.spec_index(callee_ptr).view().owning_proc),
        pre.thr_mp.spec_index(callee_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(callee_ptr).view().caller == Some(caller_ptr),
        pre.thr_mp.spec_index(callee_ptr).view().callee is None,
        pre.thr_mp.spec_index(callee_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.thr_mp.spec_index(callee_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().state is WAITING_REPLY,
        pre.thr_mp.spec_index(caller_ptr).view().callee == Some(callee_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() == 0 || pre.ep_mp.spec_index(endpoint_ptr).view().queue_state is RECEIVE,
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(callee_ptr),
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.map().dom().contains(pre.thr_mp.spec_index(callee_ptr).view().endpoint_linkedlist_node.addr()),
        ipc_reply_handoff_eof_transition_framing(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, entry_regs),
        post.subsystems_inv(),
    ensures
        process_emptied_threads_wf(post.prc_mp, post.thr_mp),
        container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr),
        process_cpu_wf(post.prc_mp, post.cpu_arr),
        thread_cpu_wf(post.thr_mp, post.cpu_arr),
        thread_caller_callee_wf(post.thr_mp),
{
    reveal(ipc_reply_handoff_eof_transition_framing);
    assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
    assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); reveal(container_thread_wf); reveal(container_process_wf); reveal(process_thread_wf); };
    assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); reveal(process_pagetable_match); reveal(process_thread_wf); };
    assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { reveal(thread_cpu_wf); };
    assert(thread_caller_callee_wf(post.thr_mp)) by { reveal(thread_caller_callee_wf); };
}

/// The reply handoff leaves the endpoint queue, descriptor, and reference-counter relations closed.
proof fn ipc_reply_handoff_eof_endpoint_wf(pre: KernelK, post: KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, caller_ptr: RwLockThreadPtr, entry_regs: Registers)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        caller_ptr != callee_ptr,
        pre.thr_mp.dom().contains(caller_ptr),
        pre.thr_mp.dom().contains(callee_ptr),
        pre.prc_mp.dom().contains(pre.thr_mp.spec_index(caller_ptr).view().owning_proc),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.ctn_mp.dom().contains(pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
        pcid_valid(pre.prc_mp.spec_index(pre.thr_mp.spec_index(caller_ptr).view().owning_proc).view_rodata().view().pcid),
        !pre.cpu_arr.spec_index(cpu_id).view().being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(callee_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(pre.thr_mp.spec_index(callee_ptr).view().owning_proc),
        pre.thr_mp.spec_index(callee_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(callee_ptr).view().caller == Some(caller_ptr),
        pre.thr_mp.spec_index(callee_ptr).view().callee is None,
        pre.thr_mp.spec_index(callee_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.thr_mp.spec_index(callee_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().state is WAITING_REPLY,
        pre.thr_mp.spec_index(caller_ptr).view().callee == Some(callee_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() == 0 || pre.ep_mp.spec_index(endpoint_ptr).view().queue_state is RECEIVE,
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(callee_ptr),
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.map().dom().contains(pre.thr_mp.spec_index(callee_ptr).view().endpoint_linkedlist_node.addr()),
        ipc_reply_handoff_eof_transition_framing(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, entry_regs),
        post.subsystems_inv(),
    ensures
        thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp),
        thread_endpoint_queue_wf(post.thr_mp, post.ep_mp),
        container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp),
        container_endpoint_wf(post.ctn_mp, post.ep_mp),
{
    reveal(ipc_reply_handoff_eof_transition_framing);
    assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_descriptor_eq(pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
    assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { seq_push_lemma::<RwLockThreadPtr>(); reveal(endpoint_perms_wf); reveal(LinkedList::wf_value_list); reveal(thread_endpoint_queue_wf); };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
    assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { container_endpoint_wf_preserved_for_endpoint_owner_eq(pre.ctn_mp, post.ctn_mp, pre.ep_mp, post.ep_mp); };
}

#[verifier::spinoff_prover]
proof fn ipc_reply_handoff_eof_process_management_inv(pre: KernelK, post: KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, caller_ptr: RwLockThreadPtr, entry_regs: Registers)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        caller_ptr != callee_ptr,
        pre.thr_mp.dom().contains(caller_ptr),
        pre.thr_mp.dom().contains(callee_ptr),
        pre.prc_mp.dom().contains(pre.thr_mp.spec_index(caller_ptr).view().owning_proc),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.ctn_mp.dom().contains(pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
        pcid_valid(pre.prc_mp.spec_index(pre.thr_mp.spec_index(caller_ptr).view().owning_proc).view_rodata().view().pcid),
        !pre.cpu_arr.spec_index(cpu_id).view().being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(callee_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(pre.thr_mp.spec_index(callee_ptr).view().owning_proc),
        pre.thr_mp.spec_index(callee_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(callee_ptr).view().caller == Some(caller_ptr),
        pre.thr_mp.spec_index(callee_ptr).view().callee is None,
        pre.thr_mp.spec_index(callee_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.thr_mp.spec_index(callee_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().state is WAITING_REPLY,
        pre.thr_mp.spec_index(caller_ptr).view().callee == Some(callee_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() == 0 || pre.ep_mp.spec_index(endpoint_ptr).view().queue_state is RECEIVE,
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(callee_ptr),
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.map().dom().contains(pre.thr_mp.spec_index(callee_ptr).view().endpoint_linkedlist_node.addr()),
        ipc_reply_handoff_eof_transition_framing(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, entry_regs),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(ipc_reply_handoff_eof_transition_framing);
    ipc_reply_handoff_eof_cpu_wf(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, entry_regs);
    ipc_reply_handoff_eof_endpoint_wf(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, entry_regs);
    assert(post.process_management_inv()) by {
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { container_thread_wf_preserved_for_container_thread_link_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { process_thread_wf_preserved_for_process_thread_link_eq(pre.prc_mp, post.prc_mp, pre.thr_mp, post.thr_mp); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { container_thread_scheduler_wf_preserved_for_scheduled_thread_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp); };
        assert(thread_dangling_chain_end_wf(post.thr_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thr_mp, post.thr_mp); };
    };
}

/// Closes every invariant after the reply handoff from the entry invariants, the summary, and the
/// representation facts produced by the switch and the enqueue.
pub(super) proof fn ipc_reply_handoff_eof_subsystems(pre: KernelK, post: KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, caller_ptr: RwLockThreadPtr, entry_regs: Registers)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        caller_ptr != callee_ptr,
        pre.thr_mp.dom().contains(caller_ptr),
        pre.thr_mp.dom().contains(callee_ptr),
        pre.prc_mp.dom().contains(pre.thr_mp.spec_index(caller_ptr).view().owning_proc),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.ctn_mp.dom().contains(pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
        pcid_valid(pre.prc_mp.spec_index(pre.thr_mp.spec_index(caller_ptr).view().owning_proc).view_rodata().view().pcid),
        !pre.cpu_arr.spec_index(cpu_id).view().being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(callee_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(pre.thr_mp.spec_index(callee_ptr).view().owning_proc),
        pre.thr_mp.spec_index(callee_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(callee_ptr).view().caller == Some(caller_ptr),
        pre.thr_mp.spec_index(callee_ptr).view().callee is None,
        pre.thr_mp.spec_index(callee_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.thr_mp.spec_index(callee_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().state is WAITING_REPLY,
        pre.thr_mp.spec_index(caller_ptr).view().callee == Some(callee_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() == 0 || pre.ep_mp.spec_index(endpoint_ptr).view().queue_state is RECEIVE,
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(callee_ptr),
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.map().dom().contains(pre.thr_mp.spec_index(callee_ptr).view().endpoint_linkedlist_node.addr()),
        ipc_reply_handoff_eof_transition_framing(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, entry_regs),
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        post.cpu_published[cpu_id as int].inv(),
        post.cpu_arr.spec_index(cpu_id).view().view().view().tlb_dirty_bitmap.inv(),
        endpoint_perms_wf(post.ep_mp),
    ensures
        post.subsystems_inv(),
{
    hide(Seq::contains);
    reveal(ipc_reply_handoff_eof_transition_framing);
    assert(post.subsystems_inv()) by {
        assert(cpu_array_wf(post.cpu_arr, post.dflt_pt.view())) by { reveal(cpu_array_wf); };
        assert(thread_perms_wf(post.thr_mp)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked); };
        assert(pcid_needflush_wf(post.pcid_needflush)) by { reveal(pcid_needflush_wf); };
        assert(cpu_published_wf(post.cpu_published, post.cpu_arr, post.pcid_needflush)) by { reveal(process_thread_wf); reveal(process_pagetable_match); reveal(pagetable_perms_wf); reveal(PageTableHigher::table_pages_wf); reveal(cpu_published_wf); };
        assert(cpu_offline_flags_wf(post.cpu_offline_mp, post.cpu_arr)) by { reveal(cpu_offline_flags_wf); };
        reveal(KernelK::default_pagetable_wf);
    };
}

pub(super) proof fn ipc_reply_handoff_eof_memory(pre: KernelK, post: KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, caller_ptr: RwLockThreadPtr, entry_regs: Registers)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        caller_ptr != callee_ptr,
        pre.thr_mp.dom().contains(caller_ptr),
        pre.thr_mp.dom().contains(callee_ptr),
        pre.prc_mp.dom().contains(pre.thr_mp.spec_index(caller_ptr).view().owning_proc),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.ctn_mp.dom().contains(pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
        pcid_valid(pre.prc_mp.spec_index(pre.thr_mp.spec_index(caller_ptr).view().owning_proc).view_rodata().view().pcid),
        !pre.cpu_arr.spec_index(cpu_id).view().being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(callee_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(pre.thr_mp.spec_index(callee_ptr).view().owning_proc),
        pre.thr_mp.spec_index(callee_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(callee_ptr).view().caller == Some(caller_ptr),
        pre.thr_mp.spec_index(callee_ptr).view().callee is None,
        pre.thr_mp.spec_index(callee_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.thr_mp.spec_index(callee_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().state is WAITING_REPLY,
        pre.thr_mp.spec_index(caller_ptr).view().callee == Some(callee_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() == 0 || pre.ep_mp.spec_index(endpoint_ptr).view().queue_state is RECEIVE,
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(callee_ptr),
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.map().dom().contains(pre.thr_mp.spec_index(callee_ptr).view().endpoint_linkedlist_node.addr()),
        ipc_reply_handoff_eof_transition_framing(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, entry_regs),
    ensures
        post.memory_management_inv(),
{
    hide(Seq::contains);
    reveal(ipc_reply_handoff_eof_transition_framing);
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_endpoint_memory_fields(pre, post); };
}

pub(super) proof fn ipc_reply_handoff_eof(pre: KernelK, post: KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, caller_ptr: RwLockThreadPtr, entry_regs: Registers)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        caller_ptr != callee_ptr,
        pre.thr_mp.dom().contains(caller_ptr),
        pre.thr_mp.dom().contains(callee_ptr),
        pre.prc_mp.dom().contains(pre.thr_mp.spec_index(caller_ptr).view().owning_proc),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.ctn_mp.dom().contains(pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
        pcid_valid(pre.prc_mp.spec_index(pre.thr_mp.spec_index(caller_ptr).view().owning_proc).view_rodata().view().pcid),
        !pre.cpu_arr.spec_index(cpu_id).view().being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(callee_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(pre.thr_mp.spec_index(callee_ptr).view().owning_proc),
        pre.thr_mp.spec_index(callee_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre.thr_mp.spec_index(callee_ptr).view().caller == Some(caller_ptr),
        pre.thr_mp.spec_index(callee_ptr).view().callee is None,
        pre.thr_mp.spec_index(callee_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.thr_mp.spec_index(callee_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().state is WAITING_REPLY,
        pre.thr_mp.spec_index(caller_ptr).view().callee == Some(callee_ptr),
        pre.thr_mp.spec_index(caller_ptr).view().owning_container == pre.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() == 0 || pre.ep_mp.spec_index(endpoint_ptr).view().queue_state is RECEIVE,
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(callee_ptr),
        !pre.ep_mp.spec_index(endpoint_ptr).view().queue.map().dom().contains(pre.thr_mp.spec_index(callee_ptr).view().endpoint_linkedlist_node.addr()),
        ipc_reply_handoff_eof_transition_framing(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, entry_regs),
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        post.cpu_published[cpu_id as int].inv(),
        post.cpu_arr.spec_index(cpu_id).view().view().view().tlb_dirty_bitmap.inv(),
        endpoint_perms_wf(post.ep_mp),
    ensures post.inv(),
{
    hide(Seq::contains);
    reveal(ipc_reply_handoff_eof_transition_framing);
    ipc_reply_handoff_eof_subsystems(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, entry_regs);
    ipc_reply_handoff_eof_memory(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, entry_regs);
    ipc_reply_handoff_eof_process_management_inv(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, entry_regs);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
        reveal(process_pagetable_match); reveal(container_process_wf); reveal(process_thread_wf);
    };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}
}
