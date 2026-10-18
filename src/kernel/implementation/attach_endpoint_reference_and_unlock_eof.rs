use vstd::prelude::*;
use crate::*;

verus! {
/// Writes `endpoint_ptr` into descriptor 0 of the write-held thread and records the reference on the write-held
/// endpoint; no other object changes.
#[verifier::opaque]
pub open spec fn attach_endpoint_reference_and_unlock_eof_transition_framing(pre: KernelK, post: KernelK, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr) -> bool {
    let thread_before = pre.thr_mp.spec_index(thread_ptr);
    let thread_after = post.thr_mp.spec_index(thread_ptr);
    let endpoint_before = pre.ep_mp.spec_index(endpoint_ptr);
    let endpoint_after = post.ep_mp.spec_index(endpoint_ptr);
    &&& post == (KernelK { thr_mp: post.thr_mp, ep_mp: post.ep_mp, ..pre })
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr)
    &&& post.ep_mp.unchanged_except(&pre.ep_mp, endpoint_ptr)
    &&& thread_after.is_init()
    &&& thread_after.view_rodata() == thread_before.view_rodata()
    &&& thread_after.view_ghost() == thread_before.view_ghost()
    &&& thread_after.locking_thread() == thread_before.locking_thread()
    &&& thread_after.being_killed() == thread_before.being_killed()
    &&& thread_after.killer_info() == thread_before.killer_info()
    &&& thread_after.view() == (Thread { endpoint_descriptors: thread_after.view().endpoint_descriptors, ..thread_before.view() })
    &&& thread_after.view().endpoint_descriptors.wf()
    &&& thread_after.view().endpoint_descriptors.view() =~= thread_before.view().endpoint_descriptors.view().update(0, Some(endpoint_ptr))
    &&& endpoint_after.is_init()
    &&& endpoint_after.view_rodata() == endpoint_before.view_rodata()
    &&& endpoint_after.view_ghost() == endpoint_before.view_ghost()
    &&& endpoint_after.locking_thread() == endpoint_before.locking_thread()
    &&& endpoint_after.being_killed() == endpoint_before.being_killed()
    &&& endpoint_after.killer_info() == endpoint_before.killer_info()
    &&& endpoint_after.view() == (Endpoint { rf_counter: endpoint_after.view().rf_counter, owning_threads: endpoint_after.view().owning_threads, ..endpoint_before.view() })
    &&& endpoint_after.view().rf_counter == endpoint_before.view().rf_counter + 1
    &&& endpoint_after.view().owning_threads.view() =~= endpoint_before.view().owning_threads.view().insert((thread_ptr, 0))
}

/// Closes every kernel invariant after descriptor 0 of the scheduled thread is bound to the endpoint.
pub(super) proof fn attach_endpoint_reference_and_unlock_eof(pre: KernelK, post: KernelK, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr)
    requires
        pre.inv(),
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).view().state is SCHEDULED,
        pre.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.spec_index(0) is None,
        pre.ep_mp.dom().contains(endpoint_ptr),
        {
            ||| pre.ep_mp.spec_index(endpoint_ptr).view().owning_container == pre.thr_mp.spec_index(thread_ptr).view().owning_container
            ||| pre.ctn_mp.spec_index(pre.ep_mp.spec_index(endpoint_ptr).view().owning_container).view_ghost().subtree_set.view().contains(pre.thr_mp.spec_index(thread_ptr).view().owning_container)
        },
        attach_endpoint_reference_and_unlock_eof_transition_framing(pre, post, thread_ptr, endpoint_ptr),
        post.thr_mp.perms_wf(),
        post.ep_mp.perms_wf(),
    ensures post.inv(),
{
    reveal(attach_endpoint_reference_and_unlock_eof_transition_framing);
    thread_endpoint_ref_counter_wf_endpoint_at(pre.thr_mp, pre.ep_mp, endpoint_ptr, thread_ptr, 0);
    assert(post.subsystems_inv()) by {
        assert(thread_perms_wf(post.thr_mp)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); };
        assert(endpoint_perms_wf(post.ep_mp)) by { reveal(endpoint_perms_wf); };
        reveal(KernelK::default_pagetable_wf);
    };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_endpoint_memory_fields(pre, post); };
    assert(post.process_management_inv()) by {
        assert(thread_caller_callee_wf(post.thr_mp)) by { thread_caller_callee_wf_preserved_for_call_link_eq(pre.thr_mp, post.thr_mp); };
        assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { container_endpoint_wf_preserved_for_endpoint_owner_eq(pre.ctn_mp, post.ctn_mp, pre.ep_mp, post.ep_mp); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_queue_fields(pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(container_thread_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { container_thread_scheduler_wf_preserved_for_scheduled_thread_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp); };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { container_thread_wf_preserved_for_container_thread_link_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { process_thread_wf_preserved_for_process_thread_link_eq(pre.prc_mp, post.prc_mp, pre.thr_mp, post.thr_mp); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_running_thread_eq(pre.thr_mp, post.thr_mp, pre.cpu_arr, post.cpu_arr); };
    };
}
} // verus!
