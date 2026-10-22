use vstd::prelude::*;
use crate::*;

verus! {
/// Clears descriptor `index` of `thread_ptr` and drops its reference from the still write-held `endpoint_ptr`; every other
/// kernel field is unchanged.
#[verifier::opaque]
pub(super) open spec fn drop_endpoint_descriptor_eof_transition_framing(pre: KernelK, post: KernelK, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, index: EndpointIdx) -> bool {
    let old_thread = pre.thr_mp.spec_index(thread_ptr);
    let new_thread = post.thr_mp.spec_index(thread_ptr);
    let old_endpoint = pre.ep_mp.spec_index(endpoint_ptr);
    let new_endpoint = post.ep_mp.spec_index(endpoint_ptr);
    &&& post == (KernelK { thr_mp: post.thr_mp, ep_mp: post.ep_mp, ..pre })
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr)
    &&& new_thread.is_init()
    &&& new_thread.locking_thread() == old_thread.locking_thread()
    &&& new_thread.being_killed() == old_thread.being_killed()
    &&& new_thread.killer_info() == old_thread.killer_info()
    &&& new_thread.view_rodata() == old_thread.view_rodata()
    &&& new_thread.view_ghost() == old_thread.view_ghost()
    &&& new_thread.view() == (Thread { endpoint_descriptors: new_thread.view().endpoint_descriptors, ..old_thread.view() })
    &&& new_thread.view().endpoint_descriptors.view() == old_thread.view().endpoint_descriptors.view().update(index as int, None)
    &&& post.ep_mp.unchanged_except(&pre.ep_mp, endpoint_ptr)
    &&& new_endpoint.is_init()
    &&& new_endpoint.locking_thread() == old_endpoint.locking_thread()
    &&& new_endpoint.being_killed() == old_endpoint.being_killed()
    &&& new_endpoint.killer_info() == old_endpoint.killer_info()
    &&& new_endpoint.view_rodata() == old_endpoint.view_rodata()
    &&& new_endpoint.view_ghost() == old_endpoint.view_ghost()
    &&& new_endpoint.view() == (Endpoint { rf_counter: new_endpoint.view().rf_counter, owning_threads: new_endpoint.view().owning_threads, ..old_endpoint.view() })
    &&& new_endpoint.view().rf_counter == old_endpoint.view().rf_counter - 1
    &&& new_endpoint.view().owning_threads.view() == old_endpoint.view().owning_threads.view().remove((thread_ptr, index))
}

/// The cleared descriptor and the dropped endpoint reference keep the thread-endpoint reference relation.
proof fn drop_endpoint_descriptor_eof_thread_endpoint_ref_counter(pre: KernelK, post: KernelK, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, index: EndpointIdx)
    requires
        pre.inv(),
        drop_endpoint_descriptor_eof_transition_framing(pre, post, thread_ptr, endpoint_ptr, index),
        forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t).view().endpoint_descriptors] post.thr_mp.dom().contains(t) && t != thread_ptr ==> post.thr_mp.spec_index(t).view().endpoint_descriptors == pre.thr_mp.spec_index(t).view().endpoint_descriptors,
        index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[index as int] == Some(endpoint_ptr),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((thread_ptr, index)),
        post.thr_mp.spec_index(thread_ptr).inv(),
    ensures thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp),
{
    reveal(drop_endpoint_descriptor_eof_transition_framing);
    assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); };
}

/// The cleared descriptor and the dropped endpoint reference keep the kernel invariant.
pub(super) proof fn drop_endpoint_descriptor_eof(pre: KernelK, post: KernelK, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, index: EndpointIdx)
    requires
        pre.inv(),
        drop_endpoint_descriptor_eof_transition_framing(pre, post, thread_ptr, endpoint_ptr, index),
        index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).view().state is RUNNING || pre.thr_mp.spec_index(thread_ptr).view().state is KILLED,
        pre.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[index as int] == Some(endpoint_ptr),
        pre.ep_mp.dom().contains(endpoint_ptr),
        pre.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((thread_ptr, index)),
        post.thr_mp.perms_wf(),
        post.thr_mp.spec_index(thread_ptr).inv(),
        post.thr_mp.spec_index(thread_ptr).locking_thread() is Write,
        post.ep_mp.perms_wf(),
        post.ep_mp.spec_index(endpoint_ptr).inv(),
        post.ep_mp.spec_index(endpoint_ptr).locking_thread() is Write,
    ensures post.inv(),
{
    reveal(drop_endpoint_descriptor_eof_transition_framing);
    assert(post.subsystems_inv()) by {
        assert(thread_perms_wf(post.thr_mp)) by {
            reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
            reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_partner_only_when_wlocked); reveal(thread_peer_implies_ipc_partner);
        };
        assert(endpoint_perms_wf(post.ep_mp)) by { reveal(endpoint_perms_wf); };
        reveal(KernelK::default_pagetable_wf);
    };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_endpoint_memory_fields(pre, post); };
    assert(post.process_management_inv()) by {
        assert(thread_caller_callee_wf(post.thr_mp)) by { thread_caller_callee_wf_preserved_for_call_link_eq(pre.thr_mp, post.thr_mp); };
        assert(thread_dangling_chain_end_wf(post.thr_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thr_mp, post.thr_mp); };
        assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { container_endpoint_wf_preserved_for_endpoint_owner_eq(pre.ctn_mp, post.ctn_mp, pre.ep_mp, post.ep_mp); };
        drop_endpoint_descriptor_eof_thread_endpoint_ref_counter(pre, post, thread_ptr, endpoint_ptr, index);
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_queue_fields(pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(container_thread_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { container_thread_scheduler_wf_preserved_for_scheduled_thread_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp); };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { container_thread_wf_preserved_for_container_thread_link_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { process_thread_wf_preserved_for_process_thread_link_eq(pre.prc_mp, post.prc_mp, pre.thr_mp, post.thr_mp); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); reveal(process_thread_wf); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_running_thread_eq(pre.thr_mp, post.thr_mp, pre.cpu_arr, post.cpu_arr); };
    };
}
} // verus!
