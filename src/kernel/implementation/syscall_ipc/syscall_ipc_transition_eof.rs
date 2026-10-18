use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_transition_spec::ipc_schedule_waiting_peer_transition;

verus! {
pub(super) proof fn ipc_schedule_waiting_peer_eof_process(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, peer_result: RetValueType, thread_id: LockThreadId,
)
    requires
        ipc_schedule_waiting_peer_transition(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, peer_result, thread_id),
        thread_perms_wf(post.thr_mp),
        endpoint_perms_wf(post.ep_mp),
        scheduler_perms_wf(post.sched_mp),
    ensures
        post.process_management_inv(),
{
    reveal(ipc_schedule_waiting_peer_transition);
    assert(post.process_management_inv()) by {
        assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_perms_wf); thread_endpoint_ref_counter_wf_preserved_for_descriptor_eq(pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
        assert({
            &&& container_endpoint_wf(post.ctn_mp, post.ep_mp)
            &&& thread_caller_callee_wf(post.thr_mp)
        }) by { container_endpoint_wf_preserved_for_endpoint_owner_eq(pre.ctn_mp, post.ctn_mp, pre.ep_mp, post.ep_mp); thread_caller_callee_wf_preserved_for_call_link_eq(pre.thr_mp, post.thr_mp); };
        assert({
            &&& container_scheduler_wf(post.ctn_mp, post.sched_mp)
            &&& container_thread_wf(post.ctn_mp, post.thr_mp)
            &&& process_thread_wf(post.prc_mp, post.thr_mp)
        }) by { reveal(container_scheduler_wf); reveal(container_thread_wf); reveal(process_thread_wf); };
        assert({
            &&& container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)
            &&& process_cpu_wf(post.prc_mp, post.cpu_arr)
            &&& thread_cpu_wf(post.thr_mp, post.cpu_arr)
        }) by { reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by {
            seq_skip_lemma::<RwLockThreadPtr>(); reveal(endpoint_perms_wf); reveal(LinkedList::wf_value_list); reveal(LinkedList::value_list_unique); reveal(thread_endpoint_queue_wf);
        };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by {
            reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf); container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp);
        };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by {
            seq_push_lemma::<RwLockThreadPtr>();
            reveal(scheduler_perms_wf); reveal(LinkedList::wf_map); reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
        };
    };
}

pub(super) proof fn ipc_schedule_waiting_peer_eof(
    pre: KernelK, post: KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, peer_result: RetValueType, thread_id: LockThreadId,
)
    requires
        ipc_schedule_waiting_peer_transition(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, peer_result, thread_id),
        thread_perms_wf(post.thr_mp),
        endpoint_perms_wf(post.ep_mp),
        scheduler_perms_wf(post.sched_mp),
    ensures post.inv(),
{
    reveal(ipc_schedule_waiting_peer_transition);
    ipc_schedule_waiting_peer_eof_process(pre, post, current_thread_ptr, peer_thread_ptr, endpoint_ptr, peer_scheduler_ptr, wake_cpu, peer_result, thread_id);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_thread_endpoint_memory_fields(pre, post); };
}
} // verus!
