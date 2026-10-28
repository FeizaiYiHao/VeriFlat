use vstd::prelude::*;
use vstd::assert_seqs_equal;
use crate::*;

verus! {
/// `pre` to `mid` creates the child's scheduled root thread; `mid` to `post` releases every lock, clears the
/// staging thread's progress, and attaches the initial endpoint to the new thread.
#[verifier::opaque]
pub(super) open spec fn create_new_container_root_thread_and_unlock_eof_transition_framing(
    pre: KernelK, mid: KernelK, post: KernelK, child_process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr,
    child_container_ptr: RwLockContainerPtr, caller_cpu_id: CpuId, new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, endpoint: Option<RwLockEndpointPtr>,
) -> bool {
    &&& kernel_new_thread_fields(&pre, &mid, child_process_ptr, current_thread_ptr, child_container_ptr, caller_cpu_id, new_thread_ptr, initial_regs, None,
        pre.thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view())
    &&& post == (KernelK { ctn_mp: post.ctn_mp, prc_mp: post.prc_mp, pt_mp: post.pt_mp, pt_lower: post.pt_lower, pg_arr: post.pg_arr, sched_mp: post.sched_mp, thr_mp: post.thr_mp,
        ep_mp: post.ep_mp, cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, ..mid })
    &&& post.ctn_mp.dom() == mid.ctn_mp.dom()
    &&& forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)]
        mid.ctn_mp.dom().contains(c) ==> {
            &&& post.ctn_mp.spec_index(c).view() == mid.ctn_mp.spec_index(c).view()
            &&& post.ctn_mp.spec_index(c).view_rodata() == mid.ctn_mp.spec_index(c).view_rodata()
            &&& post.ctn_mp.spec_index(c).view_ghost() == mid.ctn_mp.spec_index(c).view_ghost()
            &&& post.ctn_mp.spec_index(c).being_killed() == mid.ctn_mp.spec_index(c).being_killed()
        }
    &&& post.pt_mp.dom() == mid.pt_mp.dom()
    &&& kernel_pagetable_nonlock_fields_unchanged(mid.pt_mp, mid.pt_lower.view(), post.pt_mp, post.pt_lower.view())
    &&& kernel_cpu_nonlock_fields_unchanged(mid.cpu_arr, post.cpu_arr)
    &&& kernel_process_nonlock_fields_unchanged(mid.prc_mp, post.prc_mp)
    &&& post.sched_mp.dom() == mid.sched_mp.dom()
    &&& forall|s: RwLockSchedulerPtr| #![trigger scheduler_shards_of(post.sched_mp.spec_index(s))]
        mid.sched_mp.dom().contains(s) ==> scheduler_shards_of(post.sched_mp.spec_index(s)) == scheduler_shards_of(mid.sched_mp.spec_index(s))
    &&& post.thr_mp.dom() == mid.thr_mp.dom()
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)]
        mid.thr_mp.dom().contains(t) ==> {
            &&& post.thr_mp.spec_index(t).being_killed() == mid.thr_mp.spec_index(t).being_killed()
            &&& t != current_thread_ptr && t != new_thread_ptr ==> post.thr_mp.spec_index(t).view() == mid.thr_mp.spec_index(t).view()
        }
    &&& post.thr_mp.spec_index(current_thread_ptr).view() == (Thread { syscall_progress: post.thr_mp.spec_index(current_thread_ptr).view().syscall_progress, ..mid.thr_mp.spec_index(current_thread_ptr).view() })
    &&& post.thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None
    &&& post.thr_mp.spec_index(new_thread_ptr).view() == (Thread { endpoint_descriptors: post.thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors, ..mid.thr_mp.spec_index(new_thread_ptr).view() })
    &&& post.thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.view() == if endpoint is Some {
            mid.thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.view().update(0, endpoint)
        } else { mid.thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.view() }
    &&& post.ep_mp.dom() == mid.ep_mp.dom()
    &&& endpoint is Some ==> post.ep_mp.dom().contains(endpoint->Some_0)
    &&& forall|e: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(e)]
        mid.ep_mp.dom().contains(e) ==> {
            let a = mid.ep_mp.spec_index(e);
            let b = post.ep_mp.spec_index(e);
            &&& b.view().queue.view() == a.view().queue.view()
            &&& b.view().queue_state == a.view().queue_state
            &&& b.view().owning_threads.view() == if endpoint == Some(e) { a.view().owning_threads.view().insert((new_thread_ptr, 0usize)) } else { a.view().owning_threads.view() }
            &&& b.view().owning_container == a.view().owning_container
            &&& b.being_killed() == a.being_killed()
        }
}

/// Composes the root-thread creation fields with the lock releases, the cleared progress, and the endpoint attachment.
pub(super) proof fn create_new_container_root_thread_and_unlock_eof(
    pre: KernelK, mid: KernelK, post: KernelK, child_process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr,
    child_container_ptr: RwLockContainerPtr, caller_cpu_id: CpuId, new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, endpoint: Option<RwLockEndpointPtr>,
)
    requires create_new_container_root_thread_and_unlock_eof_transition_framing(pre, mid, post, child_process_ptr, current_thread_ptr, child_container_ptr, caller_cpu_id, new_thread_ptr, initial_regs, endpoint),
    ensures kernel_new_thread_fields(&pre, &post, child_process_ptr, current_thread_ptr, child_container_ptr, caller_cpu_id, new_thread_ptr, initial_regs, endpoint, None),
{
    reveal(create_new_container_root_thread_and_unlock_eof_transition_framing); reveal(kernel_new_thread_fields);
    reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
    kernel_pagetable_nonlock_fields_unchanged_transitive(pre.pt_mp, pre.pt_lower.view(), mid.pt_mp, mid.pt_lower.view(), post.pt_mp, post.pt_lower.view());
    assert_seqs_equal!(post.thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.view() == Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| if i == 0 { endpoint } else { None }), i => {});
}
}
