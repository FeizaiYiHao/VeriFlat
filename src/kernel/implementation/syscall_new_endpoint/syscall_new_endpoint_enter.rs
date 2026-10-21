use vstd::prelude::*;
use crate::*;
use super::syscall_new_endpoint_spec::*;
use super::syscall_new_endpoint_trace::*;

verus! {
/// Records the new-endpoint progress on the caller thread and ends the enter step.
pub(super) fn enter_new_endpoint_commit(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx, Tracked(thread_lock_perm): Tracked<&LockPerm>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        edp_idx_valid(endpoint_index),
        old(krnl).inv(),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, ctn_mp: old(krnl).ctn_mp, prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).ctn_mp.unchanged_except(&old(steps).snapshot_k().ctn_mp, container_ptr),
        old(krnl).prc_mp.unchanged_except(&old(steps).snapshot_k().prc_mp, process_ptr),
        old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, thread_ptr),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        old(steps).snapshot_k().ctn_mp.spec_index(container_ptr).locking_thread() is None,
        old(steps).snapshot_k().prc_mp.spec_index(process_ptr).locking_thread() is None,
        old(steps).snapshot_k().thr_mp.spec_index(thread_ptr).locking_thread() is None,
        old(lctx).kernel_view_locking_state() is Acquire,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).being_killed() == false,
        !old(krnl).ctn_mp.spec_index(container_ptr).view().zombie,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
        old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= 1,
        old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) is None,
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom() =~= set![container_ptr],
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).view().len() == old(steps).view().len() + 1,
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
        new_endpoint_trace_after_enter(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
            cpu_id, endpoint_index),
        final(steps).snapshot_k() == *final(krnl),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr) == old(krnl).ctn_mp.spec_index(container_ptr),
        final(krnl).prc_mp.dom().contains(process_ptr),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread {
            syscall_progress: Ghost(Some(SyscallProgress::NewEndpoint { slot: endpoint_index })), ..old(krnl).thr_mp.spec_index(thread_ptr).view()
        }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
{
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::NewEndpoint { slot: endpoint_index })), Tracked(&*lctx), Tracked(thread_lock_perm));
    proof {
        assert(steps.snapshot_k().thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); };
        let ghost entered_k = *krnl;
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        assert(new_endpoint_trace_after_enter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index)) by {
            kernel_cpu_process_thread_endpoint_lock_modes_changed_implies_u_step(&old(steps).snapshot_k(), old(krnl), old(lctx), cpu_id, process_ptr, thread_ptr, None, true, Some(container_ptr), false, None);
            kernel_thread_syscall_progress_changed_implies_u_step(old(krnl), &entered_k, thread_ptr);
            new_endpoint_enter_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(entered_k), cpu_id, container_ptr, process_ptr, thread_ptr, endpoint_index);
            new_endpoint_trace_enter_step(&*steps, old(steps).view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(entered_k), cpu_id, endpoint_index);
        };
    }
}
} // verus!
