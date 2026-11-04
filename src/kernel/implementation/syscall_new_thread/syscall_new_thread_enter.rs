use vstd::prelude::*;
use crate::*;
use super::syscall_new_thread_spec::*;
use super::syscall_new_thread_trace::*;

verus! {
/// Records the new-thread progress on the caller thread and ends the enter step.
pub(super) fn enter_new_thread_commit(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    current_thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, sched_ptr: RwLockSchedulerPtr, Tracked(current_thread_lock_perm): Tracked<&LockPerm>,
    initial_regs: &Registers,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, prc_mp: old(krnl).prc_mp, thrd_mp: old(krnl).thrd_mp, ep_mp: old(krnl).ep_mp, sched_mp: old(krnl).sched_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(krnl).prc_mp.unchanged_except(&old(steps).snapshot_k().prc_mp, prc_ptr),
        old(krnl).thrd_mp.unchanged_except(&old(steps).snapshot_k().thrd_mp, current_thrd_ptr),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        old(steps).snapshot_k().prc_mp.spec_index(prc_ptr).locking_thread() is None,
        old(steps).snapshot_k().thrd_mp.spec_index(current_thrd_ptr).locking_thread() is None,
        old(krnl).ep_mp == old(steps).snapshot_k().ep_mp,
        old(lctx).kernel_view_locking_state() is Acquire,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        old(krnl).thrd_mp.dom().contains(current_thrd_ptr),
        old(krnl).ctn_mp.dom().contains(ctn_ptr),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thrd_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == ctn_ptr,
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (sched_ptr, cpu_id), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), prc_ptr, TypedLockMode::Write),
        old(krnl).prc_mp.spec_index(prc_ptr).being_killed() == false,
        old(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is Running,
        old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == ctn_ptr,
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(current_thrd_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thrd_ptr, TypedLockMode::Write),
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).being_killed() == false,
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().owning_container == ctn_ptr,
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().syscall_progress.view() is None,
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().quota_4k >= 1,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).thread_lock_map().dom() =~= set![current_thrd_ptr],
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).view().len() == old(steps).view().len() + 1,
        new_thread_trace_after_enter(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id,
            *initial_regs, None),
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
        held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).ctn_mp.dom().contains(ctn_ptr),
        final(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata(),
        final(krnl).prc_mp.dom().contains(prc_ptr),
        final(krnl).prc_mp.spec_index(prc_ptr) == old(krnl).prc_mp.spec_index(prc_ptr),
        final(krnl).sched_mp.dom().contains(sched_ptr),
        final(krnl).sched_mp.spec_index(sched_ptr).shards.spec_index(cpu_id) == old(krnl).sched_mp.spec_index(sched_ptr).shards.spec_index(cpu_id),
        final(krnl).thrd_mp.dom().contains(current_thrd_ptr),
        final(krnl).thrd_mp.spec_index(current_thrd_ptr).view() == (Thread {
            syscall_progress: Ghost(Some(SyscallProgress::NewThread { regs: *initial_regs, endpoint_index: None })), ..old(krnl).thrd_mp.spec_index(current_thrd_ptr).view()
        }),
        final(krnl).thrd_mp.spec_index(current_thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(current_thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(current_thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(current_thrd_ptr).being_killed(),
        final(krnl).thrd_mp.spec_index(current_thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(current_thrd_ptr).view_ghost(),
{
    krnl.set_thread_syscall_progress(current_thrd_ptr, Ghost(Some(SyscallProgress::NewThread { regs: *initial_regs, endpoint_index: None })), Tracked(&*lctx), Tracked(current_thread_lock_perm));
    proof {
        assert(steps.snapshot_k().thrd_mp.spec_index(current_thrd_ptr).view().syscall_progress.view() is None) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); };
        let ghost entered_k = *krnl;
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, current_thrd_ptr);
        assert(new_thread_trace_after_enter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, *initial_regs, None)) by {
            kernel_cpu_process_thread_endpoint_lock_modes_changed_implies_u_step(&old(steps).snapshot_k(), old(krnl), old(lctx), cpu_id, prc_ptr, current_thrd_ptr, None, true, None, false, None);
            kernel_thread_syscall_progress_changed_implies_u_step(old(krnl), &entered_k, current_thrd_ptr);
            new_thread_enter_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(entered_k), cpu_id, prc_ptr, current_thrd_ptr, ctn_ptr, None, *initial_regs, None);
            new_thread_trace_enter_step(&*steps, old(steps).view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(entered_k), cpu_id, *initial_regs, None);
        };
        assert(krnl.ctn_mp.dom().contains(ctn_ptr)) by { container_thread_wf_at(krnl.ctn_mp, krnl.thrd_mp, current_thrd_ptr); };
    }
}
} // verus!
