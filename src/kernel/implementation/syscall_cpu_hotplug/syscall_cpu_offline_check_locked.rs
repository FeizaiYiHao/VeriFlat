use vstd::prelude::*;
use crate::*;
use super::syscall_cpu_offline_check_spec::*;
use super::syscall_cpu_offline_check_trace::*;
use super::syscall_cpu_offline_check::OfflineCheckResult;
use super::syscall_cpu_offline_check_locked_helpers::cpu_offline_check_recheck;

verus! {
/// With `cpu_id` write-held and not Off, owned by `container_ptr` and running `current_thread` of `current_process`, if
/// any: reads the container's request bit for the cpu under its flag lock. A clear bit releases the cpu and continues
/// without a step. A set bit holds the cpu across a boundary inside its kernel step, recording the hold step, and rechecks
/// from the snapshot after it, which the result returns as the decision state.
pub(super) fn cpu_offline_check_locked(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, pt_regs: &Registers,
    Tracked(cpu_lock_perm): Tracked<LockPerm>, container_ptr: RwLockContainerPtr, current_process: Option<RwLockProcessPtr>, current_thread: Option<RwLockThreadPtr>,
) -> (ret: (OfflineCheckResult, Ghost<KernelK>))
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).nonlock_view().len() == 0,
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, ..old(steps).snapshot_k() }),
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] == cpu_op_after_step(old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view().state),
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        ({
            let pre = old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view();
            let post = old(krnl).cpu_arr.spec_index(cpu_id).view();
            &&& post.view().view() == pre.view().view()
            &&& post.locking_thread() == RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cpu_lock_perm.lock_id() }
            &&& post.being_killed() == pre.being_killed()
            &&& pre.locked() == false
            &&& cpu_lock_perm.state() is WriteLock
            &&& cpu_lock_perm.thread_id() == old(lctx).thread_id()
        }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        {
            let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            &&& !(cpu.state is Off)
            &&& cpu.owning_container == container_ptr
            &&& cpu.current_process == current_process
            &&& cpu.current_thread == current_thread
            &&& old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cpu.current_cr3, cpu.current_pcid)
        },
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        cpu_offline_check_entry_trace(
            final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, *pt_regs, ret.0 is Off, if ret.0 is Off { cpu_offline_check_flushed_default_pcid(ret.1.view(), cpu_id) } else { false },
        ),
        final(steps).nonlock_view().len() == if ret.0 is Off { 1nat } else { 0nat },
        ret.0 == cpu_offline_check_result(kernel_k_to_kernel_u(ret.1.view()), cpu_id),
        ret.0 is Off ==> {
            let step = final(steps).nonlock_view()[0];
            &&& step.old_u == kernel_k_to_nonlock_kernel_u(ret.1.view())
            &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
            &&& cpu_offline_check_step(step.old_u, step.new_u, cpu_id, *pt_regs, cpu_offline_check_flushed_default_pcid(ret.1.view(), cpu_id))
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Off
        },
{
    let ghost entry = steps.snapshot_k();
    let ghost start = steps.view().len() as int;
    proof {
        assert({
            &&& krnl.ctn_mp.dom().contains(container_ptr)
            &&& krnl.cpu_offline_mp.dom().contains(cpu_offline_flags_ptr(container_ptr))
            &&& krnl.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(container_ptr)).container_depth.view() == krnl.cpu_arr.spec_index(cpu_id).view().view().view().container_depth
        }) by { container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id); container_cpu_offline_flags_wf_container_at(krnl.ctn_mp, krnl.cpu_offline_mp, container_ptr); };
        assert(page_ptr_2m_valid(container_ptr)) by { container_pages_backward_at(krnl.pg_arr, krnl.ctn_mp, container_ptr); };
    }
    let flags_ptr = container_ptr + 4096;
    let Tracked(flag_lock_perm) = krnl.wlock_cpu_offline_flag(flags_ptr, cpu_id, Tracked(&mut *lctx));
    let requested = krnl.cpu_offline_mp.read_flag(flags_ptr, cpu_id, Tracked(&flag_lock_perm));
    krnl.wunlock_cpu_offline_flag(flags_ptr, cpu_id, Tracked(&mut *lctx), Tracked(flag_lock_perm));
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    if !requested {
        release_cpu_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Tracked(cpu_lock_perm));
        proof {
            assert(krnl.cpu_op.view().view() =~= old(steps).snapshot_k().cpu_op.view().view());
            cpu_offline_check_trace_stutter_released(&*steps, old(steps).view(), &old(steps).snapshot_k(), &*krnl, cpu_id, *pt_regs);
            cpu_offline_check_result_from_k(&old(steps).snapshot_k(), cpu_id, OfflineCheckResult::Continue);
        }
        return (OfflineCheckResult::Continue, Ghost(entry));
    }
    let ghost held = *krnl;
    proof {
        let before = steps.view();
        krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        assert(cpu_offline_check_trace_after_hold(steps.view().subrange(before.len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id)) by {
            kernel_cpu_lock_mode_changed_implies_u_step(&old(steps).snapshot_k(), &held, cpu_id); cpu_offline_check_hold_step_from_u(&old(steps).snapshot_k(), &held, cpu_id);
            cpu_offline_check_hold_step_pre_from_k(&old(steps).snapshot_k(), cpu_id);
            cpu_offline_check_trace_hold_step(&*steps, before, kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(held), cpu_id);
        };
    }
    let ghost decision = *krnl;
    let ret = cpu_offline_check_recheck(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, pt_regs, Tracked(cpu_lock_perm), container_ptr, current_process, current_thread,
        Ghost(entry), Ghost(start),
    );
    (ret, Ghost(decision))
}
} // verus!
