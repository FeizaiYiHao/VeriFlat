use vstd::prelude::*;
use crate::*;
use super::syscall_cpu_hotplug_spec::*;
use super::syscall_cpu_hotplug_trace::*;
use super::cpu_offline_request_child_locked::cpu_offline_request_child_locked;
#[cfg(verus_keep_ghost)]
use crate::kernel::implementation::locker_unlocker::u_sys_exit_eof;

verus! {
/// Asks `target`, a cpu of the `child`-th child of the caller's live, non-zombie container, to go Off at its next schedule
/// check: under the cpu, the caller's container, the child's request cell, and the child's cpu-set lock, the
/// child's table records the request. The target notices the request on its next pass through its idle loop or schedule
/// check.
pub fn syscall_cpu_offline_request_child(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, child: usize, target: CpuId) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        old(steps).nonlock_view().len() == 0,
        old(steps).snapshot_k() == *old(krnl),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        cpu_offline_request_child_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, target, ret),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).no_locks_held(),
        ret == cpu_offline_request_child_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, child, target),
        !(ret is Success && !cpu_offline_request_child_pending(kernel_k_to_kernel_u(*old(krnl)), target)) ==> final(steps).nonlock_view().len() == 0,
        ret is Success && !cpu_offline_request_child_pending(kernel_k_to_kernel_u(*old(krnl)), target) ==> {
            let step = final(steps).nonlock_view()[0];
            &&& final(steps).nonlock_view().len() == 1
            &&& step.old_u == kernel_k_to_nonlock_kernel_u(*old(krnl))
            &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
            &&& cpu_offline_request_child_step_pre(step.old_u, cpu_id, target)
            &&& cpu_offline_request_child_step(step.old_u, step.new_u, cpu_id, target)
        },
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }
    if target >= NUM_CPUS {
        proof {
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
            cpu_offline_request_child_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, target, RetValueType::ErrorCpuOwnerMismatch);
        }
        return RetValueType::ErrorCpuOwnerMismatch;
    }
    let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
    if cpu_lock_res.is_none() {
        proof {
            cpu_offline_request_child_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, target, RetValueType::CpuIdle);
            cpu_offline_request_child_result_from_k(&*old(krnl), cpu_id, child, target, RetValueType::CpuIdle, false);
        }
        return RetValueType::CpuIdle;
    }
    let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
    proof { assert(krnl.ctn_mp.dom().contains(krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container)) by { container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id); }; }
    proof {
        assert(krnl.ctn_mp.spec_index(krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container).view_rodata().view().depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().container_depth) by {
            container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id);
        };
    }
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let caller_ptr = cpu.owning_container();
    let requested = LockOwnerId::Some(cpu.process_depth());
    let container_res = krnl.wlock_container_unless_killed(caller_ptr, requested, Tracked(&mut *lctx));
    let Tracked(container_lock_perm) = match container_res {
        DynamicWLockResult::Acquired(perm) => perm,
        DynamicWLockResult::Killed(_) => {
            proof {
                let ghost pre = *krnl;
                let ghost pre_lctx = *lctx;
                krnl.u_sys_exit(lctx);
                u_sys_exit_eof(pre, *krnl, pre_lctx, *lctx);
            }
            krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
            proof {
                assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
                steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(caller_ptr), None, None, None, None, None);
                cpu_offline_request_child_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, target, RetValueType::ErrorContainerKilled);
                cpu_offline_request_child_result_from_k(&*old(krnl), cpu_id, child, target, RetValueType::ErrorContainerKilled, false);
            }
            return RetValueType::ErrorContainerKilled;
        },
        DynamicWLockResult::DepthConflict { .. } => {
            proof {
                let ghost pre = *krnl;
                let ghost pre_lctx = *lctx;
                krnl.u_sys_exit(lctx);
                u_sys_exit_eof(pre, *krnl, pre_lctx, *lctx);
            }
            krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
            proof {
                assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
                steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(caller_ptr), None, None, None, None, None);
                cpu_offline_request_child_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, target, RetValueType::ErrorContainerLockOrderConflict);
                cpu_offline_request_child_result_from_k(&*old(krnl), cpu_id, child, target, RetValueType::ErrorContainerLockOrderConflict, false);
            }
            return RetValueType::ErrorContainerLockOrderConflict;
        },
    };
    let caller = krnl.ctn_mp.borrow_typed(caller_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(&container_lock_perm));
    if caller.zombie {
        krnl.wunlock_container(caller_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        proof {
            let ghost pre = *krnl;
            let ghost pre_lctx = *lctx;
            krnl.u_sys_exit(lctx);
            u_sys_exit_eof(pre, *krnl, pre_lctx, *lctx);
        }
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(caller_ptr), None, None, None, None, None);
            cpu_offline_request_child_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, target, RetValueType::ErrorContainerZombie);
            cpu_offline_request_child_result_from_k(&*old(krnl), cpu_id, child, target, RetValueType::ErrorContainerZombie, false);
        }
        return RetValueType::ErrorContainerZombie;
    }
    proof { caller.children.lemma_len_view(); }
    if child >= caller.children.len() {
        krnl.wunlock_container(caller_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        proof {
            let ghost pre = *krnl;
            let ghost pre_lctx = *lctx;
            krnl.u_sys_exit(lctx);
            u_sys_exit_eof(pre, *krnl, pre_lctx, *lctx);
        }
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(caller_ptr), None, None, None, None, None);
            cpu_offline_request_child_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, target, RetValueType::ErrorCpuOwnerMismatch);
            cpu_offline_request_child_result_from_k(&*old(krnl), cpu_id, child, target, RetValueType::ErrorCpuOwnerMismatch, false);
        }
        return RetValueType::ErrorCpuOwnerMismatch;
    }
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    cpu_offline_request_child_locked(krnl, Tracked(lctx), Tracked(steps), cpu_id, child, target, caller_ptr, Tracked(cpu_lock_perm), Tracked(container_lock_perm))
}
}
