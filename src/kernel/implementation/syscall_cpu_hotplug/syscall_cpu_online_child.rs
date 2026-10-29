use vstd::prelude::*;
use crate::*;
use super::syscall_cpu_hotplug_spec::*;
use super::syscall_cpu_hotplug_trace::*;
use super::syscall_cpu_online_child_locked::cpu_online_child_locked;

verus! {
/// Brings `target`, an Off cpu of the `child`-th child of the caller's live, non-zombie container, back to Idle under the
/// cpu, the caller's container, the child's cpu-set, and the Off-cpu locks and wakes it with an IPI while still holding it.
/// Any request bit of an Off cpu is already clear.
pub fn syscall_cpu_online_child(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, child: usize, target: CpuId) -> (ret: RetValueType)
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
        cpu_online_child_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, target, ret),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).no_locks_held(),
        ret == cpu_online_child_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, child, target),
        !(ret is Success) ==> final(steps).nonlock_view().len() == 0,
        ret is Success ==> {
            let step = final(steps).nonlock_view()[0];
            &&& final(steps).nonlock_view().len() == 1
            &&& step.old_u == kernel_k_to_nonlock_kernel_u(*old(krnl))
            &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
            &&& cpu_online_child_step_pre(step.old_u, cpu_id, target)
            &&& cpu_online_child_step(step.old_u, step.new_u, cpu_id, target)
        },
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    if target >= NUM_CPUS {
        proof {
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
            cpu_online_child_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, target, RetValueType::ErrorCpuOwnerMismatch);
        }
        return RetValueType::ErrorCpuOwnerMismatch;
    }
    let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
    if cpu_lock_res.is_none() {
        proof {
            cpu_online_child_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, target, RetValueType::CpuIdle);
            cpu_online_child_result_from_k(&*old(krnl), cpu_id, child, target, RetValueType::CpuIdle);
        }
        return RetValueType::CpuIdle;
    }
    let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
    proof {
        let cpu = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
        assert(krnl.ctn_mp.dom().contains(cpu.owning_container) && krnl.ctn_mp.spec_index(cpu.owning_container).view_rodata().view().depth == cpu.container_depth) by { container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id); };
    }
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let caller_ptr = cpu.owning_container();
    let requested = LockOwnerId::Some(cpu.process_depth());
    let container_res = krnl.wlock_container_unless_killed(caller_ptr, requested, Tracked(&mut *lctx));
    let Tracked(container_lock_perm) = match container_res {
        DynamicWLockResult::Acquired(perm) => perm,
        DynamicWLockResult::Killed(_) => {
            krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
            proof {
                assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
                steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(caller_ptr), None, None, None, None, None);
                cpu_online_child_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, target, RetValueType::ErrorContainerKilled);
                cpu_online_child_result_from_k(&*old(krnl), cpu_id, child, target, RetValueType::ErrorContainerKilled);
            }
            return RetValueType::ErrorContainerKilled;
        },
        DynamicWLockResult::DepthConflict { .. } => {
            krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
            proof {
                assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
                steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(caller_ptr), None, None, None, None, None);
                cpu_online_child_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, target, RetValueType::ErrorContainerLockOrderConflict);
                cpu_online_child_result_from_k(&*old(krnl), cpu_id, child, target, RetValueType::ErrorContainerLockOrderConflict);
            }
            return RetValueType::ErrorContainerLockOrderConflict;
        },
    };
    proof { assert(!krnl.ctn_mp.spec_index(caller_ptr).view_ghost().owned_processes.view().is_empty()); }
    let caller = krnl.ctn_mp.borrow_typed(caller_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(&container_lock_perm));
    proof { caller.children.lemma_len_view(); }
    if caller.zombie || child >= caller.children.len() {
        let result = if caller.zombie { RetValueType::ErrorContainerZombie } else { RetValueType::ErrorCpuOwnerMismatch };
        krnl.wunlock_container(caller_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(caller_ptr), None, None, None, None, None);
            cpu_online_child_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, target, result);
            cpu_online_child_result_from_k(&*old(krnl), cpu_id, child, target, result);
        }
        return result;
    }
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    cpu_online_child_locked(krnl, Tracked(lctx), Tracked(steps), cpu_id, child, target, caller_ptr, Tracked(cpu_lock_perm), Tracked(container_lock_perm))
}
}
