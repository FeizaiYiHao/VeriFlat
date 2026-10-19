use vstd::prelude::*;
use crate::*;
use super::syscall_cpu_hotplug_spec::*;
use super::syscall_cpu_hotplug_trace::*;
#[cfg(verus_keep_ghost)]
use super::cpu_online_child_eof::{cpu_online_child_eof, cpu_online_child_eof_transition_framing};

verus! {
/// Brings `target`, an Off cpu of the `child`-th child of the caller's live, non-zombie container, back to Idle under the
/// cpu, the caller's container, the child's cpu-set, and the Off-cpu locks, then wakes it with an IPI. Any
/// request bit of an Off cpu is already clear.
pub fn syscall_cpu_online_child(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, child: usize, target: CpuId) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
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
    proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }
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
    let container_res = krnl.wlock_container_unless_killed(caller_ptr, Tracked(&mut *lctx));
    if container_res.is_none() {
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(caller_ptr), None, None, None, None, None);
            cpu_online_child_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, target, RetValueType::ErrorContainerKilled);
            cpu_online_child_result_from_k(&*old(krnl), cpu_id, child, target, RetValueType::ErrorContainerKilled);
        }
        return RetValueType::ErrorContainerKilled;
    }
    let Tracked(container_lock_perm) = container_res.unwrap();
    proof { assert(!krnl.ctn_mp.spec_index(caller_ptr).view_ghost().owned_processes.view().is_empty()); }
    let caller = krnl.ctn_mp.borrow_typed(caller_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(&container_lock_perm));
    proof { caller.children.lemma_len_view(); }
    if caller.zombie || child >= caller.children.len() {
        let result = if caller.zombie { RetValueType::ErrorContainerZombie } else { RetValueType::ErrorCpuOwnerMismatch };
        krnl.wunlock_container(caller_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(caller_ptr), None, None, None, None, None);
            cpu_online_child_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, target, result);
            cpu_online_child_result_from_k(&*old(krnl), cpu_id, child, target, result);
        }
        return result;
    }
    let child_ptr = caller.children.get(child);
    proof {
        assert({
            &&& krnl.ctn_mp.dom().contains(child_ptr)
            &&& krnl.ctn_mp.spec_index(child_ptr).view_rodata().view().parent == Some(caller_ptr)
            &&& child_ptr != caller_ptr
        }) by { container_children_parent_wf_at(krnl.rt_ctn, krnl.ctn_mp, caller_ptr, child_ptr); container_root_wf_at(krnl.rt_ctn, krnl.ctn_mp, child_ptr); container_root_wf_at(krnl.rt_ctn, krnl.ctn_mp, krnl.rt_ctn); };
    }
    let child_ro = krnl.ctn_mp.borrow_rodata(child_ptr);
    let cpu_set_ptr = child_ro.borrow().cpu_set;
    proof { assert(krnl.cpu_set_mp.dom().contains(cpu_set_ptr) && krnl.cpu_set_mp.spec_index(cpu_set_ptr).inv()) by { container_cpu_set_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, child_ptr); cpu_set_perms_wf_at(krnl.cpu_set_mp, cpu_set_ptr); }; }
    let ghost cpu_set_unlocked_k = *krnl;
    let Tracked(cpu_set_lock_perm) = krnl.wlock_cpu_set(cpu_set_ptr, Tracked(lctx));
    let cpu_set = krnl.cpu_set_mp.borrow_typed(cpu_set_ptr, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&cpu_set_lock_perm));
    let result = if !cpu_set.owned_cpus.contains(target) { RetValueType::ErrorCpuOwnerMismatch }
        else if !cpu_set.owned_cpus.is_closed(target) { RetValueType::ErrorCpuNotOff }
        else { RetValueType::Success };
    proof {
        assert(result == cpu_online_child_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, child, target)) by {
            cpu_online_child_result_from_k(&*old(krnl), cpu_id, child, target, result);
        };
    }
    let success = if let RetValueType::Success = result { true } else { false };
    if !success {
        krnl.wunlock_cpu_set(cpu_set_ptr, Tracked(lctx), Tracked(cpu_set_lock_perm));
        proof { container_nonlock_fields_and_quotas_unchanged_for_cpu_set_relock(&cpu_set_unlocked_k, &*krnl, cpu_set_ptr); }
        krnl.wunlock_container(caller_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            cpu_online_child_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, target, result);
        }
        return result;
    }
    proof {
        assert({
            &&& krnl.cpu_arr.spec_index(target).view().view().view().state is Off
            &&& krnl.cpu_arr.spec_index(target).view().view().view().owning_container == child_ptr
            &&& target != cpu_id
            &&& !lctx.cpu_lock_map().dom().contains(target)
        }) by { container_cpu_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, child_ptr, target); cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), target); reveal(LockedArray::typed_lock_map_aligned); };
    }
    let Tracked(target_lock_perm) = krnl.wlock_off_cpu(target, cpu_set_ptr, Tracked(lctx));
    let ghost old_target_lock_id = krnl.cpu_arr.lock_id_by_index(target);
    let ghost online_pre = *krnl;
    {
        let cpu_set_mut = krnl.cpu_set_mp.borrow_mut_typed(cpu_set_ptr, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&cpu_set_lock_perm));
        cpu_set_mut.owned_cpus.mark_open(target);
        let target_cpu = krnl.cpu_arr.borrow_mut_typed(target, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&target_lock_perm));
        target_cpu.publish_idle_from_off();
    }
    proof {
        lctx.enter_kernel_view_release();
        lctx.update_lock_id(KernelObjId::Cpu(target), old_target_lock_id, krnl.cpu_arr.lock_id_by_index(target));
        assert(cpu_online_child_eof_transition_framing(online_pre, *krnl, cpu_set_ptr, target, child_ptr)) by { reveal(cpu_online_child_eof_transition_framing); };
        cpu_online_child_eof(online_pre, *krnl, cpu_set_ptr, target, child_ptr);
    }
    krnl.wunlock_cpu(target, Tracked(lctx), Tracked(target_lock_perm));
    krnl.wunlock_cpu_set(cpu_set_ptr, Tracked(lctx), Tracked(cpu_set_lock_perm));
    krnl.wunlock_container(caller_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
    proof {
        let ghost online_before = steps.view();
        assert(kernel_cpu_online_changed(&steps.snapshot_k(), &*krnl, cpu_id, child_ptr, target)) by { reveal(kernel_cpu_online_changed); };
        steps.end_kernel_step_cpu_online_changed(&*krnl, &*lctx, cpu_id, child_ptr, target);
        assert({
            &&& cpu_online_child_syscall_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, target, RetValueType::Success)
            &&& cpu_online_child_step_pre(steps.nonlock_view().last().old_u, cpu_id, target)
            &&& cpu_online_child_step(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, target)
        }) by {
            cpu_online_child_step_from_u(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, child_ptr, target);
            cpu_online_child_step_from_u(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, child_ptr, target);
            cpu_online_child_trace_step(&*steps, online_before, kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, target);
        };
    }
    send_ipi(target, Tracked(&*lctx));
    RetValueType::Success
}
}
