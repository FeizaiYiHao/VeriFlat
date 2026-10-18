use vstd::prelude::*;
use crate::*;
use super::syscall_cpu_hotplug_spec::*;
use super::syscall_cpu_hotplug_trace::*;
#[cfg(verus_keep_ghost)]
use super::cpu_offline_request_child_eof::{cpu_offline_request_child_eof, cpu_offline_request_child_transition_framing};

verus! {
/// Asks `target`, a cpu of the `child`-th child of the caller's live, non-zombie container, to go Off at its next schedule
/// check: under the cpu, the caller's container, the child's request cell, and the child's cpu-set lock, the
/// child's table records the request, and `target` is kicked into the kernel.
pub fn syscall_cpu_offline_request_child(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, child: usize, target: CpuId) -> (ret: RetValueType)
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
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let caller_ptr = cpu.owning_container();
    let container_res = krnl.wlock_container_unless_killed(caller_ptr, Tracked(&mut *lctx));
    if container_res.is_none() {
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(caller_ptr), None, None, None, None, None);
            cpu_offline_request_child_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, target, RetValueType::ErrorContainerKilled);
            cpu_offline_request_child_result_from_k(&*old(krnl), cpu_id, child, target, RetValueType::ErrorContainerKilled, false);
        }
        return RetValueType::ErrorContainerKilled;
    }
    let Tracked(container_lock_perm) = container_res.unwrap();
    proof { assert(!krnl.ctn_mp.spec_index(caller_ptr).view_ghost().owned_processes.view().is_empty()) by { reveal(container_process_wf); }; }
    let caller = krnl.ctn_mp.borrow_typed(caller_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(&container_lock_perm));
    if caller.zombie {
        krnl.wunlock_container(caller_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(caller_ptr), None, None, None, None, None);
            cpu_offline_request_child_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, target, RetValueType::ErrorContainerZombie);
            cpu_offline_request_child_result_from_k(&*old(krnl), cpu_id, child, target, RetValueType::ErrorContainerZombie, false);
        }
        return RetValueType::ErrorContainerZombie;
    }
    proof { caller.children.lemma_len_view(); }
    if child >= caller.children.len() {
        krnl.wunlock_container(caller_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(caller_ptr), None, None, None, None, None);
            cpu_offline_request_child_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, target, RetValueType::ErrorCpuOwnerMismatch);
            cpu_offline_request_child_result_from_k(&*old(krnl), cpu_id, child, target, RetValueType::ErrorCpuOwnerMismatch, false);
        }
        return RetValueType::ErrorCpuOwnerMismatch;
    }
    let child_ptr = caller.children.get(child);
    proof {
        assert({
            &&& krnl.ctn_mp.dom().contains(child_ptr)
            &&& krnl.ctn_mp.spec_index(child_ptr).view_rodata().view().parent == Some(caller_ptr)
            &&& child_ptr != caller_ptr
        }) by { reveal(container_children_parent_wf); reveal(container_root_wf); };
        assert(page_ptr_2m_valid(child_ptr)) by { reveal(container_pages_wf); };
        assert({
            &&& krnl.cpu_offline_mp.dom().contains(cpu_offline_flags_ptr(child_ptr))
            &&& krnl.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(child_ptr)).owning_container.view() == child_ptr
        }) by { reveal(container_cpu_offline_flags_wf); };
    }
    let flags_ptr = child_ptr + 4096;
    let Tracked(flag_lock_perm) = krnl.wlock_cpu_offline_flag(flags_ptr, target, Tracked(lctx));
    let child_ro = krnl.ctn_mp.borrow_rodata(child_ptr);
    let cpu_set_ptr = child_ro.borrow().cpu_set;
    proof { assert(krnl.cpu_set_mp.dom().contains(cpu_set_ptr) && krnl.cpu_set_mp.spec_index(cpu_set_ptr).inv()) by { reveal(container_cpu_set_wf); reveal(cpu_set_perms_wf); }; }
    let Tracked(cpu_set_lock_perm) = krnl.wlock_cpu_set(cpu_set_ptr, Tracked(lctx));
    let cpu_set = krnl.cpu_set_mp.borrow_typed(cpu_set_ptr, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&cpu_set_lock_perm));
    let result = if !cpu_set.owned_cpus.contains(target) { RetValueType::ErrorCpuOwnerMismatch }
        else if cpu_set.owned_cpus.is_closed(target) { RetValueType::ErrorCpuAlreadyOff }
        else { RetValueType::Success };
    let pending = krnl.cpu_offline_mp.read_flag(flags_ptr, target, Tracked(&flag_lock_perm));
    proof {
        assert(result == cpu_offline_request_child_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, child, target)
            && (result is Success ==> pending == cpu_offline_request_child_pending(kernel_k_to_kernel_u(*old(krnl)), target))) by {
            container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, target); container_cpu_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, child_ptr, target);
            container_cpu_wf_cpu_at(old(krnl).ctn_mp, old(krnl).cpu_set_mp, old(krnl).cpu_arr, target); container_cpu_wf_container_at(old(krnl).ctn_mp, old(krnl).cpu_set_mp, old(krnl).cpu_arr, child_ptr, target);
            cpu_offline_request_child_result_from_k(&*old(krnl), cpu_id, child, target, result, pending);
        };
        assert(result is Success ==> {
            &&& krnl.cpu_arr.spec_index(target).view().view().view().owning_container == child_ptr
            &&& !(krnl.cpu_arr.spec_index(target).view().view().view().state is Off)
            &&& target != cpu_id
        }) by {
            container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, target); container_cpu_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, child_ptr, target);
            container_cpu_wf_cpu_at(old(krnl).ctn_mp, old(krnl).cpu_set_mp, old(krnl).cpu_arr, target); container_cpu_wf_container_at(old(krnl).ctn_mp, old(krnl).cpu_set_mp, old(krnl).cpu_arr, child_ptr, target);
        };
    }
    let success = if let RetValueType::Success = result { true } else { false };
    if !success || pending {
        krnl.wunlock_cpu_set(cpu_set_ptr, Tracked(lctx), Tracked(cpu_set_lock_perm));
        krnl.wunlock_cpu_offline_flag(flags_ptr, target, Tracked(lctx), Tracked(flag_lock_perm));
        krnl.wunlock_container(caller_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by {
                reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_cpu_set_wf);
            };
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            cpu_offline_request_child_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, target, result);
        }
        return result;
    }
    let ghost request_pre = *krnl;
    krnl.cpu_offline_mp.set_flag(flags_ptr, target, true, Tracked(&*lctx), Tracked(&flag_lock_perm));
    proof {
        assert(cpu_offline_request_child_transition_framing(request_pre, *krnl, flags_ptr, target, child_ptr)) by { reveal(cpu_offline_request_child_transition_framing); };
        cpu_offline_request_child_eof(request_pre, *krnl, flags_ptr, target, child_ptr);
        assert(typed_lock_maps_aligned(&*krnl, &*lctx)) by { reveal(UnLockedMap::typed_flag_lock_map_aligned); };
    }
    krnl.wunlock_cpu_set(cpu_set_ptr, Tracked(lctx), Tracked(cpu_set_lock_perm));
    krnl.wunlock_cpu_offline_flag(flags_ptr, target, Tracked(lctx), Tracked(flag_lock_perm));
    krnl.wunlock_container(caller_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
    proof {
        let ghost request_before = steps.view();
        assert(kernel_cpu_offline_request_changed(&steps.snapshot_k(), &*krnl, cpu_id, child_ptr, target)) by { reveal(kernel_cpu_offline_request_changed); };
        steps.end_kernel_step_cpu_offline_request_changed(&*krnl, &*lctx, cpu_id, child_ptr, target);
        no_locks_held_imply_all_objects_unlocked(&*krnl, &*lctx);
        assert({
            &&& cpu_offline_request_child_syscall_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, target, RetValueType::Success)
            &&& cpu_offline_request_child_step_pre(steps.nonlock_view().last().old_u, cpu_id, target)
            &&& cpu_offline_request_child_step(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, target)
        }) by {
            cpu_offline_request_child_step_from_u(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, child_ptr, target);
            cpu_offline_request_child_step_from_u(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, child_ptr, target);
            cpu_offline_request_child_trace_step(&*steps, request_before, kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, target);
        };
    }
    send_ipi(target, Tracked(&*lctx));
    RetValueType::Success
}
}
