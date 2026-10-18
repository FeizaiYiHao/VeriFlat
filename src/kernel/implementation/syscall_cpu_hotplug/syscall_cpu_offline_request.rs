use vstd::prelude::*;
use crate::*;
use super::syscall_cpu_hotplug_spec::*;
use super::syscall_cpu_hotplug_trace::*;
#[cfg(verus_keep_ghost)]
use super::cpu_offline_request_eof::{cpu_offline_request_eof, cpu_offline_request_eof_transition_framing};

verus! {
/// Asks `target`, a cpu of the caller's container, to go Off at its next schedule check: the caller's
/// container table records the request under the cpu, the request cell, and the cpu-set lock, and
/// `target` is kicked into the kernel. The check itself is a separate step of the target cpu.
pub fn syscall_cpu_offline_request(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, target: CpuId) -> (ret: RetValueType)
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
        cpu_offline_request_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, target, ret),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).no_locks_held(),
        ret == cpu_offline_request_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, target),
        !(ret is Success && !cpu_offline_request_pending(kernel_k_to_kernel_u(*old(krnl)), cpu_id, target)) ==> final(steps).nonlock_view().len() == 0,
        ret is Success && !cpu_offline_request_pending(kernel_k_to_kernel_u(*old(krnl)), cpu_id, target) ==> {
            let step = final(steps).nonlock_view()[0];
            &&& final(steps).nonlock_view().len() == 1
            &&& step.old_u == kernel_k_to_nonlock_kernel_u(*old(krnl))
            &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
            &&& cpu_offline_request_step_pre(step.old_u, cpu_id, target)
            &&& cpu_offline_request_step(step.old_u, step.new_u, cpu_id, target)
        },
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }
    if target >= NUM_CPUS {
        proof {
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
            cpu_offline_request_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, target, RetValueType::ErrorCpuOwnerMismatch);
        }
        return RetValueType::ErrorCpuOwnerMismatch;
    }
    let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
    if cpu_lock_res.is_none() {
        proof {
            cpu_offline_request_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, target, RetValueType::CpuIdle);
            cpu_offline_request_result_from_k(&*old(krnl), cpu_id, target, RetValueType::CpuIdle, false);
        }
        return RetValueType::CpuIdle;
    }
    let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
    proof { assert(krnl.ctn_mp.dom().contains(krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container)) by { container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id); }; }
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let container_ptr = cpu.owning_container();
    proof {
        assert(page_ptr_2m_valid(container_ptr)) by { container_pages_backward_at(krnl.pg_arr, krnl.ctn_mp, container_ptr); };
        assert({
            &&& krnl.cpu_offline_mp.dom().contains(cpu_offline_flags_ptr(container_ptr))
            &&& krnl.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(container_ptr)).owning_container.view() == container_ptr
        }) by { container_cpu_offline_flags_wf_container_at(krnl.ctn_mp, krnl.cpu_offline_mp, container_ptr); };
    }
    let flags_ptr = container_ptr + 4096;
    let Tracked(flag_lock_perm) = krnl.wlock_cpu_offline_flag(flags_ptr, target, Tracked(lctx));
    proof { assert(krnl.ctn_mp.view().spec_index(container_ptr).is_init() && krnl.ctn_mp.view().spec_index(container_ptr).addr() == container_ptr) by { container_perms_wf_at(krnl.ctn_mp, container_ptr); }; }
    let container_ro = krnl.ctn_mp.borrow_rodata(container_ptr);
    let cpu_set_ptr = container_ro.borrow().cpu_set;
    proof { assert(krnl.cpu_set_mp.dom().contains(cpu_set_ptr) && krnl.cpu_set_mp.spec_index(cpu_set_ptr).inv()) by { container_cpu_set_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, container_ptr); cpu_set_perms_wf_at(krnl.cpu_set_mp, cpu_set_ptr); }; }
    let Tracked(cpu_set_lock_perm) = krnl.wlock_cpu_set(cpu_set_ptr, Tracked(lctx));
    let cpu_set = krnl.cpu_set_mp.borrow_typed(cpu_set_ptr, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&cpu_set_lock_perm));
    let result = if !cpu_set.owned_cpus.contains(target) { RetValueType::ErrorCpuOwnerMismatch }
        else if cpu_set.owned_cpus.is_closed(target) { RetValueType::ErrorCpuAlreadyOff }
        else { RetValueType::Success };
    let pending = krnl.cpu_offline_mp.read_flag(flags_ptr, target, Tracked(&flag_lock_perm));
    proof {
        assert(result == cpu_offline_request_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, target)
            && (result is Success ==> pending == cpu_offline_request_pending(kernel_k_to_kernel_u(*old(krnl)), cpu_id, target))) by {
            container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, target); container_cpu_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, container_ptr, target);
            container_cpu_wf_cpu_at(old(krnl).ctn_mp, old(krnl).cpu_set_mp, old(krnl).cpu_arr, target); container_cpu_wf_container_at(old(krnl).ctn_mp, old(krnl).cpu_set_mp, old(krnl).cpu_arr, container_ptr, target);
            cpu_offline_request_result_from_k(&*old(krnl), cpu_id, target, result, pending);
        };
        assert(result is Success ==> {
            &&& krnl.cpu_arr.spec_index(target).view().view().view().owning_container == container_ptr
            &&& !(krnl.cpu_arr.spec_index(target).view().view().view().state is Off)
        }) by { container_cpu_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, container_ptr, target); };
    }
    let success = if let RetValueType::Success = result { true } else { false };
    if !success || pending {
        krnl.wunlock_cpu_set(cpu_set_ptr, Tracked(lctx), Tracked(cpu_set_lock_perm));
        krnl.wunlock_cpu_offline_flag(flags_ptr, target, Tracked(lctx), Tracked(flag_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by {
                reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_cpu_set_wf);
            };
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            cpu_offline_request_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, target, result);
        }
        return result;
    }
    let ghost request_pre = *krnl;
    krnl.cpu_offline_mp.set_flag(flags_ptr, target, true, Tracked(&*lctx), Tracked(&flag_lock_perm));
    proof {
        assert(cpu_offline_request_eof_transition_framing(request_pre, *krnl, flags_ptr, target, container_ptr)) by { reveal(cpu_offline_request_eof_transition_framing); };
        cpu_offline_request_eof(request_pre, *krnl, flags_ptr, target, container_ptr);
        assert(typed_lock_maps_aligned(&*krnl, &*lctx)) by { reveal(UnLockedMap::typed_flag_lock_map_aligned); };
    }
    krnl.wunlock_cpu_set(cpu_set_ptr, Tracked(lctx), Tracked(cpu_set_lock_perm));
    krnl.wunlock_cpu_offline_flag(flags_ptr, target, Tracked(lctx), Tracked(flag_lock_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
    proof {
        let ghost request_before = steps.view();
        assert(kernel_cpu_offline_request_changed(&steps.snapshot_k(), &*krnl, cpu_id, container_ptr, target)) by { reveal(kernel_cpu_offline_request_changed); };
        steps.end_kernel_step_cpu_offline_request_changed(&*krnl, &*lctx, cpu_id, container_ptr, target);
        assert({
            &&& cpu_offline_request_syscall_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, target, RetValueType::Success)
            &&& cpu_offline_request_step_pre(steps.nonlock_view().last().old_u, cpu_id, target)
            &&& cpu_offline_request_step(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, target)
        }) by {
            cpu_offline_request_step_from_u(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, container_ptr, target);
            cpu_offline_request_step_from_u(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, container_ptr, target);
            cpu_offline_request_trace_step(&*steps, request_before, kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, target);
        };
    }
    if target != cpu_id { send_ipi(target, Tracked(&*lctx)); }
    RetValueType::Success
}
}
