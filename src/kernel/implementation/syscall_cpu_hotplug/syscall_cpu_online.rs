use vstd::prelude::*;
use crate::*;
use super::syscall_cpu_hotplug_spec::*;
use super::syscall_cpu_hotplug_trace::*;

verus! {
/// Brings `target`, an Off cpu of the caller's container, back to Idle under the cpu, cpu-set, and
/// Off-cpu locks, then wakes it with an IPI. Any request bit of an Off cpu is already clear.
pub fn syscall_cpu_online(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, target: CpuId) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running,
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
        cpu_online_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, target, ret),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).no_locks_held(),
        ret == cpu_online_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, target),
        !(ret is Success) ==> final(steps).nonlock_view().len() == 0,
        ret is Success ==> {
            let step = final(steps).nonlock_view()[0];
            &&& final(steps).nonlock_view().len() == 1
            &&& step.old_u == kernel_k_to_nonlock_kernel_u(*old(krnl))
            &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
            &&& cpu_online_step_pre(step.old_u, cpu_id, target)
            &&& cpu_online_step(step.old_u, step.new_u, cpu_id, target)
        },
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }
    if target >= NUM_CPUS {
        proof {
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
            cpu_online_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, target, RetValueType::ErrorCpuOwnerMismatch);
        }
        return RetValueType::ErrorCpuOwnerMismatch;
    }
    proof {
        assert(krnl.ctn_mp.dom().contains(krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container)) by { reveal(container_cpu_wf); };
    }
    let Tracked(cpu_lock_perm) = krnl.wlock_cpu(cpu_id, Tracked(lctx));
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let container_ptr = cpu.owning_container();
    proof {
        assert(krnl.ctn_mp.view().spec_index(container_ptr).is_init() && krnl.ctn_mp.view().spec_index(container_ptr).addr() == container_ptr) by { reveal(container_perms_wf); };
    }
    let container_ro = krnl.ctn_mp.borrow_rodata(container_ptr);
    let cpu_set_ptr = container_ro.borrow().cpu_set;
    proof { assert(krnl.cpu_set_mp.dom().contains(cpu_set_ptr) && krnl.cpu_set_mp.spec_index(cpu_set_ptr).inv()) by { reveal(container_cpu_set_wf); reveal(cpu_set_perms_wf); }; }
    let Tracked(cpu_set_lock_perm) = krnl.wlock_cpu_set(cpu_set_ptr, Tracked(lctx));
    let cpu_set = krnl.cpu_set_mp.borrow_typed(cpu_set_ptr, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&cpu_set_lock_perm));
    let result = if !cpu_set.owned_cpus.contains(target) { RetValueType::ErrorCpuOwnerMismatch }
        else if !cpu_set.owned_cpus.is_closed(target) { RetValueType::ErrorCpuNotOff }
        else { RetValueType::Success };
    proof {
        assert(result == cpu_online_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, target)) by {
            reveal(container_cpu_wf); kernel_cpu_projection_at(&*old(krnl), cpu_id); kernel_cpu_projection_at(&*old(krnl), target);
        };
    }
    let success = if let RetValueType::Success = result { true } else { false };
    if !success {
        krnl.wunlock_cpu_set(cpu_set_ptr, Tracked(lctx), Tracked(cpu_set_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_cpu_set_wf); };
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            cpu_online_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, target, result);
        }
        return result;
    }
    proof {
        assert({
            &&& krnl.cpu_arr.spec_index(target).view().view().view().state is Off
            &&& krnl.cpu_arr.spec_index(target).view().view().view().owning_container == container_ptr
            &&& target != cpu_id
            &&& !lctx.cpu_lock_map().dom().contains(target)
        }) by { reveal(container_cpu_wf); reveal(cpu_array_wf); reveal(LockedArray::typed_lock_map_aligned); };
    }
    let Tracked(target_lock_perm) = krnl.wlock_off_cpu(target, cpu_set_ptr, Tracked(lctx));
    let ghost old_target_lock_id = krnl.cpu_arr.lock_id_by_index(target);
    {
        let cpu_set_mut = krnl.cpu_set_mp.borrow_mut_typed(cpu_set_ptr, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&cpu_set_lock_perm));
        cpu_set_mut.owned_cpus.mark_open(target);
        let target_cpu = krnl.cpu_arr.borrow_mut_typed(target, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&target_lock_perm));
        target_cpu.publish_idle_from_off();
    }
    proof {
        lctx.enter_kernel_view_release();
        lctx.update_lock_id(KernelObjId::Cpu(target), old_target_lock_id, krnl.cpu_arr.lock_id_by_index(target));
        assert(krnl.subsystems_inv()) by {
            reveal(cpu_array_wf); reveal(cpu_published_wf); reveal(cpu_offline_flags_wf); reveal(cpu_set_perms_wf); reveal(KernelK::default_pagetable_wf);
        };
        assert(krnl.memory_management_inv()) by { reveal(cpu_set_pages_wf); };
        assert(krnl.process_management_inv()) by {
            reveal(container_cpu_wf); reveal(container_cpu_set_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf); reveal(cpu_array_wf);
        };
        assert(cpu_dirty_map_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.prc_mp, krnl.cpu_arr, krnl.cpu_tlb, krnl.pt_mp, krnl.pcid_needflush)) by {
            reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match);
        };
        assert(tlb_wf_spec(krnl.cpu_tlb, krnl.pt_mp, krnl.cpu_arr, krnl.pcid_needflush)) by { reveal(tlb_wf_spec); };
    }
    krnl.wunlock_cpu(target, Tracked(lctx), Tracked(target_lock_perm));
    krnl.wunlock_cpu_set(cpu_set_ptr, Tracked(lctx), Tracked(cpu_set_lock_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
    proof {
        let ghost online_before = steps.view();
        assert(kernel_cpu_online_changed(&steps.snapshot_k(), &*krnl, cpu_id, container_ptr, target)) by { reveal(kernel_cpu_online_changed); };
        steps.end_kernel_step_cpu_online_changed(&*krnl, &*lctx, cpu_id, container_ptr, target);
        no_locks_held_imply_all_objects_unlocked(&*krnl, &*lctx);
        assert({
            &&& cpu_online_syscall_trace(
                steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, target,
                RetValueType::Success,
            )
            &&& cpu_online_step_pre(steps.nonlock_view().last().old_u, cpu_id, target)
            &&& cpu_online_step(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, target)
        }) by {
            cpu_online_step_from_u(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, container_ptr, target);
            cpu_online_step_from_u(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, container_ptr, target);
            cpu_online_trace_step(&*steps, online_before, kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, target);
        };
    }
    send_ipi(target, Tracked(&*lctx));
    RetValueType::Success
}
}
