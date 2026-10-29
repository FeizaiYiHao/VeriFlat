use vstd::prelude::*;
use crate::*;
use super::syscall_cpu_hotplug_spec::*;
use super::syscall_cpu_hotplug_trace::*;
#[cfg(verus_keep_ghost)]
use super::cpu_online_child_eof::{cpu_online_child_eof, cpu_online_child_eof_transition_framing};

verus! {
/// With `cpu_id` and the caller's live, non-zombie container `caller_ptr` write-held since the step's start, brings `target`,
/// an Off cpu of the `child`-th child, back to Idle under the child's cpu-set and the Off-cpu locks, wakes `target` with an
/// IPI while still holding it, and releases every lock.
pub(super) fn cpu_online_child_locked(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, child: usize, target: CpuId,
    caller_ptr: RwLockContainerPtr, Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(container_lock_perm): Tracked<LockPerm>,
) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, target),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(steps).snapshot_k().inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).nonlock_view().len() == 0,
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, ctn_mp: old(krnl).ctn_mp, ..old(steps).snapshot_k() }),
        old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).ctn_mp.unchanged_except(&old(steps).snapshot_k().ctn_mp, caller_ptr),
        old(krnl).ctn_mp.perms_wf(),
        !old(krnl).ctn_mp.spec_index(caller_ptr).view_ghost().owned_processes.view().is_empty(),
        ({
            let pre = old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view();
            let post = old(krnl).cpu_arr.spec_index(cpu_id).view();
            &&& post.view().view() == pre.view().view()
            &&& post.locking_thread() == RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cpu_lock_perm.lock_id() }
            &&& post.being_killed() == pre.being_killed()
            &&& post.killer_info() == pre.killer_info()
            &&& pre.locked() == false
            &&& cpu_lock_perm.state() is WriteLock
            &&& cpu_lock_perm.thread_id() == old(lctx).thread_id()
        }),
        !old(steps).snapshot_k().ctn_mp.spec_index(caller_ptr).locked(),
        ({
            let pre_c = old(steps).snapshot_k().ctn_mp.spec_index(caller_ptr);
            let c = old(krnl).ctn_mp.spec_index(caller_ptr);
            &&& c.locking_thread() == RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: container_lock_perm.lock_id() }
            &&& c.inv()
            &&& !c.being_killed()
            &&& c.view() == pre_c.view()
            &&& c.view_rodata() == pre_c.view_rodata()
            &&& c.view_ghost() == pre_c.view_ghost()
            &&& container_lock_perm.state() is WriteLock
            &&& container_lock_perm.thread_id() == old(lctx).thread_id()
        }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), caller_ptr, TypedLockMode::Write),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom() =~= set![caller_ptr],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
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
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        !old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view().owning_container == caller_ptr,
        old(steps).snapshot_k().ctn_mp.dom().contains(caller_ptr),
        !old(steps).snapshot_k().ctn_mp.spec_index(caller_ptr).being_killed(),
        !old(steps).snapshot_k().ctn_mp.spec_index(caller_ptr).view().zombie,
        child < old(steps).snapshot_k().ctn_mp.spec_index(caller_ptr).view().children.view().len(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        cpu_online_child_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, target, ret),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).no_locks_held(),
        ret == cpu_online_child_syscall_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, child, target),
        !(ret is Success) ==> final(steps).nonlock_view().len() == 0,
        ret is Success ==> {
            let step = final(steps).nonlock_view()[0];
            &&& final(steps).nonlock_view().len() == 1
            &&& step.old_u == kernel_k_to_nonlock_kernel_u(old(steps).snapshot_k())
            &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
            &&& cpu_online_child_step_pre(step.old_u, cpu_id, target)
            &&& cpu_online_child_step(step.old_u, step.new_u, cpu_id, target)
        },
{
    let ghost entry = steps.snapshot_k();
    let caller = krnl.ctn_mp.borrow_typed(caller_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(&container_lock_perm));
    proof { caller.children.lemma_len_view(); }
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
    proof {
        // A marked set belongs to a marked child, whose killer write-holds the caller container held here; that
        // killer's process lock would then be held here too.
        assert(!krnl.cpu_set_mp.spec_index(cpu_set_ptr).being_killed()) by {
            container_cpu_set_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, child_ptr); cpu_set_kill_mark_wf_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.prc_mp, cpu_set_ptr);
            container_kill_mark_wf_at(krnl.ctn_mp, krnl.prc_mp, child_ptr); krnl.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), caller_ptr);
            if krnl.cpu_set_mp.spec_index(cpu_set_ptr).being_killed() {
                krnl.prc_mp.typed_lock_map_aligned_locked_at(lctx.process_lock_map(), lctx.thread_id(), krnl.ctn_mp.spec_index(child_ptr).killer_info()->Some_0.process);
            }
        };
    }
    let ghost cpu_set_unlocked_k = *krnl;
    let Tracked(cpu_set_lock_perm) = krnl.wlock_cpu_set(cpu_set_ptr, Tracked(lctx));
    let cpu_set = krnl.cpu_set_mp.borrow_typed(cpu_set_ptr, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&cpu_set_lock_perm));
    let result = if !cpu_set.owned_cpus.contains(target) { RetValueType::ErrorCpuOwnerMismatch }
        else if !cpu_set.owned_cpus.is_closed(target) { RetValueType::ErrorCpuNotOff }
        else { RetValueType::Success };
    proof {
        assert(result == cpu_online_child_syscall_result(kernel_k_to_kernel_u(entry), cpu_id, child, target)) by {
            cpu_online_child_result_from_k(&entry, cpu_id, child, target, result);
        };
    }
    let success = if let RetValueType::Success = result { true } else { false };
    if !success {
        krnl.wunlock_cpu_set(cpu_set_ptr, Tracked(lctx), Tracked(cpu_set_lock_perm));
        proof { container_nonlock_fields_and_quotas_unchanged_for_cpu_set_relock(&cpu_set_unlocked_k, &*krnl, cpu_set_ptr); }
        krnl.wunlock_container(caller_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_own_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
        proof {
            assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            cpu_online_child_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(entry), cpu_id, target, result);
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
    proof { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, target); }
    let ghost old_target_lock_id = krnl.cpu_arr.lock_id_by_index(target);
    let ghost online_pre = *krnl;
    {
        let cpu_set_mut = krnl.cpu_set_mp.borrow_mut_typed(cpu_set_ptr, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&cpu_set_lock_perm));
        cpu_set_mut.owned_cpus.mark_open(target);
        let target_cpu = krnl.cpu_arr.borrow_mut_typed(target, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&target_lock_perm));
        target_cpu.publish_idle_from_off();
    }
    proof { lctx.enter_kernel_view_release(); lctx.update_lock_id(KernelObjId::Cpu(target), old_target_lock_id, krnl.cpu_arr.lock_id_by_index(target)); }
    krnl.cpu_arr.wake_remote(target, Tracked(krnl.cpu_op.borrow_mut()), Tracked(&*lctx), Tracked(&target_lock_perm));
    proof {
        assert(cpu_online_child_eof_transition_framing(online_pre, *krnl, cpu_set_ptr, target, child_ptr)) by { reveal(cpu_online_child_eof_transition_framing); };
        cpu_online_child_eof(online_pre, *krnl, cpu_set_ptr, target, child_ptr);
    }
    krnl.wunlock_cpu(target, Tracked(lctx), Tracked(target_lock_perm));
    krnl.wunlock_cpu_set(cpu_set_ptr, Tracked(lctx), Tracked(cpu_set_lock_perm));
    krnl.wunlock_container(caller_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
    krnl.wunlock_own_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
    proof {
        let ghost online_before = steps.view();
        assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view().update(target as int, CpuOpState::Idle));
        assert(kernel_cpu_online_changed(&steps.snapshot_k(), &*krnl, cpu_id, child_ptr, target)) by { reveal(kernel_cpu_online_changed); };
        steps.end_kernel_step_cpu_online_changed(&*krnl, &*lctx, cpu_id, child_ptr, target);
        assert({
            &&& cpu_online_child_syscall_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(entry), kernel_k_to_kernel_u(*krnl), cpu_id, target, RetValueType::Success)
            &&& cpu_online_child_step_pre(steps.nonlock_view().last().old_u, cpu_id, target)
            &&& cpu_online_child_step(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, target)
        }) by {
            cpu_online_child_step_from_u(kernel_k_to_kernel_u(entry), kernel_k_to_kernel_u(*krnl), cpu_id, child_ptr, target);
            cpu_online_child_step_from_u(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, child_ptr, target);
            cpu_online_child_trace_step(&*steps, online_before, kernel_k_to_kernel_u(entry), kernel_k_to_kernel_u(*krnl), cpu_id, target);
        };
    }
    RetValueType::Success
}
}
