use vstd::prelude::*;
use crate::*;
use super::syscall_cpu_hotplug_spec::*;
use super::syscall_cpu_hotplug_trace::*;
#[cfg(verus_keep_ghost)]
use super::cpu_offline_request_child_eof::{cpu_offline_request_child_eof, cpu_offline_request_child_eof_transition_framing};
#[cfg(verus_keep_ghost)]
use crate::kernel::implementation::locker_unlocker::u_sys_exit_eof;

verus! {
/// With `cpu_id` and the caller's live, non-zombie container `caller_ptr` write-held since the step's start, asks `target`, a
/// cpu of the `child`-th child, to go Off under the child's request cell and cpu-set locks and releases every lock; the
/// target notices the request on its next pass through its idle loop or schedule check.
pub(super) fn cpu_offline_request_child_locked(
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
            &&& post.view_ghost() == Some(cpu_id)
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
        cpu_offline_request_child_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, target, ret),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).no_locks_held(),
        ret == cpu_offline_request_child_syscall_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, child, target),
        !(ret is Success && !cpu_offline_request_child_pending(kernel_k_to_kernel_u(old(steps).snapshot_k()), target)) ==> final(steps).nonlock_view().len() == 0,
        ret is Success && !cpu_offline_request_child_pending(kernel_k_to_kernel_u(old(steps).snapshot_k()), target) ==> {
            let step = final(steps).nonlock_view()[0];
            &&& final(steps).nonlock_view().len() == 1
            &&& step.old_u == kernel_k_to_nonlock_kernel_u(old(steps).snapshot_k())
            &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
            &&& cpu_offline_request_child_step_pre(step.old_u, cpu_id, target)
            &&& cpu_offline_request_child_step(step.old_u, step.new_u, cpu_id, target)
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
            &&& krnl.ctn_mp.spec_index(child_ptr).view_rodata().view().depth == krnl.ctn_mp.spec_index(caller_ptr).view_rodata().view().depth + 1
            &&& krnl.ctn_mp.spec_index(caller_ptr).view_rodata().view().depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().container_depth
        }) by {
            container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id); container_children_parent_wf_at(krnl.rt_ctn, krnl.ctn_mp, caller_ptr, child_ptr);
            container_root_wf_at(krnl.rt_ctn, krnl.ctn_mp, child_ptr); container_root_wf_at(krnl.rt_ctn, krnl.ctn_mp, krnl.rt_ctn);
        };
        assert(page_ptr_2m_valid(child_ptr)) by { container_pages_backward_at(krnl.pg_arr, krnl.ctn_mp, child_ptr); };
        assert({
            &&& krnl.cpu_offline_mp.dom().contains(cpu_offline_flags_ptr(child_ptr))
            &&& krnl.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(child_ptr)).owning_container.view() == child_ptr
            &&& krnl.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(child_ptr)).container_depth.view() == krnl.ctn_mp.spec_index(child_ptr).view_rodata().view().depth
        }) by { container_cpu_offline_flags_wf_container_at(krnl.ctn_mp, krnl.cpu_offline_mp, child_ptr); };
    }
    let flags_ptr = child_ptr + 4096;
    let Tracked(flag_lock_perm) = krnl.wlock_cpu_offline_flag(flags_ptr, target, Tracked(lctx));
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
    let Tracked(cpu_set_lock_perm) = krnl.wlock_cpu_set(cpu_set_ptr, Tracked(lctx));
    let cpu_set = krnl.cpu_set_mp.borrow_typed(cpu_set_ptr, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&cpu_set_lock_perm));
    let result = if !cpu_set.owned_cpus.contains(target) { RetValueType::ErrorCpuOwnerMismatch }
        else if cpu_set.owned_cpus.is_closed(target) { RetValueType::ErrorCpuAlreadyOff }
        else { RetValueType::Success };
    let pending = krnl.cpu_offline_mp.read_flag(flags_ptr, target, Tracked(&flag_lock_perm));
    proof {
        assert(result == cpu_offline_request_child_syscall_result(kernel_k_to_kernel_u(entry), cpu_id, child, target)
            && (result is Success ==> pending == cpu_offline_request_child_pending(kernel_k_to_kernel_u(entry), target))) by {
            container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, target); container_cpu_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, child_ptr, target);
            container_cpu_wf_cpu_at(entry.ctn_mp, entry.cpu_set_mp, entry.cpu_arr, target); container_cpu_wf_container_at(entry.ctn_mp, entry.cpu_set_mp, entry.cpu_arr, child_ptr, target);
            cpu_offline_request_child_result_from_k(&entry, cpu_id, child, target, result, pending);
        };
        assert(result is Success ==> {
            &&& krnl.cpu_arr.spec_index(target).view().view().view().owning_container == child_ptr
            &&& !(krnl.cpu_arr.spec_index(target).view().view().view().state is Off)
            &&& target != cpu_id
        }) by {
            container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, target); container_cpu_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, child_ptr, target);
            container_cpu_wf_cpu_at(entry.ctn_mp, entry.cpu_set_mp, entry.cpu_arr, target); container_cpu_wf_container_at(entry.ctn_mp, entry.cpu_set_mp, entry.cpu_arr, child_ptr, target);
        };
    }
    let success = if let RetValueType::Success = result { true } else { false };
    if !success || pending {
        krnl.wunlock_cpu_set(cpu_set_ptr, Tracked(lctx), Tracked(cpu_set_lock_perm));
        krnl.wunlock_cpu_offline_flag(flags_ptr, target, Tracked(lctx), Tracked(flag_lock_perm));
        krnl.wunlock_container(caller_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        proof {
            let ghost pre = *krnl;
            let ghost pre_lctx = *lctx;
            krnl.u_sys_exit(lctx);
            u_sys_exit_eof(pre, *krnl, pre_lctx, *lctx);
        }
        krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
        proof {
            assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            cpu_offline_request_child_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(entry), cpu_id, target, result);
        }
        return result;
    }
    let ghost request_pre = *krnl;
    krnl.cpu_offline_mp.set_flag(flags_ptr, target, true, Tracked(&*lctx), Tracked(&flag_lock_perm));
    proof {
        assert(cpu_offline_request_child_eof_transition_framing(request_pre, *krnl, flags_ptr, target, child_ptr)) by { reveal(cpu_offline_request_child_eof_transition_framing); };
        cpu_offline_request_child_eof(request_pre, *krnl, flags_ptr, target, child_ptr);
        assert(typed_lock_maps_aligned(&*krnl, &*lctx)) by { reveal(UnLockedMap::typed_flag_lock_map_aligned); };
    }
    krnl.wunlock_cpu_set(cpu_set_ptr, Tracked(lctx), Tracked(cpu_set_lock_perm));
    krnl.wunlock_cpu_offline_flag(flags_ptr, target, Tracked(lctx), Tracked(flag_lock_perm));
    krnl.wunlock_container(caller_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
    proof {
        let ghost pre = *krnl;
        let ghost pre_lctx = *lctx;
        krnl.u_sys_exit(lctx);
        u_sys_exit_eof(pre, *krnl, pre_lctx, *lctx);
    }
    krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
    proof {
        let ghost request_before = steps.view();
        assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
        assert(kernel_cpu_offline_request_changed(&steps.snapshot_k(), &*krnl, cpu_id, child_ptr, target)) by { reveal(kernel_cpu_offline_request_changed); };
        steps.end_kernel_step_cpu_offline_request_changed(&*krnl, &*lctx, cpu_id, child_ptr, target);
        no_locks_held_imply_all_objects_unlocked(&*krnl, &*lctx);
        assert({
            &&& cpu_offline_request_child_syscall_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(entry), kernel_k_to_kernel_u(*krnl), cpu_id, target, RetValueType::Success)
            &&& cpu_offline_request_child_step_pre(steps.nonlock_view().last().old_u, cpu_id, target)
            &&& cpu_offline_request_child_step(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, target)
        }) by {
            cpu_offline_request_child_step_from_u(kernel_k_to_kernel_u(entry), kernel_k_to_kernel_u(*krnl), cpu_id, child_ptr, target);
            cpu_offline_request_child_step_from_u(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, child_ptr, target);
            cpu_offline_request_child_trace_step(&*steps, request_before, kernel_k_to_kernel_u(entry), kernel_k_to_kernel_u(*krnl), cpu_id, target);
        };
    }
    RetValueType::Success
}
}
