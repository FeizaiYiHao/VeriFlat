use vstd::prelude::*;
use crate::*;
use super::syscall_thread_exit_spec::*;
use super::syscall_thread_exit_trace::*;

verus! {
pub(super) struct ThreadExitEntered {
    pub container_ptr: RwLockContainerPtr, pub process_ptr: RwLockProcessPtr, pub thread_ptr: RwLockThreadPtr,
    pub cpu_lock_perm: Tracked<LockPerm>, pub container_lock_perm: Tracked<LockPerm>, pub process_lock_perm: Tracked<LockPerm>, pub thread_lock_perm: Tracked<LockPerm>,
}

/// Write-locks cpu `cpu_id`, its container, process, and running thread, and the caller the thread serves, rejecting an
/// idle or killed cpu and a killed container, process, thread, or caller with every lock released and no step; otherwise
/// wakes the caller with `ErrorIpcCalleeExited` or takes over and reclaims the dangling thread of a killed caller,
/// records the entering and reclaiming steps, and returns the cpu, container, process, and thread locks held.
pub(super) fn thread_exit_lock_entry(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId)
    -> (ret: Result<ThreadExitEntered, RetValueType>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).nonlock_view().len() == 0,
        old(steps).snapshot_k() == *old(krnl),
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        ret is Err ==> ({
            let r = ret->Err_0;
            &&& r == thread_exit_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id)
            &&& !(r is CpuIdle && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed())
            &&& final(lctx).kernel_view_locking_state() is Release
            &&& final(lctx).no_locks_held()
            &&& final(krnl).all_objects_unlocked(final(lctx))
            &&& final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl))
            &&& final(steps).nonlock_view().len() == 0
            &&& kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(*old(krnl))
            &&& thread_exit_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)),
                kernel_k_to_kernel_u(*final(krnl)), cpu_id, false)
        }),
        ret is Ok ==> ({
            let e = ret->Ok_0;
            let cpu = final(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            let thread = final(krnl).thr_mp.spec_index(e.thread_ptr).view();
            &&& thread_exit_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id) == RetValueType::CpuIdle
            &&& old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& final(lctx).kernel_view_locking_state() is Acquire
            &&& thread_exit_partial_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id)
            &&& final(lctx).cpu_lock_map().dom() =~= set![cpu_id]
            &&& final(lctx).container_lock_map().dom() =~= set![e.container_ptr]
            &&& final(lctx).process_lock_map().dom() =~= set![e.process_ptr]
            &&& final(lctx).thread_lock_map().dom() =~= set![e.thread_ptr]
            &&& final(lctx).page_lock_map().dom().is_empty()
            &&& final(lctx).endpoint_lock_map().dom().is_empty()
            &&& final(lctx).scheduler_lock_map().dom().is_empty()
            &&& final(lctx).pcid_allocator_lock_map().dom().is_empty()
            &&& final(lctx).cpu_set_lock_map().dom().is_empty()
            &&& final(lctx).pagetable_lock_map().dom().is_empty()
            &&& final(lctx).iommu_table_lock_map().dom().is_empty()
            &&& final(lctx).iommu_root_table_lock_map().dom().is_empty()
            &&& final(lctx).holds_no_allocator_locks(PageSize::SZ4k)
            &&& final(lctx).holds_no_allocator_locks(PageSize::SZ2m)
            &&& final(lctx).holds_no_allocator_locks(PageSize::SZ1g)
            &&& final(lctx).pcid_needflush_lock_map().dom().is_empty()
            &&& final(lctx).cpu_offline_flag_lock_map().dom().is_empty()
            &&& typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write)
            &&& e.cpu_lock_perm.view().state() is WriteLock && e.cpu_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& e.cpu_lock_perm.view().lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(final(lctx).container_lock_map(), e.container_ptr, TypedLockMode::Write)
            &&& e.container_lock_perm.view().state() is WriteLock && e.container_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& e.container_lock_perm.view().lock_id() == final(krnl).ctn_mp.spec_index(e.container_ptr).locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(final(lctx).process_lock_map(), e.process_ptr, TypedLockMode::Write)
            &&& e.process_lock_perm.view().state() is WriteLock && e.process_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& e.process_lock_perm.view().lock_id() == final(krnl).prc_mp.spec_index(e.process_ptr).locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(final(lctx).thread_lock_map(), e.thread_ptr, TypedLockMode::Write)
            &&& e.thread_lock_perm.view().state() is WriteLock && e.thread_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& e.thread_lock_perm.view().lock_id() == final(krnl).thr_mp.spec_index(e.thread_ptr).locking_thread()->Write_lock_id
            &&& cpu.state is Running && cpu.current_process == Some(e.process_ptr) && cpu.current_thread == Some(e.thread_ptr) && cpu.owning_container == e.container_ptr
            &&& !final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& final(krnl).cpu_published[cpu_id as int].view() == (cpu.current_cr3, cpu.current_pcid)
            &&& final(krnl).ctn_mp.dom().contains(e.container_ptr) && !final(krnl).ctn_mp.spec_index(e.container_ptr).being_killed()
            &&& final(krnl).prc_mp.dom().contains(e.process_ptr) && !final(krnl).prc_mp.spec_index(e.process_ptr).being_killed()
            &&& final(krnl).prc_mp.spec_index(e.process_ptr).view().state.view() is Running
            &&& final(krnl).thr_mp.dom().contains(e.thread_ptr) && !final(krnl).thr_mp.spec_index(e.thread_ptr).being_killed()
            &&& thread.state == (ThreadState::RUNNING { cpu_id }) && thread.owning_proc == e.process_ptr && thread.owning_container == e.container_ptr
            &&& thread.caller is None && thread.callee is None && thread.temp_alloc_clean() && thread.free_quota_pending_clean()
            &&& thread.syscall_progress.view() == Some(SyscallProgress::ThreadExit { next: 0 })
        }),
{
    let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
    if cpu_lock_res.is_none() {
        proof {
            thread_exit_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id);
            thread_exit_syscall_result_from_k(&*old(krnl), cpu_id, RetValueType::CpuIdle);
        }
        return Err(RetValueType::CpuIdle);
    }
    let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
    assert({
        let cpu = krnl.cpu_arr.spec_index(cpu_id).view().view();
        &&& cpu.current_process() is Some
        &&& cpu.current_thread() is Some
        &&& krnl.ctn_mp.dom().contains(cpu.owning_container())
        &&& krnl.prc_mp.dom().contains(cpu.current_process().unwrap())
        &&& krnl.thr_mp.dom().contains(cpu.current_thread().unwrap())
        &&& krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view_rodata().view().owning_container == cpu.owning_container()
        &&& krnl.ctn_mp.spec_index(cpu.owning_container()).view_ghost().owned_processes.view().contains(cpu.current_process().unwrap())
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().owning_proc == cpu.current_process().unwrap()
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().owning_container == cpu.owning_container()
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().state == (ThreadState::RUNNING { cpu_id })
        &&& krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view().owned_threads.view().len() != 0
        &&& !krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view().zombie
        &&& krnl.ctn_mp.spec_index(cpu.owning_container()).view_rodata().view().depth == cpu.view().container_depth
        &&& krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view_rodata().view().container_depth == cpu.view().container_depth
        &&& krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view_rodata().view().depth == cpu.view().process_depth
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().container_depth == cpu.view().container_depth
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().process_depth == cpu.view().process_depth
    }) by {
        thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id);
        process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap());
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap());
    };
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let process_ptr = cpu.current_process().unwrap();
    let thread_ptr = cpu.current_thread().unwrap();
    let container_ptr = cpu.owning_container();
    let container_res = krnl.wlock_container_unless_killed(container_ptr, Tracked(&mut *lctx));
    if container_res.is_none() {
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), None, None, None, None, None);
            thread_exit_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id);
            thread_exit_syscall_result_from_k(&*old(krnl), cpu_id, RetValueType::ErrorContainerKilled);
        }
        return Err(RetValueType::ErrorContainerKilled);
    }
    let Tracked(container_lock_perm) = container_res.unwrap();
    let process_res = krnl.wlock_process_unless_killed(process_ptr, Ghost(cpu_id), Tracked(&mut *lctx));
    if process_res.is_none() {
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), Some(process_ptr), None, None, None, None);
            thread_exit_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id);
            thread_exit_syscall_result_from_k(&*old(krnl), cpu_id, RetValueType::ErrorProcessKilled);
        }
        return Err(RetValueType::ErrorProcessKilled);
    }
    let Tracked(process_lock_perm) = process_res.unwrap();
    let thread_res = krnl.wlock_thread_unless_killed(thread_ptr, Tracked(&mut *lctx));
    if thread_res.is_none() {
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), Some(process_ptr), Some(thread_ptr), None, None, None);
            thread_exit_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id);
            thread_exit_syscall_result_from_k(&*old(krnl), cpu_id, RetValueType::ErrorThreadKilled);
        }
        return Err(RetValueType::ErrorThreadKilled);
    }
    let Tracked(thread_lock_perm) = thread_res.unwrap();
    let ghost locked_k = *krnl;
    let ghost locked_lctx = *lctx;
    proof { thread_perms_wf_at(krnl.thr_mp, thread_ptr); }
    let caller = krnl.thr_mp.borrow_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_lock_perm)).caller;
    proof {
        assert(krnl.thr_mp.spec_index(thread_ptr).view().callee is None && (caller matches Some(caller_ptr) ==> {
            &&& krnl.thr_mp.dom().contains(caller_ptr)
            &&& caller_ptr != thread_ptr
            &&& krnl.thr_mp.spec_index(caller_ptr).view().state.is_reply_waiting()
            &&& krnl.thr_mp.spec_index(caller_ptr).view().callee == Some(thread_ptr)
            &&& krnl.thr_mp.spec_index(caller_ptr).view().owning_container == container_ptr
        })) by { thread_caller_callee_wf_at(krnl.thr_mp, thread_ptr); };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &locked_k)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &locked_k)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, locked_k.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
    }
    let mut dangling: Option<RwLockThreadPtr> = None;
    let tracked mut dangling_lock_perm: Option<LockPerm> = None;
    if let Some(caller_ptr) = caller {
        let caller_res = krnl.wlock_thread_unless_killed(caller_ptr, Tracked(&mut *lctx));
        if caller_res.is_none() {
            krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
            krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
            krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
            krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
            proof {
                steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), Some(process_ptr), Some(thread_ptr), None, None, None);
                thread_exit_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id);
                thread_exit_syscall_result_from_k(&*old(krnl), cpu_id, RetValueType::ErrorIpcPeerKilled);
            }
            return Err(RetValueType::ErrorIpcPeerKilled);
        }
        let Tracked(caller_lock_perm) = caller_res.unwrap();
        proof { thread_perms_wf_at(krnl.thr_mp, caller_ptr); }
        let caller_dangling = match krnl.thr_mp.borrow_typed(caller_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&caller_lock_perm)).state {
            ThreadState::DANGLING => true,
            _ => false,
        };
        if caller_dangling {
            take_over_dangling_caller(krnl, Tracked(&mut *lctx), thread_ptr, caller_ptr, Tracked(&thread_lock_perm), Tracked(&caller_lock_perm));
            dangling = Some(caller_ptr);
            proof { dangling_lock_perm = Some(caller_lock_perm); }
        } else {
            wake_waiting_reply_caller(krnl, Tracked(&mut *lctx), cpu_id, container_ptr, thread_ptr, caller_ptr, Tracked(&thread_lock_perm), Tracked(caller_lock_perm));
        }
    } else {
        proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); }
    }
    let ghost woken_k = *krnl;
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::ThreadExit { next: 0 })), Tracked(&*lctx), Tracked(&thread_lock_perm));
    proof {
        let entered_k = *krnl;
        let enter_before = steps.view();
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        assert(thread_exit_partial_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id)) by {
            thread_exit_enter_step_pre_from_k(old(krnl), cpu_id, container_ptr, process_ptr, thread_ptr, caller, dangling is Some);
            kernel_cpu_process_thread_endpoint_lock_modes_changed_implies_u_step(old(krnl), &locked_k, &locked_lctx, cpu_id, process_ptr, thread_ptr, None, true, Some(container_ptr), false, None);
            if let Some(caller_ptr) = caller {
                if dangling is Some { kernel_dangling_caller_taken_over_implies_u_step(&locked_k, &woken_k, thread_ptr, caller_ptr, None); } else { kernel_caller_woken_implies_u_step(&locked_k, &woken_k, cpu_id, thread_ptr, caller_ptr); }
            }
            kernel_thread_syscall_progress_changed_implies_u_step(&woken_k, &entered_k, thread_ptr);
            thread_exit_enter_step_from_u(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(locked_k), kernel_k_to_kernel_u(woken_k), kernel_k_to_kernel_u(entered_k), cpu_id, container_ptr, process_ptr, thread_ptr, caller, dangling is Some);
            thread_exit_trace_enter_step(&*steps, enter_before, kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(entered_k), cpu_id);
        };
        thread_exit_syscall_result_from_k(&*old(krnl), cpu_id, RetValueType::CpuIdle);
    }
    if let Some(dangling_ptr) = dangling {
        let tracked dangling_perm = dangling_lock_perm.tracked_unwrap();
        thread_exit_reclaim_dangling_caller(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, process_ptr, thread_ptr, dangling_ptr, Tracked(dangling_perm),
            Ghost(old(steps).view().len() as int), Ghost(kernel_k_to_kernel_u(*old(krnl))));
    }
    Ok(ThreadExitEntered {
        container_ptr, process_ptr, thread_ptr, cpu_lock_perm: Tracked(cpu_lock_perm), container_lock_perm: Tracked(container_lock_perm),
        process_lock_perm: Tracked(process_lock_perm), thread_lock_perm: Tracked(thread_lock_perm),
    })
}

/// Reclaims the dangling thread `dangling_ptr` taken over from the killed caller of the running `thread_ptr` and every
/// killed caller it takes over, extending the partial trace that starts at `start`.
fn thread_exit_reclaim_dangling_caller(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, container_ptr: RwLockContainerPtr,
    process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, dangling_ptr: RwLockThreadPtr, Tracked(dangling_lock_perm): Tracked<LockPerm>, Ghost(start): Ghost<int>,
    Ghost(pre): Ghost<KernelU>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(steps).snapshot_k() == *old(krnl),
        killed_thread_reclaim_lock_context(*old(krnl), *old(lctx)),
        old(krnl).thr_mp.dom().contains(dangling_ptr),
        old(krnl).thr_mp.spec_index(dangling_ptr).view().state is KILLED,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), dangling_ptr, TypedLockMode::Write),
        dangling_lock_perm.state() is WriteLock,
        dangling_lock_perm.thread_id() == old(lctx).thread_id(),
        dangling_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(dangling_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(dangling_ptr).view().callee is None,
        old(krnl).thr_mp.spec_index(dangling_ptr).view().proc_linkedlist_node.is_init(),
        old(krnl).thr_mp.spec_index(dangling_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(dangling_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(dangling_ptr).view().quota_4k == 0,
        old(krnl).thr_mp.spec_index(dangling_ptr).view().quota_2m == 0,
        old(krnl).thr_mp.spec_index(dangling_ptr).view().quota_1g == 0,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExit { next: 0 }),
        0 <= start <= old(steps).view().len(),
        thread_exit_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() < final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] #![trigger final(krnl).ctn_mp.spec_index(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).view() == old(krnl).ctn_mp.spec_index(c).view()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).being_killed() == old(krnl).ctn_mp.spec_index(c).being_killed()
        },
        typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Thread(dangling_ptr)),
        held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![dangling_ptr]),
        thread_exit_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id),
{
    let ghost reclaim_before = steps.view();
    proof { assert(kernel_steps_prefix_unchanged(reclaim_before, reclaim_before)) by { reveal(kernel_steps_prefix_unchanged); }; }
    reclaim_killed_thread_chain(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, dangling_ptr, Tracked(dangling_lock_perm));
    assert(thread_exit_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id)) by {
        thread_exit_drop_step_pre_from_k(old(krnl), old(lctx), cpu_id, container_ptr, process_ptr, thread_ptr, 0);
        thread_exit_trace_from_killed_thread_reclaim(&*steps, reclaim_before, start, pre, kernel_k_to_kernel_u(*old(krnl)), cpu_id, container_ptr, process_ptr);
    };
}
} // verus!
