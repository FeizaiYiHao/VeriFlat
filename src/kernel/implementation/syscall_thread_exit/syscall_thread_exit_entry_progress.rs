use vstd::prelude::*;
use crate::*;
use super::syscall_thread_exit_spec::*;
use super::syscall_thread_exit_trace::*;

verus! {
/// Progress step of the thread-exit entry: `held_k`/`held_lctx` hold cpu `cpu_id`, its container, process, and running
/// thread write-locked since `pre`, and the current state has woken the thread's caller `caller` or, when `dangling`,
/// taken over its dangling thread. Records `ThreadExit { next: 0 }` on the thread and the enter step on `pre`.
pub(super) fn thread_exit_enter_record_progress(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, thread_ptr: RwLockThreadPtr, Ghost(cpu_id): Ghost<CpuId>,
    Ghost(container_ptr): Ghost<RwLockContainerPtr>, Ghost(process_ptr): Ghost<RwLockProcessPtr>, Tracked(thread_lock_perm): Tracked<&LockPerm>, Ghost(pre): Ghost<KernelK>,
    Ghost(held_k): Ghost<KernelK>, Ghost(held_lctx): Ghost<LocalContext>, Ghost(caller): Ghost<Option<RwLockThreadPtr>>, Ghost(dangling): Ghost<bool>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).cpu_id() == cpu_id,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        caller is Some && dangling ==> old(lctx).thread_lock_map().dom().contains(caller->Some_0),
        thread_lock_perm.state() is WriteLock && thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(steps).snapshot_k() == pre,
        held_k.inv(),
        typed_lock_maps_aligned(&held_k, &held_lctx),
        typed_lock_map_contains_mode(held_lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(held_lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(held_lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(held_lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        held_k.ctn_mp.dom().contains(container_ptr) && held_k.prc_mp.dom().contains(process_ptr) && held_k.thr_mp.dom().contains(thread_ptr),
        held_k.ctn_mp.spec_index(container_ptr).lock_process_owner_u() == Some(LockOwnerId::Some(pre.prc_mp.spec_index(process_ptr).view_rodata().view().depth)),
        held_k == (KernelK { cpu_arr: held_k.cpu_arr, ctn_mp: held_k.ctn_mp, prc_mp: held_k.prc_mp, thr_mp: held_k.thr_mp, ..pre }),
        held_k.cpu_arr.unchanged_except(&pre.cpu_arr, cpu_id),
        held_k.ctn_mp.unchanged_except(&pre.ctn_mp, container_ptr),
        held_k.prc_mp.unchanged_except(&pre.prc_mp, process_ptr),
        held_k.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        held_k.thr_mp.spec_index(thread_ptr).view() == pre.thr_mp.spec_index(thread_ptr).view(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &held_k),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &held_k),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, held_k.ep_mp),
        ({
            let cpu = pre.cpu_arr.spec_index(cpu_id).view();
            let c = cpu.view().view();
            let thread = pre.thr_mp.spec_index(thread_ptr);
            &&& cpu.locking_thread() is None
            &&& c.state is Running
            &&& !cpu.being_killed()
            &&& c.current_process == Some(process_ptr)
            &&& c.current_thread == Some(thread_ptr)
            &&& c.owning_container == container_ptr
            &&& pre.ctn_mp.dom().contains(container_ptr)
            &&& pre.ctn_mp.spec_index(container_ptr).locking_thread() is None
            &&& !pre.ctn_mp.spec_index(container_ptr).being_killed()
            &&& pre.prc_mp.dom().contains(process_ptr)
            &&& pre.prc_mp.spec_index(process_ptr).locking_thread() is None
            &&& !pre.prc_mp.spec_index(process_ptr).being_killed()
            &&& pre.thr_mp.dom().contains(thread_ptr)
            &&& thread.locking_thread() is None
            &&& thread.view().syscall_progress.view() is None
            &&& !thread.being_killed()
            &&& thread.view().state == (ThreadState::RUNNING { cpu_id })
            &&& thread.view().owning_proc == process_ptr
            &&& thread.view().owning_container == container_ptr
            &&& thread.view().caller == caller
        }),
        caller matches Some(caller_ptr) ==> {
            let caller_thread = pre.thr_mp.spec_index(caller_ptr);
            &&& pre.thr_mp.dom().contains(caller_ptr)
            &&& caller_thread.locking_thread() is None
            &&& !caller_thread.being_killed()
            &&& caller_thread.view().state.is_reply_waiting()
            &&& (caller_thread.view().state is DANGLING) == dangling
        },
        caller is None ==> *old(krnl) == held_k,
        caller matches Some(caller_ptr) ==> {
            &&& held_k.thr_mp.dom().contains(caller_ptr)
            &&& caller_ptr != thread_ptr
            &&& old(krnl).thr_mp.dom() == held_k.thr_mp.dom()
            &&& forall|t: RwLockThreadPtr| #![trigger old(krnl).thr_mp.spec_index(t)]
                held_k.thr_mp.dom().contains(t) && t != thread_ptr && t != caller_ptr ==> old(krnl).thr_mp.spec_index(t) == held_k.thr_mp.spec_index(t)
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { caller: None, ..held_k.thr_mp.spec_index(thread_ptr).view() })
            &&& old(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == held_k.thr_mp.spec_index(thread_ptr).locking_thread()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == held_k.thr_mp.spec_index(thread_ptr).being_killed()
            &&& old(krnl).thr_mp.spec_index(caller_ptr).being_killed() == held_k.thr_mp.spec_index(caller_ptr).being_killed()
        },
        caller is Some && dangling ==> {
            let caller_ptr = caller->Some_0;
            &&& *old(krnl) == (KernelK { thr_mp: old(krnl).thr_mp, ..held_k })
            &&& old(krnl).thr_mp.spec_index(caller_ptr).view() == (Thread { state: ThreadState::KILLED, callee: None, ..held_k.thr_mp.spec_index(caller_ptr).view() })
            &&& old(krnl).thr_mp.spec_index(caller_ptr).locking_thread() is Write
        },
        caller is Some && !dangling ==> {
            let caller_ptr = caller->Some_0;
            &&& *old(krnl) == (KernelK { thr_mp: old(krnl).thr_mp, sched_mp: old(krnl).sched_mp, ..held_k })
            &&& old(krnl).thr_mp.spec_index(caller_ptr).view() == (Thread {
                state: ThreadState::SCHEDULED { cpu_id }, callee: None, error_code: Some(RetValueType::ErrorIpcCalleeExited),
                scheduler_linkedlist_node: old(krnl).thr_mp.spec_index(caller_ptr).view().scheduler_linkedlist_node, ..held_k.thr_mp.spec_index(caller_ptr).view()
            })
            &&& old(krnl).thr_mp.spec_index(caller_ptr).locking_thread() == held_k.thr_mp.spec_index(caller_ptr).locking_thread()
            &&& old(krnl).sched_mp.dom() == held_k.sched_mp.dom()
            &&& forall|s: RwLockSchedulerPtr| #![trigger old(krnl).sched_mp.spec_index(s)] held_k.sched_mp.dom().contains(s) ==>
                scheduler_shards_of(old(krnl).sched_mp.spec_index(s)) == if s == held_k.ctn_mp.spec_index(held_k.thr_mp.spec_index(caller_ptr).view().owning_container).view_rodata().view().scheduler {
                    scheduler_shards_of(held_k.sched_mp.spec_index(s)).update(cpu_id as int, scheduler_shards_of(held_k.sched_mp.spec_index(s))[cpu_id as int].push(caller_ptr))
                } else { scheduler_shards_of(held_k.sched_mp.spec_index(s)) }
        },
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).snapshot_k() == *final(krnl),
        thread_exit_partial_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(pre), cpu_id),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).ctn_mp.dom().contains(container_ptr) && final(krnl).ctn_mp.spec_index(container_ptr) == old(krnl).ctn_mp.spec_index(container_ptr),
        final(krnl).prc_mp.dom().contains(process_ptr) && final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: Ghost(Some(SyscallProgress::ThreadExit { next: 0 })), ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        caller is Some && dangling ==> final(krnl).thr_mp.dom().contains(caller->Some_0) && final(krnl).thr_mp.spec_index(caller->Some_0) == old(krnl).thr_mp.spec_index(caller->Some_0),
{
    let ghost woken_k = *krnl;
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::ThreadExit { next: 0 })), Tracked(&*lctx), Tracked(thread_lock_perm));
    proof {
        let entered_k = *krnl;
        let enter_before = steps.view();
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        assert(thread_exit_partial_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(pre), cpu_id)) by {
            thread_exit_enter_step_pre_from_k(&pre, cpu_id, container_ptr, process_ptr, thread_ptr, caller, dangling);
            kernel_cpu_process_thread_endpoint_lock_modes_changed_implies_u_step(&pre, &held_k, &held_lctx, cpu_id, process_ptr, thread_ptr, None, true, Some(container_ptr), false, None);
            if let Some(caller_ptr) = caller {
                if dangling { kernel_dangling_caller_taken_over_implies_u_step(&held_k, &woken_k, thread_ptr, caller_ptr, None); } else { kernel_caller_woken_implies_u_step(&held_k, &woken_k, cpu_id, thread_ptr, caller_ptr); }
            }
            kernel_thread_syscall_progress_changed_implies_u_step(&woken_k, &entered_k, thread_ptr);
            thread_exit_enter_step_from_u(kernel_k_to_kernel_u(pre), kernel_k_to_kernel_u(held_k), kernel_k_to_kernel_u(woken_k), kernel_k_to_kernel_u(entered_k), cpu_id, container_ptr, process_ptr, thread_ptr, caller, dangling);
            thread_exit_trace_enter_step(&*steps, enter_before, kernel_k_to_kernel_u(pre), kernel_k_to_kernel_u(entered_k), cpu_id);
        };
    }
}
} // verus!
