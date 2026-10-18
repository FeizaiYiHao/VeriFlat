use vstd::prelude::*;
use crate::*;
use super::syscall_thread_exit_spec::*;
use super::syscall_thread_exit_trace::*;
use super::syscall_thread_exit_drop::thread_exit_drop_descriptors;
use super::syscall_thread_exit_reclaim::thread_exit_reclaim;
use super::syscall_thread_exit_finish::thread_exit_finish;

verus! {
/// Exit the running thread. Success records an entering step that write-locks the cpu, container, process, and thread
/// and wakes the caller the thread serves with `ErrorIpcCalleeExited` or takes over the dangling thread of a killed caller; steps
/// reclaiming that dangling thread and the killed callers it takes over; one step per descriptor holding an endpoint; for the
/// process's last thread, the reclaiming steps that unmap every user 4K page of the process, flush its PCID once, and
/// return the thread's and the process's quota to their container; and a finishing step that removes the thread,
/// returns its page and quotas, makes an emptied process a zombie that releases its PCID, leaves the cpu idle, and
/// unlocks the cpu, container, and process. Failure records no step. The result is `thread_exit_syscall_result` of the
/// state at entry.
pub fn syscall_thread_exit(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId) -> (ret: RetValueType)
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
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        ret == thread_exit_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id),
        thread_exit_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, ret is CpuIdle && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed()),
        !(ret is CpuIdle && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed())
            ==> final(steps).nonlock_view().len() == 0 && kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(*old(krnl)),
{
    let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
    if cpu_lock_res.is_none() {
        proof {
            thread_exit_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id);
            thread_exit_syscall_result_from_k(&*old(krnl), cpu_id, RetValueType::CpuIdle);
        }
        return RetValueType::CpuIdle;
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
    }) by {
        thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id);
        process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap());
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
        return RetValueType::ErrorContainerKilled;
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
        return RetValueType::ErrorProcessKilled;
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
        return RetValueType::ErrorThreadKilled;
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
            return RetValueType::ErrorIpcPeerKilled;
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
    let ghost start = old(steps).view().len() as int;
    let ghost pre = kernel_k_to_kernel_u(*old(krnl));
    if let Some(dangling_ptr) = dangling {
        let ghost reclaim_k = *krnl;
        let ghost reclaim_lctx = *lctx;
        let ghost reclaim_before = steps.view();
        let tracked dangling_perm = dangling_lock_perm.tracked_unwrap();
        proof {
            assert(kernel_steps_prefix_unchanged(reclaim_before, reclaim_before)) by { reveal(kernel_steps_prefix_unchanged); };
        }
        reclaim_killed_thread_chain(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, dangling_ptr, Tracked(dangling_perm));
        proof {
            assert(thread_exit_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id)) by {
                thread_exit_drop_step_pre_from_k(&reclaim_k, &reclaim_lctx, cpu_id, container_ptr, process_ptr, thread_ptr, 0);
                thread_exit_trace_from_killed_thread_reclaim(&*steps, reclaim_before, start, pre, kernel_k_to_kernel_u(reclaim_k), cpu_id, container_ptr, process_ptr);
            };
        }
    }
    thread_exit_drop_descriptors(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, process_ptr, thread_ptr, Tracked(&thread_lock_perm), Ghost(start), Ghost(pre));
    proof { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, process_ptr); krnl.prc_mp.spec_index(process_ptr).view().owned_threads.lemma_len_view(); }
    let last = krnl.prc_mp.borrow_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(&process_lock_perm)).owned_threads.len() == 1;
    if last {
        thread_exit_reclaim(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, process_ptr, thread_ptr, Tracked(&cpu_lock_perm), Tracked(&process_lock_perm),
            Tracked(&thread_lock_perm), Ghost(start), Ghost(pre));
    }
    thread_exit_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, process_ptr, thread_ptr, last, Tracked(cpu_lock_perm), Tracked(container_lock_perm),
        Tracked(process_lock_perm), Tracked(thread_lock_perm), Ghost(start), Ghost(pre));
    proof { no_locks_held_imply_all_objects_unlocked(&*krnl, &*lctx); }
    RetValueType::CpuIdle
}
} // verus!
