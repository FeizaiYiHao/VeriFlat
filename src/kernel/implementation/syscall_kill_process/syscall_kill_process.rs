use vstd::prelude::*;
use crate::*;
use super::syscall_kill_process_spec::*;
use super::syscall_kill_process_trace::*;
use super::syscall_kill_process_walk::*;
use super::syscall_kill_process_reclaim::kill_reclaim_target;
#[cfg(verus_keep_ghost)]
use crate::kernel::implementation::locker_unlocker::u_sys_exit_eof;

verus! {
/// Kill the child at `child_index` of the running thread's process together with its whole subtree. Success records an
/// entering step that write-locks the cpu, the process, and the thread and marks and write-locks the child; the steps of
/// the walk, which descends into the first child of each marked process, marks every thread of a childless one, takes
/// the thread off its queue or cpu, unlinks and reclaims it, turns a thread waiting for a reply into a dangling thread, and reclaims
/// and retires the emptied process; and a finishing step that unlocks the cpu, the process, and the thread. Failure
/// records no step. The result is `kill_process_syscall_result` of the state at entry.
pub fn syscall_kill_process(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, child_index: usize) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
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
        ret == kill_process_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, child_index),
        kill_process_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, child_index, ret is Success),
        !(ret is Success) ==> final(steps).nonlock_view().len() == 0 && kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(*old(krnl)),
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
    if cpu_lock_res.is_none() {
        proof {
            kill_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, child_index);
            kill_idle_pre_from_k(&*old(krnl), cpu_id, child_index);
        }
        return RetValueType::CpuIdle;
    }
    let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
    assert({
        let cpu = krnl.cpu_arr.spec_index(cpu_id).view().view();
        let process = krnl.prc_mp.spec_index(cpu.current_process().unwrap());
        let thread = krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view();
        &&& cpu.current_process() is Some
        &&& cpu.current_thread() is Some
        &&& krnl.prc_mp.dom().contains(cpu.current_process().unwrap())
        &&& krnl.thr_mp.dom().contains(cpu.current_thread().unwrap())
        &&& process.view_rodata().view().owning_container == cpu.owning_container()
        &&& process.view().owned_threads.view().len() != 0
        &&& thread.owning_proc == cpu.current_process().unwrap()
        &&& thread.owning_container == cpu.owning_container()
        &&& thread.state == (ThreadState::RUNNING { cpu_id })
        &&& cpu.view().process_depth == process.view_rodata().view().depth
        &&& cpu.view().container_depth == process.view_rodata().view().container_depth
        &&& thread.container_depth == process.view_rodata().view().container_depth
        &&& thread.process_depth == process.view_rodata().view().depth
    }) by {
        let cpu = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
        thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id);
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, cpu.current_process->Some_0); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, cpu.current_thread->Some_0);
    };
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let process_ptr = cpu.current_process().unwrap();
    let thread_ptr = cpu.current_thread().unwrap();
    let container_ptr = cpu.owning_container();
    let process_res = krnl.wlock_process_unless_killed(process_ptr, Ghost(cpu_id), Tracked(&mut *lctx));
    if process_res.is_none() {
        proof {
            let exit_k = *krnl;
            let exit_lctx = *lctx;
            krnl.u_sys_exit(lctx);
            u_sys_exit_eof(exit_k, *krnl, exit_lctx, *lctx);
        }
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(krnl.cpu_op.view().view() =~= old(krnl).cpu_op.view().view());
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(process_ptr), None, None, None, None);
            kill_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, child_index);
            kill_result_pre_from_k(&*old(krnl), cpu_id, child_index, process_ptr, thread_ptr);
        }
        return RetValueType::ErrorProcessKilled;
    }
    let Tracked(process_lock_perm) = process_res.unwrap();
    let thread_res = krnl.wlock_current_running_thread_unless_killed(thread_ptr, Tracked(&mut *lctx));
    if thread_res.is_none() {
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        proof {
            let exit_k = *krnl;
            let exit_lctx = *lctx;
            krnl.u_sys_exit(lctx);
            u_sys_exit_eof(exit_k, *krnl, exit_lctx, *lctx);
        }
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(krnl.cpu_op.view().view() =~= old(krnl).cpu_op.view().view());
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(process_ptr), Some(thread_ptr), None, None, None);
            kill_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, child_index);
            kill_result_pre_from_k(&*old(krnl), cpu_id, child_index, process_ptr, thread_ptr);
        }
        return RetValueType::ErrorThreadKilled;
    }
    let Tracked(thread_lock_perm) = thread_res.unwrap();
    proof { process_perms_wf_at(krnl.prc_mp, process_ptr); krnl.prc_mp.spec_index(process_ptr).view().children.lemma_len_view(); }
    let num_children = krnl.prc_mp.borrow_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(&process_lock_perm)).children.len();
    if child_index >= num_children {
        krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        proof {
            let exit_k = *krnl;
            let exit_lctx = *lctx;
            krnl.u_sys_exit(lctx);
            u_sys_exit_eof(exit_k, *krnl, exit_lctx, *lctx);
        }
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(krnl.cpu_op.view().view() =~= old(krnl).cpu_op.view().view());
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(process_ptr), Some(thread_ptr), None, None, None);
            kill_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, child_index);
            kill_result_pre_from_k(&*old(krnl), cpu_id, child_index, process_ptr, thread_ptr);
        }
        return RetValueType::ErrorInvalidChild;
    }
    let child_ptr = krnl.prc_mp.borrow_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(&process_lock_perm)).children.get(child_index);
    let (container_depth, process_depth) = {
        let process_ro = krnl.prc_mp.borrow_rodata(process_ptr).borrow();
        (process_ro.container_depth, process_ro.depth)
    };
    let killer_info = KillerInfo { container: container_ptr, container_depth, process: process_ptr, process_depth, thread: thread_ptr, cpu_id };
    let ghost locked_k = *krnl;
    let ghost locked_lctx = *lctx;
    proof {
        let process_ro = krnl.prc_mp.spec_index(process_ptr).view_rodata().view();
        assert({
            let child_ro = krnl.prc_mp.spec_index(child_ptr).view_rodata().view();
            &&& krnl.prc_mp.dom().contains(child_ptr)
            &&& child_ro.parent == Some(process_ptr)
            &&& child_ro.depth == process_ro.depth + 1
            &&& child_ro.owning_container == process_ro.owning_container
        }) by {
            let tree = krnl.ctn_mp.spec_index(process_ro.owning_container).view_ghost().owned_processes.view();
            let root = krnl.ctn_mp.spec_index(process_ro.owning_container).view().root_process;
            container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, process_ptr); per_container_process_tree_wf_at(krnl.ctn_mp, krnl.prc_mp, process_ro.owning_container);
            process_children_parent_wf_at(root, tree, krnl.prc_mp, process_ptr, child_ptr); process_root_wf_at(root, tree, krnl.prc_mp, child_ptr);
            container_process_wf_container_at(krnl.ctn_mp, krnl.prc_mp, process_ro.owning_container, child_ptr);
        };
        assert(krnl.prc_mp.spec_index(process_ptr).view_ghost().subtree_set.view().contains(child_ptr)) by {
            let tree = krnl.ctn_mp.spec_index(process_ro.owning_container).view_ghost().owned_processes.view();
            let root = krnl.ctn_mp.spec_index(process_ro.owning_container).view().root_process;
            process_perms_wf_at(krnl.prc_mp, child_ptr); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, child_ptr); per_container_process_tree_wf_at(krnl.ctn_mp, krnl.prc_mp, process_ro.owning_container);
            process_root_wf_at(root, tree, krnl.prc_mp, child_ptr); process_uppertree_seq_wf_at(root, tree, krnl.prc_mp, child_ptr, process_ptr);
            assert(krnl.prc_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().contains(process_ptr)) by { process_children_depth_wf_at(root, tree, krnl.prc_mp, child_ptr); };
        };
    }
    let child_res = krnl.try_wlock_process_and_mark_kill(child_ptr, process_ptr, thread_ptr, killer_info, Tracked(&mut *lctx));
    if child_res.is_none() {
        krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        proof {
            let exit_k = *krnl;
            let exit_lctx = *lctx;
            krnl.u_sys_exit(lctx);
            u_sys_exit_eof(exit_k, *krnl, exit_lctx, *lctx);
        }
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(krnl.cpu_op.view().view() =~= old(krnl).cpu_op.view().view());
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(process_ptr), Some(thread_ptr), None, None, None);
            kill_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, child_index);
            kill_result_pre_from_k(&*old(krnl), cpu_id, child_index, process_ptr, thread_ptr);
        }
        return RetValueType::ErrorProcessKilled;
    }
    let Tracked(child_perm) = child_res.unwrap();
    let ghost marked_k = *krnl;
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_progress(child_ptr, KillStage::Walk)), Tracked(&*lctx), Tracked(&thread_lock_perm));
    let ghost entered_k = *krnl;
    let ghost start = old(steps).view().len() as int;
    let ghost pre = kernel_k_to_kernel_u(*old(krnl));
    proof {
        let enter_before = steps.view();
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &locked_k)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &locked_k)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, locked_k.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
        kernel_cpu_process_thread_endpoint_lock_modes_changed_implies_u_step(old(krnl), &locked_k, &locked_lctx, cpu_id, process_ptr, thread_ptr, None, true, None, false, None);
        kernel_process_locked_and_marked_implies_u_step(&locked_k, &marked_k, child_ptr);
        kernel_thread_syscall_progress_changed_implies_u_step(&marked_k, &entered_k, thread_ptr);
        kill_enter_pre_from_k(&*old(krnl), cpu_id, child_index, process_ptr, thread_ptr, child_ptr);
        kill_enter_step_from_u(pre, kernel_k_to_kernel_u(locked_k), kernel_k_to_kernel_u(marked_k), kernel_k_to_kernel_u(entered_k), cpu_id, child_index, process_ptr, thread_ptr,
            child_ptr);
        kill_trace_enter_step(&*steps, enter_before, pre, kernel_k_to_kernel_u(entered_k), cpu_id, child_index);
    }
    let tracked mut chain_perms: Map<RwLockProcessPtr, LockPerm> = Map::tracked_empty();
    proof { chain_perms.tracked_insert(child_ptr, child_perm); }
    kill_walk_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, child_ptr, killer_info, Tracked(cpu_lock_perm), Tracked(process_lock_perm),
        Tracked(thread_lock_perm), Tracked(chain_perms), Ghost(start), Ghost(pre), Ghost(child_index));
    RetValueType::Success
}

/// Walk the subtree of the marked child `child_ptr` until every process of it is retired, then clear the kill and
/// unlock the cpu, the process, and the thread.
pub(crate) fn kill_walk_and_finish(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, child_ptr: RwLockProcessPtr, killer_info: KillerInfo, Tracked(cpu_perm): Tracked<LockPerm>, Tracked(process_perm): Tracked<LockPerm>,
    Tracked(thread_perm): Tracked<LockPerm>, Tracked(chain_perms): Tracked<Map<RwLockProcessPtr, LockPerm>>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
    Ghost(child_index): Ghost<usize>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, KillTraceCtx::Process { child_index }),
        kill_walk_state(*old(krnl), *old(lctx), cpu_id, KillScope::Subtree { process: process_ptr }, process_ptr, thread_ptr, seq![child_ptr], None, KillStage::Walk, cpu_perm, process_perm, thread_perm, chain_perms),
        killer_info.process == process_ptr,
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
        kill_process_syscall_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, kernel_k_to_kernel_u(*final(krnl)), cpu_id, child_index, true),
{
    let ghost scope = KillScope::Subtree { process: process_ptr };
    let ghost ctx = KillTraceCtx::Process { child_index };
    let tracked mut chain_perms = chain_perms;
    let ghost mut chain: Seq<RwLockProcessPtr> = seq![child_ptr];
    let mut target = child_ptr;
    let mut walking = true;
    while walking
        invariant
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.kernel_view_locking_state() is Acquire,
            steps.snapshot_k() == *krnl,
            0 <= start <= old(steps).view().len() <= steps.view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
            scope == (KillScope::Subtree { process: process_ptr }) && ctx == (KillTraceCtx::Process { child_index }),
            kill_walk_state(*krnl, *lctx, cpu_id, scope, process_ptr, thread_ptr, chain, None, KillStage::Walk, cpu_perm, process_perm, thread_perm, chain_perms),
            old(lctx).cpu_id() == cpu_id,
            killer_info.process == process_ptr,
            walking == (0 < chain.len()),
            walking ==> target == chain[chain.len() - 1],
        decreases
            krnl.prc_mp.spec_index(process_ptr).view_ghost().subtree_set.view().len(), usize::MAX - chain.len(),
            if walking { krnl.prc_mp.spec_index(target).view().owned_threads.view().len() } else { 0 },
    {
        proof {
            process_perms_wf_map(krnl.prc_mp);
            process_perms_wf_at(krnl.prc_mp, target);
            krnl.prc_mp.spec_index(target).view().children.lemma_len_view(); krnl.prc_mp.spec_index(target).view().owned_threads.lemma_len_view();
        }
        let (has_children, has_threads) = {
            let tracked target_perm = chain_perms.tracked_borrow(target);
            let target_process = krnl.prc_mp.borrow_typed(target, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(target_perm));
            (target_process.children.len() != 0, target_process.owned_threads.len() != 0)
        };
        if has_children {
            let next = kill_mark_child(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, killer_info, Ghost(chain), Tracked(&mut chain_perms),
                Tracked(&cpu_perm), Tracked(&process_perm), Tracked(&thread_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
            proof { chain = chain.push(next); }
            target = next;
        } else if has_threads {
            kill_first_thread(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, killer_info, Ghost(chain), Tracked(&chain_perms),
                Tracked(&cpu_perm), Tracked(&process_perm), Tracked(&thread_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
        } else {
            let parent = kill_reclaim_target(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(&mut chain_perms),
                Tracked(&cpu_perm), Tracked(&process_perm), Tracked(&thread_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
            proof { chain = chain.drop_last(); }
            if parent == process_ptr { walking = false; } else { target = parent; }
        }
    }
    proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); }
    let ghost walk_k = *krnl;
    let ghost walk_lctx = *lctx;
    let ghost finish_before = steps.view();
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(None), Tracked(&*lctx), Tracked(&thread_perm));
    let ghost cleared_k = *krnl;
    proof { assert(krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0) by { process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr); }; }
    krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_perm));
    krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_perm));
    proof {
        let exit_k = *krnl;
        let exit_lctx = *lctx;
        assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep && krnl.cpu_arr.spec_index(cpu_id).view().view_ghost() == Some(cpu_id)) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
        krnl.u_sys_exit(lctx);
        u_sys_exit_eof(exit_k, *krnl, exit_lctx, *lctx);
    }
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
    proof {
        steps.end_kernel_step_thread_syscall_progress_changed(&*krnl, &*lctx, thread_ptr);
        kill_finish_pre_from_k(&walk_k, &walk_lctx, cpu_id, process_ptr, thread_ptr);
        kernel_thread_syscall_progress_changed_implies_u_step(&walk_k, &cleared_k, thread_ptr);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&cleared_k, krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&cleared_k, krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        assert(kernel_endpoint_nonlock_fields_unchanged(cleared_k.ep_mp, krnl.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
        kernel_cpu_process_thread_endpoint_lock_modes_changed_implies_u_step(&cleared_k, &*krnl, &*lctx, cpu_id, process_ptr, thread_ptr, None, false, None, false, None);
        kill_finish_step_from_u(kernel_k_to_kernel_u(walk_k), kernel_k_to_kernel_u(cleared_k), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, thread_ptr);
        kill_trace_finish_step(&*steps, finish_before, start, pre, kernel_k_to_kernel_u(walk_k), kernel_k_to_kernel_u(*krnl), cpu_id, child_index);
        no_locks_held_imply_all_objects_unlocked(&*krnl, &*lctx);
    }
}
} // verus!
