use vstd::prelude::*;
use crate::*;
use super::syscall_kill_container_walk::kill_container_walk_and_finish;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_walk_spec::kill_container_walk_state;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_walk_trace::*;

verus! {
/// Kill the child container at `child_index` of the running thread's container together with everything below it.
/// Success records an entering step that write-locks the cpu, the container, the process, and the thread and marks and
/// write-locks the child; the steps of the walk, which descends into the first child of each marked container, kills
/// the processes of a childless one, moves its cpus and free pages to the killer's container, and retires it; and a
/// finishing step that unlocks the cpu, the container, the process, and the thread. Failure records no step. The result
/// is `kill_container_syscall_result` of the state at entry.
pub fn syscall_kill_container(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, child_index: usize) -> (ret: RetValueType)
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
        ret == kill_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, child_index),
        kill_container_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, child_index, ret is Success),
        !(ret is Success) ==> final(steps).nonlock_view().len() == 0 && kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(*old(krnl)),
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
    if cpu_lock_res.is_none() {
        proof {
            kill_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, child_index);
            kill_container_idle_pre_from_k(&*old(krnl), cpu_id, child_index);
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
        &&& krnl.ctn_mp.dom().contains(cpu.owning_container())
        &&& krnl.ctn_mp.spec_index(cpu.owning_container()).view_rodata().view().depth == cpu.view().container_depth
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
    let container_res = krnl.wlock_container_unless_killed(container_ptr, Tracked(&mut *lctx));
    if container_res.is_none() {
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), None, None, None, None, None);
            kill_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, child_index);
            kill_container_result_pre_from_k(&*old(krnl), cpu_id, child_index, container_ptr, process_ptr, thread_ptr);
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
            kill_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, child_index);
            kill_container_result_pre_from_k(&*old(krnl), cpu_id, child_index, container_ptr, process_ptr, thread_ptr);
        }
        return RetValueType::ErrorProcessKilled;
    }
    let Tracked(process_lock_perm) = process_res.unwrap();
    proof { assert(krnl.prc_mp.spec_index(process_ptr).view().state.view() is Running) by { process_perms_wf_at(krnl.prc_mp, process_ptr); }; }
    let thread_res = krnl.wlock_thread_unless_killed(thread_ptr, Tracked(&mut *lctx));
    if thread_res.is_none() {
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), Some(process_ptr), Some(thread_ptr), None, None, None);
            kill_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, child_index);
            kill_container_result_pre_from_k(&*old(krnl), cpu_id, child_index, container_ptr, process_ptr, thread_ptr);
        }
        return RetValueType::ErrorThreadKilled;
    }
    let Tracked(thread_lock_perm) = thread_res.unwrap();
    proof { container_perms_wf_map(krnl.ctn_mp); container_perms_wf_at(krnl.ctn_mp, container_ptr); krnl.ctn_mp.spec_index(container_ptr).view().children.lemma_len_view(); }
    let num_children = krnl.ctn_mp.borrow_typed(container_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(&container_lock_perm)).children.len();
    if child_index >= num_children {
        krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), Some(process_ptr), Some(thread_ptr), None, None, None);
            kill_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, child_index);
            kill_container_result_pre_from_k(&*old(krnl), cpu_id, child_index, container_ptr, process_ptr, thread_ptr);
        }
        return RetValueType::ErrorInvalidChild;
    }
    let child_ptr = krnl.ctn_mp.borrow_typed(container_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(&container_lock_perm)).children.get(child_index);
    let (container_depth, process_depth) = {
        let process_ro = krnl.prc_mp.borrow_rodata(process_ptr).borrow();
        (process_ro.container_depth, process_ro.depth)
    };
    let killer_info = KillerInfo { container: container_ptr, container_depth, process: process_ptr, process_depth, thread: thread_ptr, cpu_id };
    let ghost locked_k = *krnl;
    let ghost locked_lctx = *lctx;
    proof {
        let container_ro = krnl.ctn_mp.spec_index(container_ptr).view_rodata().view();
        assert({
            let child = krnl.ctn_mp.spec_index(child_ptr);
            &&& krnl.ctn_mp.dom().contains(child_ptr)
            &&& child_ptr != container_ptr
            &&& child_ptr != krnl.rt_ctn
            &&& child.view_rodata().view().parent == Some(container_ptr)
            &&& child.view_rodata().view().depth == container_ro.depth + 1
            &&& child.view_ghost().uppertree_seq.view().contains(container_ptr)
        }) by {
            container_children_parent_wf_at(krnl.rt_ctn, krnl.ctn_mp, container_ptr, child_ptr); container_root_wf_at(krnl.rt_ctn, krnl.ctn_mp, child_ptr);
            container_perms_wf_at(krnl.ctn_mp, child_ptr); container_children_depth_wf_at(krnl.rt_ctn, krnl.ctn_mp, child_ptr);
            assert(krnl.ctn_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view()[container_ro.depth as int] == container_ptr);
        };
    }
    let child_res = krnl.try_wlock_container_and_mark_kill(child_ptr, killer_info, Tracked(&mut *lctx));
    if child_res.is_none() {
        krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), Some(process_ptr), Some(thread_ptr), None, None, None);
            kill_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, child_index);
            kill_container_result_pre_from_k(&*old(krnl), cpu_id, child_index, container_ptr, process_ptr, thread_ptr);
        }
        return RetValueType::ErrorContainerKilled;
    }
    let Tracked(child_perm) = child_res.unwrap();
    let ghost marked_k = *krnl;
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_container_progress(child_ptr, ContainerKillStage::Walk)), Tracked(&*lctx), Tracked(&thread_lock_perm));
    let ghost entered_k = *krnl;
    let ghost start = old(steps).view().len() as int;
    let ghost pre = kernel_k_to_kernel_u(*old(krnl));
    proof {
        let enter_before = steps.view();
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &locked_k)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &locked_k)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, locked_k.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
        kernel_cpu_process_thread_endpoint_lock_modes_changed_implies_u_step(old(krnl), &locked_k, &locked_lctx, cpu_id, process_ptr, thread_ptr, None, true, Some(container_ptr), false, None);
        kernel_container_locked_and_marked_implies_u_step(&locked_k, &marked_k, child_ptr);
        kernel_thread_syscall_progress_changed_implies_u_step(&marked_k, &entered_k, thread_ptr);
        kill_container_enter_pre_from_k(&*old(krnl), cpu_id, child_index, container_ptr, process_ptr, thread_ptr, child_ptr);
        kill_container_enter_step_from_u(pre, kernel_k_to_kernel_u(locked_k), kernel_k_to_kernel_u(marked_k), kernel_k_to_kernel_u(entered_k), cpu_id, child_index, container_ptr,
            process_ptr, thread_ptr, child_ptr);
        kill_container_trace_enter_step(&*steps, enter_before, pre, kernel_k_to_kernel_u(entered_k), cpu_id, child_index);
    }
    let tracked mut chain_perms: Map<RwLockContainerPtr, LockPerm> = Map::tracked_empty();
    proof { chain_perms.tracked_insert(child_ptr, child_perm); }
    assert(kill_container_walk_state(*krnl, *lctx, cpu_id, process_ptr, thread_ptr, container_ptr, killer_info, seq![child_ptr], cpu_lock_perm, process_lock_perm, thread_lock_perm,
        container_lock_perm, chain_perms));
    kill_container_walk_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, container_ptr, child_ptr, killer_info, Tracked(cpu_lock_perm),
        Tracked(process_lock_perm), Tracked(thread_lock_perm), Tracked(container_lock_perm), Tracked(chain_perms), Ghost(start), Ghost(pre), Ghost(child_index));
    RetValueType::Success
}
} // verus!
