use vstd::prelude::*;
use crate::*;
use super::syscall_thread_exit_spec::*;
use super::syscall_thread_exit_trace::*;
use super::syscall_thread_exit_entry::ThreadExitEntered;
use super::syscall_thread_exit_entry_progress::thread_exit_enter_record_progress;

verus! {
/// Lock phase of the entry of thread exit: write-locks cpu `cpu_id`, its container, process, and running thread,
/// rejecting an idle or killed cpu and a killed container, process, or thread with every lock released and no step.
pub(super) fn thread_exit_lock_running_thread(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId)
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
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        ret is Err ==> ({
            let r = ret->Err_0;
            &&& r == thread_exit_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id)
            &&& !(r is CpuIdle && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed())
            &&& final(lctx).kernel_view_locking_state() is Release
            &&& final(lctx).no_locks_held()
            &&& final(steps).snapshot_k() == *final(krnl)
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
            &&& *final(steps) == *old(steps)
            &&& old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& final(lctx).kernel_view_locking_state() is Acquire
            &&& old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() is None && old(krnl).ctn_mp.spec_index(e.container_ptr).locking_thread() is None
            &&& old(krnl).prc_mp.spec_index(e.process_ptr).locking_thread() is None && old(krnl).thr_mp.spec_index(e.thread_ptr).locking_thread() is None
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
            &&& final(krnl).cpu_published[cpu_id as int].view() == (cpu.current_cr3, cpu.current_pcid)
            &&& final(krnl).ctn_mp.dom().contains(e.container_ptr) && final(krnl).prc_mp.dom().contains(e.process_ptr) && final(krnl).thr_mp.dom().contains(e.thread_ptr)
            &&& final(krnl).thr_mp.perms_wf()
            &&& !final(krnl).ctn_mp.spec_index(e.container_ptr).view_ghost().owned_processes.view().is_empty()
            &&& final(krnl).prc_mp.spec_index(e.process_ptr).view().state.view() is Running
            &&& thread.state == (ThreadState::RUNNING { cpu_id }) && thread.owning_proc == e.process_ptr && thread.owning_container == e.container_ptr
            &&& thread.temp_alloc_clean() && thread.free_quota_pending_clean() && thread.syscall_progress.view() is None
            &&& !final(krnl).thr_mp.spec_index(e.thread_ptr).view_ghost().exited
            &&& *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, ctn_mp: final(krnl).ctn_mp, prc_mp: final(krnl).prc_mp, thr_mp: final(krnl).thr_mp, ..*old(krnl) })
            &&& final(krnl).cpu_arr.unchanged_except(&old(krnl).cpu_arr, cpu_id)
            &&& final(krnl).ctn_mp.unchanged_except(&old(krnl).ctn_mp, e.container_ptr)
            &&& final(krnl).prc_mp.unchanged_except(&old(krnl).prc_mp, e.process_ptr)
            &&& final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, e.thread_ptr)
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info()
            &&& final(krnl).ctn_mp.spec_index(e.container_ptr).view() == old(krnl).ctn_mp.spec_index(e.container_ptr).view()
            &&& final(krnl).ctn_mp.spec_index(e.container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(e.container_ptr).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(e.container_ptr).view_ghost() == old(krnl).ctn_mp.spec_index(e.container_ptr).view_ghost()
            &&& !final(krnl).ctn_mp.spec_index(e.container_ptr).being_killed() && !old(krnl).ctn_mp.spec_index(e.container_ptr).being_killed()
            &&& final(krnl).prc_mp.spec_index(e.process_ptr).view() == old(krnl).prc_mp.spec_index(e.process_ptr).view()
            &&& final(krnl).prc_mp.spec_index(e.process_ptr).view_rodata() == old(krnl).prc_mp.spec_index(e.process_ptr).view_rodata()
            &&& final(krnl).prc_mp.spec_index(e.process_ptr).view_ghost() == old(krnl).prc_mp.spec_index(e.process_ptr).view_ghost()
            &&& !final(krnl).prc_mp.spec_index(e.process_ptr).being_killed() && !old(krnl).prc_mp.spec_index(e.process_ptr).being_killed()
            &&& final(krnl).thr_mp.spec_index(e.thread_ptr).view() == old(krnl).thr_mp.spec_index(e.thread_ptr).view()
            &&& !final(krnl).thr_mp.spec_index(e.thread_ptr).being_killed() && !old(krnl).thr_mp.spec_index(e.thread_ptr).being_killed()
            &&& kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl))
            &&& kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl))
            &&& kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp)
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
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
    }
    Ok(ThreadExitEntered {
        container_ptr, process_ptr, thread_ptr, cpu_lock_perm: Tracked(cpu_lock_perm), container_lock_perm: Tracked(container_lock_perm),
        process_lock_perm: Tracked(process_lock_perm), thread_lock_perm: Tracked(thread_lock_perm),
    })
}

/// Enter step of thread exit with cpu `cpu_id`, its container, process, and running thread write-locked since `pre`:
/// write-locks the caller the thread serves, returning `None` with nothing else changed when it is killed; otherwise
/// wakes the caller with `ErrorIpcCalleeExited` or takes over the dangling thread of a killed caller, records the
/// thread's progress and the enter step on `pre`, and returns the dangling thread with its lock perm.
pub(super) fn thread_exit_enter_with_caller(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, container_ptr: RwLockContainerPtr,
    process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, Tracked(thread_lock_perm): Tracked<&LockPerm>, Ghost(pre): Ghost<KernelK>,
) -> (ret: Option<(Option<RwLockThreadPtr>, Tracked<Option<LockPerm>>)>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(steps).snapshot_k() == pre,
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom() =~= set![container_ptr],
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        old(krnl).ctn_mp.dom().contains(container_ptr) && old(krnl).prc_mp.dom().contains(process_ptr) && old(krnl).thr_mp.dom().contains(thread_ptr),
        thread_lock_perm.state() is WriteLock && thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        old(krnl).thr_mp.perms_wf(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr && old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean() && old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None && !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, ctn_mp: old(krnl).ctn_mp, prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, ..pre }),
        old(krnl).cpu_arr.unchanged_except(&pre.cpu_arr, cpu_id),
        old(krnl).ctn_mp.unchanged_except(&pre.ctn_mp, container_ptr),
        old(krnl).prc_mp.unchanged_except(&pre.prc_mp, process_ptr),
        old(krnl).thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view() == pre.thr_mp.spec_index(thread_ptr).view(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, old(krnl)),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, old(krnl).ep_mp),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !pre.cpu_arr.spec_index(cpu_id).view().being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().locking_thread() is None && pre.ctn_mp.spec_index(container_ptr).locking_thread() is None,
        pre.prc_mp.spec_index(process_ptr).locking_thread() is None && pre.thr_mp.spec_index(thread_ptr).locking_thread() is None,
        !pre.ctn_mp.spec_index(container_ptr).being_killed() && !pre.prc_mp.spec_index(process_ptr).being_killed() && !pre.thr_mp.spec_index(thread_ptr).being_killed(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        ret is None ==> ({
            let c = old(krnl).thr_mp.spec_index(thread_ptr).view().caller->Some_0;
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().caller is Some && c != thread_ptr
            &&& *final(steps) == *old(steps)
            &&& typed_lock_maps_unchanged(old(lctx), final(lctx))
            &&& *final(krnl) == (KernelK { thr_mp: final(krnl).thr_mp, ..*old(krnl) })
            &&& final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, c)
            &&& final(krnl).thr_mp.spec_index(c) == old(krnl).thr_mp.spec_index(c)
            &&& thread_exit_syscall_result(kernel_k_to_kernel_u(pre), cpu_id) == RetValueType::ErrorIpcPeerKilled
        }),
        ret is Some ==> ({
            let d = ret->Some_0.0;
            let dp = ret->Some_0.1.view();
            let thread = final(krnl).thr_mp.spec_index(thread_ptr).view();
            &&& final(steps).snapshot_k() == *final(krnl)
            &&& thread_exit_partial_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(pre), cpu_id)
            &&& thread_exit_syscall_result(kernel_k_to_kernel_u(pre), cpu_id) == RetValueType::CpuIdle
            &&& final(lctx).cpu_lock_map().dom() =~= set![cpu_id]
            &&& final(lctx).container_lock_map().dom() =~= set![container_ptr]
            &&& final(lctx).process_lock_map().dom() =~= set![process_ptr]
            &&& final(lctx).thread_lock_map().dom() =~= match d { Some(dangling_ptr) => set![thread_ptr, dangling_ptr], None => set![thread_ptr] }
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
            &&& typed_lock_map_contains_mode(final(lctx).container_lock_map(), container_ptr, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(final(lctx).process_lock_map(), process_ptr, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(final(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write)
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view()
            &&& final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view()
            &&& final(krnl).ctn_mp.dom().contains(container_ptr) && final(krnl).ctn_mp.spec_index(container_ptr) == old(krnl).ctn_mp.spec_index(container_ptr)
            &&& final(krnl).prc_mp.dom().contains(process_ptr) && final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr)
            &&& final(krnl).thr_mp.dom().contains(thread_ptr) && final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()
            &&& !final(krnl).thr_mp.spec_index(thread_ptr).being_killed()
            &&& thread.state == (ThreadState::RUNNING { cpu_id }) && thread.owning_proc == process_ptr && thread.owning_container == container_ptr
            &&& thread.caller is None && thread.callee is None && thread.temp_alloc_clean() && thread.free_quota_pending_clean()
            &&& thread.syscall_progress.view() == Some(SyscallProgress::ThreadExit { next: 0 })
            &&& d matches Some(dangling_ptr) ==> {
                let dangling = final(krnl).thr_mp.spec_index(dangling_ptr).view();
                &&& killed_thread_reclaim_lock_context(*final(krnl), *final(lctx))
                &&& final(krnl).thr_mp.dom().contains(dangling_ptr)
                &&& typed_lock_map_contains_mode(final(lctx).thread_lock_map(), dangling_ptr, TypedLockMode::Write)
                &&& dp is Some && dp->Some_0.state() is WriteLock && dp->Some_0.thread_id() == final(lctx).thread_id()
                &&& dp->Some_0.lock_id() == final(krnl).thr_mp.spec_index(dangling_ptr).locking_thread()->Write_lock_id
                &&& dangling.state is KILLED && dangling.callee is None && dangling.proc_linkedlist_node.is_init()
                &&& dangling.temp_alloc_clean() && dangling.free_quota_pending_clean() && dangling.quota_4k == 0 && dangling.quota_2m == 0 && dangling.quota_1g == 0
            }
        }),
{
    let ghost held_k = *krnl;
    let ghost held_lctx = *lctx;
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
    }
    let mut dangling: Option<RwLockThreadPtr> = None;
    let tracked mut dangling_lock_perm: Option<LockPerm> = None;
    if let Some(caller_ptr) = caller {
        let caller_res = krnl.wlock_thread_unless_killed(caller_ptr, Tracked(&mut *lctx));
        if caller_res.is_none() {
            proof { thread_exit_syscall_result_from_k(&pre, cpu_id, RetValueType::ErrorIpcPeerKilled); }
            return None;
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
    thread_exit_enter_record_progress(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), thread_ptr, Ghost(cpu_id), Ghost(container_ptr), Ghost(process_ptr), Tracked(thread_lock_perm),
        Ghost(pre), Ghost(held_k), Ghost(held_lctx), Ghost(caller), Ghost(dangling is Some));
    proof { thread_exit_syscall_result_from_k(&pre, cpu_id, RetValueType::CpuIdle); }
    Some((dangling, Tracked(dangling_lock_perm)))
}
} // verus!
