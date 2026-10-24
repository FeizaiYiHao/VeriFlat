use vstd::prelude::*;
use crate::*;
use super::syscall_schedule_spec::*;
use super::syscall_schedule_trace::*;
#[cfg(verus_keep_ghost)]
use super::syscall_schedule::schedule_current_cpu_references_wf;

verus! {
/// With `cpu_id`, its shard of `scheduler_ptr`, and the live `current_process` and `current_thread`, if any, write-held since
/// the entry snapshot: releases them all and finishes the call without recording a step.
pub(super) fn schedule_continue(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr,
    current_process: Option<RwLockProcessPtr>, current_thread: Option<RwLockThreadPtr>, process_lock_perm: Option<Tracked<LockPerm>>,
    current_thread_lock_perm: Option<Tracked<LockPerm>>, Tracked(scheduler_lock_perm): Tracked<LockPerm>, Tracked(cpu_lock_perm): Tracked<LockPerm>, Ghost(entry_regs): Ghost<Registers>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).nonlock_view().len() == 0,
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, sched_mp: old(krnl).sched_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        forall|p: RwLockProcessPtr| #![trigger old(krnl).prc_mp.spec_index(p)]
            old(steps).snapshot_k().prc_mp.dom().contains(p) ==> if current_process == Some(p) {
                old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() },
        forall|t: RwLockThreadPtr| #![trigger old(krnl).thr_mp.spec_index(t)]
            old(steps).snapshot_k().thr_mp.dom().contains(t) ==> if current_thread == Some(t) {
                old(steps).snapshot_k().thr_mp.spec_index(t).locking_thread() is None
            } else { old(krnl).thr_mp.spec_index(t).locking_thread() == old(steps).snapshot_k().thr_mp.spec_index(t).locking_thread() },
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).sched_mp.dom().contains(scheduler_ptr),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (scheduler_ptr, cpu_id), TypedLockMode::Write),
        scheduler_lock_perm.state() is WriteLock,
        scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        current_process is Some == current_thread is Some,
        current_process is Some == process_lock_perm is Some,
        current_thread is Some == current_thread_lock_perm is Some,
        current_process is Some ==> {
            let process_ptr = current_process.unwrap();
            let perm = process_lock_perm.unwrap().view();
            &&& old(krnl).prc_mp.dom().contains(process_ptr)
            &&& !old(krnl).prc_mp.spec_index(process_ptr).being_killed()
            &&& old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running || old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Zombie
            &&& typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write)
            &&& perm.state() is WriteLock
            &&& perm.thread_id() == old(lctx).thread_id()
            &&& perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id
        },
        current_thread is Some ==> {
            let thread_ptr = current_thread.unwrap();
            let perm = current_thread_lock_perm.unwrap().view();
            &&& old(krnl).thr_mp.dom().contains(thread_ptr)
            &&& !old(krnl).thr_mp.spec_index(thread_ptr).being_killed()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id })
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None
            &&& !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited
            &&& typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write)
            &&& perm.state() is WriteLock
            &&& perm.thread_id() == old(lctx).thread_id()
            &&& perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id
        },
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).scheduler_lock_map().dom() =~= set![(scheduler_ptr, cpu_id)],
        old(lctx).process_lock_map().dom() =~= match current_process {
            Some(ptr) => set![ptr],
            None => Set::empty(),
        },
        old(lctx).thread_lock_map().dom() =~= match current_thread {
            Some(ptr) => set![ptr],
            None => Set::empty(),
        },
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).nonlock_view() == old(steps).nonlock_view(),
        final(steps).nonlock_snapshot_u() == old(steps).nonlock_snapshot_u(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        schedule_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, entry_regs, false, None),
        forall|i: CpuId| #![trigger final(krnl).cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> final(krnl).cpu_arr.spec_index(i).view().view().view() == old(steps).snapshot_k().cpu_arr.spec_index(i).view().view().view(),
{
    krnl.wunlock_scheduler_shard(scheduler_ptr, cpu_id, Tracked(&mut *lctx), Tracked(scheduler_lock_perm));
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    if let Some(thread_perm) = current_thread_lock_perm {
        release_cpu_and_process_and_thread_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, current_process.unwrap(), current_thread.unwrap(), thread_perm, process_lock_perm.unwrap(), Tracked(cpu_lock_perm));
    } else {
        release_cpu_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Tracked(cpu_lock_perm));
    }
    proof {
        assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(old(steps).snapshot_k())) by { kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&old(steps).snapshot_k(), &*krnl); };
        schedule_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, entry_regs);
    }
}

/// With `cpu_id` write-held since the entry snapshot and not Off: write-locks its live `current_process` and
/// `current_thread`, if any, and then its shard of `scheduler_ptr`, and returns the process, thread, shard, and cpu perms.
/// If the current process or thread is being killed, releases every lock and finishes the call without recording a step.
pub(super) fn schedule_lock_current_and_shard(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr,
    current_process: Option<RwLockProcessPtr>, current_thread: Option<RwLockThreadPtr>, Tracked(cpu_lock_perm): Tracked<LockPerm>, Ghost(entry_regs): Ghost<Registers>,
) -> (ret: Option<(Option<Tracked<LockPerm>>, Option<Tracked<LockPerm>>, Tracked<LockPerm>, Tracked<LockPerm>)>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).nonlock_view().len() == 0,
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        old(krnl).cpu_arr.spec_index(cpu_id).value.killer_info() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.killer_info(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        {
            let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            &&& !(cpu.state is Off)
            &&& cpu.current_process == current_process
            &&& cpu.current_thread == current_thread
            &&& old(krnl).ctn_mp.spec_index(cpu.owning_container).view_rodata().view().scheduler == scheduler_ptr
        },
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        forall|i: CpuId| #![trigger final(krnl).cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> final(krnl).cpu_arr.spec_index(i).view().view().view() == old(krnl).cpu_arr.spec_index(i).view().view().view(),
        (ret is None) == (current_process is Some && (old(krnl).prc_mp.spec_index(current_process.unwrap()).being_killed() || old(krnl).thr_mp.spec_index(current_thread.unwrap()).being_killed())),
        ret is None ==> {
            &&& final(lctx).kernel_view_locking_state() is Release
            &&& final(lctx).no_locks_held()
            &&& final(krnl).all_objects_unlocked(final(lctx))
            &&& final(steps).view() == old(steps).view()
            &&& final(steps).nonlock_view() == old(steps).nonlock_view()
            &&& kernel_k_to_nonlock_kernel_u(*final(krnl)) == old(steps).nonlock_snapshot_u()
            &&& final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl))
            &&& final(steps).snapshot_k() == *final(krnl)
            &&& schedule_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
                kernel_k_to_kernel_u(*final(krnl)), cpu_id, entry_regs, false, None)
        },
        ret is Some ==> *final(steps) == *old(steps),
        ret is Some ==> *final(krnl) == (KernelK { prc_mp: final(krnl).prc_mp, thr_mp: final(krnl).thr_mp, sched_mp: final(krnl).sched_mp, ..*old(krnl) }),
        ret is Some ==> kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), final(krnl)),
        ret is Some ==> kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), final(krnl)),
        ret is Some ==> final(krnl).sched_mp.unchanged_except(&old(krnl).sched_mp, scheduler_ptr),
        ret is Some ==> scheduler_shards_of(final(krnl).sched_mp.spec_index(scheduler_ptr)) == scheduler_shards_of(old(krnl).sched_mp.spec_index(scheduler_ptr)),
        ret is Some ==> final(krnl).sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view() == old(krnl).sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view(),
        ret is Some ==> match current_process {
            Some(p) => final(krnl).prc_mp.unchanged_except(&old(krnl).prc_mp, p),
            None => final(krnl).prc_mp == old(krnl).prc_mp,
        },
        ret is Some ==> match current_thread {
            Some(t) => final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, t),
            None => final(krnl).thr_mp == old(krnl).thr_mp,
        },
        ret is Some ==> {
            let (process_lock_perm, current_thread_lock_perm, scheduler_lock_perm, cpu_lock_perm) = ret.unwrap();
            &&& final(lctx).kernel_view_locking_state() is Acquire
            &&& current_process is Some == process_lock_perm is Some
            &&& current_thread is Some == current_thread_lock_perm is Some
            &&& final(krnl).sched_mp.dom().contains(scheduler_ptr)
            &&& typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write)
            &&& cpu_lock_perm.view().state() is WriteLock
            &&& cpu_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& cpu_lock_perm.view().lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(final(lctx).scheduler_lock_map(), (scheduler_ptr, cpu_id), TypedLockMode::Write)
            &&& scheduler_lock_perm.view().state() is WriteLock
            &&& scheduler_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& scheduler_lock_perm.view().lock_id() == final(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id
            &&& (current_process is Some ==> {
                let process_ptr = current_process.unwrap();
                let perm = process_lock_perm.unwrap().view();
                &&& old(krnl).prc_mp.spec_index(process_ptr).locking_thread() is None
                &&& final(krnl).prc_mp.spec_index(process_ptr).view() == old(krnl).prc_mp.spec_index(process_ptr).view()
                &&& final(krnl).prc_mp.spec_index(process_ptr).view_rodata() == old(krnl).prc_mp.spec_index(process_ptr).view_rodata()
                &&& !final(krnl).prc_mp.spec_index(process_ptr).being_killed()
                &&& final(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running || final(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Zombie
                &&& typed_lock_map_contains_mode(final(lctx).process_lock_map(), process_ptr, TypedLockMode::Write)
                &&& perm.state() is WriteLock
                &&& perm.thread_id() == final(lctx).thread_id()
                &&& perm.lock_id() == final(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id
            })
            &&& (current_thread is Some ==> {
                let thread_ptr = current_thread.unwrap();
                let perm = current_thread_lock_perm.unwrap().view();
                &&& old(krnl).thr_mp.spec_index(thread_ptr).locking_thread() is None
                &&& final(krnl).thr_mp.spec_index(thread_ptr).view() == old(krnl).thr_mp.spec_index(thread_ptr).view()
                &&& !final(krnl).thr_mp.spec_index(thread_ptr).being_killed()
                &&& final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean()
                &&& final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean()
                &&& final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None
                &&& !final(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited
                &&& typed_lock_map_contains_mode(final(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write)
                &&& perm.state() is WriteLock
                &&& perm.thread_id() == final(lctx).thread_id()
                &&& perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id
            })
            &&& final(lctx).cpu_lock_map().dom() =~= set![cpu_id]
            &&& final(lctx).process_lock_map().dom() =~= match current_process {
                Some(ptr) => set![ptr],
                None => Set::empty(),
            }
            &&& final(lctx).thread_lock_map().dom() =~= match current_thread {
                Some(ptr) => set![ptr],
                None => Set::empty(),
            }
            &&& final(lctx).scheduler_lock_map().dom() =~= set![(scheduler_ptr, cpu_id)]
            &&& final(lctx).page_lock_map().dom().is_empty()
            &&& final(lctx).container_lock_map().dom().is_empty()
            &&& final(lctx).endpoint_lock_map().dom().is_empty()
            &&& final(lctx).pcid_allocator_lock_map().dom().is_empty()
            &&& final(lctx).cpu_set_lock_map().dom().is_empty()
            &&& final(lctx).pagetable_lock_map().dom().is_empty()
            &&& final(lctx).pagetable_window_lock_map().dom().is_empty()
            &&& final(lctx).iommu_table_lock_map().dom().is_empty()
            &&& final(lctx).iommu_root_table_lock_map().dom().is_empty()
            &&& final(lctx).allocator_quota_4k_lock_map().dom().is_empty()
            &&& final(lctx).allocator_cache_4k_lock_map().dom().is_empty()
            &&& final(lctx).allocator_global_pool_4k_lock_map().dom().is_empty()
            &&& final(lctx).allocator_quota_2m_lock_map().dom().is_empty()
            &&& final(lctx).allocator_cache_2m_lock_map().dom().is_empty()
            &&& final(lctx).allocator_global_pool_2m_lock_map().dom().is_empty()
            &&& final(lctx).allocator_quota_1g_lock_map().dom().is_empty()
            &&& final(lctx).allocator_cache_1g_lock_map().dom().is_empty()
            &&& final(lctx).allocator_global_pool_1g_lock_map().dom().is_empty()
            &&& final(lctx).cpu_offline_flag_lock_map().dom().is_empty()
            &&& final(lctx).pcid_needflush_lock_map().dom().is_empty()
        },
{
    proof { schedule_current_cpu_references_wf(&*krnl, cpu_id); }
    let mut process_lock_perm: Option<Tracked<LockPerm>> = None;
    let mut current_thread_lock_perm: Option<Tracked<LockPerm>> = None;
    if let Some(process_ptr) = current_process {
        let res = krnl.wlock_process_unless_killed(process_ptr, Ghost(cpu_id), Tracked(&mut *lctx));
        if res.is_none() {
            krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
            proof {
                steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(process_ptr), None, None, None, None);
                schedule_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, entry_regs);
            }
            return None;
        }
        process_lock_perm = res;
        let thread_ptr = current_thread.unwrap();
        let res = krnl.wlock_current_running_thread_unless_killed(thread_ptr, Tracked(&mut *lctx));
        if res.is_none() {
            krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), process_lock_perm.unwrap());
            krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
            proof {
                steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(process_ptr), Some(thread_ptr), None, None, None);
                schedule_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, entry_regs);
            }
            return None;
        }
        current_thread_lock_perm = res;
    }
    proof { container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container); }
    let Tracked(scheduler_lock_perm) = krnl.wlock_scheduler_shard(scheduler_ptr, cpu_id, Tracked(&mut *lctx));
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    Some((process_lock_perm, current_thread_lock_perm, Tracked(scheduler_lock_perm), Tracked(cpu_lock_perm)))
}

/// With `cpu_id`, its shard of `scheduler_ptr`, and the live `current_process` and `current_thread`, if any, write-held:
/// write-locks the head of the shard queue unless the queue is empty or its head is being killed.
pub(super) fn schedule_lock_queue_head(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr, current_process: Option<RwLockProcessPtr>,
    current_thread: Option<RwLockThreadPtr>, Tracked(scheduler_lock_perm): Tracked<&LockPerm>,
) -> (ret: Option<(RwLockThreadPtr, Tracked<LockPerm>)>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        {
            let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            &&& !(cpu.state is Off)
            &&& cpu.current_process == current_process
            &&& cpu.current_thread == current_thread
            &&& old(krnl).ctn_mp.spec_index(cpu.owning_container).view_rodata().view().scheduler == scheduler_ptr
        },
        old(krnl).sched_mp.dom().contains(scheduler_ptr),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (scheduler_ptr, cpu_id), TypedLockMode::Write),
        scheduler_lock_perm.state() is WriteLock,
        scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).process_lock_map().dom() =~= match current_process {
            Some(ptr) => set![ptr],
            None => Set::empty(),
        },
        old(lctx).thread_lock_map().dom() =~= match current_thread {
            Some(ptr) => set![ptr],
            None => Set::empty(),
        },
        old(lctx).scheduler_lock_map().dom() =~= set![(scheduler_ptr, cpu_id)],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        ({
            let queue = old(krnl).sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view();
            &&& (ret is None) == (queue.len() == 0 || old(krnl).thr_mp.spec_index(queue[0]).being_killed())
            &&& (current_thread is Some ==> !queue.contains(current_thread.unwrap()))
            &&& (queue.len() > 0 ==> old(krnl).thr_mp.dom().contains(queue[0]))
            &&& (queue.len() == 0 ==> *final(krnl) == *old(krnl) && *final(lctx) == *old(lctx))
            &&& (queue.len() > 0 ==> kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)))
            &&& (queue.len() > 0 ==> kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)))
        }),
        *final(krnl) == (KernelK { thr_mp: final(krnl).thr_mp, ..*old(krnl) }),
        ret is None ==> final(krnl).thr_mp.dom() == old(krnl).thr_mp.dom(),
        ret is None ==> forall|t: RwLockThreadPtr| #![trigger final(krnl).thr_mp.spec_index(t)] old(krnl).thr_mp.dom().contains(t) ==> final(krnl).thr_mp.spec_index(t) == old(krnl).thr_mp.spec_index(t),
        ret is None ==> typed_lock_maps_unchanged(old(lctx), final(lctx)),
        ret is Some ==> {
            let (next_thread, next_perm) = ret.unwrap();
            let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            let queue = old(krnl).sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view();
            &&& queue.len() > 0
            &&& queue[0] == next_thread
            &&& old(krnl).thr_mp.dom().contains(next_thread)
            &&& !old(krnl).thr_mp.spec_index(next_thread).being_killed()
            &&& old(krnl).thr_mp.spec_index(next_thread).locking_thread() is None
            &&& old(krnl).thr_mp.spec_index(next_thread).view().state == (ThreadState::SCHEDULED { cpu_id })
            &&& old(krnl).thr_mp.spec_index(next_thread).view().owning_container == cpu.owning_container
            &&& old(krnl).prc_mp.dom().contains(old(krnl).thr_mp.spec_index(next_thread).view().owning_proc)
            &&& final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, next_thread)
            &&& final(krnl).thr_mp.spec_index(next_thread).view() == old(krnl).thr_mp.spec_index(next_thread).view()
            &&& !final(krnl).thr_mp.spec_index(next_thread).being_killed()
            &&& final(krnl).thr_mp.spec_index(next_thread).view().free_quota_pending_clean()
            &&& final(krnl).thr_mp.spec_index(next_thread).view().temp_alloc_clean()
            &&& final(krnl).thr_mp.spec_index(next_thread).view().syscall_progress.view() is None
            &&& !final(krnl).thr_mp.spec_index(next_thread).view_ghost().exited
            &&& typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Thread(next_thread), TypedHeldLock { lock_id: final(krnl).thr_mp.lock_id_by_key(next_thread), mode: TypedLockMode::Write })
            &&& typed_lock_map_contains_mode(final(lctx).thread_lock_map(), next_thread, TypedLockMode::Write)
            &&& next_perm.view().state() is WriteLock
            &&& next_perm.view().thread_id() == final(lctx).thread_id()
            &&& next_perm.view().lock_id() == final(krnl).thr_mp.spec_index(next_thread).locking_thread()->Write_lock_id
        },
{
    proof {
        let container_ptr = krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container;
        schedule_current_cpu_references_wf(&*krnl, cpu_id);
        assert({
            &&& krnl.sched_mp.perms_wf()
            &&& krnl.sched_mp.spec_index(scheduler_ptr).inv()
            &&& krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view().len() == krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.len()
            &&& krnl.sched_mp.spec_index(scheduler_ptr).owning_container == container_ptr
            &&& (current_thread is Some ==> !krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view().contains(current_thread.unwrap()))
        }) by {
            scheduler_perms_wf_map(krnl.sched_mp);
            scheduler_perms_wf_at(krnl.sched_mp, scheduler_ptr); container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, container_ptr);
            container_thread_scheduler_wf_at(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp, scheduler_ptr, cpu_id, current_thread.unwrap()); reveal(LinkedList::wf_value_list);
        };
    }
    let shard = krnl.sched_mp.borrow_shard_typed(scheduler_ptr, cpu_id, Ghost(lctx.scheduler_lock_map()), Tracked(&*lctx), Tracked(scheduler_lock_perm));
    if shard.queue.len() == 0 { return None; }
    let (_, next_thread) = shard.queue.peek_head();
    assert(krnl.thr_mp.dom().contains(next_thread) && krnl.thr_mp.spec_index(next_thread).view().state == (ThreadState::SCHEDULED { cpu_id })
        && krnl.thr_mp.spec_index(next_thread).view().owning_container == krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container) by {
        container_thread_scheduler_wf_at(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp, scheduler_ptr, cpu_id, next_thread);
    };
    assert(krnl.prc_mp.dom().contains(krnl.thr_mp.spec_index(next_thread).view().owning_proc)) by { process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, next_thread); };
    let res = krnl.wlock_scheduled_thread_unless_killed(next_thread, Tracked(&mut *lctx));
    if res.is_none() { return None; }
    Some((next_thread, res.unwrap()))
}
} // verus!
