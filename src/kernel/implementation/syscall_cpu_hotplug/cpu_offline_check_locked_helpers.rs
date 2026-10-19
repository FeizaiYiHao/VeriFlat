use vstd::prelude::*;
use crate::*;
use super::cpu_offline_check_spec::*;
use super::cpu_offline_check_trace::*;
use super::cpu_offline_check::cpu_offline_commit;

verus! {
/// With `cpu_id`, its offline request flag, and, if `process_lock_perm` is given, `current_process` write-held since the
/// entry snapshot: releases them all and finishes the check without recording a step.
pub(super) fn cpu_offline_check_continue(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, pt_regs: &Registers,
    flags_ptr: RwLockCpuOfflineFlagsPtr, current_process: Option<RwLockProcessPtr>, process_lock_perm: Option<Tracked<LockPerm>>,
    Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(flag_lock_perm): Tracked<LockPerm>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).nonlock_view().len() == 0,
        *old(krnl) == (KernelK {
            cpu_arr: old(krnl).cpu_arr, prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, cpu_offline_mp: old(krnl).cpu_offline_mp, cpu_set_mp: old(krnl).cpu_set_mp,
            ..old(steps).snapshot_k()
        }),
        old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        forall|p: RwLockProcessPtr| #![trigger old(krnl).prc_mp.spec_index(p)]
            old(steps).snapshot_k().prc_mp.dom().contains(p) ==> if process_lock_perm is Some && current_process == Some(p) {
                old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() },
        forall|t: RwLockThreadPtr| #![trigger old(krnl).thr_mp.spec_index(t)]
            old(steps).snapshot_k().thr_mp.dom().contains(t) ==> old(krnl).thr_mp.spec_index(t).locking_thread() == old(steps).snapshot_k().thr_mp.spec_index(t).locking_thread(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).cpu_offline_mp.dom().contains(flags_ptr),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).cpu_offline_flag_lock_map(), (flags_ptr, cpu_id), TypedLockMode::Write),
        flag_lock_perm.state() is WriteLock,
        flag_lock_perm.thread_id() == old(lctx).thread_id(),
        flag_lock_perm.lock_id() == old(krnl).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        process_lock_perm is Some ==> {
            let process_ptr = current_process.unwrap();
            let perm = process_lock_perm.unwrap().view();
            &&& current_process is Some
            &&& old(krnl).prc_mp.dom().contains(process_ptr)
            &&& !old(krnl).prc_mp.spec_index(process_ptr).being_killed()
            &&& old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running || old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Zombie
            &&& typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write)
            &&& perm.state() is WriteLock
            &&& perm.thread_id() == old(lctx).thread_id()
            &&& perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id
        },
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).process_lock_map().dom() =~= if process_lock_perm is Some { set![current_process.unwrap()] } else { Set::empty() },
        old(lctx).cpu_offline_flag_lock_map().dom() =~= set![(flags_ptr, cpu_id)],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom().is_empty(),
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
        cpu_offline_check_entry_trace(
            final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, *pt_regs, false, false,
        ),
        final(steps).nonlock_view().len() == 0,
        kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(old(steps).snapshot_k()),
        forall|other_cpu: CpuId| #![trigger final(krnl).cpu_arr.spec_index(other_cpu)]
            index_valid(NUM_CPUS, other_cpu) && other_cpu != cpu_id ==> final(krnl).cpu_arr.spec_index(other_cpu).view().view().view() == old(steps).snapshot_k().cpu_arr.spec_index(other_cpu).view().view().view(),
{
    krnl.wunlock_cpu_offline_flag(flags_ptr, cpu_id, Tracked(&mut *lctx), Tracked(flag_lock_perm));
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    if process_lock_perm.is_some() {
        release_cpu_and_process_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, current_process.unwrap(), process_lock_perm.unwrap(), Tracked(cpu_lock_perm));
    } else {
        release_cpu_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Tracked(cpu_lock_perm));
    }
    proof {
        assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(old(steps).snapshot_k())) by { kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&old(steps).snapshot_k(), &*krnl); };
        cpu_offline_check_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, *pt_regs);
    }
}

/// With `cpu_id`, its requested offline flag, and the live `current_process` and `current_thread`, if any, write-held since
/// the entry snapshot: write-locks the container's cpu set and scheduler shard of the cpu and commits the offline.
pub(super) fn cpu_offline_check_lock_and_commit(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, pt_regs: &Registers,
    container_ptr: RwLockContainerPtr, flags_ptr: RwLockCpuOfflineFlagsPtr, current_process: Option<RwLockProcessPtr>, current_thread: Option<RwLockThreadPtr>,
    process_lock_perm: Option<Tracked<LockPerm>>, thread_lock_perm: Option<Tracked<LockPerm>>, Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(flag_lock_perm): Tracked<LockPerm>,
) -> (committed: bool)
    requires
        old(krnl).inv(),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, cpu_offline_mp: old(krnl).cpu_offline_mp, ..old(steps).snapshot_k() }),
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
        old(krnl).cpu_offline_mp.unchanged_except(&old(steps).snapshot_k().cpu_offline_mp, flags_ptr),
        old(krnl).cpu_offline_mp.spec_index(flags_ptr).flags.entries_unchanged_except(&old(steps).snapshot_k().cpu_offline_mp.spec_index(flags_ptr).flags, cpu_id),
        old(steps).snapshot_k().cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().locking_thread() is None,
        cpu_offline_requests_of(old(krnl).cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(old(steps).snapshot_k().cpu_offline_mp.spec_index(flags_ptr)),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).nonlock_view().len() == 0,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom() =~= match current_process {
            Some(ptr) => set![ptr],
            None => Set::empty(),
        },
        old(lctx).thread_lock_map().dom() =~= match current_thread {
            Some(ptr) => set![ptr],
            None => Set::empty(),
        },
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
        old(lctx).cpu_offline_flag_lock_map().dom() =~= set![(flags_ptr, cpu_id)],
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        {
            let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            &&& !(cpu.state is Off)
            &&& cpu.current_process == current_process
            &&& cpu.current_thread == current_thread
            &&& cpu.owning_container == container_ptr
            &&& old(krnl).ctn_mp.dom().contains(container_ptr)
            &&& flags_ptr == cpu_offline_flags_ptr(container_ptr)
            &&& old(krnl).cpu_published[cpu_id as int].view() == (cpu.current_cr3, cpu.current_pcid)
        },
        current_process is Some == current_thread is Some,
        current_process is Some == process_lock_perm is Some,
        current_thread is Some == thread_lock_perm is Some,
        old(krnl).cpu_offline_mp.dom().contains(flags_ptr),
        old(krnl).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().view().requested,
        old(krnl).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().wlocked_by(old(lctx)),
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
            let perm = thread_lock_perm.unwrap().view();
            &&& old(krnl).thr_mp.dom().contains(thread_ptr)
            &&& !old(krnl).thr_mp.spec_index(thread_ptr).being_killed()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id })
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == current_process.unwrap()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None
            &&& !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited
            &&& typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write)
            &&& perm.state() is WriteLock
            &&& perm.thread_id() == old(lctx).thread_id()
            &&& perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id
        },
        typed_lock_map_contains_mode(old(lctx).cpu_offline_flag_lock_map(), (flags_ptr, cpu_id), TypedLockMode::Write),
        flag_lock_perm.state() is WriteLock,
        flag_lock_perm.thread_id() == old(lctx).thread_id(),
        flag_lock_perm.lock_id() == old(krnl).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
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
        committed == !old(krnl).cpu_set_mp.spec_index(old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set).being_killed(),
        cpu_offline_check_entry_trace(
            final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, *pt_regs, committed, if committed { cpu_offline_check_flushed_default_pcid(old(steps).snapshot_k(), cpu_id) } else { false },
        ),
        final(steps).nonlock_view().len() == if committed { 1nat } else { 0nat },
        !committed ==> kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(old(steps).snapshot_k()),
        committed ==> {
            let step = final(steps).nonlock_view()[0];
            &&& step.old_u == kernel_k_to_nonlock_kernel_u(old(steps).snapshot_k())
            &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
            &&& cpu_offline_check_step_pre(step.old_u, cpu_id)
            &&& cpu_offline_check_step(step.old_u, step.new_u, cpu_id, *pt_regs, cpu_offline_check_flushed_default_pcid(old(steps).snapshot_k(), cpu_id))
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Off
        },
        forall|other_cpu: CpuId| #![trigger final(krnl).cpu_arr.spec_index(other_cpu)]
            index_valid(NUM_CPUS, other_cpu) && other_cpu != cpu_id ==> final(krnl).cpu_arr.spec_index(other_cpu).view().view().view() == old(steps).snapshot_k().cpu_arr.spec_index(other_cpu).view().view().view(),
{
    proof {
        assert({
            &&& krnl.ctn_mp.spec_index(container_ptr).is_init()
            &&& krnl.ctn_mp.view().spec_index(container_ptr).is_init()
            &&& krnl.ctn_mp.view().spec_index(container_ptr).addr() == container_ptr
        }) by { container_perms_wf_at(krnl.ctn_mp, container_ptr); };
    }
    let container_ro = krnl.ctn_mp.borrow_rodata(container_ptr).borrow();
    let scheduler_ptr = container_ro.scheduler;
    let cpu_set_ptr = container_ro.cpu_set;
    proof { assert(krnl.sched_mp.dom().contains(scheduler_ptr)) by { container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, container_ptr); }; assert(krnl.cpu_set_mp.dom().contains(cpu_set_ptr)) by { container_cpu_set_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, container_ptr); }; }
    let cpu_set_res = krnl.wlock_cpu_set_unless_killed(cpu_set_ptr, Tracked(&mut *lctx));
    if cpu_set_res.is_none() {
        // A marked set's container owns no process, so the cpu runs none and only the cpu and flag locks are held.
        proof {
            container_cpu_wf_cpu_at(old(krnl).ctn_mp, old(krnl).cpu_set_mp, old(krnl).cpu_arr, cpu_id); container_cpu_set_wf_container_at(old(krnl).ctn_mp, old(krnl).cpu_set_mp, container_ptr);
            cpu_set_kill_mark_wf_at(old(krnl).ctn_mp, old(krnl).cpu_set_mp, old(krnl).prc_mp, cpu_set_ptr);
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        }
        cpu_offline_check_continue(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, pt_regs, flags_ptr, current_process, None, Tracked(cpu_lock_perm), Tracked(flag_lock_perm));
        return false;
    }
    let Tracked(cpu_set_lock_perm) = cpu_set_res.unwrap();
    let Tracked(scheduler_lock_perm) = krnl.wlock_scheduler_shard(scheduler_ptr, cpu_id, Tracked(&mut *lctx));
    proof {
        assert(current_thread is Some ==> !krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view().contains(current_thread.unwrap())) by { container_thread_scheduler_wf_at(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp, scheduler_ptr, cpu_id, current_thread.unwrap()); };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
    }
    cpu_offline_commit(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, pt_regs, container_ptr, scheduler_ptr, cpu_set_ptr, flags_ptr, current_process, current_thread,
        process_lock_perm, thread_lock_perm, Tracked(cpu_lock_perm), Tracked(flag_lock_perm), Tracked(cpu_set_lock_perm), Tracked(scheduler_lock_perm),
    );
    true
}
} // verus!
