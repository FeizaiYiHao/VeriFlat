use vstd::prelude::*;
use crate::*;
use super::syscall_cpu_offline_check_spec::*;
use super::syscall_cpu_offline_check_trace::*;
use super::syscall_cpu_offline_check::{OfflineCheckResult, cpu_offline_commit};

verus! {
/// With `cpu_id` write-held since the hold step recorded after the partial trace from `entry_k` starting at `start`, and
/// with the offline request flag, `current_thread`, and `current_process` write-held since the snapshot of `steps` when
/// their perms are given: releases them all and records the release step.
pub(super) fn cpu_offline_check_continue(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, pt_regs: &Registers,
    flags_ptr: RwLockCpuOfflineFlagsPtr, current_process: Option<RwLockProcessPtr>, current_thread: Option<RwLockThreadPtr>, process_lock_perm: Option<Tracked<LockPerm>>,
    thread_lock_perm: Option<Tracked<LockPerm>>, flag_lock_perm: Option<Tracked<LockPerm>>, Tracked(cpu_lock_perm): Tracked<LockPerm>, Ghost(entry_k): Ghost<KernelK>,
    Ghost(start): Ghost<int>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        0 <= start <= old(steps).view().len(),
        cpu_offline_check_trace_after_hold(old(steps).view().subrange(start, old(steps).view().len() as int), kernel_k_to_kernel_u(entry_k), cpu_id),
        *old(krnl) == (KernelK { prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, cpu_offline_mp: old(krnl).cpu_offline_mp, cpu_set_mp: old(krnl).cpu_set_mp, ..old(steps).snapshot_k() }),
        old(krnl).prc_mp.dom() == old(steps).snapshot_k().prc_mp.dom(),
        old(krnl).thr_mp.dom() == old(steps).snapshot_k().thr_mp.dom(),
        forall|p: RwLockProcessPtr| #![trigger old(krnl).prc_mp.spec_index(p)]
            old(steps).snapshot_k().prc_mp.dom().contains(p) ==> if process_lock_perm is Some && current_process == Some(p) {
                old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() },
        forall|t: RwLockThreadPtr| #![trigger old(krnl).thr_mp.spec_index(t)]
            old(steps).snapshot_k().thr_mp.dom().contains(t) ==> if thread_lock_perm is Some && current_thread == Some(t) {
                old(steps).snapshot_k().thr_mp.spec_index(t).locking_thread() is None
            } else { old(krnl).thr_mp.spec_index(t).locking_thread() == old(steps).snapshot_k().thr_mp.spec_index(t).locking_thread() },
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).cpu_offline_mp.dom().contains(flags_ptr),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cpu_lock_perm.lock_id() }),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        flag_lock_perm is Some ==> {
            let perm = flag_lock_perm.unwrap().view();
            &&& typed_lock_map_contains_mode(old(lctx).cpu_offline_flag_lock_map(), (flags_ptr, cpu_id), TypedLockMode::Write)
            &&& perm.state() is WriteLock
            &&& perm.thread_id() == old(lctx).thread_id()
            &&& perm.lock_id() == old(krnl).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().locking_thread()->Write_lock_id
        },
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
        thread_lock_perm is Some ==> {
            let thread_ptr = current_thread.unwrap();
            let perm = thread_lock_perm.unwrap().view();
            &&& current_thread is Some
            &&& process_lock_perm is Some
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
        old(lctx).process_lock_map().dom() =~= if process_lock_perm is Some { set![current_process.unwrap()] } else { Set::empty() },
        old(lctx).thread_lock_map().dom() =~= if thread_lock_perm is Some { set![current_thread.unwrap()] } else { Set::empty() },
        old(lctx).cpu_offline_flag_lock_map().dom() =~= if flag_lock_perm is Some { set![(flags_ptr, cpu_id)] } else { Set::empty() },
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
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
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        cpu_offline_check_entry_trace(
            final(steps).view().subrange(start, final(steps).view().len() as int), kernel_k_to_kernel_u(entry_k), kernel_k_to_kernel_u(*final(krnl)), cpu_id, *pt_regs, false, false,
        ),
{
    if let Some(perm) = flag_lock_perm { krnl.wunlock_cpu_offline_flag(flags_ptr, cpu_id, Tracked(&mut *lctx), perm); }
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    if thread_lock_perm.is_some() {
        release_cpu_and_process_and_thread_and_finish_syscall(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, current_process.unwrap(), current_thread.unwrap(), thread_lock_perm.unwrap(), process_lock_perm.unwrap(),
            Tracked(cpu_lock_perm),
        );
    } else if process_lock_perm.is_some() {
        release_cpu_and_process_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, current_process.unwrap(), process_lock_perm.unwrap(), Tracked(cpu_lock_perm));
    } else {
        release_cpu_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Tracked(cpu_lock_perm));
    }
    proof {
        assert(cpu_offline_check_entry_trace(steps.view().subrange(start, steps.view().len() as int), kernel_k_to_kernel_u(entry_k), kernel_k_to_kernel_u(*krnl), cpu_id, *pt_regs, false, false)) by {
            kernel_cpu_lock_mode_changed_implies_u_step(&old(steps).snapshot_k(), &*krnl, cpu_id); cpu_offline_check_release_step_from_u(&old(steps).snapshot_k(), &*krnl, cpu_id);
            cpu_offline_check_trace_release_step(
                &*steps, start, old(steps).view(), kernel_k_to_kernel_u(entry_k), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, *pt_regs,
            );
        };
    }
}

/// From the snapshot after the hold step, recorded after the partial trace from `entry_k` starting at `start`, with `cpu_id`
/// write-held, not Off, owned by `container_ptr`, and running `current_thread` of `current_process`, if any: write-locks that
/// process and thread unless killed, rereads the container's request bit for the cpu under its flag lock, and commits the
/// offline unless the bit is clear or a killer intervened; otherwise releases every lock with the release step.
pub(super) fn cpu_offline_check_recheck(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, pt_regs: &Registers,
    Tracked(cpu_lock_perm): Tracked<LockPerm>, container_ptr: RwLockContainerPtr, current_process: Option<RwLockProcessPtr>, current_thread: Option<RwLockThreadPtr>,
    Ghost(entry_k): Ghost<KernelK>, Ghost(start): Ghost<int>,
) -> (ret: OfflineCheckResult)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        cpu_offline_check_trace_after_hold(old(steps).view().subrange(start, old(steps).view().len() as int), kernel_k_to_kernel_u(entry_k), cpu_id),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cpu_lock_perm.lock_id() }),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
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
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        {
            let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            &&& !(cpu.state is Off)
            &&& cpu.owning_container == container_ptr
            &&& cpu.current_process == current_process
            &&& cpu.current_thread == current_thread
            &&& old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cpu.current_cr3, cpu.current_pcid)
        },
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        cpu_offline_check_entry_trace(
            final(steps).view().subrange(start, final(steps).view().len() as int), kernel_k_to_kernel_u(entry_k), kernel_k_to_kernel_u(*final(krnl)), cpu_id, *pt_regs,
            ret is Off, if ret is Off { cpu_offline_check_flushed_default_pcid(*old(krnl), cpu_id) } else { false },
        ),
        ret == cpu_offline_check_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id),
        ret is Off ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Off,
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    proof {
        assert({
            &&& krnl.ctn_mp.dom().contains(container_ptr)
            &&& krnl.cpu_offline_mp.dom().contains(cpu_offline_flags_ptr(container_ptr))
            &&& krnl.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(container_ptr)).container_depth.view() == krnl.cpu_arr.spec_index(cpu_id).view().view().view().container_depth
        }) by { container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id); container_cpu_offline_flags_wf_container_at(krnl.ctn_mp, krnl.cpu_offline_mp, container_ptr); };
        assert(page_ptr_2m_valid(container_ptr)) by { container_pages_backward_at(krnl.pg_arr, krnl.ctn_mp, container_ptr); };
        assert({
            &&& (current_process is Some ==> krnl.prc_mp.dom().contains(current_process.unwrap()) && krnl.cpu_arr.spec_index(cpu_id).view().view().view().state is Running)
            &&& (current_process is Some == current_thread is Some)
            &&& (current_process is Some ==> krnl.prc_mp.spec_index(current_process.unwrap()).view_rodata().view().owning_container == container_ptr)
            &&& (current_process is Some ==> {
                &&& krnl.prc_mp.spec_index(current_process.unwrap()).view_rodata().view().container_depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().container_depth
                &&& krnl.prc_mp.spec_index(current_process.unwrap()).view_rodata().view().depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().process_depth
            })
            &&& (current_thread is Some ==> {
                let ptr = current_thread.unwrap();
                &&& krnl.thr_mp.dom().contains(ptr)
                &&& krnl.thr_mp.spec_index(ptr).view().container_depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().container_depth
                &&& krnl.thr_mp.spec_index(ptr).view().process_depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().process_depth
                &&& krnl.thr_mp.spec_index(ptr).view().state == (ThreadState::RUNNING { cpu_id })
                &&& krnl.thr_mp.spec_index(ptr).view().owning_proc == current_process.unwrap()
                &&& krnl.thr_mp.spec_index(ptr).view().owning_container == container_ptr
            })
        }) by {
            thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id);
            cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_id);
            if current_thread is Some { process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, current_thread.unwrap()); }
            if current_process is Some { container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, current_process.unwrap()); }
        };
    }
    let flags_ptr = container_ptr + 4096;
    let mut process_lock_perm: Option<Tracked<LockPerm>> = None;
    let mut thread_lock_perm: Option<Tracked<LockPerm>> = None;
    let mut live = true;
    if let Some(process_ptr) = current_process {
        process_lock_perm = krnl.wlock_process_unless_killed(process_ptr, Ghost(cpu_id), Tracked(&mut *lctx));
        if process_lock_perm.is_some() { thread_lock_perm = krnl.wlock_current_running_thread_unless_killed(current_thread.unwrap(), Tracked(&mut *lctx)); }
        live = thread_lock_perm.is_some();
    }
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    if !live {
        cpu_offline_check_continue(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, pt_regs, flags_ptr, current_process, current_thread, process_lock_perm, thread_lock_perm, None,
            Tracked(cpu_lock_perm), Ghost(entry_k), Ghost(start),
        );
        proof { cpu_offline_check_result_from_k(old(krnl), cpu_id, OfflineCheckResult::Continue); }
        return OfflineCheckResult::Continue;
    }
    let Tracked(flag_lock_perm) = krnl.wlock_cpu_offline_flag(flags_ptr, cpu_id, Tracked(&mut *lctx));
    let requested = krnl.cpu_offline_mp.read_flag(flags_ptr, cpu_id, Tracked(&flag_lock_perm));
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    if !requested {
        cpu_offline_check_continue(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, pt_regs, flags_ptr, current_process, current_thread, process_lock_perm, thread_lock_perm,
            Some(Tracked(flag_lock_perm)), Tracked(cpu_lock_perm), Ghost(entry_k), Ghost(start),
        );
        proof { cpu_offline_check_result_from_k(old(krnl), cpu_id, OfflineCheckResult::Continue); }
        return OfflineCheckResult::Continue;
    }
    let committed = cpu_offline_check_lock_and_commit(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, pt_regs, container_ptr, flags_ptr, current_process, current_thread, process_lock_perm, thread_lock_perm,
        Tracked(cpu_lock_perm), Tracked(flag_lock_perm), Ghost(entry_k), Ghost(start),
    );
    if !committed {
        proof { cpu_offline_check_result_from_k(old(krnl), cpu_id, OfflineCheckResult::Continue); }
        return OfflineCheckResult::Continue;
    }
    proof { cpu_offline_check_result_from_k(old(krnl), cpu_id, OfflineCheckResult::Off); }
    OfflineCheckResult::Off
}

/// From the snapshot after the hold step, recorded after the partial trace from `entry_k` starting at `start`, with
/// `cpu_id`, its requested offline flag, and the live `current_process` and `current_thread`, if any, write-held since that
/// snapshot: write-locks the container's cpu set and scheduler shard of the cpu and commits the offline, or releases every
/// lock with the release step when a killer marked the cpu set.
pub(super) fn cpu_offline_check_lock_and_commit(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, pt_regs: &Registers,
    container_ptr: RwLockContainerPtr, flags_ptr: RwLockCpuOfflineFlagsPtr, current_process: Option<RwLockProcessPtr>, current_thread: Option<RwLockThreadPtr>,
    process_lock_perm: Option<Tracked<LockPerm>>, thread_lock_perm: Option<Tracked<LockPerm>>, Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(flag_lock_perm): Tracked<LockPerm>,
    Ghost(entry_k): Ghost<KernelK>, Ghost(start): Ghost<int>,
) -> (committed: bool)
    requires
        old(krnl).inv(),
        *old(krnl) == (KernelK { prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, cpu_offline_mp: old(krnl).cpu_offline_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cpu_lock_perm.lock_id() }),
        old(krnl).prc_mp.dom() == old(steps).snapshot_k().prc_mp.dom(),
        old(krnl).thr_mp.dom() == old(steps).snapshot_k().thr_mp.dom(),
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
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        0 <= start <= old(steps).view().len(),
        cpu_offline_check_trace_after_hold(old(steps).view().subrange(start, old(steps).view().len() as int), kernel_k_to_kernel_u(entry_k), cpu_id),
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
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
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
        {
            let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            &&& !(cpu.state is Off)
            &&& cpu.current_process == current_process
            &&& cpu.current_thread == current_thread
            &&& cpu.owning_container == container_ptr
            &&& old(krnl).ctn_mp.dom().contains(container_ptr)
            &&& flags_ptr == cpu_offline_flags_ptr(container_ptr)
            &&& old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cpu.current_cr3, cpu.current_pcid)
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
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        committed == !old(krnl).cpu_set_mp.spec_index(old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set).being_killed(),
        cpu_offline_check_entry_trace(
            final(steps).view().subrange(start, final(steps).view().len() as int), kernel_k_to_kernel_u(entry_k), kernel_k_to_kernel_u(*final(krnl)), cpu_id, *pt_regs,
            committed, if committed { cpu_offline_check_flushed_default_pcid(old(steps).snapshot_k(), cpu_id) } else { false },
        ),
        committed ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Off,
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
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        }
        cpu_offline_check_continue(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, pt_regs, flags_ptr, current_process, current_thread, process_lock_perm, thread_lock_perm,
            Some(Tracked(flag_lock_perm)), Tracked(cpu_lock_perm), Ghost(entry_k), Ghost(start),
        );
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
    proof {
        cpu_offline_check_trace_went_off_step(
            &*steps, start, old(steps).view(), kernel_k_to_kernel_u(entry_k), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, *pt_regs,
            cpu_offline_check_flushed_default_pcid(old(steps).snapshot_k(), cpu_id),
        );
    }
    true
}
} // verus!
