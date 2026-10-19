use vstd::prelude::*;
use crate::*;
use super::cpu_offline_check_spec::*;
use super::cpu_offline_check_trace::*;
#[cfg(verus_keep_ghost)]
use super::cpu_offline_check_eof::{cpu_went_off_eof, cpu_went_off_eof_fields};

verus! {
/// Finish of the offline of `cpu_id` committed from `before_k`, which is `entry_k` with the `(cpu_id, KERNEL_DEFAULT_PCID)`
/// needflush cell write-locked: close the kernel invariant, release every lock, and record the went-off step that starts
/// at the snapshot of `steps`.
pub(super) fn cpu_offline_commit_unlock_and_record(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, pt_regs: &Registers,
    container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr, cpu_set_ptr: RwLockCpuSetPtr, flags_ptr: RwLockCpuOfflineFlagsPtr,
    current_process: Option<RwLockProcessPtr>, current_thread: Option<RwLockThreadPtr>, process_lock_perm: Option<Tracked<LockPerm>>,
    thread_lock_perm: Option<Tracked<LockPerm>>, Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(flag_lock_perm): Tracked<LockPerm>,
    Tracked(cpu_set_lock_perm): Tracked<LockPerm>, Tracked(scheduler_lock_perm): Tracked<LockPerm>, Tracked(needflush_perm): Tracked<LockPerm>,
    Ghost(entry_k): Ghost<KernelK>, Ghost(before_k): Ghost<KernelK>,
)
    requires
        entry_k.inv(),
        entry_k == (KernelK {
            cpu_arr: entry_k.cpu_arr, prc_mp: entry_k.prc_mp, thr_mp: entry_k.thr_mp, sched_mp: entry_k.sched_mp, cpu_set_mp: entry_k.cpu_set_mp,
            cpu_offline_mp: entry_k.cpu_offline_mp, ..old(steps).snapshot_k()
        }),
        entry_k.cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        forall|p: RwLockProcessPtr| #![trigger entry_k.prc_mp.spec_index(p)]
            old(steps).snapshot_k().prc_mp.dom().contains(p) ==> if current_process == Some(p) {
                old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() is None
            } else { entry_k.prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() },
        forall|t: RwLockThreadPtr| #![trigger entry_k.thr_mp.spec_index(t)]
            old(steps).snapshot_k().thr_mp.dom().contains(t) ==> if current_thread == Some(t) {
                old(steps).snapshot_k().thr_mp.spec_index(t).locking_thread() is None
            } else { entry_k.thr_mp.spec_index(t).locking_thread() == old(steps).snapshot_k().thr_mp.spec_index(t).locking_thread() },
        entry_k.sched_mp.unchanged_except(&old(steps).snapshot_k().sched_mp, scheduler_ptr),
        entry_k.cpu_set_mp.unchanged_except(&old(steps).snapshot_k().cpu_set_mp, cpu_set_ptr),
        old(steps).snapshot_k().cpu_set_mp.spec_index(cpu_set_ptr).locking_thread() is None,
        entry_k.cpu_offline_mp.unchanged_except(&old(steps).snapshot_k().cpu_offline_mp, flags_ptr),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), &entry_k),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, entry_k.ep_mp),
        entry_k.irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
        entry_k.irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
        entry_k.cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        entry_k.iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        scheduler_shards_of(entry_k.sched_mp.spec_index(scheduler_ptr)) == scheduler_shards_of(old(steps).snapshot_k().sched_mp.spec_index(scheduler_ptr)),
        cpu_offline_requests_of(entry_k.cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(old(steps).snapshot_k().cpu_offline_mp.spec_index(flags_ptr)),
        index_valid(NUM_CPUS, cpu_id),
        !entry_k.cpu_arr.spec_index(cpu_id).view().being_killed(),
        {
            let cpu = entry_k.cpu_arr.spec_index(cpu_id).view().view().view();
            &&& !(cpu.state is Off)
            &&& cpu.current_process == current_process
            &&& cpu.current_thread == current_thread
            &&& cpu.owning_container == container_ptr
            &&& entry_k.ctn_mp.dom().contains(container_ptr)
            &&& entry_k.ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr
            &&& entry_k.ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set == cpu_set_ptr
            &&& flags_ptr == cpu_offline_flags_ptr(container_ptr)
        },
        current_process is Some == current_thread is Some,
        current_process is Some == process_lock_perm is Some,
        current_thread is Some == thread_lock_perm is Some,
        entry_k.sched_mp.dom().contains(scheduler_ptr),
        entry_k.cpu_set_mp.dom().contains(cpu_set_ptr),
        entry_k.cpu_offline_mp.dom().contains(flags_ptr),
        entry_k.cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().view().requested,
        current_process is Some ==> entry_k.prc_mp.dom().contains(current_process.unwrap()) && !entry_k.prc_mp.spec_index(current_process.unwrap()).being_killed(),
        current_thread is Some ==> {
            let thread = entry_k.thr_mp.spec_index(current_thread.unwrap());
            &&& entry_k.thr_mp.dom().contains(current_thread.unwrap())
            &&& !thread.being_killed()
            &&& thread.view().state == (ThreadState::RUNNING { cpu_id })
            &&& thread.view().owning_proc == current_process.unwrap()
        },
        before_k == (KernelK { pcid_needflush: before_k.pcid_needflush, ..entry_k }),
        before_k.pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).view() == entry_k.pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).view(),
        cpu_went_off_eof_transition_framing(before_k, *old(krnl), cpu_id, container_ptr, scheduler_ptr, cpu_set_ptr, flags_ptr, *pt_regs),
        before_k.inv(),
        current_thread is Some ==> {
            let queue_before = before_k.sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().view().queue;
            &&& !queue_before.view().contains(current_thread.unwrap())
            &&& !queue_before.map().dom().contains(before_k.thr_mp.spec_index(current_thread.unwrap()).view().scheduler_linkedlist_node.addr())
        },
        old(krnl).cpu_arr.inv(),
        old(krnl).cpu_tlb.inv(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().wf(),
        old(krnl).sched_mp.perms_wf(),
        old(krnl).sched_mp.spec_index(scheduler_ptr).shards.inv(),
        old(krnl).sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.wf(),
        old(krnl).cpu_set_mp.perms_wf(),
        old(krnl).cpu_set_mp.spec_index(cpu_set_ptr).view().owned_cpus.wf(),
        old(krnl).cpu_offline_mp.perms_wf(),
        old(krnl).cpu_offline_mp.spec_index(flags_ptr).inv(),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).sched_mp.dom().contains(scheduler_ptr),
        old(krnl).cpu_set_mp.dom().contains(cpu_set_ptr),
        old(krnl).cpu_offline_mp.dom().contains(flags_ptr),
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
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::SCHEDULED { cpu_id })
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None
            &&& typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write)
            &&& perm.state() is WriteLock
            &&& perm.thread_id() == old(lctx).thread_id()
            &&& perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id
        },
        cpu_id == old(lctx).cpu_id(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).pcid_needflush_lock_map().dom() =~= set![(cpu_id, KERNEL_DEFAULT_PCID)],
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
        old(lctx).scheduler_lock_map().dom() =~= set![(scheduler_ptr, cpu_id)],
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom() =~= set![cpu_set_ptr],
        old(lctx).pagetable_lock_map().dom().is_empty(),
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
        old(lctx).cpu_offline_flag_lock_map().dom() =~= set![(flags_ptr, cpu_id)],
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).pcid_needflush_lock_map(), (cpu_id, KERNEL_DEFAULT_PCID), TypedLockMode::Write),
        needflush_perm.state() is WriteLock,
        needflush_perm.thread_id() == old(lctx).thread_id(),
        needflush_perm.lock_id() == old(krnl).pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (scheduler_ptr, cpu_id), TypedLockMode::Write),
        scheduler_lock_perm.state() is WriteLock,
        scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), cpu_set_ptr, TypedLockMode::Write),
        cpu_set_lock_perm.state() is WriteLock,
        cpu_set_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_set_lock_perm.lock_id() == old(krnl).cpu_set_mp.spec_index(cpu_set_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).cpu_offline_flag_lock_map(), (flags_ptr, cpu_id), TypedLockMode::Write),
        flag_lock_perm.state() is WriteLock,
        flag_lock_perm.thread_id() == old(lctx).thread_id(),
        flag_lock_perm.lock_id() == old(krnl).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) }),
        cpu_offline_check_entry_trace(
            final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, *pt_regs, true, cpu_offline_check_flushed_default_pcid(entry_k, cpu_id),
        ),
        final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep { old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*final(krnl)) }),
        cpu_offline_check_step_pre(final(steps).nonlock_view().last().old_u, cpu_id),
        cpu_offline_check_step(final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, cpu_id, *pt_regs, cpu_offline_check_flushed_default_pcid(entry_k, cpu_id)),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Off,
        forall|other_cpu: CpuId| #![trigger final(krnl).cpu_arr.spec_index(other_cpu)]
            index_valid(NUM_CPUS, other_cpu) && other_cpu != cpu_id ==> final(krnl).cpu_arr.spec_index(other_cpu).view().view().view() == entry_k.cpu_arr.spec_index(other_cpu).view().view().view(),
{
    proof { cpu_went_off_eof(before_k, *krnl, cpu_id, container_ptr, scheduler_ptr, cpu_set_ptr, flags_ptr, *pt_regs); }
    let ghost mid = *krnl;
    krnl.wunlock_pcid_needflush(cpu_id, KERNEL_DEFAULT_PCID, Tracked(&mut *lctx), Tracked(needflush_perm));
    krnl.wunlock_scheduler_shard(scheduler_ptr, cpu_id, Tracked(&mut *lctx), Tracked(scheduler_lock_perm));
    krnl.wunlock_cpu_set(cpu_set_ptr, Tracked(&mut *lctx), Tracked(cpu_set_lock_perm));
    if let Some(perm) = thread_lock_perm { krnl.wunlock_thread(current_thread.unwrap(), Tracked(&mut *lctx), perm); }
    if let Some(perm) = process_lock_perm {
        krnl.wunlock_process(current_process.unwrap(), Tracked(&mut *lctx), perm);
    }
    krnl.wunlock_cpu_offline_flag(flags_ptr, cpu_id, Tracked(&mut *lctx), Tracked(flag_lock_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        let ghost flushed = cpu_offline_check_flushed_default_pcid(entry_k, cpu_id);
        let ghost commit_before = steps.view();
        cpu_went_off_eof_fields(steps.snapshot_k(), entry_k, before_k, mid, *krnl, cpu_id, container_ptr, scheduler_ptr, cpu_set_ptr, flags_ptr, current_process, current_thread, *pt_regs);
        steps.end_kernel_step_cpu_went_off(&*krnl, &*lctx, cpu_id, *pt_regs, flushed);
        assert({
            &&& cpu_offline_check_entry_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, *pt_regs, true, flushed)
            &&& cpu_offline_check_step_pre(steps.nonlock_view().last().old_u, cpu_id)
            &&& cpu_offline_check_step(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, *pt_regs, flushed)
        }) by {
            cpu_offline_check_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, *pt_regs, flushed);
            cpu_offline_check_step_from_u(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, *pt_regs, flushed);
            cpu_offline_check_trace_step(&*steps, commit_before, kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, *pt_regs, flushed);
        };
    }
}

/// `cpu_offline_commit` once the point facts of the held scheduler shard, cpu set, offline flags, cpu, and current thread
/// are established: write-locks the default-pcid needflush cell of `cpu_id`, requeues the running thread, if any, takes
/// the cpu Off, and finishes through `cpu_offline_commit_unlock_and_record`.
pub(super) fn cpu_offline_commit_go_off(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, pt_regs: &Registers,
    container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr, cpu_set_ptr: RwLockCpuSetPtr, flags_ptr: RwLockCpuOfflineFlagsPtr,
    current_process: Option<RwLockProcessPtr>, current_thread: Option<RwLockThreadPtr>, process_lock_perm: Option<Tracked<LockPerm>>,
    thread_lock_perm: Option<Tracked<LockPerm>>, cpu_lock_perm: Tracked<LockPerm>, flag_lock_perm: Tracked<LockPerm>,
    cpu_set_lock_perm: Tracked<LockPerm>, scheduler_lock_perm: Tracked<LockPerm>,
)
    requires
        old(krnl).inv(),
        *old(krnl) == (KernelK {
            cpu_arr: old(krnl).cpu_arr, prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, sched_mp: old(krnl).sched_mp,
            cpu_set_mp: old(krnl).cpu_set_mp, cpu_offline_mp: old(krnl).cpu_offline_mp, ..old(steps).snapshot_k()
        }),
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
        old(krnl).sched_mp.unchanged_except(&old(steps).snapshot_k().sched_mp, scheduler_ptr),
        old(krnl).cpu_set_mp.unchanged_except(&old(steps).snapshot_k().cpu_set_mp, cpu_set_ptr),
        old(steps).snapshot_k().cpu_set_mp.spec_index(cpu_set_ptr).locking_thread() is None,
        old(krnl).cpu_offline_mp.unchanged_except(&old(steps).snapshot_k().cpu_offline_mp, flags_ptr),
        old(krnl).cpu_offline_mp.spec_index(flags_ptr).flags.entries_unchanged_except(&old(steps).snapshot_k().cpu_offline_mp.spec_index(flags_ptr).flags, cpu_id),
        old(steps).snapshot_k().cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().locking_thread() is None,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).nonlock_view().len() == 0,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
        old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        scheduler_shards_of(old(krnl).sched_mp.spec_index(scheduler_ptr)) == scheduler_shards_of(old(steps).snapshot_k().sched_mp.spec_index(scheduler_ptr)),
        cpu_offline_requests_of(old(krnl).cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(old(steps).snapshot_k().cpu_offline_mp.spec_index(flags_ptr)),
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
        old(lctx).scheduler_lock_map().dom() =~= set![(scheduler_ptr, cpu_id)],
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom() =~= set![cpu_set_ptr],
        old(lctx).pagetable_lock_map().dom().is_empty(),
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
        old(lctx).cpu_offline_flag_lock_map().dom() =~= set![(flags_ptr, cpu_id)],
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        {
            let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            &&& !(cpu.state is Off)
            &&& cpu.current_process == current_process
            &&& cpu.current_thread == current_thread
            &&& cpu.owning_container == container_ptr
            &&& old(krnl).ctn_mp.dom().contains(container_ptr)
            &&& old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr
            &&& old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set == cpu_set_ptr
            &&& flags_ptr == cpu_offline_flags_ptr(container_ptr)
            &&& old(krnl).cpu_published[cpu_id as int].view() == (cpu.current_cr3, cpu.current_pcid)
        },
        current_process is Some == current_thread is Some,
        current_process is Some == process_lock_perm is Some,
        current_thread is Some == thread_lock_perm is Some,
        old(krnl).sched_mp.dom().contains(scheduler_ptr),
        old(krnl).cpu_set_mp.dom().contains(cpu_set_ptr),
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
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None
            &&& !old(krnl).sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view().contains(thread_ptr)
            &&& typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write)
            &&& perm.state() is WriteLock
            &&& perm.thread_id() == old(lctx).thread_id()
            &&& perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id
        },
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (scheduler_ptr, cpu_id), TypedLockMode::Write),
        scheduler_lock_perm.view().state() is WriteLock,
        scheduler_lock_perm.view().thread_id() == old(lctx).thread_id(),
        scheduler_lock_perm.view().lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), cpu_set_ptr, TypedLockMode::Write),
        cpu_set_lock_perm.view().state() is WriteLock,
        cpu_set_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_set_lock_perm.view().lock_id() == old(krnl).cpu_set_mp.spec_index(cpu_set_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).cpu_offline_flag_lock_map(), (flags_ptr, cpu_id), TypedLockMode::Write),
        flag_lock_perm.view().state() is WriteLock,
        flag_lock_perm.view().thread_id() == old(lctx).thread_id(),
        flag_lock_perm.view().lock_id() == old(krnl).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).sched_mp.perms_wf(),
        old(krnl).sched_mp.spec_index(scheduler_ptr).inv(),
        old(krnl).sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.length <= NUM_PAGES,
        old(krnl).cpu_set_mp.perms_wf(),
        old(krnl).cpu_set_mp.spec_index(cpu_set_ptr).inv(),
        old(krnl).cpu_set_mp.spec_index(cpu_set_ptr).view().owned_cpus.view().contains(cpu_id),
        !old(krnl).cpu_set_mp.spec_index(cpu_set_ptr).view().owned_cpus.closed_view().contains(cpu_id),
        old(krnl).cpu_offline_mp.perms_wf(),
        old(krnl).cpu_offline_mp.spec_index(flags_ptr).inv(),
        old(krnl).cpu_arr.inv(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().is_init(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().wf(),
        current_thread is Some ==> {
            let thread_ptr = current_thread.unwrap();
            &&& old(krnl).thr_mp.perms_wf()
            &&& old(krnl).thr_mp.view().spec_index(thread_ptr).is_init()
            &&& old(krnl).thr_mp.view().spec_index(thread_ptr).addr() == thread_ptr
            &&& old(krnl).thr_mp.spec_index(thread_ptr).inv()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).is_init()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().inv()
        },
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) }),
        cpu_offline_check_entry_trace(
            final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, *pt_regs, true, cpu_offline_check_flushed_default_pcid(*old(krnl), cpu_id),
        ),
        final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep { old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*final(krnl)) }),
        cpu_offline_check_step_pre(final(steps).nonlock_view().last().old_u, cpu_id),
        cpu_offline_check_step(final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, cpu_id, *pt_regs, cpu_offline_check_flushed_default_pcid(*old(krnl), cpu_id)),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Off,
        forall|other_cpu: CpuId| #![trigger final(krnl).cpu_arr.spec_index(other_cpu)]
            index_valid(NUM_CPUS, other_cpu) && other_cpu != cpu_id ==> final(krnl).cpu_arr.spec_index(other_cpu).view().view().view() == old(krnl).cpu_arr.spec_index(other_cpu).view().view().view(),
{
    let tracked cpu_lock_perm = cpu_lock_perm.get();
    let tracked flag_lock_perm = flag_lock_perm.get();
    let tracked cpu_set_lock_perm = cpu_set_lock_perm.get();
    let tracked scheduler_lock_perm = scheduler_lock_perm.get();
    let Tracked(needflush_perm) = krnl.wlock_pcid_needflush(cpu_id, KERNEL_DEFAULT_PCID, Tracked(&mut *lctx));
    let ghost before = *krnl;
    let default_cr3 = krnl.dflt_pt.borrow().cr3;
    assert(page_ptr_valid(default_cr3)) by { krnl.default_pagetable_view_inv(); krnl.dflt_pt.view().table_pages_wf_cr3_at(); };
    let ghost old_cpu_lock_id = krnl.cpu_arr.lock_id_by_index(cpu_id);
    if let Some(prev) = current_thread {
        let ghost old_prev_lock_id = krnl.thr_mp.lock_id_by_key(prev);
        let prev_perm = thread_lock_perm.as_ref().unwrap();
        let previous = krnl.thr_mp.borrow_mut_typed(prev, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(prev_perm.borrow()));
        let (addr, perm) = previous.running_to_scheduled(prev, cpu_id, pt_regs);
        let shard = krnl.sched_mp.borrow_mut_shard_typed(scheduler_ptr, cpu_id, Ghost(lctx.scheduler_lock_map()), Tracked(&*lctx), Tracked(&scheduler_lock_perm));
        shard.queue.push_tail(addr, perm);
        krnl.cpu_arr.block_current(cpu_id, default_cr3, &mut krnl.cpu_tlb, &mut krnl.pcid_needflush, &mut krnl.cpu_published, Tracked(&needflush_perm), Tracked(&mut *lctx), Tracked(&cpu_lock_perm));
        proof { lctx.update_lock_id(KernelObjId::Cpu(cpu_id), old_cpu_lock_id, krnl.cpu_arr.lock_id_by_index(cpu_id)); lctx.update_lock_id(KernelObjId::Thread(prev), old_prev_lock_id, krnl.thr_mp.lock_id_by_key(prev)); }
    } else {
        proof {
            lctx.enter_kernel_view_release();
            assert({
                &&& krnl.cpu_published[cpu_id as int].inv()
                &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == default_cr3
                &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == KERNEL_DEFAULT_PCID
            }) by { cpu_published_wf_at(krnl.cpu_published, krnl.cpu_arr, krnl.pcid_needflush, cpu_id); cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_id); };
        }
    }
    let ghost idle_cpu_lock_id = krnl.cpu_arr.lock_id_by_index(cpu_id);
    let cpu = krnl.cpu_arr.borrow_mut_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    cpu.publish_off_from_idle();
    krnl.cpu_tlb.flush_all_local_pcids(cpu_id, Tracked(&*lctx));
    let cpu_set = krnl.cpu_set_mp.borrow_mut_typed(cpu_set_ptr, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&cpu_set_lock_perm));
    cpu_set.owned_cpus.mark_closed(cpu_id);
    krnl.cpu_offline_mp.set_flag(flags_ptr, cpu_id, false, Tracked(&*lctx), Tracked(&flag_lock_perm));
    proof {
        lctx.update_lock_id(KernelObjId::Cpu(cpu_id), idle_cpu_lock_id, krnl.cpu_arr.lock_id_by_index(cpu_id));
        assert(cpu_went_off_eof_transition_framing(before, *krnl, cpu_id, container_ptr, scheduler_ptr, cpu_set_ptr, flags_ptr, *pt_regs)) by {
            reveal(cpu_went_off_eof_transition_framing); scheduler_perms_wf_at(before.sched_mp, scheduler_ptr); cpu_set_perms_wf_at(before.cpu_set_mp, cpu_set_ptr); pcid_needflush_wf_at(krnl.pcid_needflush, cpu_id, KERNEL_DEFAULT_PCID);
            assert(krnl.cpu_tlb.view() == cpu_tlb_after_cpu_went_off(before.cpu_tlb.view(), cpu_id, cpu_offline_check_flushed_default_pcid(before, cpu_id))) by {
                vstd::assert_maps_equal!(krnl.cpu_tlb.view(), cpu_tlb_after_cpu_went_off(before.cpu_tlb.view(), cpu_id, cpu_offline_check_flushed_default_pcid(before, cpu_id)), key => {});
            };
        };
        assert(typed_lock_maps_aligned(&*krnl, &*lctx)) by { reveal(UnLockedMap::typed_flag_lock_map_aligned); };
        if current_thread is Some { process_thread_wf_at(before.prc_mp, before.thr_mp, current_thread.unwrap()); }
    }
    cpu_offline_commit_unlock_and_record(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, pt_regs, container_ptr, scheduler_ptr, cpu_set_ptr, flags_ptr,
        current_process, current_thread, process_lock_perm, thread_lock_perm, Tracked(cpu_lock_perm), Tracked(flag_lock_perm), Tracked(cpu_set_lock_perm),
        Tracked(scheduler_lock_perm), Tracked(needflush_perm), Ghost(*old(krnl)), Ghost(before));
}

} // verus!
