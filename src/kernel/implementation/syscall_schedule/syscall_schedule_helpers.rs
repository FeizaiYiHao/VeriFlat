use vstd::prelude::*;
use crate::*;
use super::syscall_schedule_spec::*;
use super::syscall_schedule_trace::*;
use super::syscall_schedule_switch_unlock::schedule_switch_release_locks;
#[cfg(verus_keep_ghost)]
use super::syscall_schedule_eof::scheduler_context_switch_eof;

verus! {
/// Finish of the switch to the shard head `next_thread` on `cpu_id` once the cpu, shard, and threads are committed from
/// `switch_k`, which is `entry_k` with the `(cpu_id, pcid)` needflush cell write-locked: close the kernel invariant,
/// release every lock, and record the context-switch step that starts at the snapshot of `steps`.
pub(super) fn schedule_switch_unlock_and_record(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr,
    next_thread: RwLockThreadPtr, current_process: Option<RwLockProcessPtr>, current_thread: Option<RwLockThreadPtr>, pcid: Pcid,
    process_lock_perm: Option<Tracked<LockPerm>>, current_thread_lock_perm: Option<Tracked<LockPerm>>, Tracked(scheduler_lock_perm): Tracked<LockPerm>,
    Tracked(next_lock_perm): Tracked<LockPerm>, Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(needflush_perm): Tracked<LockPerm>,
    Ghost(entry_k): Ghost<KernelK>, Ghost(switch_k): Ghost<KernelK>, Ghost(entry_regs): Ghost<Registers>,
)
    requires
        entry_k == (KernelK { cpu_arr: entry_k.cpu_arr, prc_mp: entry_k.prc_mp, thr_mp: entry_k.thr_mp, sched_mp: entry_k.sched_mp, ..old(steps).snapshot_k() }),
        entry_k.cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        entry_k.sched_mp.unchanged_except(&old(steps).snapshot_k().sched_mp, scheduler_ptr),
        scheduler_shards_of(entry_k.sched_mp.spec_index(scheduler_ptr)) == scheduler_shards_of(old(steps).snapshot_k().sched_mp.spec_index(scheduler_ptr)),
        forall|p: RwLockProcessPtr| #![trigger entry_k.prc_mp.spec_index(p)]
            old(steps).snapshot_k().prc_mp.dom().contains(p) ==> if current_process == Some(p) {
                old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() is None
            } else { entry_k.prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() },
        forall|t: RwLockThreadPtr| #![trigger entry_k.thr_mp.spec_index(t)]
            old(steps).snapshot_k().thr_mp.dom().contains(t) ==> if current_thread == Some(t) || t == next_thread {
                old(steps).snapshot_k().thr_mp.spec_index(t).locking_thread() is None
            } else { entry_k.thr_mp.spec_index(t).locking_thread() == old(steps).snapshot_k().thr_mp.spec_index(t).locking_thread() },
        old(steps).nonlock_view().len() == 0,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), &entry_k),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, entry_k.ep_mp),
        entry_k.irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
        entry_k.irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
        entry_k.cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        entry_k.iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), &entry_k),
        switch_k.inv(),
        switch_k == (KernelK { pcid_needflush: switch_k.pcid_needflush, ..entry_k }),
        switch_k.pcid_needflush.spec_index(cpu_id, pcid).view() == entry_k.pcid_needflush.spec_index(cpu_id, pcid).view(),
        pcid == entry_k.prc_mp.spec_index(entry_k.thr_mp.spec_index(next_thread).view().owning_proc).view_rodata().view().pcid,
        pcid_valid(pcid),
        index_valid(NUM_CPUS, cpu_id),
        !entry_k.cpu_arr.spec_index(cpu_id).view().being_killed(),
        {
            let cpu = entry_k.cpu_arr.spec_index(cpu_id).view().view().view();
            &&& !(cpu.state is Off)
            &&& cpu.current_process == current_process
            &&& cpu.current_thread == current_thread
            &&& entry_k.ctn_mp.dom().contains(cpu.owning_container)
            &&& entry_k.ctn_mp.spec_index(cpu.owning_container).view_rodata().view().scheduler == scheduler_ptr
            &&& entry_k.sched_mp.spec_index(scheduler_ptr).owning_container == cpu.owning_container
            &&& entry_k.thr_mp.spec_index(next_thread).view().owning_container == cpu.owning_container
        },
        current_process is Some == current_thread is Some,
        current_process is Some == process_lock_perm is Some,
        current_thread is Some == current_thread_lock_perm is Some,
        current_thread is Some ==> current_thread.unwrap() != next_thread,
        entry_k.sched_mp.dom().contains(scheduler_ptr),
        current_process is Some ==> {
            let process_ptr = current_process.unwrap();
            &&& entry_k.prc_mp.dom().contains(process_ptr)
            &&& !entry_k.prc_mp.spec_index(process_ptr).being_killed()
            &&& entry_k.prc_mp.spec_index(process_ptr).view().state.view() is Running || entry_k.prc_mp.spec_index(process_ptr).view().state.view() is Zombie
        },
        current_thread is Some ==> {
            let thread_ptr = current_thread.unwrap();
            let queue_before = entry_k.sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().view().queue;
            &&& entry_k.thr_mp.dom().contains(thread_ptr)
            &&& !entry_k.thr_mp.spec_index(thread_ptr).being_killed()
            &&& entry_k.thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id })
            &&& entry_k.thr_mp.spec_index(thread_ptr).view().owning_proc == current_process.unwrap()
            &&& entry_k.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean()
            &&& entry_k.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean()
            &&& entry_k.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None
            &&& !queue_before.map().remove(entry_k.thr_mp.spec_index(next_thread).view().scheduler_linkedlist_node.addr()).dom().contains(entry_k.thr_mp.spec_index(thread_ptr).view().scheduler_linkedlist_node.addr())
        },
        entry_k.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view().len() > 0,
        entry_k.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view()[0] == next_thread,
        entry_k.thr_mp.dom().contains(next_thread),
        !entry_k.thr_mp.spec_index(next_thread).being_killed(),
        entry_k.thr_mp.spec_index(next_thread).view().state is SCHEDULED,
        entry_k.thr_mp.spec_index(next_thread).view().free_quota_pending_clean(),
        entry_k.thr_mp.spec_index(next_thread).view().temp_alloc_clean(),
        entry_k.thr_mp.spec_index(next_thread).view().syscall_progress.view() is None,
        entry_k.prc_mp.dom().contains(entry_k.thr_mp.spec_index(next_thread).view().owning_proc),
        scheduler_context_switch_eof_transition_framing(switch_k, *old(krnl), cpu_id, scheduler_ptr, next_thread, entry_regs),
        old(krnl).cpu_arr.inv(),
        old(krnl).cpu_tlb.inv(),
        old(krnl).cpu_published[cpu_id as int].inv(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().tlb_dirty_bitmap.inv(),
        old(krnl).sched_mp.perms_wf(),
        old(krnl).sched_mp.spec_index(scheduler_ptr).shards.inv(),
        old(krnl).sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.wf(),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, pcid_needflush: old(krnl).pcid_needflush, cpu_published: old(krnl).cpu_published, sched_mp: old(krnl).sched_mp, thr_mp: old(krnl).thr_mp, cpu_tlb: old(krnl).cpu_tlb, ..switch_k }),
        old(krnl).thr_mp.dom() == entry_k.thr_mp.dom(),
        old(krnl).sched_mp.dom().contains(scheduler_ptr),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, pcid),
        !old(krnl).thr_mp.spec_index(next_thread).being_killed(),
        old(krnl).thr_mp.spec_index(next_thread).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(next_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(next_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(next_thread).view().syscall_progress.view() is None,
        current_thread is Some ==> {
            let thread_ptr = current_thread.unwrap();
            &&& !old(krnl).thr_mp.spec_index(thread_ptr).being_killed()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::SCHEDULED { cpu_id })
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None
        },
        cpu_id == old(lctx).cpu_id(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).pcid_needflush_lock_map().dom() =~= set![(cpu_id, pcid)],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom() =~= match current_process {
            Some(ptr) => set![ptr],
            None => Set::empty(),
        },
        old(lctx).thread_lock_map().dom() =~= match current_thread {
            Some(ptr) => set![ptr, next_thread],
            None => set![next_thread],
        },
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom() =~= set![(scheduler_ptr, cpu_id)],
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
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
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).pcid_needflush_lock_map(), (cpu_id, pcid), TypedLockMode::Write),
        needflush_perm.state() is WriteLock,
        needflush_perm.thread_id() == old(lctx).thread_id(),
        needflush_perm.lock_id() == old(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread()->Write_lock_id,
        current_process is Some ==> {
            let process_ptr = current_process.unwrap();
            let perm = process_lock_perm.unwrap().view();
            &&& typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write)
            &&& perm.state() is WriteLock
            &&& perm.thread_id() == old(lctx).thread_id()
            &&& perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id
        },
        current_thread is Some ==> {
            let thread_ptr = current_thread.unwrap();
            let perm = current_thread_lock_perm.unwrap().view();
            &&& typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write)
            &&& perm.state() is WriteLock
            &&& perm.thread_id() == old(lctx).thread_id()
            &&& perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id
        },
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (scheduler_ptr, cpu_id), TypedLockMode::Write),
        scheduler_lock_perm.state() is WriteLock,
        scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), next_thread, TypedLockMode::Write),
        next_lock_perm.state() is WriteLock,
        next_lock_perm.thread_id() == old(lctx).thread_id(),
        next_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(next_thread).locking_thread()->Write_lock_id,
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
        schedule_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, entry_regs, true, schedule_flushed_pcid(entry_k, cpu_id, next_thread)),
        final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep { old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*final(krnl)) }),
        schedule_step_pre(final(steps).nonlock_view().last().old_u, cpu_id),
        schedule_step(final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, cpu_id, entry_regs, schedule_flushed_pcid(entry_k, cpu_id, next_thread)),
        forall|other_cpu: CpuId| #![trigger final(krnl).cpu_arr.spec_index(other_cpu)]
            index_valid(NUM_CPUS, other_cpu) && other_cpu != cpu_id ==> final(krnl).cpu_arr.spec_index(other_cpu).view().view().view() == entry_k.cpu_arr.spec_index(other_cpu).view().view().view(),
        {
            let next_process = entry_k.thr_mp.spec_index(next_thread).view().owning_proc;
            let shards = scheduler_shards_of(entry_k.sched_mp.spec_index(scheduler_ptr));
            let queue = shards[cpu_id as int];
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(next_process)
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(next_thread)
            &&& final(krnl).thr_mp.spec_index(next_thread).view().state == (ThreadState::RUNNING { cpu_id })
            &&& final(krnl).thr_mp.spec_index(next_thread).view().error_code is None
            &&& scheduler_shards_of(final(krnl).sched_mp.spec_index(scheduler_ptr)) == shards.update(cpu_id as int, match current_thread { Some(ptr) => queue.skip(1).push(ptr), None => queue.skip(1) })
            &&& (current_thread is Some ==> {
                let prev = current_thread.unwrap();
                &&& final(krnl).thr_mp.spec_index(prev).view().state == (ThreadState::SCHEDULED { cpu_id })
                &&& *final(krnl).thr_mp.spec_index(prev).view().trap_frame.get_some_0() == entry_regs
            })
        },
{
    proof {
        assert({
            &&& old(steps).snapshot_k().prc_mp.dom() == entry_k.prc_mp.dom()
            &&& (current_process is Some ==> !old(steps).snapshot_k().prc_mp.spec_index(current_process.unwrap()).being_killed())
        }) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged); };
        kernel_scheduler_shards_projection_at(entry_k.sched_mp.spec_index(scheduler_ptr), cpu_id);
        scheduler_context_switch_eof(switch_k, *krnl, cpu_id, scheduler_ptr, next_thread, entry_regs);
    }
    schedule_switch_release_locks(krnl, Tracked(&mut *lctx), cpu_id, scheduler_ptr, next_thread, current_process, current_thread, pcid, process_lock_perm,
        current_thread_lock_perm, Tracked(scheduler_lock_perm), Tracked(next_lock_perm), Tracked(cpu_lock_perm), Tracked(needflush_perm));
    proof {
        let ghost flushed_pcid = schedule_flushed_pcid(entry_k, cpu_id, next_thread);
        let ghost switch_before = steps.view();
        assert(kernel_context_switch_fields(&steps.snapshot_k(), &*krnl, cpu_id, next_thread, entry_regs, flushed_pcid)) by {
            reveal(kernel_context_switch_fields); reveal(scheduler_context_switch_eof_transition_framing);
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
            broadcast use kernel_process_nonlock_fields_unchanged_transitive;
        };
        steps.end_kernel_step_context_switch(&*krnl, &*lctx, cpu_id, next_thread, entry_regs, flushed_pcid);
        assert(schedule_syscall_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, entry_regs, true, flushed_pcid)
            && schedule_step_pre(steps.nonlock_view().last().old_u, cpu_id)
            && schedule_step(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, entry_regs, flushed_pcid)) by {
            schedule_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, next_thread, entry_regs, flushed_pcid);
            schedule_step_from_u(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, next_thread, entry_regs, flushed_pcid);
            schedule_trace_switch_step(&*steps, switch_before, kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, entry_regs, flushed_pcid);
        };
    }
}
} // verus!
