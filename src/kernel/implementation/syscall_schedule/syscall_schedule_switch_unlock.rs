use vstd::prelude::*;
use crate::*;

verus! {
/// With the `(cpu_id, pcid)` needflush cell, `next_thread`, shard `cpu_id` of `scheduler_ptr`, the live `current_thread` and
/// `current_process`, if any, and `cpu_id` write-held after the context switch: releases them all in that order.
pub(super) fn schedule_switch_release_locks(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr, next_thread: RwLockThreadPtr,
    current_process: Option<RwLockProcessPtr>, current_thread: Option<RwLockThreadPtr>, pcid: Pcid, process_lock_perm: Option<Tracked<LockPerm>>,
    current_thread_lock_perm: Option<Tracked<LockPerm>>, Tracked(scheduler_lock_perm): Tracked<LockPerm>, Tracked(next_lock_perm): Tracked<LockPerm>,
    Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(needflush_perm): Tracked<LockPerm>,
)
    requires
        old(krnl).inv(),
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(krnl).sched_mp.dom().contains(scheduler_ptr),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, pcid),
        old(krnl).thr_mp.dom().contains(next_thread),
        !old(krnl).thr_mp.spec_index(next_thread).being_killed(),
        old(krnl).thr_mp.spec_index(next_thread).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(next_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(next_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(next_thread).view().syscall_progress.view() is None,
        current_process is Some == process_lock_perm is Some,
        current_thread is Some == current_thread_lock_perm is Some,
        current_thread is Some ==> current_thread.unwrap() != next_thread,
        current_process is Some ==> {
            let process_ptr = current_process.unwrap();
            &&& old(krnl).prc_mp.dom().contains(process_ptr)
            &&& !old(krnl).prc_mp.spec_index(process_ptr).being_killed()
            &&& old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running || old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Zombie
        },
        current_thread is Some ==> {
            let thread_ptr = current_thread.unwrap();
            &&& old(krnl).thr_mp.dom().contains(thread_ptr)
            &&& !old(krnl).thr_mp.spec_index(thread_ptr).being_killed()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::SCHEDULED { cpu_id })
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None
        },
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
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, pcid_needflush: final(krnl).pcid_needflush, sched_mp: final(krnl).sched_mp, thr_mp: final(krnl).thr_mp, prc_mp: final(krnl).prc_mp, ..*old(krnl) }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        final(krnl).cpu_arr.unchanged_except(&old(krnl).cpu_arr, cpu_id),
        wunlock_ensures(old(krnl).cpu_arr.spec_index(cpu_id).view(), final(krnl).cpu_arr.spec_index(cpu_id).view()),
        final(krnl).prc_mp.dom() == old(krnl).prc_mp.dom(),
        forall|p: RwLockProcessPtr| #![trigger final(krnl).prc_mp.spec_index(p)]
            old(krnl).prc_mp.dom().contains(p) ==> if current_process == Some(p) {
                wunlock_ensures(old(krnl).prc_mp.spec_index(p), final(krnl).prc_mp.spec_index(p))
            } else { final(krnl).prc_mp.spec_index(p) == old(krnl).prc_mp.spec_index(p) },
        final(krnl).thr_mp.dom() == old(krnl).thr_mp.dom(),
        forall|t: RwLockThreadPtr| #![trigger final(krnl).thr_mp.spec_index(t)]
            old(krnl).thr_mp.dom().contains(t) ==> if current_thread == Some(t) || t == next_thread {
                wunlock_ensures(old(krnl).thr_mp.spec_index(t), final(krnl).thr_mp.spec_index(t))
            } else { final(krnl).thr_mp.spec_index(t) == old(krnl).thr_mp.spec_index(t) },
        final(krnl).sched_mp.dom() == old(krnl).sched_mp.dom(),
        forall|s: RwLockSchedulerPtr| #![trigger scheduler_shards_of(final(krnl).sched_mp.spec_index(s))]
            old(krnl).sched_mp.dom().contains(s) ==> scheduler_shards_of(final(krnl).sched_mp.spec_index(s)) == scheduler_shards_of(old(krnl).sched_mp.spec_index(s)),
{
    krnl.wunlock_pcid_needflush(cpu_id, pcid, Tracked(&mut *lctx), Tracked(needflush_perm));
    krnl.wunlock_thread(next_thread, Tracked(&mut *lctx), Tracked(next_lock_perm));
    krnl.wunlock_scheduler_shard(scheduler_ptr, cpu_id, Tracked(&mut *lctx), Tracked(scheduler_lock_perm));
    if let Some(perm) = current_thread_lock_perm { krnl.wunlock_thread(current_thread.unwrap(), Tracked(&mut *lctx), perm); }
    if let Some(perm) = process_lock_perm { krnl.wunlock_process(current_process.unwrap(), Tracked(&mut *lctx), perm); }
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
}
} // verus!
