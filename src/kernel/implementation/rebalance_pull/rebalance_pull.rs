use vstd::prelude::*;
use crate::*;
use super::rebalance_pull_spec::*;
use super::rebalance_pull_trace::*;
use super::rebalance_pull_release::rebalance_pull_release_unpulled;
#[cfg(verus_keep_ghost)]
use super::rebalance_pull_eof::rebalance_pull_eof;
#[cfg(verus_keep_ghost)]
use super::super::syscall_schedule::syscall_schedule::schedule_current_cpu_references_wf;
#[cfg(verus_keep_ghost)]
use crate::kernel::implementation::locker_unlocker::u_sys_exit_eof;

verus! {
pub enum RebalanceResult {
    Nothing,
    Pulled { thread_ptr: RwLockThreadPtr },
}

/// Write-locks shards `0, 1, ...` of `scheduler_ptr` in cpu-id order until one is nonempty; returns how many
/// shards are locked and whether the last locked one is nonempty.
fn rebalance_lock_shards_until_nonempty(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr) -> (ret: (usize, bool, Tracked<Map<CpuId, LockPerm>>))
    requires
        old(krnl).inv(),
        old(krnl).sched_mp.dom().contains(scheduler_ptr),
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        !(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Off),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        *final(krnl) == (KernelK { sched_mp: final(krnl).sched_mp, ..*old(krnl) }),
        final(krnl).sched_mp.unchanged_except(&old(krnl).sched_mp, scheduler_ptr),
        final(krnl).sched_mp.spec_index(scheduler_ptr).owning_container == old(krnl).sched_mp.spec_index(scheduler_ptr).owning_container,
        scheduler_shards_of(final(krnl).sched_mp.spec_index(scheduler_ptr)) == scheduler_shards_of(old(krnl).sched_mp.spec_index(scheduler_ptr)),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_quota_4k_lock_map() == old(lctx).allocator_quota_4k_lock_map(),
        final(lctx).allocator_cache_4k_lock_map() == old(lctx).allocator_cache_4k_lock_map(),
        final(lctx).allocator_global_pool_4k_lock_map() == old(lctx).allocator_global_pool_4k_lock_map(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        0 < ret.0 <= NUM_CPUS,
        forall|k: (RwLockSchedulerPtr, CpuId)| #![trigger final(lctx).scheduler_lock_map().dom().contains(k)] final(lctx).scheduler_lock_map().dom().contains(k) <==> (k.0 == scheduler_ptr && k.1 < ret.0),
        forall|i: CpuId| #![trigger ret.2.view().spec_index(i)] #![trigger ret.2.view().dom().contains(i)] i < ret.0 ==> {
            &&& ret.2.view().dom().contains(i)
            &&& ret.2.view().spec_index(i).state() is WriteLock
            &&& ret.2.view().spec_index(i).thread_id() == final(lctx).thread_id()
            &&& ret.2.view().spec_index(i).lock_id() == final(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(i).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(final(lctx).scheduler_lock_map(), (scheduler_ptr, i), TypedLockMode::Write)
        },
        {
            let queues = scheduler_shards_of(old(krnl).sched_mp.spec_index(scheduler_ptr));
            &&& (ret.1 ==> queues[ret.0 - 1].len() > 0 && first_nonempty_shard(queues, 0, cpu_id) == first_nonempty_shard(queues, ret.0 - 1, cpu_id))
            &&& (ret.1 && cpu_id < ret.0 - 1 ==> queues[cpu_id as int].len() == 0)
            &&& (!ret.1 ==> ret.0 == NUM_CPUS && first_nonempty_shard(queues, 0, cpu_id) is None && queues[cpu_id as int].len() == 0)
        },
{
    let tracked mut shard_perms: Map<CpuId, LockPerm> = Map::tracked_empty();
    let ghost queues = scheduler_shards_of(old(krnl).sched_mp.spec_index(scheduler_ptr));
    let mut next: usize = 0;
    let mut found = false;
    proof { assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); }; }
    while !found && next < NUM_CPUS
        invariant
            krnl.inv(),
            typed_lock_maps_aligned(krnl, &*lctx),
            krnl.sched_mp.dom().contains(scheduler_ptr),
            index_valid(NUM_CPUS, cpu_id),
            next <= NUM_CPUS,
            found ==> next > 0,
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.kernel_view_locking_state() is Acquire,
            *krnl == (KernelK { sched_mp: krnl.sched_mp, ..*old(krnl) }),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl),
            krnl.sched_mp.unchanged_except(&old(krnl).sched_mp, scheduler_ptr),
            krnl.sched_mp.spec_index(scheduler_ptr).owning_container == old(krnl).sched_mp.spec_index(scheduler_ptr).owning_container,
            scheduler_shards_of(krnl.sched_mp.spec_index(scheduler_ptr)) == queues,
            !(krnl.cpu_arr.spec_index(cpu_id).view().view().view().state is Off),
            lctx.page_lock_map() == old(lctx).page_lock_map(),
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
            lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            lctx.cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.process_lock_map() == old(lctx).process_lock_map(),
            lctx.thread_lock_map() == old(lctx).thread_lock_map(),
            lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            lctx.pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
            lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            lctx.iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
            lctx.allocator_quota_4k_lock_map() == old(lctx).allocator_quota_4k_lock_map(),
            lctx.allocator_cache_4k_lock_map() == old(lctx).allocator_cache_4k_lock_map(),
            lctx.allocator_global_pool_4k_lock_map() == old(lctx).allocator_global_pool_4k_lock_map(),
            lctx.allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            lctx.allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).thread_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            forall|k: (RwLockSchedulerPtr, CpuId)| #![trigger lctx.scheduler_lock_map().dom().contains(k)] lctx.scheduler_lock_map().dom().contains(k) <==> (k.0 == scheduler_ptr && k.1 < next),
            forall|i: CpuId| #![trigger shard_perms.spec_index(i)] #![trigger shard_perms.dom().contains(i)] i < next ==> {
                &&& shard_perms.dom().contains(i)
                &&& shard_perms.spec_index(i).state() is WriteLock
                &&& shard_perms.spec_index(i).thread_id() == lctx.thread_id()
                &&& shard_perms.spec_index(i).lock_id() == krnl.sched_mp.spec_index(scheduler_ptr).shards.spec_index(i).view().locking_thread()->Write_lock_id
                &&& typed_lock_map_contains_mode(lctx.scheduler_lock_map(), (scheduler_ptr, i), TypedLockMode::Write)
            },
            !found ==> first_nonempty_shard(queues, 0, cpu_id) == first_nonempty_shard(queues, next as int, cpu_id),
            !found && cpu_id < next ==> queues[cpu_id as int].len() == 0,
            found ==> queues[next - 1].len() > 0 && first_nonempty_shard(queues, 0, cpu_id) == first_nonempty_shard(queues, next - 1, cpu_id),
            found && cpu_id < next - 1 ==> queues[cpu_id as int].len() == 0,
        decreases NUM_CPUS - next,
    {
        let Tracked(perm) = krnl.wlock_scheduler_shard(scheduler_ptr, next, Tracked(&mut *lctx));
        proof {
            scheduler_perms_wf_map(krnl.sched_mp); scheduler_perms_wf_at(krnl.sched_mp, scheduler_ptr); kernel_scheduler_shards_projection_at(krnl.sched_mp.spec_index(scheduler_ptr), next); krnl.sched_mp.spec_index(scheduler_ptr).shard(next).queue.lemma_len_view();
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        }
        let shard = krnl.sched_mp.borrow_shard_typed(scheduler_ptr, next, Ghost(lctx.scheduler_lock_map()), Tracked(&*lctx), Tracked(&perm));
        found = shard.queue.len() != 0;
        proof { shard_perms.tracked_insert(next, perm); }
        next = next + 1;
    }
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
    }
    (next, found, Tracked(shard_perms))
}

/// Releases shards `0..count` of `scheduler_ptr`, the only scheduler shards held.
pub(super) fn rebalance_unlock_shard_prefix(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, scheduler_ptr: RwLockSchedulerPtr, count: usize, Tracked(shard_perms): Tracked<Map<CpuId, LockPerm>>)
    requires
        old(krnl).inv(),
        old(krnl).sched_mp.dom().contains(scheduler_ptr),
        0 < count <= NUM_CPUS,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        forall|k: (RwLockSchedulerPtr, CpuId)| #![trigger old(lctx).scheduler_lock_map().dom().contains(k)] old(lctx).scheduler_lock_map().dom().contains(k) <==> (k.0 == scheduler_ptr && k.1 < count),
        forall|i: CpuId| #![trigger shard_perms.spec_index(i)] #![trigger shard_perms.dom().contains(i)] i < count ==> {
            &&& shard_perms.dom().contains(i)
            &&& shard_perms.spec_index(i).state() is WriteLock
            &&& shard_perms.spec_index(i).thread_id() == old(lctx).thread_id()
            &&& shard_perms.spec_index(i).lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(i).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (scheduler_ptr, i), TypedLockMode::Write)
        },
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        *final(krnl) == (KernelK { sched_mp: final(krnl).sched_mp, ..*old(krnl) }),
        final(krnl).sched_mp.unchanged_except(&old(krnl).sched_mp, scheduler_ptr),
        final(krnl).sched_mp.spec_index(scheduler_ptr).owning_container == old(krnl).sched_mp.spec_index(scheduler_ptr).owning_container,
        scheduler_shards_of(final(krnl).sched_mp.spec_index(scheduler_ptr)) == scheduler_shards_of(old(krnl).sched_mp.spec_index(scheduler_ptr)),
        final(lctx).scheduler_lock_map().dom().is_empty(),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_quota_4k_lock_map() == old(lctx).allocator_quota_4k_lock_map(),
        final(lctx).allocator_cache_4k_lock_map() == old(lctx).allocator_cache_4k_lock_map(),
        final(lctx).allocator_global_pool_4k_lock_map() == old(lctx).allocator_global_pool_4k_lock_map(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
{
    let tracked mut perms = shard_perms;
    let mut next: usize = 0;
    proof { assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); }; }
    while next < count
        invariant
            krnl.inv(),
            typed_lock_maps_aligned(krnl, &*lctx),
            krnl.sched_mp.dom().contains(scheduler_ptr),
            next <= count <= NUM_CPUS,
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            next > 0 ==> lctx.kernel_view_locking_state() is Release,
            *krnl == (KernelK { sched_mp: krnl.sched_mp, ..*old(krnl) }),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl),
            krnl.sched_mp.unchanged_except(&old(krnl).sched_mp, scheduler_ptr),
            krnl.sched_mp.spec_index(scheduler_ptr).owning_container == old(krnl).sched_mp.spec_index(scheduler_ptr).owning_container,
            scheduler_shards_of(krnl.sched_mp.spec_index(scheduler_ptr)) == scheduler_shards_of(old(krnl).sched_mp.spec_index(scheduler_ptr)),
            lctx.page_lock_map() == old(lctx).page_lock_map(),
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
            lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            lctx.cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.process_lock_map() == old(lctx).process_lock_map(),
            lctx.thread_lock_map() == old(lctx).thread_lock_map(),
            lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            lctx.pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
            lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            lctx.iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
            lctx.allocator_quota_4k_lock_map() == old(lctx).allocator_quota_4k_lock_map(),
            lctx.allocator_cache_4k_lock_map() == old(lctx).allocator_cache_4k_lock_map(),
            lctx.allocator_global_pool_4k_lock_map() == old(lctx).allocator_global_pool_4k_lock_map(),
            lctx.allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            lctx.allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            forall|k: (RwLockSchedulerPtr, CpuId)| #![trigger lctx.scheduler_lock_map().dom().contains(k)] lctx.scheduler_lock_map().dom().contains(k) <==> (k.0 == scheduler_ptr && next <= k.1 && k.1 < count),
            forall|i: CpuId| #![trigger perms.spec_index(i)] #![trigger perms.dom().contains(i)] next <= i < count ==> {
                &&& perms.dom().contains(i)
                &&& perms.spec_index(i).state() is WriteLock
                &&& perms.spec_index(i).thread_id() == lctx.thread_id()
                &&& perms.spec_index(i).lock_id() == krnl.sched_mp.spec_index(scheduler_ptr).shards.spec_index(i).view().locking_thread()->Write_lock_id
                &&& typed_lock_map_contains_mode(lctx.scheduler_lock_map(), (scheduler_ptr, i), TypedLockMode::Write)
            },
        decreases count - next,
    {
        let tracked perm = perms.tracked_remove(next);
        krnl.wunlock_scheduler_shard(scheduler_ptr, next, Tracked(&mut *lctx), Tracked(perm));
        proof { assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; }; }
        next = next + 1;
    }
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
    }
}

/// Moves the head `thread_ptr` of shard `victim` to the empty shard `cpu_id`, releases every lock, and records
/// the pull step.
fn rebalance_pull_move_head(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    scheduler_ptr: RwLockSchedulerPtr, victim: CpuId, thread_ptr: RwLockThreadPtr, count: usize, shard_perms: Tracked<Map<CpuId, LockPerm>>,
    local_lock_perm: Option<Tracked<LockPerm>>, thread_lock_perm: Tracked<LockPerm>, cpu_lock_perm: Tracked<LockPerm>,
)
    requires
        old(krnl).inv(),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, thr_mp: old(krnl).thr_mp, sched_mp: old(krnl).sched_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view(),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.killer_info(),
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] == cpu_op_after_step(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state),
        old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view() == old(steps).snapshot_k().thr_mp.spec_index(thread_ptr).view(),
        old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(steps).snapshot_k().thr_mp.spec_index(thread_ptr).being_killed(),
        old(steps).snapshot_k().thr_mp.spec_index(thread_ptr).locking_thread() is None,
        old(krnl).sched_mp.unchanged_except(&old(steps).snapshot_k().sched_mp, scheduler_ptr),
        scheduler_shards_of(old(krnl).sched_mp.spec_index(scheduler_ptr)) == scheduler_shards_of(old(steps).snapshot_k().sched_mp.spec_index(scheduler_ptr)),
        old(steps).nonlock_view().len() == 0,
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, victim),
        victim != cpu_id,
        cpu_id == old(lctx).cpu_id(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
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
        forall|k: (RwLockSchedulerPtr, CpuId)| #![trigger old(lctx).scheduler_lock_map().dom().contains(k)] old(lctx).scheduler_lock_map().dom().contains(k) <==> (k.0 == scheduler_ptr && (k.1 < count || k.1 == cpu_id)),
        count <= NUM_CPUS,
        victim < count,
        local_lock_perm is None ==> cpu_id < count,
        local_lock_perm is Some ==> count <= cpu_id,
        forall|i: CpuId| #![trigger shard_perms.view().spec_index(i)] #![trigger shard_perms.view().dom().contains(i)] i < count ==> {
            &&& shard_perms.view().dom().contains(i)
            &&& shard_perms.view().spec_index(i).state() is WriteLock
            &&& shard_perms.view().spec_index(i).thread_id() == old(lctx).thread_id()
            &&& shard_perms.view().spec_index(i).lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(i).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (scheduler_ptr, i), TypedLockMode::Write)
        },
        local_lock_perm is Some ==> {
            let perm = local_lock_perm.unwrap().view();
            &&& perm.state() is WriteLock
            &&& perm.thread_id() == old(lctx).thread_id()
            &&& perm.lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (scheduler_ptr, cpu_id), TypedLockMode::Write)
        },
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_lock_perm.view().state() is WriteLock,
        thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        {
            let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            let queues = scheduler_shards_of(old(krnl).sched_mp.spec_index(scheduler_ptr));
            let thread = old(krnl).thr_mp.spec_index(thread_ptr);
            &&& cpu.state is Idle
            &&& old(krnl).ctn_mp.dom().contains(cpu.owning_container)
            &&& old(krnl).ctn_mp.spec_index(cpu.owning_container).view_rodata().view().scheduler == scheduler_ptr
            &&& old(krnl).sched_mp.dom().contains(scheduler_ptr)
            &&& queues[cpu_id as int].len() == 0
            &&& first_nonempty_shard(queues, 0, cpu_id) == Some(victim)
            &&& queues[victim as int].len() > 0
            &&& queues[victim as int][0] == thread_ptr
            &&& old(krnl).thr_mp.dom().contains(thread_ptr)
            &&& !thread.being_killed()
            &&& thread.view().state == (ThreadState::SCHEDULED { cpu_id: victim })
            &&& thread.view().owning_container == cpu.owning_container
            &&& thread.view().free_quota_pending_clean()
            &&& thread.view().temp_alloc_clean()
            &&& thread.view().syscall_progress.view() is None
            &&& !thread.view_ghost().exited
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
        rebalance_pull_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, true),
        final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep { old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*final(krnl)) }),
        rebalance_pull_step_pre(final(steps).nonlock_view().last().old_u, cpu_id),
        rebalance_pull_step(final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, cpu_id),
{
    let tracked shard_perms = shard_perms.get();
    let tracked thread_lock_perm = thread_lock_perm.get();
    let tracked cpu_lock_perm = cpu_lock_perm.get();
    let ghost before_move = *krnl;
    proof {
        kernel_scheduler_shards_projection_at(krnl.sched_mp.spec_index(scheduler_ptr), victim);
        kernel_scheduler_shards_projection_at(krnl.sched_mp.spec_index(scheduler_ptr), cpu_id);
        scheduler_perms_wf_at(krnl.sched_mp, scheduler_ptr);
        thread_perms_wf_map(krnl.thr_mp);
        thread_perms_wf_at(krnl.thr_mp, thread_ptr);
        assert(krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.length == 0) by { reveal(LinkedList::wf_value_list); };
        assert({
            let queue = krnl.sched_mp.spec_index(scheduler_ptr).shard(victim).queue;
            let node = krnl.thr_mp.spec_index(thread_ptr).view().scheduler_linkedlist_node.addr();
            &&& queue.map().dom().contains(node)
            &&& queue.map().spec_index(node) == thread_ptr
        }) by { container_thread_scheduler_wf_thread_at(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp, thread_ptr); };
    }
    let node_addr = if let Some(local_perm) = &local_lock_perm {
        scheduler_map_move_shard_head(&mut krnl.sched_mp, scheduler_ptr, victim, cpu_id, Tracked(&*lctx), Tracked(shard_perms.tracked_borrow(victim)), Tracked(local_perm.borrow()))
    } else {
        scheduler_map_move_shard_head(&mut krnl.sched_mp, scheduler_ptr, victim, cpu_id, Tracked(&*lctx), Tracked(shard_perms.tracked_borrow(victim)), Tracked(shard_perms.tracked_borrow(cpu_id)))
    };
    proof {
        let queue = before_move.sched_mp.spec_index(scheduler_ptr).shard(victim).queue;
        queue.lemma_value_addr_unique(node_addr, before_move.thr_mp.spec_index(thread_ptr).view().scheduler_linkedlist_node.addr());
    }
    let ghost old_thread_lock_id = krnl.thr_mp.lock_id_by_key(thread_ptr);
    let thread = krnl.thr_mp.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_lock_perm));
    thread.move_scheduled(cpu_id);
    proof {
        lctx.enter_kernel_view_release();
        lctx.update_lock_id(KernelObjId::Thread(thread_ptr), old_thread_lock_id, krnl.thr_mp.lock_id_by_key(thread_ptr));
        assert(rebalance_pull_eof_transition_framing(before_move, *krnl, cpu_id, scheduler_ptr, victim, thread_ptr)) by { reveal(rebalance_pull_eof_transition_framing); };
        rebalance_pull_eof(before_move, *krnl, cpu_id, scheduler_ptr, victim, thread_ptr);
    }
    let ghost after_move = *krnl;
    krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
    if let Some(local_perm) = local_lock_perm { krnl.wunlock_scheduler_shard(scheduler_ptr, cpu_id, Tracked(&mut *lctx), local_perm); }
    rebalance_unlock_shard_prefix(krnl, Tracked(&mut *lctx), scheduler_ptr, count, Tracked(shard_perms));
    proof {
        let ghost pre = *krnl;
        let ghost pre_lctx = *lctx;
        assert(krnl.cpu_arr.spec_index(cpu_id).view().view_ghost() == Some(cpu_id)) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
        krnl.u_sys_exit(lctx);
        u_sys_exit_eof(pre, *krnl, pre_lctx, *lctx);
    }
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        let ghost pull_before = steps.view();
        assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
        assert(kernel_rebalance_pull_fields(&steps.snapshot_k(), &*krnl, cpu_id, victim, thread_ptr)) by { reveal(kernel_rebalance_pull_fields); reveal(rebalance_pull_eof_transition_framing); };
        steps.end_kernel_step_rebalance_pull(&*krnl, &*lctx, cpu_id, victim, thread_ptr);
        no_locks_held_imply_all_objects_unlocked(krnl, lctx);
        assert(rebalance_pull_syscall_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
            kernel_k_to_kernel_u(*krnl), cpu_id, true) && rebalance_pull_step_pre(steps.nonlock_view().last().old_u, cpu_id) && rebalance_pull_step(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id)) by {
            rebalance_pull_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, victim, thread_ptr);
            rebalance_pull_step_from_u(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, victim, thread_ptr);
            rebalance_pull_trace_pull_step(&*steps, pull_before, kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id);
        };
    }
}

/// Idle-cpu entry: pulls the head of the lowest-numbered other nonempty shard of the cpu's container scheduler
/// into the cpu's own empty shard. The trap layer schedules again after `Pulled` and halts after `Nothing`.
#[verifier::spinoff_prover]
pub fn rebalance_pull(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId) -> (ret: RebalanceResult)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is Idle,
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
        rebalance_pull_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, ret is Pulled),
        final(steps).nonlock_view().len() == if ret is Pulled { 1nat } else { 0nat },
        ret == rebalance_pull_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id),
        !(ret is Pulled) ==> kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(*old(krnl)),
        ret is Pulled ==> final(steps).nonlock_view()[0].old_u == kernel_k_to_nonlock_kernel_u(*old(krnl)) && final(steps).nonlock_view()[0].new_u == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        ret is Pulled ==> rebalance_pull_step_pre(final(steps).nonlock_view()[0].old_u, cpu_id) && rebalance_pull_step(final(steps).nonlock_view()[0].old_u, final(steps).nonlock_view()[0].new_u, cpu_id),
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }

    let cpu_lock_res = krnl.wlock_cpu(cpu_id, Tracked(&mut *lctx));
    if cpu_lock_res.is_none() {
        proof {
            no_locks_held_imply_all_objects_unlocked(&*krnl, &*lctx); enter_kernel_view_release_preserving_lock_alignments(&*krnl, lctx);
            rebalance_pull_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id);
            assert(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running) by { thread_cpu_wf_killed_cpu_at(old(krnl).thr_mp, old(krnl).cpu_arr, cpu_id); };
            rebalance_pull_result_from_k(old(krnl), cpu_id, RebalanceResult::Nothing);
        }
        return RebalanceResult::Nothing;
    }
    let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
    proof { assert(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Idle) by { cpu_op_wf_at(old(krnl).cpu_op.view().view(), old(krnl).cpu_arr, cpu_id); }; }
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let idle = match cpu.state() { CpuState::Idle => true, _ => false };
    let container_ptr = cpu.owning_container();
    if !idle {
        proof {
            let ghost pre = *krnl;
            let ghost pre_lctx = *lctx;
            krnl.u_sys_exit(lctx);
            u_sys_exit_eof(pre, *krnl, pre_lctx, *lctx);
        }
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, None, None, None, None);
            rebalance_pull_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id);
            rebalance_pull_result_from_k(old(krnl), cpu_id, RebalanceResult::Nothing);
        }
        return RebalanceResult::Nothing;
    }
    proof { schedule_current_cpu_references_wf(&*krnl, cpu_id); }
    let scheduler_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().scheduler;
    proof { container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, container_ptr); }
    let ghost queues = scheduler_shards_of(old(krnl).sched_mp.spec_index(scheduler_ptr));
    let (count, found, Tracked(shard_perms)) = rebalance_lock_shards_until_nonempty(krnl, Tracked(&mut *lctx), cpu_id, scheduler_ptr);
    if !found || count - 1 == cpu_id {
        proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
        proof { assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; }; }
        rebalance_pull_release_unpulled(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, scheduler_ptr, count, Tracked(shard_perms), None, Tracked(cpu_lock_perm));
        proof { rebalance_pull_result_from_k(old(krnl), cpu_id, RebalanceResult::Nothing); }
        return RebalanceResult::Nothing;
    }
    let victim = count - 1;
    let mut local_lock_perm: Option<Tracked<LockPerm>> = None;
    if victim < cpu_id {
        let Tracked(local_perm) = krnl.wlock_scheduler_shard(scheduler_ptr, cpu_id, Tracked(&mut *lctx));
        proof { scheduler_perms_wf_map(krnl.sched_mp); scheduler_perms_wf_at(krnl.sched_mp, scheduler_ptr); kernel_scheduler_shards_projection_at(krnl.sched_mp.spec_index(scheduler_ptr), cpu_id); krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.lemma_len_view(); }
        let local_len = krnl.sched_mp.borrow_shard_typed(scheduler_ptr, cpu_id, Ghost(lctx.scheduler_lock_map()), Tracked(&*lctx), Tracked(&local_perm)).queue.len();
        if local_len != 0 {
            proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
            proof { assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; }; }
            rebalance_pull_release_unpulled(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, scheduler_ptr, count, Tracked(shard_perms), Some(Tracked(local_perm)), Tracked(cpu_lock_perm));
            proof { rebalance_pull_result_from_k(old(krnl), cpu_id, RebalanceResult::Nothing); }
            return RebalanceResult::Nothing;
        }
        local_lock_perm = Some(Tracked(local_perm));
    }
    proof { scheduler_perms_wf_map(krnl.sched_mp); scheduler_perms_wf_at(krnl.sched_mp, scheduler_ptr); kernel_scheduler_shards_projection_at(krnl.sched_mp.spec_index(scheduler_ptr), victim); krnl.sched_mp.spec_index(scheduler_ptr).shard(victim).queue.lemma_len_view(); }
    let (_, thread_ptr) = krnl.sched_mp.borrow_shard_typed(scheduler_ptr, victim, Ghost(lctx.scheduler_lock_map()), Tracked(&*lctx), Tracked(shard_perms.tracked_borrow(victim))).queue.peek_head();
    proof { container_thread_scheduler_wf_at(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp, scheduler_ptr, victim, thread_ptr); }
    let res = krnl.wlock_scheduled_thread_unless_killed(thread_ptr, Tracked(&mut *lctx));
    if res.is_none() {
        proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
        proof { assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; }; }
        rebalance_pull_release_unpulled(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, scheduler_ptr, count, Tracked(shard_perms), local_lock_perm, Tracked(cpu_lock_perm));
        proof { rebalance_pull_result_from_k(old(krnl), cpu_id, RebalanceResult::Nothing); }
        return RebalanceResult::Nothing;
    }
    rebalance_pull_move_head(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, scheduler_ptr, victim, thread_ptr, count, Tracked(shard_perms), local_lock_perm, res.unwrap(), Tracked(cpu_lock_perm));
    proof { rebalance_pull_result_from_k(old(krnl), cpu_id, RebalanceResult::Pulled { thread_ptr }); }
    RebalanceResult::Pulled { thread_ptr }
}
}
