use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_sets_equal};
use crate::*;
use super::rebalance_pull::RebalanceResult;
#[cfg(verus_keep_ghost)]
use super::rebalance_pull_spec::*;
#[cfg(verus_keep_ghost)]
use super::rebalance_pull_orphan_trace::*;
#[cfg(verus_keep_ghost)]
use super::rebalance_pull_orphan_eof::rebalance_orphan_pull_eof;
#[cfg(verus_keep_ghost)]
use super::super::syscall_schedule::syscall_schedule::schedule_current_cpu_references_wf;

verus! {
/// The first shard index at or after `cursor`, then from 0, other than `cpu_id`, whose cpu does not serve the container
/// `ctn_ptr` of `cpu_id`, decided from that container's cpu set `cpu_set` as of the state `entry`.
fn rebalance_orphan_pull_find_victim(cpu_set: &CpuSet, Ghost(ctn_ptr): Ghost<RwLockContainerPtr>, cpu_id: CpuId, cursor: CpuId, Ghost(entry): Ghost<KernelK>) -> (ret: Option<CpuId>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        entry.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == ctn_ptr,
        entry.ctn_mp.dom().contains(ctn_ptr),
        container_cpu_wf(entry.ctn_mp, entry.cpu_set_mp, entry.cpu_arr),
        *cpu_set == entry.cpu_set_mp.spec_index(entry.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).view(),
        cpu_set.owned_cpus.wf(),
    ensures
        ret == orphan_victim(kernel_k_to_kernel_u(entry), kernel_k_to_kernel_u(entry).cpu_array[cpu_id as int].owning_container, cursor, cpu_id),
        ret is Some ==> {
            let victim_cpu = entry.cpu_arr.spec_index(ret->Some_0).view().view().view();
            &&& index_valid(NUM_CPUS, ret->Some_0)
            &&& ret->Some_0 != cpu_id
            &&& !(victim_cpu.owning_container == ctn_ptr && !(victim_cpu.state is Off))
        },
{
    let ghost u = kernel_k_to_kernel_u(entry);
    let ghost ctn = kernel_k_to_kernel_u(entry).cpu_array[cpu_id as int].owning_container;
    let mut i = cursor;
    while i < NUM_CPUS
        invariant
            index_valid(NUM_CPUS, cpu_id),
            entry.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == ctn_ptr,
            entry.ctn_mp.dom().contains(ctn_ptr),
            container_cpu_wf(entry.ctn_mp, entry.cpu_set_mp, entry.cpu_arr),
            *cpu_set == entry.cpu_set_mp.spec_index(entry.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).view(),
            cpu_set.owned_cpus.wf(),
            u == kernel_k_to_kernel_u(entry),
            ctn == u.cpu_array[cpu_id as int].owning_container,
            cursor <= i,
            first_orphan_shard(u, ctn, cursor as int, cpu_id) == first_orphan_shard(u, ctn, i as int, cpu_id),
        decreases NUM_CPUS - i,
    {
        let orphan = i != cpu_id && !(cpu_set.owned_cpus.contains(i) && !cpu_set.owned_cpus.is_closed(i));
        proof {
            container_cpu_wf_container_at(entry.ctn_mp, entry.cpu_set_mp, entry.cpu_arr, ctn_ptr, i); container_cpu_wf_cpu_at(entry.ctn_mp, entry.cpu_set_mp, entry.cpu_arr, i);
            rebalance_orphan_pull_victim_scan_from_k(&entry, ctn_ptr, i, cpu_id, orphan);
        }
        if orphan { return Some(i); }
        i = i + 1;
    }
    proof { rebalance_orphan_pull_victim_scan_from_k(&entry, ctn_ptr, i, cpu_id, false); }
    let mut i: usize = 0;
    while i < cursor && i < NUM_CPUS
        invariant
            index_valid(NUM_CPUS, cpu_id),
            entry.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == ctn_ptr,
            entry.ctn_mp.dom().contains(ctn_ptr),
            container_cpu_wf(entry.ctn_mp, entry.cpu_set_mp, entry.cpu_arr),
            *cpu_set == entry.cpu_set_mp.spec_index(entry.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).view(),
            cpu_set.owned_cpus.wf(),
            u == kernel_k_to_kernel_u(entry),
            ctn == u.cpu_array[cpu_id as int].owning_container,
            i <= cursor,
            i <= NUM_CPUS,
            first_orphan_shard(u, ctn, cursor as int, cpu_id) is None,
            first_orphan_shard(u, ctn, 0, cpu_id) == first_orphan_shard(u, ctn, i as int, cpu_id),
        decreases NUM_CPUS - i,
    {
        let orphan = i != cpu_id && !(cpu_set.owned_cpus.contains(i) && !cpu_set.owned_cpus.is_closed(i));
        proof {
            container_cpu_wf_container_at(entry.ctn_mp, entry.cpu_set_mp, entry.cpu_arr, ctn_ptr, i); container_cpu_wf_cpu_at(entry.ctn_mp, entry.cpu_set_mp, entry.cpu_arr, i);
            rebalance_orphan_pull_victim_scan_from_k(&entry, ctn_ptr, i, cpu_id, orphan);
        }
        if orphan { return Some(i); }
        i = i + 1;
    }
    proof { if i >= NUM_CPUS { rebalance_orphan_pull_victim_scan_from_k(&entry, ctn_ptr, i, cpu_id, false); } }
    None
}

/// Takes the cpu set `set_ptr` of the held non-Off cpu `cpu_id`: a read hold on a running cpu, whose set is unmarked; a
/// write hold unless marked on an idle cpu, which returns `None` for a marked set and changes nothing.
fn rebalance_orphan_pull_lock_cpu_set(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, set_ptr: RwLockCpuSetPtr, running: bool)
    -> (ret: Option<Tracked<LockPerm>>)
    requires
        cpu_id == old(lctx).cpu_id(),
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).inv(),
        old(krnl).cpu_set_mp.dom().contains(set_ptr),
        running ==> !old(krnl).cpu_set_mp.spec_index(set_ptr).being_killed(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        !(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Off),
        !old(krnl).cpu_set_mp.spec_index(set_ptr).locked_by_thread(old(lctx).thread_id()),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        (ret is None) == (!running && old(krnl).cpu_set_mp.spec_index(set_ptr).being_killed()),
        ret is None ==> *final(lctx) == *old(lctx) && kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        *final(krnl) == (KernelK { cpu_set_mp: final(krnl).cpu_set_mp, ..*old(krnl) }),
        forall|c: RwLockContainerPtr| #![trigger final(krnl).cpu_set_mp.spec_index(final(krnl).ctn_mp.spec_index(c).view_rodata().view().cpu_set)]
            old(krnl).ctn_mp.dom().contains(c) && old(krnl).ctn_mp.spec_index(c).view_rodata().view().cpu_set != set_ptr
                ==> final(krnl).cpu_set_mp.spec_index(final(krnl).ctn_mp.spec_index(c).view_rodata().view().cpu_set) == old(krnl).cpu_set_mp.spec_index(old(krnl).ctn_mp.spec_index(c).view_rodata().view().cpu_set),
        ret is Some ==> {
            let before = old(krnl).cpu_set_mp.spec_index(set_ptr);
            let after = final(krnl).cpu_set_mp.spec_index(set_ptr);
            let perm = ret->Some_0.view();
            &&& final(krnl).cpu_set_mp.unchanged_except(&old(krnl).cpu_set_mp, set_ptr)
            &&& final(krnl).cpu_set_mp.perms_wf()
            &&& after.is_init()
            &&& after.view() == before.view()
            &&& !after.being_killed()
            &&& !before.being_killed()
            &&& perm.thread_id() == final(lctx).thread_id()
            &&& final(lctx).cpu_set_lock_map().dom() =~= set![set_ptr]
            &&& final(lctx).page_lock_map() == old(lctx).page_lock_map()
            &&& final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map()
            &&& final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map()
            &&& final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map()
            &&& final(lctx).container_lock_map() == old(lctx).container_lock_map()
            &&& final(lctx).process_lock_map() == old(lctx).process_lock_map()
            &&& final(lctx).thread_lock_map() == old(lctx).thread_lock_map()
            &&& final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map()
            &&& final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map()
            &&& final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map()
            &&& final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map()
            &&& final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map()
            &&& final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map()
            &&& final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map()
            &&& final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps()
            &&& final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps()
            &&& final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps()
            &&& !running ==> {
                &&& before.locking_thread() is None
                &&& typed_lock_map_contains_mode(final(lctx).cpu_set_lock_map(), set_ptr, TypedLockMode::Write)
                &&& perm.state() is WriteLock
                &&& perm.lock_id() == after.locking_thread()->Write_lock_id
            }
            &&& running ==> {
                &&& !(before.locking_thread() is Write)
                &&& !(before.locking_thread() is Read && before.locking_thread()->Read_reader_map.dom().contains(final(lctx).thread_id()))
                &&& before.locking_thread() is Read ==> !before.locking_thread()->Read_reader_map.dom().is_empty()
                &&& typed_lock_map_contains_mode(final(lctx).cpu_set_lock_map(), set_ptr, TypedLockMode::Read)
                &&& perm.state() is ReadLock
                &&& after.read_lock_perm_match(&perm)
                &&& after.locking_thread() == (RwLockState::Read {
                    reader_map: (if before.locking_thread() is Read { before.locking_thread()->Read_reader_map } else { Map::empty() }).insert(final(lctx).thread_id(), perm.lock_id()),
                })
            }
        },
{
    proof { cpu_set_perms_wf_at(krnl.cpu_set_mp, set_ptr); }
    if running {
        let ret = krnl.rlock_cpu_set(cpu_id, set_ptr, Tracked(&mut *lctx));
        Some(ret)
    } else {
        let ret = krnl.wlock_cpu_set_unless_killed(set_ptr, Tracked(&mut *lctx));
        proof { if ret is None { assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); }; } }
        ret
    }
}

/// Releases this cpu's hold on the cpu set `set_ptr`, a write hold when `set_write` and a read hold otherwise; the set's
/// holders return to `base`, those before the acquisition.
fn rebalance_orphan_pull_unlock_cpu_set(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, set_ptr: RwLockCpuSetPtr, set_write: bool, Tracked(set_perm): Tracked<LockPerm>,
    Ghost(base): Ghost<RwLockState>,
)
    requires
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(krnl).cpu_set_mp.dom().contains(set_ptr),
        !old(krnl).cpu_set_mp.spec_index(set_ptr).being_killed(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        set_perm.thread_id() == old(lctx).thread_id(),
        set_write ==> {
            &&& base is None
            &&& typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), set_ptr, TypedLockMode::Write)
            &&& set_perm.state() is WriteLock
            &&& set_perm.lock_id() == old(krnl).cpu_set_mp.spec_index(set_ptr).locking_thread()->Write_lock_id
        },
        !set_write ==> {
            &&& !(base is Write)
            &&& !(base is Read && base->Read_reader_map.dom().contains(old(lctx).thread_id()))
            &&& base is Read ==> !base->Read_reader_map.dom().is_empty()
            &&& typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), set_ptr, TypedLockMode::Read)
            &&& set_perm.state() is ReadLock
            &&& old(krnl).cpu_set_mp.spec_index(set_ptr).read_lock_perm_match(&set_perm)
            &&& old(krnl).cpu_set_mp.spec_index(set_ptr).locking_thread()
                == (RwLockState::Read { reader_map: (if base is Read { base->Read_reader_map } else { Map::empty() }).insert(old(lctx).thread_id(), set_perm.lock_id()) })
        },
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(krnl).inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        *final(krnl) == (KernelK { cpu_set_mp: final(krnl).cpu_set_mp, ..*old(krnl) }),
        forall|c: RwLockContainerPtr| #![trigger final(krnl).cpu_set_mp.spec_index(final(krnl).ctn_mp.spec_index(c).view_rodata().view().cpu_set)]
            old(krnl).ctn_mp.dom().contains(c) && old(krnl).ctn_mp.spec_index(c).view_rodata().view().cpu_set != set_ptr
                ==> final(krnl).cpu_set_mp.spec_index(final(krnl).ctn_mp.spec_index(c).view_rodata().view().cpu_set) == old(krnl).cpu_set_mp.spec_index(old(krnl).ctn_mp.spec_index(c).view_rodata().view().cpu_set),
        final(krnl).cpu_set_mp.unchanged_except(&old(krnl).cpu_set_mp, set_ptr),
        final(krnl).cpu_set_mp.spec_index(set_ptr).locking_thread() == base,
        final(krnl).cpu_set_mp.spec_index(set_ptr).being_killed() == old(krnl).cpu_set_mp.spec_index(set_ptr).being_killed(),
        typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::CpuSet(set_ptr)),
{
    if set_write {
        krnl.wunlock_cpu_set(set_ptr, Tracked(&mut *lctx), Tracked(set_perm));
    } else {
        proof {
            if base is Read {
                assert_maps_equal!(base->Read_reader_map.insert(lctx.thread_id(), set_perm.lock_id()).remove(lctx.thread_id()), base->Read_reader_map);
            } else {
                assert_sets_equal!(Map::<LockThreadId, LockToken>::empty().insert(lctx.thread_id(), set_perm.lock_id()).remove(lctx.thread_id()).dom(), Set::empty());
            }
        }
        krnl.runlock_cpu_set(cpu_id, set_ptr, Tracked(&mut *lctx), Tracked(set_perm));
    }
}

/// Write-locks shards `cpu_id` and `victim` of `sched_ptr`, the lower index first.
fn rebalance_orphan_pull_lock_shards(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, sched_ptr: RwLockSchedulerPtr, victim: CpuId)
    -> (ret: (Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        old(krnl).inv(),
        old(krnl).sched_mp.dom().contains(sched_ptr),
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, victim),
        victim != cpu_id,
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
        final(krnl).sched_mp.unchanged_except(&old(krnl).sched_mp, sched_ptr),
        final(krnl).sched_mp.spec_index(sched_ptr).owning_container == old(krnl).sched_mp.spec_index(sched_ptr).owning_container,
        scheduler_shards_of(final(krnl).sched_mp.spec_index(sched_ptr)) == scheduler_shards_of(old(krnl).sched_mp.spec_index(sched_ptr)),
        final(lctx).scheduler_lock_map().dom() =~= set![(sched_ptr, cpu_id), (sched_ptr, victim)],
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
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == final(lctx).thread_id(),
        ret.0.view().lock_id() == final(krnl).sched_mp.spec_index(sched_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).scheduler_lock_map(), (sched_ptr, cpu_id), TypedLockMode::Write),
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().lock_id() == final(krnl).sched_mp.spec_index(sched_ptr).shards.spec_index(victim).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).scheduler_lock_map(), (sched_ptr, victim), TypedLockMode::Write),
{
    let (lo, hi) = if victim < cpu_id { (victim, cpu_id) } else { (cpu_id, victim) };
    let Tracked(lo_perm) = krnl.wlock_scheduler_shard(sched_ptr, lo, Tracked(&mut *lctx));
    let Tracked(hi_perm) = krnl.wlock_scheduler_shard(sched_ptr, hi, Tracked(&mut *lctx));
    proof {
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl)) by {
            broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
        };
    }
    if victim < cpu_id { (Tracked(hi_perm), Tracked(lo_perm)) } else { (Tracked(lo_perm), Tracked(hi_perm)) }
}

/// With the cpu `cpu_id` and its container's cpu set `set_ptr` held since the entry snapshot and nothing moved, releases
/// them and finishes the call without recording a step.
fn rebalance_orphan_pull_release_unpulled(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, Ghost(cursor): Ghost<CpuId>, set_ptr: RwLockCpuSetPtr,
    set_write: bool, Tracked(set_perm): Tracked<LockPerm>, Tracked(cpu_lock_perm): Tracked<LockPerm>, Ghost(cs_locked): Ghost<KernelK>,
)
    requires
        old(krnl).inv(),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, thrd_mp: old(krnl).thrd_mp, sched_mp: old(krnl).sched_mp, cpu_set_mp: old(krnl).cpu_set_mp, ..old(steps).snapshot_k() }),
        cs_locked == (KernelK { cpu_arr: cs_locked.cpu_arr, cpu_op: cs_locked.cpu_op, cpu_set_mp: cs_locked.cpu_set_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_set_mp == cs_locked.cpu_set_mp,
        kernel_container_nonlock_fields_and_quotas_unchanged(&cs_locked, old(krnl)),
        forall|c: RwLockContainerPtr| #![trigger cs_locked.cpu_set_mp.spec_index(cs_locked.ctn_mp.spec_index(c).view_rodata().view().cpu_set)]
            cs_locked.ctn_mp.dom().contains(c) && cs_locked.ctn_mp.spec_index(c).view_rodata().view().cpu_set != set_ptr
                ==> cs_locked.cpu_set_mp.spec_index(cs_locked.ctn_mp.spec_index(c).view_rodata().view().cpu_set) == old(steps).snapshot_k().cpu_set_mp.spec_index(cs_locked.ctn_mp.spec_index(c).view_rodata().view().cpu_set),
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] == cpu_op_after_step(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state),
        forall|t: RwLockThreadPtr| #![trigger old(krnl).thrd_mp.spec_index(t)] old(steps).snapshot_k().thrd_mp.dom().contains(t) ==> old(krnl).thrd_mp.spec_index(t) == old(steps).snapshot_k().thrd_mp.spec_index(t),
        old(krnl).cpu_set_mp.unchanged_except(&old(steps).snapshot_k().cpu_set_mp, set_ptr),
        old(krnl).cpu_set_mp.spec_index(set_ptr).being_killed() == old(steps).snapshot_k().cpu_set_mp.spec_index(set_ptr).being_killed(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(lctx).kernel_view_locking_state() is Acquire || old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom() =~= set![set_ptr],
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(steps).snapshot_k().cpu_set_mp.dom().contains(set_ptr),
        !old(krnl).cpu_set_mp.spec_index(set_ptr).being_killed(),
        set_perm.thread_id() == old(lctx).thread_id(),
        set_write ==> {
            &&& old(steps).snapshot_k().cpu_set_mp.spec_index(set_ptr).locking_thread() is None
            &&& typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), set_ptr, TypedLockMode::Write)
            &&& set_perm.state() is WriteLock
            &&& set_perm.lock_id() == old(krnl).cpu_set_mp.spec_index(set_ptr).locking_thread()->Write_lock_id
        },
        !set_write ==> {
            let base = old(steps).snapshot_k().cpu_set_mp.spec_index(set_ptr).locking_thread();
            &&& !(base is Write)
            &&& !(base is Read && base->Read_reader_map.dom().contains(old(lctx).thread_id()))
            &&& base is Read ==> !base->Read_reader_map.dom().is_empty()
            &&& typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), set_ptr, TypedLockMode::Read)
            &&& set_perm.state() is ReadLock
            &&& old(krnl).cpu_set_mp.spec_index(set_ptr).read_lock_perm_match(&set_perm)
            &&& old(krnl).cpu_set_mp.spec_index(set_ptr).locking_thread()
                == (RwLockState::Read { reader_map: (if base is Read { base->Read_reader_map } else { Map::empty() }).insert(old(lctx).thread_id(), set_perm.lock_id()) })
        },
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
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
        orphan_pull_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, cursor, false),
{
    let ghost snap = steps.snapshot_k();
    rebalance_orphan_pull_unlock_cpu_set(krnl, Tracked(&mut *lctx), cpu_id, set_ptr, set_write, Tracked(set_perm), Ghost(snap.cpu_set_mp.spec_index(set_ptr).locking_thread()));
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&snap, &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&snap, &*krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    }
    release_cpu_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Tracked(cpu_lock_perm));
    proof {
        assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(snap)) by {
            assert(krnl.cpu_op.view().view() =~= snap.cpu_op.view().view());
            kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&snap, &*krnl);
        };
        rebalance_orphan_pull_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(snap), cpu_id, cursor);
    }
}

/// Moves the head `thrd_ptr` of the orphan shard `victim` to the tail of shard `cpu_id`, releases every lock, and records
/// the orphan pull step.
fn rebalance_orphan_pull_move_head(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, Ghost(cursor): Ghost<CpuId>, sched_ptr: RwLockSchedulerPtr,
    set_ptr: RwLockCpuSetPtr, victim: CpuId, thrd_ptr: RwLockThreadPtr, set_write: bool, Tracked(set_perm): Tracked<LockPerm>, Tracked(own_perm): Tracked<LockPerm>,
    Tracked(victim_perm): Tracked<LockPerm>, Tracked(thread_lock_perm): Tracked<LockPerm>, Tracked(cpu_lock_perm): Tracked<LockPerm>,
)
    requires
        old(krnl).inv(),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, thrd_mp: old(krnl).thrd_mp, sched_mp: old(krnl).sched_mp, cpu_set_mp: old(krnl).cpu_set_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view(),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.killer_info(),
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] == cpu_op_after_step(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state),
        old(krnl).thrd_mp.unchanged_except(&old(steps).snapshot_k().thrd_mp, thrd_ptr),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view() == old(steps).snapshot_k().thrd_mp.spec_index(thrd_ptr).view(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(steps).snapshot_k().thrd_mp.spec_index(thrd_ptr).being_killed(),
        old(steps).snapshot_k().thrd_mp.spec_index(thrd_ptr).locking_thread() is None,
        old(krnl).sched_mp.unchanged_except(&old(steps).snapshot_k().sched_mp, sched_ptr),
        scheduler_shards_of(old(krnl).sched_mp.spec_index(sched_ptr)) == scheduler_shards_of(old(steps).snapshot_k().sched_mp.spec_index(sched_ptr)),
        old(krnl).cpu_set_mp.unchanged_except(&old(steps).snapshot_k().cpu_set_mp, set_ptr),
        old(krnl).cpu_set_mp.spec_index(set_ptr).being_killed() == old(steps).snapshot_k().cpu_set_mp.spec_index(set_ptr).being_killed(),
        old(steps).snapshot_k().cpu_set_mp.dom().contains(set_ptr),
        !old(krnl).cpu_set_mp.spec_index(set_ptr).being_killed(),
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
        old(lctx).thread_lock_map().dom() =~= set![thrd_ptr],
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom() =~= set![set_ptr],
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).scheduler_lock_map().dom() =~= set![(sched_ptr, cpu_id), (sched_ptr, victim)],
        own_perm.state() is WriteLock,
        own_perm.thread_id() == old(lctx).thread_id(),
        own_perm.lock_id() == old(krnl).sched_mp.spec_index(sched_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (sched_ptr, cpu_id), TypedLockMode::Write),
        victim_perm.state() is WriteLock,
        victim_perm.thread_id() == old(lctx).thread_id(),
        victim_perm.lock_id() == old(krnl).sched_mp.spec_index(sched_ptr).shards.spec_index(victim).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (sched_ptr, victim), TypedLockMode::Write),
        set_perm.thread_id() == old(lctx).thread_id(),
        set_write ==> {
            &&& old(steps).snapshot_k().cpu_set_mp.spec_index(set_ptr).locking_thread() is None
            &&& typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), set_ptr, TypedLockMode::Write)
            &&& set_perm.state() is WriteLock
            &&& set_perm.lock_id() == old(krnl).cpu_set_mp.spec_index(set_ptr).locking_thread()->Write_lock_id
        },
        !set_write ==> {
            let base = old(steps).snapshot_k().cpu_set_mp.spec_index(set_ptr).locking_thread();
            &&& !(base is Write)
            &&& !(base is Read && base->Read_reader_map.dom().contains(old(lctx).thread_id()))
            &&& base is Read ==> !base->Read_reader_map.dom().is_empty()
            &&& typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), set_ptr, TypedLockMode::Read)
            &&& set_perm.state() is ReadLock
            &&& old(krnl).cpu_set_mp.spec_index(set_ptr).read_lock_perm_match(&set_perm)
            &&& old(krnl).cpu_set_mp.spec_index(set_ptr).locking_thread()
                == (RwLockState::Read { reader_map: (if base is Read { base->Read_reader_map } else { Map::empty() }).insert(old(lctx).thread_id(), set_perm.lock_id()) })
        },
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        orphan_victim(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(old(steps).snapshot_k()).cpu_array[cpu_id as int].owning_container, cursor, cpu_id) == Some(victim),
        {
            let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            let victim_cpu = old(krnl).cpu_arr.spec_index(victim).view().view().view();
            let queues = scheduler_shards_of(old(krnl).sched_mp.spec_index(sched_ptr));
            let thread = old(krnl).thrd_mp.spec_index(thrd_ptr);
            &&& !(cpu.state is Off)
            &&& old(krnl).ctn_mp.dom().contains(cpu.owning_container)
            &&& old(krnl).ctn_mp.spec_index(cpu.owning_container).view_rodata().view().scheduler == sched_ptr
            &&& old(krnl).sched_mp.dom().contains(sched_ptr)
            &&& !(victim_cpu.owning_container == cpu.owning_container && !(victim_cpu.state is Off))
            &&& queues[victim as int].len() > 0
            &&& queues[victim as int][0] == thrd_ptr
            &&& old(krnl).thrd_mp.dom().contains(thrd_ptr)
            &&& !thread.being_killed()
            &&& thread.view().state == (ThreadState::SCHEDULED { cpu_id: victim })
            &&& thread.view().owning_container == cpu.owning_container
            &&& thread.view().free_quota_pending_clean()
            &&& thread.view().temp_alloc_clean()
            &&& thread.view().syscall_progress.view() is None
            &&& !thread.view().exited.view()
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
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) }),
        orphan_pull_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, cursor, true),
{
    let ghost before_move = *krnl;
    proof {
        kernel_scheduler_shards_projection_at(krnl.sched_mp.spec_index(sched_ptr), victim);
        scheduler_perms_wf_map(krnl.sched_mp);
        scheduler_perms_wf_at(krnl.sched_mp, sched_ptr);
        thread_perms_wf_map(krnl.thrd_mp);
        thread_perms_wf_at(krnl.thrd_mp, thrd_ptr);
        container_thread_scheduler_wf_shard_at(krnl.ctn_mp, krnl.thrd_mp, krnl.sched_mp, sched_ptr, cpu_id, thrd_ptr);
        scheduler_queue_len_bounded(&*krnl, sched_ptr, cpu_id);
        assert({
            let queue = krnl.sched_mp.spec_index(sched_ptr).shard(victim).queue;
            let node = krnl.thrd_mp.spec_index(thrd_ptr).view().scheduler_linkedlist_node.addr();
            &&& queue.map().dom().contains(node)
            &&& queue.map().spec_index(node) == thrd_ptr
        }) by { container_thread_scheduler_wf_thread_at(krnl.ctn_mp, krnl.thrd_mp, krnl.sched_mp, thrd_ptr); };
    }
    let node_addr = scheduler_map_move_shard_head(&mut krnl.sched_mp, sched_ptr, victim, cpu_id, Tracked(&*lctx), Tracked(&victim_perm), Tracked(&own_perm));
    proof {
        let queue = before_move.sched_mp.spec_index(sched_ptr).shard(victim).queue;
        queue.wf_and_equal_values_implies_equal_addrs(node_addr, before_move.thrd_mp.spec_index(thrd_ptr).view().scheduler_linkedlist_node.addr());
    }
    let ghost old_thread_lock_id = krnl.thrd_mp.lock_id_by_key(thrd_ptr);
    let thread = krnl.thrd_mp.borrow_mut_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_lock_perm));
    thread.move_scheduled(cpu_id);
    proof {
        lctx.enter_kernel_view_release();
        lctx.update_lock_id(KernelObjId::Thread(thrd_ptr), old_thread_lock_id, krnl.thrd_mp.lock_id_by_key(thrd_ptr));
        assert(rebalance_orphan_pull_eof_transition_framing(before_move, *krnl, cpu_id, sched_ptr, victim, thrd_ptr)) by { reveal(rebalance_orphan_pull_eof_transition_framing); };
        rebalance_orphan_pull_eof(before_move, *krnl, cpu_id, sched_ptr, victim, thrd_ptr);
    }
    krnl.wunlock_thread(thrd_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
    krnl.wunlock_scheduler_shard(sched_ptr, victim, Tracked(&mut *lctx), Tracked(victim_perm));
    krnl.wunlock_scheduler_shard(sched_ptr, cpu_id, Tracked(&mut *lctx), Tracked(own_perm));
    let ghost snap = steps.snapshot_k();
    rebalance_orphan_pull_unlock_cpu_set(krnl, Tracked(&mut *lctx), cpu_id, set_ptr, set_write, Tracked(set_perm), Ghost(snap.cpu_set_mp.spec_index(set_ptr).locking_thread()));
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        let ghost pull_before = steps.view();
        assert(kernel_orphan_pull_fields(&snap, &*krnl, cpu_id, victim, thrd_ptr)) by {
            reveal(kernel_orphan_pull_fields); reveal(rebalance_orphan_pull_eof_transition_framing); assert(krnl.cpu_op.view().view() =~= snap.cpu_op.view().view());
        };
        steps.end_kernel_step_orphan_pull(&*krnl, &*lctx, cpu_id, victim, thrd_ptr);
        no_locks_held_imply_all_objects_unlocked(krnl, lctx);
        assert(orphan_pull_syscall_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(snap), kernel_k_to_kernel_u(*krnl), cpu_id, cursor, true)) by {
            rebalance_orphan_pull_step_from_u(kernel_k_to_kernel_u(snap), kernel_k_to_kernel_u(*krnl), cpu_id, cursor, victim, thrd_ptr);
            rebalance_orphan_pull_trace_pull_step(&*steps, pull_before, kernel_k_to_kernel_u(snap), kernel_k_to_kernel_u(*krnl), cpu_id, cursor);
        };
    }
}

/// With the cpu `cpu_id` and its container's cpu set held since the entry snapshot, locks the own shard and the orphan
/// shard `victim` and moves that shard's live head to the tail of the own shard; an empty or killed head moves nothing.
fn rebalance_orphan_pull_locked(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, Ghost(cursor): Ghost<CpuId>, sched_ptr: RwLockSchedulerPtr,
    set_ptr: RwLockCpuSetPtr, victim: CpuId, set_write: bool, Tracked(set_perm): Tracked<LockPerm>, Tracked(cpu_lock_perm): Tracked<LockPerm>,
) -> (ret: RebalanceResult)
    requires
        old(krnl).inv(),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, cpu_set_mp: old(krnl).cpu_set_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view(),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.killer_info(),
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] == cpu_op_after_step(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        old(krnl).cpu_set_mp.unchanged_except(&old(steps).snapshot_k().cpu_set_mp, set_ptr),
        old(krnl).cpu_set_mp.spec_index(set_ptr).being_killed() == old(steps).snapshot_k().cpu_set_mp.spec_index(set_ptr).being_killed(),
        old(steps).snapshot_k().cpu_set_mp.dom().contains(set_ptr),
        !old(krnl).cpu_set_mp.spec_index(set_ptr).being_killed(),
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
        old(lctx).thread_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom() =~= set![set_ptr],
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        set_perm.thread_id() == old(lctx).thread_id(),
        set_write ==> {
            &&& old(steps).snapshot_k().cpu_set_mp.spec_index(set_ptr).locking_thread() is None
            &&& typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), set_ptr, TypedLockMode::Write)
            &&& set_perm.state() is WriteLock
            &&& set_perm.lock_id() == old(krnl).cpu_set_mp.spec_index(set_ptr).locking_thread()->Write_lock_id
        },
        !set_write ==> {
            let base = old(steps).snapshot_k().cpu_set_mp.spec_index(set_ptr).locking_thread();
            &&& !(base is Write)
            &&& !(base is Read && base->Read_reader_map.dom().contains(old(lctx).thread_id()))
            &&& base is Read ==> !base->Read_reader_map.dom().is_empty()
            &&& typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), set_ptr, TypedLockMode::Read)
            &&& set_perm.state() is ReadLock
            &&& old(krnl).cpu_set_mp.spec_index(set_ptr).read_lock_perm_match(&set_perm)
            &&& old(krnl).cpu_set_mp.spec_index(set_ptr).locking_thread()
                == (RwLockState::Read { reader_map: (if base is Read { base->Read_reader_map } else { Map::empty() }).insert(old(lctx).thread_id(), set_perm.lock_id()) })
        },
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        orphan_victim(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(old(steps).snapshot_k()).cpu_array[cpu_id as int].owning_container, cursor, cpu_id) == Some(victim),
        {
            let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            let victim_cpu = old(krnl).cpu_arr.spec_index(victim).view().view().view();
            &&& !(cpu.state is Off)
            &&& old(krnl).ctn_mp.dom().contains(cpu.owning_container)
            &&& old(krnl).ctn_mp.spec_index(cpu.owning_container).view_rodata().view().scheduler == sched_ptr
            &&& old(krnl).ctn_mp.spec_index(cpu.owning_container).view_rodata().view().cpu_set == set_ptr
            &&& old(krnl).sched_mp.dom().contains(sched_ptr)
            &&& old(krnl).sched_mp.spec_index(sched_ptr).owning_container == cpu.owning_container
            &&& !(victim_cpu.owning_container == cpu.owning_container && !(victim_cpu.state is Off))
        },
        forall|c: RwLockContainerPtr| #![trigger old(krnl).cpu_set_mp.spec_index(old(krnl).ctn_mp.spec_index(c).view_rodata().view().cpu_set)]
            old(krnl).ctn_mp.dom().contains(c) && old(krnl).ctn_mp.spec_index(c).view_rodata().view().cpu_set != set_ptr
                ==> old(krnl).cpu_set_mp.spec_index(old(krnl).ctn_mp.spec_index(c).view_rodata().view().cpu_set) == old(steps).snapshot_k().cpu_set_mp.spec_index(old(krnl).ctn_mp.spec_index(c).view_rodata().view().cpu_set),
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
        orphan_pull_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, cursor, ret is Pulled),
        ({
            let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            let queues = scheduler_shards_of(old(krnl).sched_mp.spec_index(sched_ptr));
            let head = queues[victim as int][0];
            &&& queues[victim as int].len() > 0 ==> old(krnl).thrd_mp.dom().contains(head)
            &&& (ret is Pulled) == (queues[victim as int].len() > 0 && !old(krnl).thrd_mp.spec_index(head).being_killed())
            &&& ret is Pulled ==> ret->Pulled_thread_ptr == head
        }),
{
    let ghost snap = steps.snapshot_k();
    let (Tracked(own_perm), Tracked(victim_perm)) = rebalance_orphan_pull_lock_shards(krnl, Tracked(&mut *lctx), cpu_id, sched_ptr, victim);
    proof {
        scheduler_perms_wf_map(krnl.sched_mp); scheduler_perms_wf_at(krnl.sched_mp, sched_ptr); kernel_scheduler_shards_projection_at(krnl.sched_mp.spec_index(sched_ptr), victim);
        krnl.sched_mp.spec_index(sched_ptr).shard(victim).queue.wf_implies_view_len_eq_len();
    }
    let victim_len = krnl.sched_mp.borrow_shard_typed(sched_ptr, victim, Ghost(lctx.scheduler_lock_map()), Tracked(&*lctx), Tracked(&victim_perm)).queue.len();
    if victim_len == 0 {
        krnl.wunlock_scheduler_shard(sched_ptr, victim, Tracked(&mut *lctx), Tracked(victim_perm));
        krnl.wunlock_scheduler_shard(sched_ptr, cpu_id, Tracked(&mut *lctx), Tracked(own_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&snap, &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        }
        rebalance_orphan_pull_release_unpulled(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Ghost(cursor), set_ptr, set_write, Tracked(set_perm), Tracked(cpu_lock_perm), Ghost(*old(krnl)));
        return RebalanceResult::Nothing;
    }
    let (_, thrd_ptr) = krnl.sched_mp.borrow_shard_typed(sched_ptr, victim, Ghost(lctx.scheduler_lock_map()), Tracked(&*lctx), Tracked(&victim_perm)).queue.peek_head();
    proof { container_thread_scheduler_wf_shard_at(krnl.ctn_mp, krnl.thrd_mp, krnl.sched_mp, sched_ptr, victim, thrd_ptr); }
    let res = krnl.wlock_scheduled_thread_unless_killed(thrd_ptr, Tracked(&mut *lctx));
    if res.is_none() {
        krnl.wunlock_scheduler_shard(sched_ptr, victim, Tracked(&mut *lctx), Tracked(victim_perm));
        krnl.wunlock_scheduler_shard(sched_ptr, cpu_id, Tracked(&mut *lctx), Tracked(own_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&snap, &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        }
        rebalance_orphan_pull_release_unpulled(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Ghost(cursor), set_ptr, set_write, Tracked(set_perm), Tracked(cpu_lock_perm), Ghost(*old(krnl)));
        return RebalanceResult::Nothing;
    }
    let Tracked(thread_lock_perm) = res.unwrap();
    rebalance_orphan_pull_move_head(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Ghost(cursor), sched_ptr, set_ptr, victim, thrd_ptr, set_write, Tracked(set_perm), Tracked(own_perm),
        Tracked(victim_perm), Tracked(thread_lock_perm), Tracked(cpu_lock_perm),
    );
    RebalanceResult::Pulled { thread_ptr: thrd_ptr }
}

/// Periodic orphan pull of the non-Off cpu `cpu_id`: moves the live head of the first shard of its container's scheduler
/// at or after `cursor`, wrapping around and skipping its own, whose cpu does not serve the container (not owned by it,
/// or Off) to the tail of its own shard. A running cpu read-locks its container's cpu set; an idle one write-locks it
/// unless the container's killer marked it. A cursor at or past `NUM_CPUS` scans from shard 0.
pub fn rebalance_orphan_pull(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, cursor: CpuId)
    -> (ret: RebalanceResult)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is Trap || old(krnl).cpu_op.view().view()[cpu_id as int] is Idle,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
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
        orphan_pull_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, cursor, ret is Pulled),
        ret == orphan_pull_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, cursor),
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }
    proof { schedule_current_cpu_references_wf(&*krnl, cpu_id); }
    let cpu_lock_res = krnl.wlock_own_cpu(cpu_id, Tracked(&mut *lctx));
    if cpu_lock_res.is_none() {
        proof {
            no_locks_held_imply_all_objects_unlocked(&*krnl, &*lctx); enter_kernel_view_release_preserving_lock_alignments(&*krnl, lctx);
            rebalance_orphan_pull_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, cursor);
            rebalance_orphan_pull_result_from_k(old(krnl), cpu_id, cursor, None, RebalanceResult::Nothing);
        }
        return RebalanceResult::Nothing;
    }
    let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
    proof { cpu_op_wf_at(old(krnl).cpu_op.view().view(), old(krnl).cpu_arr, cpu_id); }
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let running = match cpu.state() { CpuState::Running => true, _ => false };
    let ctn_ptr = cpu.owning_container();
    let container_ro = krnl.ctn_mp.borrow_rodata(ctn_ptr).borrow();
    let sched_ptr = container_ro.scheduler;
    let set_ptr = container_ro.cpu_set;
    proof {
        container_scheduler_wf_container_at(krnl.ctn_mp, krnl.sched_mp, ctn_ptr); container_cpu_set_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, ctn_ptr);
        if running {
            // The running thread lives in the container, so its cpu set is not marked.
            thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id); container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id);
            cpu_set_kill_mark_wf_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.prc_mp, set_ptr);
        }
        old(krnl).cpu_set_mp.typed_lock_map_aligned_locked_at(old(lctx).cpu_set_lock_map(), old(lctx).thread_id(), set_ptr);
    }
    let set_res = rebalance_orphan_pull_lock_cpu_set(krnl, Tracked(&mut *lctx), cpu_id, set_ptr, running);
    if set_res.is_none() {
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        }
        release_cpu_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Tracked(cpu_lock_perm));
        proof {
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by {
                assert(krnl.cpu_op.view().view() =~= old(krnl).cpu_op.view().view());
                kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(old(krnl), &*krnl);
            };
            rebalance_orphan_pull_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, cursor);
            rebalance_orphan_pull_result_from_k(old(krnl), cpu_id, cursor, None, RebalanceResult::Nothing);
        }
        return RebalanceResult::Nothing;
    }
    let Tracked(set_perm) = set_res.unwrap();
    proof {
        cpu_set_perms_wf_at(krnl.cpu_set_mp, set_ptr);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
    }
    let cpu_set = krnl.cpu_set_mp.borrow_typed(set_ptr, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&set_perm));
    let victim = rebalance_orphan_pull_find_victim(cpu_set, Ghost(ctn_ptr), cpu_id, cursor, Ghost(*old(krnl)));
    if victim.is_none() {
        proof { assert(kernel_container_nonlock_fields_and_quotas_unchanged(&*krnl, &*krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); }; }
        rebalance_orphan_pull_release_unpulled(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Ghost(cursor), set_ptr, !running, Tracked(set_perm), Tracked(cpu_lock_perm), Ghost(*krnl));
        proof { rebalance_orphan_pull_result_from_k(old(krnl), cpu_id, cursor, victim, RebalanceResult::Nothing); }
        return RebalanceResult::Nothing;
    }
    let victim = victim.unwrap();
    let ret = rebalance_orphan_pull_locked(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Ghost(cursor), sched_ptr, set_ptr, victim, !running, Tracked(set_perm), Tracked(cpu_lock_perm));
    proof { rebalance_orphan_pull_result_from_k(old(krnl), cpu_id, cursor, Some(victim), ret); }
    ret
}
}
