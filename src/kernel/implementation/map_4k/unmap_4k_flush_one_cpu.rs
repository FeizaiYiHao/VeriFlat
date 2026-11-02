use vstd::prelude::*;
use crate::*;
use super::unmap_4k_tlb::*;
#[cfg(verus_keep_ghost)]
use super::unmap_4k_trace::unmap_4k_tlb_flush_step_pre_from_k;

verus! {
/// Flushes `pcid` on cpu `cpu_id` under its needflush lock, drops `cpu_id` from the stale-CPU records of `pagetable` the
/// thread may change, deletes those records after the last cpu, and records the TLB step, which also records this
/// thread's read hold on the cpu set of its container `container_ptr` when the step's start predates it. The recorded
/// step keeps the `entry` projection of the non-dangling thread that `held` write-locks and of its process, and the locks
/// `held` keeps on that process and container. Every such record lists exactly the cpus from `cpu_id` up on entry and from
/// `cpu_id + 1` up on return.
pub(super) fn flush_pagetable_tlb_on_cpu(krnl: &mut KernelK, pagetable: RwLockPageTableRoot, cr3: PageTableRoot, pcid: Pcid, cpu_id: usize, local_cpu: CpuId, thread_ptr: RwLockThreadPtr,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_perm: Tracked<&LockPerm>, Ghost(entry): Ghost<KernelK>, Ghost(held): Ghost<LocalContext>,
    Ghost(container_ptr): Ghost<RwLockContainerPtr>)
    requires
        *old(krnl) == (KernelK { pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, cpu_set_mp: old(krnl).cpu_set_mp, ..old(steps).snapshot_k() }),
        old(krnl).pt_mp.dom() == old(steps).snapshot_k().pt_mp.dom(),
        forall|pt: RwLockPageTableRoot| #![trigger old(krnl).pt_mp.spec_index(pt)] old(steps).snapshot_k().pt_mp.dom().contains(pt) ==> {
            &&& old(krnl).pt_mp.spec_index(pt).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(pt).locking_thread()
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).mapping_4k() == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pt).mapping_4k()
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).mapping_2m() == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pt).mapping_2m()
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).mapping_1g() == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pt).mapping_1g()
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).lower.pagetable_window_locks
                == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pt).lower.pagetable_window_locks
        },
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        container_ptr == entry.thr_mp.spec_index(thread_ptr).view().owning_container,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).cpu_set_mp.unchanged_except(&old(steps).snapshot_k().cpu_set_mp, old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set),
        old(krnl).cpu_set_mp.spec_index(old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set).being_killed()
            == old(steps).snapshot_k().cpu_set_mp.spec_index(old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set).being_killed(),
        old(krnl).cpu_set_mp.spec_index(old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set).locking_thread() is Read,
        old(krnl).inv(),
        entry.inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        typed_lock_maps_unchanged(&held, old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, local_cpu),
        old(lctx).cpu_id() == local_cpu,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), local_cpu, TypedLockMode::Write),
        cpu_perm.view().state() is WriteLock,
        cpu_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(local_cpu).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_cr3 == cr3,
        old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_pcid == pcid,
        old(krnl).cpu_hw_cr3_pcid[local_cpu as int].view() == (cr3, pcid),
        old(krnl).cpu_op.view().view()[local_cpu as int] is InStep,
        old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).pt_mp.dom().contains(pagetable),
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        entry.thr_mp.dom().contains(thread_ptr),
        !thread_is_dangling(entry.thr_mp.spec_index(thread_ptr)),
        entry.prc_mp.dom().contains(entry.thr_mp.spec_index(thread_ptr).view().owning_proc),
        entry.prc_mp.spec_index(entry.thr_mp.spec_index(thread_ptr).view().owning_proc).view().pagetable == pagetable,
        entry.pt_mp.dom().contains(pagetable),
        !entry.prc_mp.spec_index(entry.thr_mp.spec_index(thread_ptr).view().owning_proc).view().zombie,
        held.pagetable_lock_map().dom().contains(pagetable),
        typed_lock_map_contains_mode(held.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        held_threads_unchanged(entry.thr_mp, old(krnl).thr_mp, &held),
        held_processes_unchanged(entry.prc_mp, old(krnl).prc_mp, &held),
        old(krnl).pt_mp.spec_index(pagetable).view() == entry.pt_mp.spec_index(pagetable).view(),
        typed_lock_map_contains_mode(held.pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> {
            &&& old(krnl).pt_mp.spec_index(pagetable).locking_thread() == entry.pt_mp.spec_index(pagetable).locking_thread()
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(entry.pt_mp, entry.pt_lower.view(), pagetable).mapping_4k()
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(entry.pt_mp, entry.pt_lower.view(), pagetable).mapping_2m()
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g() == whole_pagetable(entry.pt_mp, entry.pt_lower.view(), pagetable).mapping_1g()
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(entry.pt_mp, entry.pt_lower.view(), pagetable).lower.pagetable_window_locks
        },
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> forall|k: (PageMapPtr, L2Index)|
            #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)
                ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index(k) == Set::range(cpu_id, NUM_CPUS),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))
            ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus is None
                || whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus == Some(Set::range(cpu_id, NUM_CPUS)),
    ensures
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + 1,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> {
            let old_u = final(steps).view()[j].old_u;
            let entry_u = kernel_k_to_kernel_u(entry);
            let process_ptr = entry.thr_mp.spec_index(thread_ptr).view().owning_proc;
            let locked = KernelU { container_map: old_u.container_map.insert(container_ptr, ContainerU { cpu_set_lock: LockStateU::ReadLocked, ..old_u.container_map[container_ptr] }), ..old_u };
            &&& final(steps).view()[j].new_u == locked || kernel_u_cpu_tlb_cleared(locked, final(steps).view()[j].new_u, pcid)
            &&& old_u.cpu_array[local_cpu as int].lock_state is WriteLocked
            &&& old_u.cpu_array[local_cpu as int].current_thread == Some(thread_ptr)
            &&& old_u.thread_map.dom().contains(thread_ptr)
            &&& old_u.thread_map[thread_ptr] == entry_u.thread_map[thread_ptr]
            &&& old_u.process_map.dom().contains(process_ptr)
            &&& typed_lock_map_contains_mode(held.process_lock_map(), process_ptr, TypedLockMode::Write) ==> old_u.process_map[process_ptr].lock_state == entry_u.process_map[process_ptr].lock_state
            &&& old_u.process_map[process_ptr].pagetable is Some
            &&& !(old_u.process_map[process_ptr].pagetable->Some_0.lock_state is Unlocked)
            &&& typed_lock_map_contains_mode(held.pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> old_u.process_map[process_ptr].pagetable == entry_u.process_map[process_ptr].pagetable
            &&& old_u.process_map[process_ptr].pcid == entry_u.process_map[process_ptr].pcid
            &&& old_u.container_map.dom().contains(container_ptr)
            &&& typed_lock_map_contains_mode(held.container_lock_map(), container_ptr, TypedLockMode::Write) ==> old_u.container_map[container_ptr].lock_state is WriteLocked
            &&& old_u.kernel_l4_end == entry_u.kernel_l4_end
        },
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).cpu_hw_cr3_pcid[local_cpu as int].view() == old(krnl).cpu_hw_cr3_pcid[local_cpu as int].view(),
        final(krnl).cpu_op.view().view()[local_cpu as int] == old(krnl).cpu_op.view().view()[local_cpu as int],
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> final(krnl).cpu_arr.spec_index(held_cpu_id).view().view() == old(krnl).cpu_arr.spec_index(held_cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(local_cpu).view().view() == old(krnl).cpu_arr.spec_index(local_cpu).view().view(),
        final(krnl).cpu_arr.spec_index(local_cpu).view().locking_thread() == old(krnl).cpu_arr.spec_index(local_cpu).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(local_cpu).view().being_killed() == old(krnl).cpu_arr.spec_index(local_cpu).view().being_killed(),
        final(krnl).cpu_arr.spec_index(local_cpu).view().killer_info() == old(krnl).cpu_arr.spec_index(local_cpu).view().killer_info(),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_threads_unchanged(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
        held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata(),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).view() == old(krnl).pt_mp.spec_index(pagetable).view(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Read) ==> final(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.spec_index(old(lctx).thread_id())
            == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.spec_index(old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> {
            &&& final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower == (PageTableLower { window_stale_cpus: whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus,
                ..whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower })
            &&& forall|k: (PageMapPtr, L2Index)| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)]
                whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)
                ==> cpu_id + 1 < NUM_CPUS && whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index(k) == Set::range((cpu_id + 1) as usize, NUM_CPUS)
        },
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).lock_state == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).lock_state
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus is None
                || (cpu_id + 1 < NUM_CPUS && whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus == Some(Set::range((cpu_id + 1) as usize, NUM_CPUS)))
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va)
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va)
                ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(w.va) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(w.va)
        },
        forall|w: WindowVa, v: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                    ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v)
            },
{
    let hw_cr3_pcid = flush_pcid_and_drop_stale_cpu(krnl, pagetable, cr3, pcid, cpu_id, local_cpu, Tracked(&mut *lctx), cpu_perm);
    proof {
        let flushed = *krnl;
        let flushed_lctx = *lctx;
        let snap_u = steps.snapshot_u();
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        krnl.kernel_step_boundary_cpu_tlb_updated_cpu_set_rlocked(&mut *lctx, &mut *steps, cpu_id, pcid, cpu_id == local_cpu || (hw_cr3_pcid.0 == cr3 && hw_cr3_pcid.1 == pcid), container_ptr);
        unmap_4k_tlb_flush_step_pre_from_k(&flushed, &entry, &flushed_lctx, &held, local_cpu, thread_ptr, pagetable, snap_u, container_ptr);
    }
}

/// Under the needflush lock of (`cpu_id`, `pcid`), marks the pair for flushing, loads the hardware cr3/pcid word of `cpu_id`,
/// and flushes `pcid` on `cpu_id` when it is the local cpu or currently runs `cr3` with `pcid`; returns that word.
fn flush_pcid_on_cpu_with_needflush_lock(krnl: &mut KernelK, pagetable: RwLockPageTableRoot, cr3: PageTableRoot, pcid: Pcid, cpu_id: usize, local_cpu: CpuId,
    Tracked(lctx): Tracked<&mut LocalContext>, cpu_perm: Tracked<&LockPerm>) -> (hw_cr3_pcid: (PageTableRoot, Pcid))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, local_cpu),
        old(lctx).cpu_id() == local_cpu,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), local_cpu, TypedLockMode::Write),
        cpu_perm.view().state() is WriteLock,
        cpu_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(local_cpu).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_cr3 == cr3,
        old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_pcid == pcid,
        old(krnl).cpu_hw_cr3_pcid[local_cpu as int].view() == (cr3, pcid),
        old(krnl).pt_mp.dom().contains(pagetable),
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_tlb: final(krnl).cpu_tlb, pcid_needflush: final(krnl).pcid_needflush, ..*old(krnl) }),
        forall|cpu: CpuId| #![trigger final(krnl).cpu_arr.spec_index(cpu)] index_valid(NUM_CPUS, cpu) ==> {
            &&& final(krnl).cpu_arr.spec_index(cpu).value.locking_thread() == old(krnl).cpu_arr.spec_index(cpu).value.locking_thread()
            &&& final(krnl).cpu_arr.spec_index(cpu).view().view() == old(krnl).cpu_arr.spec_index(cpu).view().view()
        },
        final(krnl).cpu_arr.spec_index(local_cpu).view().locking_thread() == old(krnl).cpu_arr.spec_index(local_cpu).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(local_cpu).view().being_killed() == old(krnl).cpu_arr.spec_index(local_cpu).view().being_killed(),
        final(krnl).cpu_arr.spec_index(local_cpu).view().killer_info() == old(krnl).cpu_arr.spec_index(local_cpu).view().killer_info(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        final(krnl).cpu_tlb.view() == if cpu_id == local_cpu || (hw_cr3_pcid.0 == cr3 && hw_cr3_pcid.1 == pcid) {
            old(krnl).cpu_tlb.view().insert((cpu_id, pcid), final(krnl).cpu_tlb.spec_index((cpu_id, pcid)))
        } else { old(krnl).cpu_tlb.view() },
        cpu_id == local_cpu || (hw_cr3_pcid.0 == cr3 && hw_cr3_pcid.1 == pcid) ==> cpu_tlb_within_may_cache(*final(krnl), cpu_id, pcid, final(krnl).cpu_tlb.spec_index((cpu_id, pcid))),
        final(krnl).cpu_tlb.spec_index((cpu_id, pcid)).is_empty()
            || (final(krnl).pcid_needflush.spec_index(cpu_id, pcid).view().needflush && final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid)
            || (final(krnl).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
                && final(krnl).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr != pagetable)
            || single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(krnl).cpu_tlb.spec_index((cpu_id, pcid)), whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable)),
{
    let Tracked(needflush_perm) = krnl.wlock_pcid_needflush(cpu_id, pcid, Tracked(&mut *lctx));
    let hw_cr3_pcid = mark_pcid_needflush_and_load(krnl, cpu_id, pcid, Tracked(&mut *lctx), Tracked(&needflush_perm));
    if cpu_id == local_cpu {
        flush_local_pcid_and_clear(krnl, cpu_id, pcid, cr3, Tracked(&*lctx), Tracked(&needflush_perm), cpu_perm);
    } else if hw_cr3_pcid.0 == cr3 && hw_cr3_pcid.1 == pcid {
        flush_remote_pcid_and_clear(krnl, cpu_id, pcid, Tracked(&*lctx), Tracked(&needflush_perm));
    }
    assert(krnl.cpu_tlb.spec_index((cpu_id, pcid)).is_empty()
        || (krnl.pcid_needflush.spec_index(cpu_id, pcid).view().needflush && krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid)
        || (krnl.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
            && krnl.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr != pagetable)
        || single_cpu_single_pcid_tlb_subset_of_present_pagetable(krnl.cpu_tlb.spec_index((cpu_id, pcid)), whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable))) by {
        cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_id); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id);
        process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap());
    };
    krnl.wunlock_pcid_needflush(cpu_id, pcid, Tracked(&mut *lctx), Tracked(needflush_perm));
    proof {
        assert(typed_lock_maps_unchanged(old(lctx), lctx)) by { map_insert_remove_absent_lemma(old(lctx).pcid_needflush_lock_map(), (cpu_id, pcid), TypedHeldLock { lock_id: krnl.pcid_needflush.lock_id_by_index(cpu_id, pcid), mode: TypedLockMode::Write }); };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by {
            broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
        };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    hw_cr3_pcid
}

/// Flushes `pcid` on cpu `cpu_id` under its needflush lock and drops `cpu_id` from the stale-CPU records of `pagetable` the
/// thread may change, deleting those records after the last cpu; returns the hardware cr3/pcid word of `cpu_id`. Every such record
/// lists exactly the cpus from `cpu_id` up on entry and from `cpu_id + 1` up on return.
fn flush_pcid_and_drop_stale_cpu(krnl: &mut KernelK, pagetable: RwLockPageTableRoot, cr3: PageTableRoot, pcid: Pcid, cpu_id: usize, local_cpu: CpuId,
    Tracked(lctx): Tracked<&mut LocalContext>, cpu_perm: Tracked<&LockPerm>) -> (hw_cr3_pcid: (PageTableRoot, Pcid))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, local_cpu),
        old(lctx).cpu_id() == local_cpu,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), local_cpu, TypedLockMode::Write),
        cpu_perm.view().state() is WriteLock,
        cpu_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(local_cpu).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_cr3 == cr3,
        old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_pcid == pcid,
        old(krnl).cpu_hw_cr3_pcid[local_cpu as int].view() == (cr3, pcid),
        old(krnl).pt_mp.dom().contains(pagetable),
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> forall|k: (PageMapPtr, L2Index)|
            #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)
                ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index(k) == Set::range(cpu_id, NUM_CPUS),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))
            ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus is None
                || whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus == Some(Set::range(cpu_id, NUM_CPUS)),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_tlb: final(krnl).cpu_tlb, pcid_needflush: final(krnl).pcid_needflush, pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, ..*old(krnl) }),
        forall|cpu: CpuId| #![trigger final(krnl).cpu_arr.spec_index(cpu)] index_valid(NUM_CPUS, cpu) ==> {
            &&& final(krnl).cpu_arr.spec_index(cpu).value.locking_thread() == old(krnl).cpu_arr.spec_index(cpu).value.locking_thread()
            &&& final(krnl).cpu_arr.spec_index(cpu).view().view() == old(krnl).cpu_arr.spec_index(cpu).view().view()
        },
        final(krnl).cpu_arr.spec_index(local_cpu).view().locking_thread() == old(krnl).cpu_arr.spec_index(local_cpu).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(local_cpu).view().being_killed() == old(krnl).cpu_arr.spec_index(local_cpu).view().being_killed(),
        final(krnl).cpu_arr.spec_index(local_cpu).view().killer_info() == old(krnl).cpu_arr.spec_index(local_cpu).view().killer_info(),
        final(krnl).pt_mp.dom() == old(krnl).pt_mp.dom(),
        forall|pt: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(pt)] old(krnl).pt_mp.dom().contains(pt) ==> {
            &&& final(krnl).pt_mp.spec_index(pt).view() == old(krnl).pt_mp.spec_index(pt).view()
            &&& final(krnl).pt_mp.spec_index(pt).locking_thread() == old(krnl).pt_mp.spec_index(pt).locking_thread()
            &&& final(krnl).pt_mp.spec_index(pt).being_killed() == old(krnl).pt_mp.spec_index(pt).being_killed()
            &&& final(krnl).pt_mp.lock_id_by_key(pt) == old(krnl).pt_mp.lock_id_by_key(pt)
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).mapping_4k() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).mapping_4k()
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).mapping_2m() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).mapping_2m()
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).mapping_1g() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).mapping_1g()
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).lower.pagetable_window_locks == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).lower.pagetable_window_locks
        },
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        final(krnl).cpu_tlb.view() == if cpu_id == local_cpu || (hw_cr3_pcid.0 == cr3 && hw_cr3_pcid.1 == pcid) {
            old(krnl).cpu_tlb.view().insert((cpu_id, pcid), final(krnl).cpu_tlb.spec_index((cpu_id, pcid)))
        } else { old(krnl).cpu_tlb.view() },
        cpu_id == local_cpu || (hw_cr3_pcid.0 == cr3 && hw_cr3_pcid.1 == pcid) ==> cpu_tlb_within_may_cache(*final(krnl), cpu_id, pcid, final(krnl).cpu_tlb.spec_index((cpu_id, pcid))),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> {
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower == (PageTableLower { window_stale_cpus: whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus,
                ..whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower })
            &&& forall|k: (PageMapPtr, L2Index)| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)]
                whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)
                ==> cpu_id + 1 < NUM_CPUS && whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index(k) == Set::range((cpu_id + 1) as usize, NUM_CPUS)
        },
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).lock_state == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).lock_state
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus is None
                || (cpu_id + 1 < NUM_CPUS && whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus == Some(Set::range((cpu_id + 1) as usize, NUM_CPUS)))
        },
{
    let hw_cr3_pcid = flush_pcid_on_cpu_with_needflush_lock(krnl, pagetable, cr3, pcid, cpu_id, local_cpu, Tracked(&mut *lctx), cpu_perm);
    let ghost flushed = *krnl;
    drop_stale_cpu(krnl, pagetable, Ghost(pcid), cpu_id, Tracked(&*lctx));
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl) && kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by {
            broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_container_nonlock_fields_and_quotas_unchanged_transitive;
        };
        let cpu = flushed.cpu_arr.spec_index(cpu_id).view().view().view();
        if cpu.current_pcid == pcid && cpu.current_pagetable is Some {
            assert(flushed.pt_mp.dom().contains(cpu.current_pagetable->Some_0)) by {
                cpu_array_wf_at(flushed.cpu_arr, flushed.dflt_pt.view(), cpu_id); process_cpu_wf_at(flushed.prc_mp, flushed.cpu_arr, cpu_id);
                process_pagetable_match_process_at(flushed.prc_mp, flushed.pt_mp, cpu.current_process.unwrap());
            };
        }
    }
    hw_cr3_pcid
}

/// Drops `cpu_id`, whose TLB for `pcid` holds nothing of `pagetable` that a flush would remove, from the stale-CPU records of
/// `pagetable` the thread may change, deleting those records after the last cpu. Every such record lists exactly the cpus
/// from `cpu_id` up on entry and from `cpu_id + 1` up on return.
pub(super) fn drop_stale_cpu(krnl: &mut KernelK, pagetable: RwLockPageTableRoot, Ghost(pcid): Ghost<Pcid>, cpu_id: usize, Tracked(lctx): Tracked<&LocalContext>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), lctx),
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).pt_mp.dom().contains(pagetable),
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        old(krnl).cpu_tlb.spec_index((cpu_id, pcid)).is_empty()
            || (old(krnl).pcid_needflush.spec_index(cpu_id, pcid).view().needflush && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid)
            || (old(krnl).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
                && old(krnl).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr != pagetable)
            || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(krnl).cpu_tlb.spec_index((cpu_id, pcid)), whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable)),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> forall|k: (PageMapPtr, L2Index)|
            #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)
                ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index(k) == Set::range(cpu_id, NUM_CPUS),
        forall|w: WindowVa| #![trigger lctx.pagetable_window_lock_map().dom().contains((pagetable, w))] lctx.pagetable_window_lock_map().dom().contains((pagetable, w))
            ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus is None
                || whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus == Some(Set::range(cpu_id, NUM_CPUS)),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), lctx),
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, ..*old(krnl) }),
        final(krnl).pt_mp.dom() == old(krnl).pt_mp.dom(),
        forall|pt: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(pt)] old(krnl).pt_mp.dom().contains(pt) ==> {
            &&& final(krnl).pt_mp.spec_index(pt).view() == old(krnl).pt_mp.spec_index(pt).view()
            &&& final(krnl).pt_mp.spec_index(pt).locking_thread() == old(krnl).pt_mp.spec_index(pt).locking_thread()
            &&& final(krnl).pt_mp.spec_index(pt).being_killed() == old(krnl).pt_mp.spec_index(pt).being_killed()
            &&& final(krnl).pt_mp.lock_id_by_key(pt) == old(krnl).pt_mp.lock_id_by_key(pt)
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).mapping_4k() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).mapping_4k()
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).mapping_2m() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).mapping_2m()
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).mapping_1g() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).mapping_1g()
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).lower.pagetable_window_locks == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).lower.pagetable_window_locks
        },
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> {
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower == (PageTableLower { window_stale_cpus: whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus,
                ..whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower })
            &&& forall|k: (PageMapPtr, L2Index)| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)]
                whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)
                ==> cpu_id + 1 < NUM_CPUS && whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index(k) == Set::range((cpu_id + 1) as usize, NUM_CPUS)
        },
        forall|w: WindowVa| #![trigger lctx.pagetable_window_lock_map().dom().contains((pagetable, w))] lctx.pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).lock_state == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).lock_state
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus is None
                || (cpu_id + 1 < NUM_CPUS && whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus == Some(Set::range((cpu_id + 1) as usize, NUM_CPUS)))
        },
{
    assert(Set::range(cpu_id, NUM_CPUS).remove(cpu_id) =~= Set::range((cpu_id + 1) as usize, NUM_CPUS));
    krnl.replace_window_stale_cpus(pagetable, Ghost(WindowStaleUpdate::RemoveCpu { cpu_id }), Tracked(lctx));
    if cpu_id + 1 == NUM_CPUS {
        assert(Set::range((cpu_id + 1) as usize, NUM_CPUS) =~= Set::<CpuId>::empty());
        krnl.replace_window_stale_cpus(pagetable, Ghost(WindowStaleUpdate::ClearEmpty), Tracked(lctx));
    }
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl) && kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by {
            broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_container_nonlock_fields_and_quotas_unchanged_transitive;
        };
    }
}
}
