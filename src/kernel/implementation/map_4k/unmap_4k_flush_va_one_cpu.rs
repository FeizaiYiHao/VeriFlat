use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::unmap_4k_spec::*;
use super::unmap_4k_tlb::*;
#[cfg(verus_keep_ghost)]
use super::unmap_4k_trace::{unmap_4k_tlb_flush_step_pre_from_k, unmap_4k_tlb_va_flush_step_from_k};

verus! {
/// Flushes the `count` pages from `va`, 4K or 2M apart by `stride_2m`, under `pcid` on cpu `cpu_id`, drops `cpu_id` from the
/// records of the windows of the read-held `pagetable` the thread holds, deletes those records after the last cpu, and
/// records the TLB step, which also records this thread's read hold on the cpu set of its container `ctn_ptr` when the
/// step's start predates it. The recorded step keeps the `entry` projection of the non-dangling thread that `held`
/// write-locks and of its process, and the locks `held` keeps on that process and container. Every such record lists
/// exactly the cpus from `cpu_id` up on entry and from `cpu_id + 1` up on return.
pub(super) fn flush_pagetable_tlb_va_range_on_cpu(krnl: &mut KernelK, pagetable: RwLockPageTableRoot, cr3: PageTableRoot, pcid: Pcid, va: VAddr, count: usize, stride_2m: bool, cpu_id: usize,
    local_cpu: CpuId, thrd_ptr: RwLockThreadPtr, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Ghost(entry): Ghost<KernelK>, Ghost(held): Ghost<LocalContext>,
    Ghost(ctn_ptr): Ghost<RwLockContainerPtr>)
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
        ctn_ptr == entry.thrd_mp.spec_index(thrd_ptr).view().owning_container,
        old(krnl).ctn_mp.dom().contains(ctn_ptr),
        old(krnl).cpu_set_mp.unchanged_except(&old(steps).snapshot_k().cpu_set_mp, old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set),
        old(krnl).cpu_set_mp.spec_index(old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).being_killed()
            == old(steps).snapshot_k().cpu_set_mp.spec_index(old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).being_killed(),
        old(krnl).cpu_set_mp.spec_index(old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).locking_thread() is Read,
        old(krnl).cpu_set_mp.spec_index(old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).lock_state_u() == old(steps).snapshot_k().cpu_set_mp.spec_index(old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).lock_state_u().with_reader(local_cpu),
        old(krnl).inv(),
        entry.inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        typed_lock_maps_unchanged(&held, old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, local_cpu),
        old(lctx).cpu_id() == local_cpu,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), local_cpu, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_cr3 == cr3,
        old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_pcid == pcid,
        old(krnl).cpu_hw_cr3_pcid[local_cpu as int].view() == (cr3, pcid),
        old(krnl).cpu_op.view().view()[local_cpu as int] is InStep,
        old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).pt_mp.dom().contains(pagetable),
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        va_4k_valid(va),
        stride_2m ==> va_2m_valid(va),
        1 <= count < 0x4000,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        entry.thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(entry.thrd_mp.spec_index(thrd_ptr)),
        entry.prc_mp.dom().contains(entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc),
        entry.prc_mp.spec_index(entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc).view().pagetable == pagetable,
        entry.prc_mp.spec_index(entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc).view_rodata().view().pcid == pcid,
        entry.pt_mp.dom().contains(pagetable),
        !entry.prc_mp.spec_index(entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc).view().zombie,
        typed_lock_map_contains_mode(held.pagetable_lock_map(), pagetable, TypedLockMode::Read),
        typed_lock_map_contains_mode(held.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        held_threads_unchanged(entry.thrd_mp, old(krnl).thrd_mp, &held),
        held_processes_unchanged(entry.prc_mp, old(krnl).prc_mp, &held),
        old(krnl).pt_mp.spec_index(pagetable).view() == entry.pt_mp.spec_index(pagetable).view(),
        held_windows_hidden_leaves_va_flushed(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable), old(lctx).pagetable_window_lock_map(), pagetable, va, count, stride_2m),
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
            let prc_ptr = entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc;
            &&& unmap_4k_tlb_va_flush_step(old_u, final(steps).view()[j].new_u, local_cpu, va, count, stride_2m)
            &&& old_u.cpu_array[local_cpu as int].lock_state is WriteLocked
            &&& old_u.cpu_array[local_cpu as int].current_thread == Some(thrd_ptr)
            &&& old_u.thread_map.dom().contains(thrd_ptr)
            &&& old_u.thread_map[thrd_ptr] == entry_u.thread_map[thrd_ptr]
            &&& old_u.process_map.dom().contains(prc_ptr)
            &&& typed_lock_map_contains_mode(held.process_lock_map(), prc_ptr, TypedLockMode::Write) ==> old_u.process_map[prc_ptr].lock_state == entry_u.process_map[prc_ptr].lock_state
            &&& old_u.process_map[prc_ptr].pagetable is Some
            &&& !(old_u.process_map[prc_ptr].pagetable->Some_0.lock_state is Unlocked)
            &&& old_u.process_map[prc_ptr].pcid == entry_u.process_map[prc_ptr].pcid
            &&& old_u.container_map.dom().contains(ctn_ptr)
            &&& typed_lock_map_contains_mode(held.container_lock_map(), ctn_ptr, TypedLockMode::Write) ==> old_u.container_map[ctn_ptr].lock_state is WriteLocked
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
        held_threads_unchanged(old(krnl).thrd_mp, final(krnl).thrd_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
        held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
        final(krnl).ctn_mp.dom().contains(ctn_ptr),
        final(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata(),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).view() == old(krnl).pt_mp.spec_index(pagetable).view(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.spec_index(old(lctx).thread_id()) == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.spec_index(old(lctx).thread_id()),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).lock_state == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).lock_state
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).l1_table == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).l1_table
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).l2_entry == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).l2_entry
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
    let hw_cr3_pcid = flush_va_range_and_drop_stale_cpu(krnl, pagetable, cr3, pcid, va, count, stride_2m, cpu_id, local_cpu, Tracked(&mut *lctx));
    proof {
        let flushed = *krnl;
        let flushed_lctx = *lctx;
        let snap_u = steps.snapshot_u();
        let before = steps.view();
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        krnl.kernel_step_boundary_cpu_tlb_va_flushed_cpu_set_rlocked(&mut *lctx, &mut *steps, cpu_id, pcid, va, count, stride_2m, cpu_id == local_cpu || (hw_cr3_pcid.0 == cr3 && hw_cr3_pcid.1 == pcid), ctn_ptr);
        unmap_4k_tlb_flush_step_pre_from_k(&flushed, &entry, &flushed_lctx, &held, local_cpu, thrd_ptr, pagetable, snap_u, ctn_ptr);
        if before.len() < steps.view().len() {
            unmap_4k_tlb_va_flush_step_from_k(&entry, steps.view()[before.len() as int].old_u, steps.view()[before.len() as int].new_u, local_cpu, cpu_id, thrd_ptr, ctn_ptr, pcid, va, count, stride_2m);
        }
    }
}

/// Under the needflush lock of (`cpu_id`, `pcid`), marks the pair for flushing, loads the hardware cr3/pcid word of `cpu_id`,
/// and flushes the `count` pages from `va`, 4K or 2M apart by `stride_2m`, under `pcid` on `cpu_id` when it is the local
/// cpu, clearing the mark, or currently runs `cr3` with `pcid`, restoring the mark it had before; returns that word.
fn flush_va_range_on_cpu_with_needflush_lock(krnl: &mut KernelK, pagetable: RwLockPageTableRoot, cr3: PageTableRoot, pcid: Pcid, va: VAddr, count: usize, stride_2m: bool, cpu_id: usize,
    local_cpu: CpuId, Tracked(lctx): Tracked<&mut LocalContext>) -> (hw_cr3_pcid: (PageTableRoot, Pcid))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, local_cpu),
        old(lctx).cpu_id() == local_cpu,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), local_cpu, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_cr3 == cr3,
        old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_pcid == pcid,
        old(krnl).cpu_hw_cr3_pcid[local_cpu as int].view() == (cr3, pcid),
        old(krnl).pt_mp.dom().contains(pagetable),
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        va_4k_valid(va),
        stride_2m ==> va_2m_valid(va),
        1 <= count < 0x4000,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { cpu_tlb: final(krnl).cpu_tlb, pcid_needflush: final(krnl).pcid_needflush, ..*old(krnl) }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        final(krnl).cpu_tlb.view() == if cpu_id == local_cpu || (hw_cr3_pcid.0 == cr3 && hw_cr3_pcid.1 == pcid) {
            old(krnl).cpu_tlb.view().insert((cpu_id, pcid), final(krnl).cpu_tlb.spec_index((cpu_id, pcid)))
        } else { old(krnl).cpu_tlb.view() },
        cpu_id == local_cpu || (hw_cr3_pcid.0 == cr3 && hw_cr3_pcid.1 == pcid) ==> cpu_tlb_va_range_flushed(*old(krnl), cpu_id, pcid, va, count, stride_2m, old(krnl).cpu_tlb.spec_index((cpu_id, pcid)),
            final(krnl).cpu_tlb.spec_index((cpu_id, pcid)), final(krnl).cpu_tlb.structure_cache((cpu_id, pcid))),
        ({
            let cpu = final(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            let dirty_entry = final(krnl).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
            let exempt = final(krnl).pcid_needflush.spec_index(cpu_id, pcid).view().needflush && cpu.current_pcid != pcid;
            let table = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            &&& final(krnl).cpu_tlb.spec_index((cpu_id, pcid)).is_empty() || exempt || (dirty_entry is Some && dirty_entry.unwrap().pagetable_ptr != pagetable)
                || ((cpu.current_pcid == pcid && cpu.current_pagetable == Some(pagetable) || !old(krnl).pcid_needflush.spec_index(cpu_id, pcid).view().needflush)
                    && single_tlb_va_range_flushed_kept_or_present(old(krnl).cpu_tlb.spec_index((cpu_id, pcid)), final(krnl).cpu_tlb.spec_index((cpu_id, pcid)), table, va, count, stride_2m))
            &&& final(krnl).cpu_tlb.structure_cache((cpu_id, pcid)).is_empty() || exempt || (dirty_entry is Some && dirty_entry.unwrap().pagetable_ptr != pagetable)
                || single_structure_cache_subset_of_present_pagetable(final(krnl).cpu_tlb.structure_cache((cpu_id, pcid)), table)
        }),
{
    let Tracked(needflush_perm) = krnl.wlock_pcid_needflush(cpu_id, pcid, Tracked(&mut *lctx));
    let needflush = krnl.read_pcid_needflush(cpu_id, pcid, Tracked(&*lctx), Tracked(&needflush_perm));
    let ghost unmarked = *krnl;
    let hw_cr3_pcid = mark_pcid_needflush_and_load(krnl, cpu_id, pcid, Tracked(&mut *lctx), Tracked(&needflush_perm));
    let ghost marked = *krnl;
    if cpu_id == local_cpu {
        flush_local_va_range_and_clear(krnl, cpu_id, pcid, va, count, stride_2m, Tracked(&*lctx), Tracked(&needflush_perm));
    } else if hw_cr3_pcid.0 == cr3 && hw_cr3_pcid.1 == pcid {
        flush_remote_va_range_and_restore_needflush(krnl, cpu_id, pcid, va, count, stride_2m, needflush, Ghost(unmarked), Tracked(&*lctx), Tracked(&needflush_perm));
    }
    assert({
        let cpu = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
        let dirty_entry = krnl.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
        let exempt = krnl.pcid_needflush.spec_index(cpu_id, pcid).view().needflush && cpu.current_pcid != pcid;
        let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        &&& krnl.cpu_tlb.spec_index((cpu_id, pcid)).is_empty() || exempt || (dirty_entry is Some && dirty_entry.unwrap().pagetable_ptr != pagetable)
            || ((cpu.current_pcid == pcid && cpu.current_pagetable == Some(pagetable) || !old(krnl).pcid_needflush.spec_index(cpu_id, pcid).view().needflush)
                && single_tlb_va_range_flushed_kept_or_present(marked.cpu_tlb.spec_index((cpu_id, pcid)), krnl.cpu_tlb.spec_index((cpu_id, pcid)), table, va, count, stride_2m))
        &&& krnl.cpu_tlb.structure_cache((cpu_id, pcid)).is_empty() || exempt || (dirty_entry is Some && dirty_entry.unwrap().pagetable_ptr != pagetable)
            || single_structure_cache_subset_of_present_pagetable(krnl.cpu_tlb.structure_cache((cpu_id, pcid)), table)
    }) by {
        cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_id); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id);
        process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap());
    };
    krnl.wunlock_pcid_needflush(cpu_id, pcid, Tracked(&mut *lctx), Tracked(needflush_perm));
    proof {
        assert(typed_lock_maps_unchanged(old(lctx), lctx)) by { map_insert_remove_absent_lemma(old(lctx).pcid_needflush_lock_map(), (cpu_id, pcid), TypedHeldLock { lock_id: krnl.pcid_needflush.lock_id_by_index(cpu_id, pcid), mode: TypedLockMode::Write }); };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged); };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    hw_cr3_pcid
}

/// Flushes the `count` pages from `va`, 4K or 2M apart by `stride_2m`, under `pcid` on cpu `cpu_id` under its needflush lock
/// and drops `cpu_id` from the records of the windows of the read-held `pagetable` the thread holds, deleting them after
/// the last cpu; returns the hardware cr3/pcid word of `cpu_id`. Every such record lists exactly the cpus from `cpu_id` up
/// on entry and from `cpu_id + 1` up on return.
fn flush_va_range_and_drop_stale_cpu(krnl: &mut KernelK, pagetable: RwLockPageTableRoot, cr3: PageTableRoot, pcid: Pcid, va: VAddr, count: usize, stride_2m: bool, cpu_id: usize,
    local_cpu: CpuId, Tracked(lctx): Tracked<&mut LocalContext>) -> (hw_cr3_pcid: (PageTableRoot, Pcid))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, local_cpu),
        old(lctx).cpu_id() == local_cpu,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), local_cpu, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_cr3 == cr3,
        old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_pcid == pcid,
        old(krnl).cpu_hw_cr3_pcid[local_cpu as int].view() == (cr3, pcid),
        old(krnl).pt_mp.dom().contains(pagetable),
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        va_4k_valid(va),
        stride_2m ==> va_2m_valid(va),
        1 <= count < 0x4000,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Read),
        held_windows_hidden_leaves_va_flushed(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable), old(lctx).pagetable_window_lock_map(), pagetable, va, count, stride_2m),
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
        *final(krnl) == (KernelK { cpu_tlb: final(krnl).cpu_tlb, pcid_needflush: final(krnl).pcid_needflush, pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, ..*old(krnl) }),
        final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable),
        final(krnl).pt_lower.view() =~= old(krnl).pt_lower.view().insert(pagetable, final(krnl).pt_lower.view().spec_index(pagetable)),
        final(krnl).pt_mp.spec_index(pagetable).view() == old(krnl).pt_mp.spec_index(pagetable).view(),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        final(krnl).cpu_tlb.view() == if cpu_id == local_cpu || (hw_cr3_pcid.0 == cr3 && hw_cr3_pcid.1 == pcid) {
            old(krnl).cpu_tlb.view().insert((cpu_id, pcid), final(krnl).cpu_tlb.spec_index((cpu_id, pcid)))
        } else { old(krnl).cpu_tlb.view() },
        cpu_id == local_cpu || (hw_cr3_pcid.0 == cr3 && hw_cr3_pcid.1 == pcid) ==> cpu_tlb_va_range_flushed(*final(krnl), cpu_id, pcid, va, count, stride_2m, old(krnl).cpu_tlb.spec_index((cpu_id, pcid)),
            final(krnl).cpu_tlb.spec_index((cpu_id, pcid)), final(krnl).cpu_tlb.structure_cache((cpu_id, pcid))),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower == (PageTableLower { window_stale_cpus: whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus,
            ..whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower }),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).lock_state == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).lock_state
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).l1_table == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).l1_table
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).l2_entry == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).l2_entry
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus is None
                || (cpu_id + 1 < NUM_CPUS && whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus == Some(Set::range((cpu_id + 1) as usize, NUM_CPUS)))
        },
{
    let ghost pre = *krnl;
    let hw_cr3_pcid = flush_va_range_on_cpu_with_needflush_lock(krnl, pagetable, cr3, pcid, va, count, stride_2m, cpu_id, local_cpu, Tracked(&mut *lctx));
    let ghost flushed = *krnl;
    drop_stale_cpu_after_va_flush(krnl, pagetable, Ghost(pcid), cpu_id, Ghost(pre), Ghost(va), Ghost(count), Ghost(stride_2m), Tracked(&*lctx));
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl) && kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by {
            broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_container_nonlock_fields_and_quotas_unchanged_transitive;
        };
        assert(cpu_id == local_cpu || (hw_cr3_pcid.0 == cr3 && hw_cr3_pcid.1 == pcid) ==> cpu_tlb_va_range_flushed(*krnl, cpu_id, pcid, va, count, stride_2m, old(krnl).cpu_tlb.spec_index((cpu_id, pcid)),
            krnl.cpu_tlb.spec_index((cpu_id, pcid)), krnl.cpu_tlb.structure_cache((cpu_id, pcid)))) by {
            let cpu = flushed.cpu_arr.spec_index(cpu_id).view().view().view();
            if cpu.current_pcid == pcid && cpu.current_pagetable is Some {
                assert(flushed.pt_mp.dom().contains(cpu.current_pagetable->Some_0)) by {
                    cpu_array_wf_at(flushed.cpu_arr, flushed.dflt_pt.view(), cpu_id); process_cpu_wf_at(flushed.prc_mp, flushed.cpu_arr, cpu_id);
                    process_pagetable_wf_process_at(flushed.prc_mp, flushed.pt_mp, cpu.current_process.unwrap());
                };
            }
        };
    }
    hw_cr3_pcid
}

/// Drops `cpu_id` from the records of the windows of the read-held `pagetable` this thread holds, deleting them after the
/// last cpu. The TLB and paging-structure cache of `cpu_id` for `pcid` hold nothing of `pagetable` a flush would remove,
/// or the cpu runs `pagetable` under `pcid` or its pair was unmarked in `pre`, and its TLB keeps, from `pre`, only
/// translations a per-address flush of `count` pages from `va`, 4K or 2M apart by `stride_2m`, left and present leaves.
/// Every such record lists exactly the cpus from `cpu_id` up on entry and from `cpu_id + 1` up on return.
pub(super) fn drop_stale_cpu_after_va_flush(krnl: &mut KernelK, pagetable: RwLockPageTableRoot, Ghost(pcid): Ghost<Pcid>, cpu_id: usize, Ghost(pre): Ghost<KernelK>, Ghost(va): Ghost<VAddr>,
    Ghost(count): Ghost<usize>, Ghost(stride_2m): Ghost<bool>, Tracked(lctx): Tracked<&LocalContext>)
    requires
        old(krnl).inv(),
        pre.inv(),
        *old(krnl) == (KernelK { cpu_tlb: old(krnl).cpu_tlb, pcid_needflush: old(krnl).pcid_needflush, ..pre }),
        typed_lock_maps_aligned(old(krnl), lctx),
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).pt_mp.dom().contains(pagetable),
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Read),
        held_windows_hidden_leaves_va_flushed(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable), lctx.pagetable_window_lock_map(), pagetable, va, count, stride_2m),
        ({
            let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            let dirty_entry = old(krnl).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
            let exempt = old(krnl).pcid_needflush.spec_index(cpu_id, pcid).view().needflush && cpu.current_pcid != pcid;
            let table = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            &&& old(krnl).cpu_tlb.spec_index((cpu_id, pcid)).is_empty() || exempt || (dirty_entry is Some && dirty_entry.unwrap().pagetable_ptr != pagetable)
                || ((cpu.current_pcid == pcid && cpu.current_pagetable == Some(pagetable) || !pre.pcid_needflush.spec_index(cpu_id, pcid).view().needflush)
                    && single_tlb_va_range_flushed_kept_or_present(pre.cpu_tlb.spec_index((cpu_id, pcid)), old(krnl).cpu_tlb.spec_index((cpu_id, pcid)), table, va, count, stride_2m))
            &&& old(krnl).cpu_tlb.structure_cache((cpu_id, pcid)).is_empty() || exempt || (dirty_entry is Some && dirty_entry.unwrap().pagetable_ptr != pagetable)
                || single_structure_cache_subset_of_present_pagetable(old(krnl).cpu_tlb.structure_cache((cpu_id, pcid)), table)
        }),
        forall|w: WindowVa| #![trigger lctx.pagetable_window_lock_map().dom().contains((pagetable, w))] lctx.pagetable_window_lock_map().dom().contains((pagetable, w))
            ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus is None
                || whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus == Some(Set::range(cpu_id, NUM_CPUS)),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), lctx),
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, ..*old(krnl) }),
        final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable),
        final(krnl).pt_lower.view() =~= old(krnl).pt_lower.view().insert(pagetable, final(krnl).pt_lower.view().spec_index(pagetable)),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower == (PageTableLower { window_stale_cpus: whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus,
            ..whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower }),
        final(krnl).pt_mp.spec_index(pagetable).view() == old(krnl).pt_mp.spec_index(pagetable).view(),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        forall|w: WindowVa| #![trigger lctx.pagetable_window_lock_map().dom().contains((pagetable, w))] lctx.pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).lock_state == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).lock_state
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).l1_table == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).l1_table
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).l2_entry == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).l2_entry
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus is None
                || (cpu_id + 1 < NUM_CPUS && whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus == Some(Set::range((cpu_id + 1) as usize, NUM_CPUS)))
        },
{
    proof {
        let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
        let dirty_entry = old(krnl).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
        if (cpu.current_pcid == pcid && cpu.current_pagetable == Some(pagetable) || !pre.pcid_needflush.spec_index(cpu_id, pcid).view().needflush && !(dirty_entry is Some && dirty_entry.unwrap().pagetable_ptr != pagetable))
            && single_tlb_va_range_flushed_kept_or_present(pre.cpu_tlb.spec_index((cpu_id, pcid)), old(krnl).cpu_tlb.spec_index((cpu_id, pcid)), whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable), va,
                count, stride_2m) {
            held_window_vas_flushed_implies_window_tlb_entries_present(pre, *old(krnl), lctx, pagetable, cpu_id, pcid, va, count, stride_2m);
        }
    }
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

/// After a per-address flush of `count` pages from `va`, 4K or 2M apart by `stride_2m`, under `pcid` on cpu `cpu_id`, which
/// runs `pagetable` under `pcid` in `pre` or whose pair is unmarked there with no other dirty table, every 4K or 2M
/// translation of the TLB of `cur` in a window of `pagetable` that `lctx` holds is a present leaf: it is a present leaf the
/// walker refilled, or a held leaf the TLB of `pre` cached and the flush left, which resolves through the window's L2 entry
/// that hides no L1 page and is present outside the flush.
pub(super) proof fn held_window_vas_flushed_implies_window_tlb_entries_present(pre: KernelK, cur: KernelK, lctx: &LocalContext, pagetable: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid, va: VAddr,
    count: usize, stride_2m: bool)
    requires
        pre.inv(),
        cur == (KernelK { cpu_tlb: cur.cpu_tlb, pcid_needflush: cur.pcid_needflush, ..pre }),
        typed_lock_maps_aligned(&cur, lctx),
        pre.pt_mp.dom().contains(pagetable),
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        ({
            let cpu = pre.cpu_arr.spec_index(cpu_id).view().view().view();
            let dirty_entry = pre.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
            ||| cpu.current_pcid == pcid && cpu.current_pagetable == Some(pagetable)
            ||| !pre.pcid_needflush.spec_index(cpu_id, pcid).view().needflush && !(dirty_entry is Some && dirty_entry.unwrap().pagetable_ptr != pagetable)
        }),
        single_tlb_va_range_flushed_kept_or_present(pre.cpu_tlb.spec_index((cpu_id, pcid)), cur.cpu_tlb.spec_index((cpu_id, pcid)), whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable), va,
            count, stride_2m),
        held_windows_hidden_leaves_va_flushed(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable), lctx.pagetable_window_lock_map(), pagetable, va, count, stride_2m),
    ensures
        single_tlb_held_window_entries_present(cur.cpu_tlb.spec_index((cpu_id, pcid)), whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable), lctx.thread_id()),
{
    let table = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable);
    cpu_array_wf_at(pre.cpu_arr, pre.dflt_pt.view(), cpu_id); process_cpu_wf_at(pre.prc_mp, pre.cpu_arr, cpu_id);
    assert(!pre.cpu_tlb.spec_index((cpu_id, pcid)).is_empty() ==> single_tlb_subset_of_whole_pagetable(pre.cpu_tlb.spec_index((cpu_id, pcid)), table)) by { reveal(cpu_tlb_wf); reveal(cpu_dirty_map_pagetable_pcid_match); };
    assert(table.mapping_4k() == table.lower.mapping_4k && table.mapping_2m() == table.lower.mapping_2m);
    reveal(pagetable_window_typed_lock_map_aligned); reveal(PageTableHigher::wf_l4); reveal(WholePageTable::l3_links_l2_wf); reveal(WholePageTable::wf_l2);
    reveal(WholePageTable::wf_mapping_4k); reveal(WholePageTable::wf_mapping_2m);
    broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid, PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq;
}
}
