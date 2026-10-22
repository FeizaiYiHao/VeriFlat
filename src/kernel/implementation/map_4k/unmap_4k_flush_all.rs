use vstd::prelude::*;
use crate::*;
use super::unmap_4k_flush_one_cpu::flush_pagetable_tlb_on_cpu;

verus! {
/// Flushes `pcid` on every cpu and deletes the stale-CPU records of `pagetable` the thread may change: all of them while it
/// write-holds the table, otherwise those of the windows it holds. Each such record lists every cpu on entry.
pub fn flush_pagetable_tlbs(krnl: &mut KernelK, pagetable: RwLockPageTableRoot, cr3: PageTableRoot, pcid: Pcid, local_cpu: CpuId, thread_ptr: RwLockThreadPtr, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_perm: Tracked<&LockPerm>)
    requires
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, local_cpu),
        old(lctx).cpu_id() == local_cpu,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), local_cpu, TypedLockMode::Write),
        cpu_perm.view().state() is WriteLock,
        cpu_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(local_cpu).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_cr3 == cr3,
        old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_pcid == pcid,
        old(krnl).cpu_published[local_cpu as int].view() == (cr3, pcid),
        old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).pt_mp.dom().contains(pagetable),
        old(lctx).pagetable_lock_map().dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> forall|k: (PageMapPtr, L2Index)|
            #![trigger pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)]
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)
                ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index(k) == Set::range(0usize, NUM_CPUS),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))
            ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus is None
                || pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus == Some(Set::range(0usize, NUM_CPUS)),
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        typed_lock_map_majors_lt(old(lctx).cpu_lock_map(), CPU_LOCK_MAJOR_OFF),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view().zombie,
        old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view().pagetable == pagetable,
        old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view_rodata().view().pcid == pcid,
        old(krnl).prc_mp.dom().contains(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc),
    ensures
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + NUM_CPUS,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        // Every flush step clears one cpu's TLB for `pcid` while the caller's held objects keep their entry projection.
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> {
            let old_u = final(steps).view()[j].old_u;
            let entry_u = kernel_k_to_kernel_u(*old(krnl));
            let process_ptr = old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc;
            let container_ptr = old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container;
            &&& kernel_u_cpu_tlb_cleared(old_u, final(steps).view()[j].new_u, pcid)
            &&& old_u.cpu_array[local_cpu as int].lock_state is WriteLocked
            &&& old_u.cpu_array[local_cpu as int].current_thread == Some(thread_ptr)
            &&& old_u.thread_map.dom().contains(thread_ptr)
            &&& old_u.thread_map[thread_ptr] == entry_u.thread_map[thread_ptr]
            &&& old_u.process_map.dom().contains(process_ptr)
            &&& old_u.process_map[process_ptr].lock_state == entry_u.process_map[process_ptr].lock_state
            &&& old_u.process_map[process_ptr].pagetable is Some
            &&& !(old_u.process_map[process_ptr].pagetable->Some_0.lock_state is Unlocked)
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> old_u.process_map[process_ptr].pagetable == entry_u.process_map[process_ptr].pagetable
            &&& old_u.process_map[process_ptr].pcid == entry_u.process_map[process_ptr].pcid
            &&& old_u.container_map.dom().contains(container_ptr)
            &&& old_u.container_map[container_ptr].lock_state is WriteLocked
            &&& old_u.kernel_l4_end == entry_u.kernel_l4_end
        },
        final(krnl).cpu_published[local_cpu as int].view() == (cr3, pcid),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> final(krnl).cpu_arr.spec_index(held_cpu_id).view().view() == old(krnl).cpu_arr.spec_index(held_cpu_id).view().view(),
        old(steps).nonlock_view().len() <= final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + NUM_CPUS,
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_threads_unchanged(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
        final(krnl).cpu_arr.spec_index(local_cpu).view().view() == old(krnl).cpu_arr.spec_index(local_cpu).view().view(),
        final(krnl).cpu_arr.spec_index(local_cpu).view().locking_thread() == old(krnl).cpu_arr.spec_index(local_cpu).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(local_cpu).view().being_killed() == old(krnl).cpu_arr.spec_index(local_cpu).view().being_killed(),
        final(krnl).cpu_arr.spec_index(local_cpu).view().killer_info() == old(krnl).cpu_arr.spec_index(local_cpu).view().killer_info(),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).view() == old(krnl).pt_mp.spec_index(pagetable).view(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Read) ==> final(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.spec_index(old(lctx).thread_id())
            == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.spec_index(old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> {
            &&& final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower == (PageTableLower { window_stale_cpus: pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus,
                ..pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower })
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()
        },
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).lock_state == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).lock_state
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus is None
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va)
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va)
                ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(w.va)
        },
        forall|w: WindowVa, v: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v)
            },
{
    assert(held_containers_unchanged(krnl.ctn_mp, krnl.ctn_mp, lctx) && held_processes_unchanged(krnl.prc_mp, krnl.prc_mp, lctx) && held_threads_unchanged(krnl.thr_mp, krnl.thr_mp, lctx)
        && held_pages_unchanged(krnl.pg_arr, krnl.pg_arr, lctx) && held_iommu_tables_unchanged(krnl.it_mp, krnl.it_mp, lctx)) by {
        held_kernel_objects_unchanged_reflexive(krnl, lctx);
    };
    let mut cpu_id = 0usize;
    while cpu_id < NUM_CPUS
        invariant
            steps.snapshot_k() == *krnl,
            old(steps).view().len() <= steps.view().len() <= old(steps).view().len() + cpu_id,
            forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
            forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len() ==> {
                let old_u = steps.view()[j].old_u;
                let entry_u = kernel_k_to_kernel_u(*old(krnl));
                let process_ptr = old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc;
                let container_ptr = old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container;
                &&& kernel_u_cpu_tlb_cleared(old_u, steps.view()[j].new_u, pcid)
                &&& old_u.cpu_array[local_cpu as int].lock_state is WriteLocked
                &&& old_u.cpu_array[local_cpu as int].current_thread == Some(thread_ptr)
                &&& old_u.thread_map.dom().contains(thread_ptr)
                &&& old_u.thread_map[thread_ptr] == entry_u.thread_map[thread_ptr]
                &&& old_u.process_map.dom().contains(process_ptr)
                &&& old_u.process_map[process_ptr].lock_state == entry_u.process_map[process_ptr].lock_state
                &&& old_u.process_map[process_ptr].pagetable is Some
                &&& !(old_u.process_map[process_ptr].pagetable->Some_0.lock_state is Unlocked)
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> old_u.process_map[process_ptr].pagetable == entry_u.process_map[process_ptr].pagetable
                &&& old_u.process_map[process_ptr].pcid == entry_u.process_map[process_ptr].pcid
                &&& old_u.container_map.dom().contains(container_ptr)
                &&& old_u.container_map[container_ptr].lock_state is WriteLocked
                &&& old_u.kernel_l4_end == entry_u.kernel_l4_end
            },
            cpu_id <= NUM_CPUS,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            index_valid(NUM_CPUS, local_cpu),
            lctx.cpu_id() == local_cpu,
            typed_lock_map_contains_mode(lctx.cpu_lock_map(), local_cpu, TypedLockMode::Write),
            cpu_perm.view().state() is WriteLock,
            cpu_perm.view().thread_id() == lctx.thread_id(),
            cpu_perm.view().lock_id() == krnl.cpu_arr.spec_index(local_cpu).view().locking_thread()->Write_lock_id,
            krnl.cpu_arr.spec_index(local_cpu).view().view().view().current_cr3 == cr3,
            krnl.cpu_arr.spec_index(local_cpu).view().view().view().current_pcid == pcid,
            krnl.cpu_published[local_cpu as int].view() == (cr3, pcid),
            krnl.pt_mp.dom().contains(pagetable),
            krnl.pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
            krnl.pt_mp.spec_index(pagetable).view().cr3 == cr3,
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            pcid != KERNEL_DEFAULT_PCID,
            lctx.pcid_needflush_lock_map().dom().is_empty(),
            lctx.cpu_offline_flag_lock_map().dom().is_empty(),
            typed_lock_map_majors_lt(lctx.cpu_lock_map(), CPU_LOCK_MAJOR_OFF),
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            old(steps).nonlock_view().len() <= steps.nonlock_view().len() <= old(steps).nonlock_view().len() + cpu_id,
            held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            held_threads_unchanged(old(krnl).thr_mp, krnl.thr_mp, old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, krnl.it_mp, old(lctx)),
            held_pages_unchanged(old(krnl).pg_arr, krnl.pg_arr, old(lctx)),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> krnl.cpu_arr.spec_index(held_cpu_id).view().view() == old(krnl).cpu_arr.spec_index(held_cpu_id).view().view(),
            old(krnl).thr_mp.dom().contains(thread_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).container_lock_map(), old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container, TypedLockMode::Write),
            !old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view().zombie,
            old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view().pagetable == pagetable,
            old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view_rodata().view().pcid == pcid,
            old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_thread == Some(thread_ptr),
            old(krnl).prc_mp.dom().contains(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc),
            old(krnl).pt_mp.dom().contains(pagetable),
            old(lctx).pagetable_lock_map().dom().contains(pagetable),
            old(krnl).inv(),
            krnl.cpu_arr.spec_index(local_cpu).view().view() == old(krnl).cpu_arr.spec_index(local_cpu).view().view(),
            krnl.cpu_arr.spec_index(local_cpu).view().locking_thread() == old(krnl).cpu_arr.spec_index(local_cpu).view().locking_thread(),
            krnl.cpu_arr.spec_index(local_cpu).view().being_killed() == old(krnl).cpu_arr.spec_index(local_cpu).view().being_killed(),
            krnl.cpu_arr.spec_index(local_cpu).view().killer_info() == old(krnl).cpu_arr.spec_index(local_cpu).view().killer_info(),
            krnl.pt_mp.dom().contains(pagetable),
            krnl.pt_mp.spec_index(pagetable).view() == old(krnl).pt_mp.spec_index(pagetable).view(),
            krnl.pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Read) ==> krnl.pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.spec_index(old(lctx).thread_id())
                == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.spec_index(old(lctx).thread_id()),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> {
                &&& krnl.pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()
                &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower == (PageTableLower { window_stale_cpus: pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus, ..pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower })
                &&& forall|k: (PageMapPtr, L2Index)| #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)] pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)
                    ==> cpu_id < NUM_CPUS && pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index(k) == Set::range(cpu_id, NUM_CPUS)
            },
            forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
                &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).window_view(w).lock_state == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).lock_state
                &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).window_view(w).stale_cpus is None || (cpu_id < NUM_CPUS && pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).window_view(w).stale_cpus == Some(Set::range(cpu_id, NUM_CPUS)))
                &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va)
                    ==> pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m().spec_index(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(w.va)
            },
            forall|w: WindowVa, v: VAddr|
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
                old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                        ==> pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v)
                },
        decreases NUM_CPUS - cpu_id,
    {
        flush_pagetable_tlb_on_cpu(krnl, pagetable, cr3, pcid, cpu_id, local_cpu, thread_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_perm, Ghost(*old(krnl)), Ghost(*old(lctx)));
        cpu_id = cpu_id + 1;
    }
    proof {
        if typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write) {
            assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus =~= Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty());
        }
    }
}
}
