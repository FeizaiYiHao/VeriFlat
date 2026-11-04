use vstd::prelude::*;
use crate::*;
use super::unmap_4k_flush_one_cpu::{drop_stale_cpu, flush_pagetable_tlb_on_cpu};
#[cfg(verus_keep_ghost)]
use super::unmap_4k_flush_all_eof::*;

verus! {
/// Flushes `pcid` on every cpu of the thread's container under a read hold on that container's cpu set, and deletes the
/// stale-CPU records of `pagetable` the thread may change: all of them, and the table stale-CPU record, while it write-holds
/// the table, which `table_write_held` tells, otherwise those of the windows it holds. Each such record lists every cpu or
/// none on entry. A cpu outside the container holds nothing to flush, so its records are dropped without a flush.
pub fn flush_pagetable_tlbs(krnl: &mut KernelK, pagetable: RwLockPageTableRoot, cr3: PageTableRoot, pcid: Pcid, local_cpu: CpuId, thread_ptr: RwLockThreadPtr, table_write_held: bool,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_perm: Tracked<&LockPerm>, Tracked(table_perm): Tracked<&LockPerm>)
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
        old(krnl).cpu_hw_cr3_pcid[local_cpu as int].view() == (cr3, pcid),
        old(krnl).cpu_op.view().view()[local_cpu as int] is InStep,
        old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).pt_mp.dom().contains(pagetable),
        old(lctx).pagetable_lock_map().dom().contains(pagetable),
        table_write_held == typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        table_write_held ==> table_perm.state() is WriteLock,
        table_write_held ==> table_perm.thread_id() == old(lctx).thread_id(),
        table_write_held ==> table_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        table_write_held ==> old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::range(0usize, NUM_CPUS) || old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> forall|k: (PageMapPtr, L2Index)|
            #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)
                ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index(k) == Set::range(0usize, NUM_CPUS),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))
            ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus is None
                || whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus == Some(Set::range(0usize, NUM_CPUS)),
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().state is Running,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view().zombie,
        old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view().pagetable == pagetable,
        old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view_rodata().view().pcid == pcid,
        old(krnl).prc_mp.dom().contains(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc),
    ensures
        // Since the last recorded step, only page-table ghost state and this thread's released read hold on the cpu set of
        // its container changed.
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, cpu_set_mp: final(krnl).cpu_set_mp, ..final(steps).snapshot_k() }),
        final(krnl).pt_mp.dom() == final(steps).snapshot_k().pt_mp.dom(),
        forall|pt: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(pt)] final(steps).snapshot_k().pt_mp.dom().contains(pt) ==> {
            &&& final(krnl).pt_mp.spec_index(pt).locking_thread() == final(steps).snapshot_k().pt_mp.spec_index(pt).locking_thread()
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).mapping_4k() == whole_pagetable(final(steps).snapshot_k().pt_mp, final(steps).snapshot_k().pt_lower.view(), pt).mapping_4k()
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).mapping_2m() == whole_pagetable(final(steps).snapshot_k().pt_mp, final(steps).snapshot_k().pt_lower.view(), pt).mapping_2m()
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).mapping_1g() == whole_pagetable(final(steps).snapshot_k().pt_mp, final(steps).snapshot_k().pt_lower.view(), pt).mapping_1g()
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).lower.pagetable_window_locks
                == whole_pagetable(final(steps).snapshot_k().pt_mp, final(steps).snapshot_k().pt_lower.view(), pt).lower.pagetable_window_locks
        },
        ({
            let container_ptr = old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container;
            let cpu_set_ptr = final(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set;
            &&& final(krnl).ctn_mp.dom().contains(container_ptr)
            &&& final(krnl).cpu_set_mp.unchanged_except(&final(steps).snapshot_k().cpu_set_mp, cpu_set_ptr)
            &&& final(krnl).cpu_set_mp.spec_index(cpu_set_ptr).being_killed() == final(steps).snapshot_k().cpu_set_mp.spec_index(cpu_set_ptr).being_killed()
            &&& !(final(krnl).cpu_set_mp.spec_index(cpu_set_ptr).locking_thread() is Write)
        }),
        old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + NUM_CPUS,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        // Every flush step read-locks the cpu set of the caller's container and clears at most one cpu's TLB for `pcid` while
        // the caller's thread and process keep their entry projection and the caller's process and container locks stay.
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> {
            let old_u = final(steps).view()[j].old_u;
            let entry_u = kernel_k_to_kernel_u(*old(krnl));
            let process_ptr = old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc;
            let container_ptr = old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container;
            let locked = KernelU { container_map: old_u.container_map.insert(container_ptr, ContainerU { cpu_set_lock: LockStateU::ReadLocked, ..old_u.container_map[container_ptr] }), ..old_u };
            &&& final(steps).view()[j].new_u == locked || kernel_u_cpu_tlb_cleared(locked, final(steps).view()[j].new_u, pcid)
            &&& old_u.cpu_array[local_cpu as int].lock_state is WriteLocked
            &&& old_u.cpu_array[local_cpu as int].current_thread == Some(thread_ptr)
            &&& old_u.thread_map.dom().contains(thread_ptr)
            &&& old_u.thread_map[thread_ptr] == entry_u.thread_map[thread_ptr]
            &&& old_u.process_map.dom().contains(process_ptr)
            &&& typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write) ==> old_u.process_map[process_ptr].lock_state == entry_u.process_map[process_ptr].lock_state
            &&& old_u.process_map[process_ptr].pagetable is Some
            &&& !(old_u.process_map[process_ptr].pagetable->Some_0.lock_state is Unlocked)
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> old_u.process_map[process_ptr].pagetable == entry_u.process_map[process_ptr].pagetable
            &&& old_u.process_map[process_ptr].pcid == entry_u.process_map[process_ptr].pcid
            &&& old_u.container_map.dom().contains(container_ptr)
            &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write) ==> old_u.container_map[container_ptr].lock_state is WriteLocked
            &&& old_u.kernel_l4_end == entry_u.kernel_l4_end
        },
        final(krnl).cpu_hw_cr3_pcid[local_cpu as int].view() == (cr3, pcid),
        final(krnl).cpu_op.view().view()[local_cpu as int] == old(krnl).cpu_op.view().view()[local_cpu as int],
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> final(krnl).cpu_arr.spec_index(held_cpu_id).view().view() == old(krnl).cpu_arr.spec_index(held_cpu_id).view().view(),
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
        final(krnl).pt_mp.spec_index(pagetable).view() == (PageTableHigher { table_stale_cpus: final(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus, ..old(krnl).pt_mp.spec_index(pagetable).view() }),
        !table_write_held ==> final(krnl).pt_mp.spec_index(pagetable).view() == old(krnl).pt_mp.spec_index(pagetable).view(),
        final(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Read) ==> final(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.spec_index(old(lctx).thread_id())
            == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.spec_index(old(lctx).thread_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> {
            &&& final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower == (PageTableLower { window_stale_cpus: whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus,
                ..whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower })
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()
        },
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).lock_state == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).lock_state
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).l1_table == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).l1_table
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).l2_entry == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).l2_entry
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus is None
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
    let ghost container_ptr = krnl.thr_mp.spec_index(thread_ptr).view().owning_container;
    let ghost process_ptr = krnl.thr_mp.spec_index(thread_ptr).view().owning_proc;
    proof {
        let cpu = krnl.cpu_arr.spec_index(local_cpu).view().view().view();
        cpu_array_wf_map(krnl.cpu_arr, krnl.dflt_pt.view()); cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), local_cpu);
        thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, local_cpu); container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, local_cpu);
        container_thread_wf_owned_thread_at(krnl.ctn_mp, krnl.thr_mp, cpu.owning_container, thread_ptr); container_perms_wf_at(krnl.ctn_mp, container_ptr);
        process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr);
        pagetable_table_stale_cpus_only_when_write_held_at(krnl.pt_mp, pagetable);
        if !table_write_held { krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable); }
    }
    let cpu = krnl.cpu_arr.borrow_typed(local_cpu, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), cpu_perm);
    let cpu_set_ptr = krnl.ctn_mp.borrow_rodata(cpu.owning_container()).borrow().cpu_set;
    proof {
        // The running thread's process lives in the container, so its cpu set is not marked.
        container_cpu_set_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, container_ptr); cpu_set_kill_mark_wf_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.prc_mp, cpu_set_ptr);
    }
    let Tracked(cpu_set_perm) = krnl.rlock_cpu_set(local_cpu, cpu_set_ptr, Tracked(&mut *lctx));
    let ghost held = *lctx;
    let ghost cpu_set_entry = TypedHeldLock { lock_id: krnl.cpu_set_mp.lock_id_by_key(cpu_set_ptr), mode: TypedLockMode::Read };
    proof { held_kernel_objects_unchanged_reflexive(krnl, lctx); }
    let cpu_set = krnl.cpu_set_mp.borrow_typed(cpu_set_ptr, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&cpu_set_perm));
    proof {
        assert(flush_pagetable_tlbs_eol_loop_framing(*old(krnl), *krnl, &held, old(steps), steps, 0, pagetable, pcid, local_cpu, thread_ptr, container_ptr, table_write_held)) by { reveal(flush_pagetable_tlbs_eol_loop_framing); };
    }
    let mut cpu_id = 0usize;
    while cpu_id < NUM_CPUS
        invariant
            *krnl == (KernelK { pt_mp: krnl.pt_mp, pt_lower: krnl.pt_lower, cpu_set_mp: krnl.cpu_set_mp, ..steps.snapshot_k() }),
            krnl.pt_mp.dom() == steps.snapshot_k().pt_mp.dom(),
            forall|pt: RwLockPageTableRoot| #![trigger krnl.pt_mp.spec_index(pt)] steps.snapshot_k().pt_mp.dom().contains(pt) ==> {
                &&& krnl.pt_mp.spec_index(pt).locking_thread() == steps.snapshot_k().pt_mp.spec_index(pt).locking_thread()
                &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pt).mapping_4k() == whole_pagetable(steps.snapshot_k().pt_mp, steps.snapshot_k().pt_lower.view(), pt).mapping_4k()
                &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pt).mapping_2m() == whole_pagetable(steps.snapshot_k().pt_mp, steps.snapshot_k().pt_lower.view(), pt).mapping_2m()
                &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pt).mapping_1g() == whole_pagetable(steps.snapshot_k().pt_mp, steps.snapshot_k().pt_lower.view(), pt).mapping_1g()
                &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pt).lower.pagetable_window_locks == whole_pagetable(steps.snapshot_k().pt_mp, steps.snapshot_k().pt_lower.view(), pt).lower.pagetable_window_locks
            },
            kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), krnl),
            container_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container,
            process_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc,
            old(krnl).ctn_mp.dom().contains(container_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set == cpu_set_ptr,
            krnl.ctn_mp.dom().contains(container_ptr),
            krnl.ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata(),
            krnl.cpu_set_mp.unchanged_except(&steps.snapshot_k().cpu_set_mp, cpu_set_ptr),
            krnl.cpu_set_mp.spec_index(cpu_set_ptr).being_killed() == steps.snapshot_k().cpu_set_mp.spec_index(cpu_set_ptr).being_killed(),
            !krnl.cpu_set_mp.spec_index(cpu_set_ptr).being_killed(),
            krnl.cpu_set_mp.spec_index(cpu_set_ptr).view() == *cpu_set,
            cpu_set.owned_cpus.wf(),
            krnl.cpu_set_mp.spec_index(cpu_set_ptr).read_lock_perm_match(&cpu_set_perm),
            cpu_set_perm.state() is ReadLock,
            cpu_set_perm.thread_id() == lctx.thread_id(),
            typed_lock_map_contains_mode(held.cpu_set_lock_map(), cpu_set_ptr, TypedLockMode::Read),
            typed_lock_maps_inserted(old(lctx), &held, KernelObjId::CpuSet(cpu_set_ptr), cpu_set_entry),
            held.thread_id() == old(lctx).thread_id(),
            flush_pagetable_tlbs_eol_loop_framing(*old(krnl), *krnl, &held, old(steps), steps, cpu_id as nat, pagetable, pcid, local_cpu, thread_ptr, container_ptr, table_write_held),
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
            krnl.cpu_hw_cr3_pcid[local_cpu as int].view() == (cr3, pcid),
            krnl.cpu_op.view().view()[local_cpu as int] == old(krnl).cpu_op.view().view()[local_cpu as int],
            old(krnl).cpu_op.view().view()[local_cpu as int] is InStep,
            krnl.pt_mp.dom().contains(pagetable),
            krnl.pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
            krnl.pt_mp.spec_index(pagetable).view().cr3 == cr3,
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            pcid != KERNEL_DEFAULT_PCID,
            held.pcid_needflush_lock_map().dom().is_empty(),
            forall|held_cpu_id: CpuId| #![trigger held.cpu_lock_map().dom().contains(held_cpu_id)] held.cpu_lock_map().dom().contains(held_cpu_id) ==> !(krnl.cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            typed_lock_maps_unchanged(&held, lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, &held),
            held_threads_unchanged(old(krnl).thr_mp, krnl.thr_mp, &held),
            old(krnl).thr_mp.dom().contains(thread_ptr),
            typed_lock_map_contains_mode(held.thread_lock_map(), thread_ptr, TypedLockMode::Write),
            !thread_is_dangling(old(krnl).thr_mp.spec_index(thread_ptr)),
            old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable,
            !old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view().zombie,
            old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view().pagetable == pagetable,
            old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view_rodata().view().pcid == pcid,
            old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_thread == Some(thread_ptr),
            old(krnl).prc_mp.dom().contains(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc),
            old(krnl).pt_mp.dom().contains(pagetable),
            held.pagetable_lock_map().dom().contains(pagetable),
            old(krnl).inv(),
            krnl.cpu_arr.spec_index(local_cpu).view().view() == old(krnl).cpu_arr.spec_index(local_cpu).view().view(),
            krnl.pt_mp.spec_index(pagetable).view() == (PageTableHigher { table_stale_cpus: krnl.pt_mp.spec_index(pagetable).view().table_stale_cpus, ..old(krnl).pt_mp.spec_index(pagetable).view() }),
            krnl.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::range(cpu_id, NUM_CPUS) || krnl.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
            !table_write_held ==> krnl.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
            table_write_held == typed_lock_map_contains_mode(held.pagetable_lock_map(), pagetable, TypedLockMode::Write),
            table_write_held ==> table_perm.state() is WriteLock,
            table_write_held ==> table_perm.thread_id() == lctx.thread_id(),
            table_write_held ==> table_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(held.pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> {
                &&& krnl.pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()
                &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower
                    == (PageTableLower { window_stale_cpus: whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus, ..whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower })
                &&& forall|k: (PageMapPtr, L2Index)| #![trigger whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)] whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)
                    ==> cpu_id < NUM_CPUS && whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index(k) == Set::range(cpu_id, NUM_CPUS)
            },
            forall|w: WindowVa| #![trigger held.pagetable_window_lock_map().dom().contains((pagetable, w))] held.pagetable_window_lock_map().dom().contains((pagetable, w))
                ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).window_view(w).stale_cpus is None
                    || (cpu_id < NUM_CPUS && whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).window_view(w).stale_cpus == Some(Set::range(cpu_id, NUM_CPUS))),
        decreases NUM_CPUS - cpu_id,
    {
        if cpu_set.owned_cpus.contains(cpu_id) {
            let ghost krnl_i = *krnl;
            let ghost lctx_i = *lctx;
            let ghost steps_i = *steps;
            flush_pagetable_tlb_on_cpu(krnl, pagetable, cr3, pcid, cpu_id, local_cpu, thread_ptr, table_write_held, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_perm, Tracked(table_perm),
                Ghost(*old(krnl)), Ghost(held), Ghost(container_ptr));
            proof {
                kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl);
                flush_pagetable_tlbs_eol_flush_step(*old(krnl), krnl_i, *krnl, &held, &lctx_i, old(steps), &steps_i, steps, cpu_id, pagetable, pcid, local_cpu, thread_ptr, container_ptr, table_write_held);
            }
        } else {
            proof {
                process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, process_ptr);
                cpu_outside_container_implies_no_tlb_of_container_pagetable(krnl, container_ptr, process_ptr, cpu_id, pcid);
            }
            let ghost krnl_i = *krnl;
            drop_stale_cpu(krnl, pagetable, Ghost(pcid), cpu_id, table_write_held, Tracked(&*lctx), Tracked(table_perm));
            proof {
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                flush_pagetable_tlbs_eol_drop_step(*old(krnl), krnl_i, *krnl, &held, lctx, old(steps), steps, cpu_id, pagetable, pcid, local_cpu, thread_ptr, container_ptr, table_write_held);
            }
        }
        cpu_id = cpu_id + 1;
    }
    let ghost krnl_flushed = *krnl;
    krnl.runlock_cpu_set(local_cpu, cpu_set_ptr, Tracked(&mut *lctx), Tracked(cpu_set_perm));
    proof {
        flush_pagetable_tlbs_eol_exit(*old(krnl), krnl_flushed, *krnl, old(lctx), &held, old(steps), steps, cpu_id, pagetable, pcid, local_cpu, thread_ptr, cpu_set_ptr, cpu_set_entry, table_write_held);
        assert(typed_lock_maps_unchanged(old(lctx), lctx)) by { map_insert_remove_absent_lemma(old(lctx).cpu_set_lock_map(), cpu_set_ptr, cpu_set_entry); };
        assert(Set::range(cpu_id, NUM_CPUS) =~= Set::<CpuId>::empty());
        if typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write) {
            assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus =~= Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty());
        }
    }
}
}
