use vstd::prelude::*;
use crate::*;
use super::syscall_thread_exit_spec::*;
use super::syscall_thread_exit_trace::*;
use super::syscall_thread_exit_reclaim_quota_helpers::{thread_exit_reclaim_return_quota_size, thread_exit_reclaim_release_tables};
#[cfg(feature = "split-crates")]
use veriflat_map_4k::map_4k::unmap_iommu_4k_reclaim_one::reclaim_detached_iommu_4k_page;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::map_4k::unmap_iommu_4k_reclaim_one::reclaim_detached_iommu_4k_page;
#[cfg(feature = "split-crates")]
use veriflat_map_4k::map_4k::reclaim_held_4k_leaves::reclaim_held_4k_leaves;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::map_4k::reclaim_held_4k_leaves::reclaim_held_4k_leaves;

verus! {
/// Flush the process's PCID from every cpu once, dropping every cpu from the page table's stale record, then record the flush.
pub(super) fn thread_exit_reclaim_flush(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    Ghost(container_ptr): Ghost<RwLockContainerPtr>, Ghost(process_ptr): Ghost<RwLockProcessPtr>, thread_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot,
    cr3: PageTableRoot, pcid: Pcid, Ghost(entry_k): Ghost<KernelK>,
    Ghost(entry_lctx): Ghost<LocalContext>, Ghost(pt_entry): Ghost<TypedHeldLock>, Ghost(entry_pt): Ghost<WholePageTable<PT_TYPE>>,
    Ghost(iommu_table): Ghost<Option<RwLockPageTableRoot>>, Ghost(table_lctx): Ghost<LocalContext>, Ghost(it_entry): Ghost<TypedHeldLock>, Ghost(locked_it): Ghost<LockCell<PageTable<IOMMU_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>>,
    Tracked(cpu_lock_perm): Tracked<&LockPerm>, Tracked(process_lock_perm): Tracked<&LockPerm>, Tracked(thread_lock_perm): Tracked<&LockPerm>,
    Tracked(pagetable_lock_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_inserted(&entry_lctx, &table_lctx, KernelObjId::PageTable(pagetable), pt_entry),
        iommu_table is Some ==> typed_lock_maps_inserted(&table_lctx, old(lctx), KernelObjId::IommuTable(iommu_table->Some_0), it_entry),
        iommu_table is None ==> typed_lock_maps_unchanged(&table_lctx, old(lctx)),
        pt_entry.mode == TypedLockMode::Write,
        it_entry.mode == TypedLockMode::Write,
        entry_k.prc_mp.spec_index(process_ptr).view().iommu_table == iommu_table,
        iommu_table is Some ==> locked_it.view().leaves_present() && locked_it.view().proc_ptr == process_ptr && locked_it.view().kernel_l4_end == 0,
        old(lctx).cpu_id() == cpu_id,
        old(lctx).thread_id() == entry_lctx.thread_id(),
        index_valid(NUM_CPUS, cpu_id),
        entry_lctx.cpu_lock_map().dom() =~= set![cpu_id],
        entry_lctx.container_lock_map().dom() =~= set![container_ptr],
        entry_lctx.process_lock_map().dom() =~= set![process_ptr],
        entry_lctx.thread_lock_map().dom() =~= set![thread_ptr],
        entry_lctx.page_lock_map().dom().is_empty(),
        entry_lctx.scheduler_lock_map().dom().is_empty(),
        entry_lctx.cpu_set_lock_map().dom().is_empty(),
        entry_lctx.pagetable_lock_map().dom().is_empty(),
        entry_lctx.pagetable_window_lock_map().dom().is_empty(),
        entry_lctx.holds_no_allocator_locks(PageSize::SZ4k),
        entry_lctx.holds_no_allocator_locks(PageSize::SZ2m),
        entry_lctx.holds_no_allocator_locks(PageSize::SZ1g),
        entry_lctx.pcid_needflush_lock_map().dom().is_empty(),
        entry_lctx.cpu_offline_flag_lock_map().dom().is_empty(),
        entry_lctx.endpoint_lock_map().dom().is_empty(),
        entry_lctx.pcid_allocator_lock_map().dom().is_empty(),
        entry_lctx.iommu_table_lock_map().dom().is_empty(),
        entry_lctx.iommu_root_table_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(entry_lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        process_lock_perm.state() is WriteLock,
        process_lock_perm.thread_id() == entry_lctx.thread_id(),
        process_lock_perm.lock_id() == entry_k.prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == entry_lctx.thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == entry_lctx.thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == entry_lctx.thread_id(),
        pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(steps).snapshot_k() == *old(krnl),
        thread_exit_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view() == entry_k.cpu_arr.spec_index(cpu_id).view().view(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == entry_k.cpu_arr.spec_index(cpu_id).view().locking_thread(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == entry_k.cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == entry_k.cpu_arr.spec_index(cpu_id).view().killer_info(),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cr3, pcid),
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr) == entry_k.ctn_mp.spec_index(container_ptr),
        entry_k.ctn_mp.dom().contains(container_ptr),
        entry_k.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
        entry_k.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().contains(thread_ptr),
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).prc_mp.spec_index(process_ptr) == entry_k.prc_mp.spec_index(process_ptr),
        entry_k.prc_mp.dom().contains(process_ptr),
        entry_k.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        entry_k.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() == 1,
        !entry_k.prc_mp.spec_index(process_ptr).view().zombie,
        entry_k.prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
        entry_k.prc_mp.spec_index(process_ptr).view_rodata().view().pcid == pcid,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == entry_k.thr_mp.spec_index(thread_ptr).locking_thread(),
        old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == entry_k.thr_mp.spec_index(thread_ptr).being_killed(),
        entry_k.thr_mp.dom().contains(thread_ptr),
        entry_k.thr_mp.spec_index(thread_ptr).inv(),
        entry_k.thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        entry_k.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        entry_k.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        entry_k.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable,
        entry_k.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        entry_k.thr_mp.spec_index(thread_ptr).view().caller is None,
        forall|j: int| #![trigger entry_k.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j]]
            0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> entry_k.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j] is None,
        entry_k.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        entry_k.thr_mp.spec_index(thread_ptr).view().container_depth <= MAX_CONTAINER_TREE_DEPTH,
        old(krnl).pt_mp.dom().contains(pagetable),
        iommu_table is Some ==> old(krnl).it_mp.dom().contains(iommu_table->Some_0) && old(krnl).it_mp.spec_index(iommu_table->Some_0) == locked_it,
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..entry_k.thr_mp.spec_index(thread_ptr).view() }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: false }),
        0 <= start <= old(steps).view().len(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() is None,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks.dom() =~= Set::<WindowVa>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::range(0usize, NUM_CPUS),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_perms == entry_pt.lower.l2_perms,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i)] #![trigger entry_pt.spec_held_2m_l2(l4i, l3i, l2i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i) == entry_pt.spec_held_2m_l2(l4i, l3i, l2i),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        iommu_table is Some ==> typed_lock_maps_inserted(&table_lctx, final(lctx), KernelObjId::IommuTable(iommu_table->Some_0), it_entry),
        iommu_table is None ==> typed_lock_maps_unchanged(&table_lctx, final(lctx)),
        final(lctx).cpu_id() == cpu_id,
        final(lctx).thread_id() == entry_lctx.thread_id(),
        cpu_lock_perm.lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        final(steps).snapshot_k() == *final(krnl),
        thread_exit_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == entry_k.cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == entry_k.cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == entry_k.cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == entry_k.cpu_arr.spec_index(cpu_id).view().killer_info(),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cr3, pcid),
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr) == entry_k.ctn_mp.spec_index(container_ptr),
        final(krnl).prc_mp.dom().contains(process_ptr),
        final(krnl).prc_mp.spec_index(process_ptr) == entry_k.prc_mp.spec_index(process_ptr),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == entry_k.thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == entry_k.thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).pt_mp.dom().contains(pagetable),
        iommu_table is Some ==> final(krnl).it_mp.dom().contains(iommu_table->Some_0) && final(krnl).it_mp.spec_index(iommu_table->Some_0) == locked_it,
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..entry_k.thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: true }),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_1g().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks.dom() =~= Set::<WindowVa>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        final(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.l2_perms == entry_pt.lower.l2_perms,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i)] #![trigger entry_pt.spec_held_2m_l2(l4i, l3i, l2i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i) == entry_pt.spec_held_2m_l2(l4i, l3i, l2i),
        forall|l4i: L4Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i),
{
    let ghost flush_before = steps.view();
    let ghost entry_flush_k = *krnl;
    let ghost entry_flush_lctx = *lctx;
    proof { assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); }; }
    flush_pagetable_tlbs(krnl, pagetable, cr3, pcid, cpu_id, thread_ptr, true, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(cpu_lock_perm), Tracked(pagetable_lock_perm));
    proof {
        assert(thread_exit_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id)) by {
            thread_exit_flush_step_pre_from_k(&entry_flush_k, &entry_flush_lctx, cpu_id, container_ptr, process_ptr, thread_ptr, pagetable, pcid);
            thread_exit_trace_from_tlb_flush(&*steps, flush_before, start, pre, kernel_k_to_kernel_u(entry_flush_k), cpu_id, thread_ptr, process_ptr, container_ptr, pcid);
        };
    }
    let ghost flush_snap = steps.snapshot_k();
    let ghost flush_k = *krnl;
    let ghost flush_lctx = *lctx;
    proof { assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k()); }
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::ThreadExitReclaim { flushed: true })), Tracked(&*lctx), Tracked(thread_lock_perm));
    proof {
        let flushed_before = steps.view();
        let flushed_k = *krnl;
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        assert(thread_exit_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id)) by {
            thread_exit_flush_recorded_implies_flushed_step(&flush_snap, &flush_k, &flush_lctx, &flushed_k, cpu_id, container_ptr, process_ptr, thread_ptr, pagetable, pcid);
            thread_exit_trace_push(&*steps, flushed_before, start, pre, kernel_k_to_kernel_u(flush_snap), kernel_k_to_kernel_u(flushed_k), cpu_id);
        };
        assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable) == whole_pagetable(flush_k.pt_mp, flush_k.pt_lower.view(), pagetable)) by {
            old(krnl).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable);
            pagetable_lower_backup_wf_at(flush_k.pt_mp, flush_k.pt_lower.view(), pagetable); pagetable_lower_backup_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        };
        pagetable_perms_wf_at(krnl.pt_mp, pagetable);
        reveal(kernel_steps_prefix_unchanged);
    }
}

/// Reclaim the page of every held 4K leaf of the hidden, flushed page table, accumulating its quota as the thread's
/// pending refund, then refund that quota to the thread's container chain.
pub(super) fn thread_exit_reclaim_unmap_leaves(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    Ghost(container_ptr): Ghost<RwLockContainerPtr>, Ghost(process_ptr): Ghost<RwLockProcessPtr>, thread_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot,
    Ghost(cr3): Ghost<PageTableRoot>, Ghost(pcid): Ghost<Pcid>, Ghost(entry_k): Ghost<KernelK>,
    Ghost(entry_lctx): Ghost<LocalContext>, Ghost(pt_entry): Ghost<TypedHeldLock>, Ghost(entry_pt): Ghost<WholePageTable<PT_TYPE>>,
    Ghost(iommu_table): Ghost<Option<RwLockPageTableRoot>>, Ghost(table_lctx): Ghost<LocalContext>, Ghost(it_entry): Ghost<TypedHeldLock>, Ghost(locked_it): Ghost<LockCell<PageTable<IOMMU_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>>,
    Tracked(cpu_lock_perm): Tracked<&LockPerm>, Tracked(process_lock_perm): Tracked<&LockPerm>, Tracked(thread_lock_perm): Tracked<&LockPerm>,
    Tracked(pagetable_lock_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_inserted(&entry_lctx, &table_lctx, KernelObjId::PageTable(pagetable), pt_entry),
        iommu_table is Some ==> typed_lock_maps_inserted(&table_lctx, old(lctx), KernelObjId::IommuTable(iommu_table->Some_0), it_entry),
        iommu_table is None ==> typed_lock_maps_unchanged(&table_lctx, old(lctx)),
        pt_entry.mode == TypedLockMode::Write,
        it_entry.mode == TypedLockMode::Write,
        entry_k.prc_mp.spec_index(process_ptr).view().iommu_table == iommu_table,
        iommu_table is Some ==> locked_it.view().leaves_present() && locked_it.view().proc_ptr == process_ptr && locked_it.view().kernel_l4_end == 0,
        old(lctx).cpu_id() == cpu_id,
        old(lctx).thread_id() == entry_lctx.thread_id(),
        index_valid(NUM_CPUS, cpu_id),
        entry_lctx.cpu_lock_map().dom() =~= set![cpu_id],
        entry_lctx.container_lock_map().dom() =~= set![container_ptr],
        entry_lctx.process_lock_map().dom() =~= set![process_ptr],
        entry_lctx.thread_lock_map().dom() =~= set![thread_ptr],
        entry_lctx.page_lock_map().dom().is_empty(),
        entry_lctx.scheduler_lock_map().dom().is_empty(),
        entry_lctx.cpu_set_lock_map().dom().is_empty(),
        entry_lctx.pagetable_lock_map().dom().is_empty(),
        entry_lctx.pagetable_window_lock_map().dom().is_empty(),
        entry_lctx.holds_no_allocator_locks(PageSize::SZ4k),
        entry_lctx.holds_no_allocator_locks(PageSize::SZ2m),
        entry_lctx.holds_no_allocator_locks(PageSize::SZ1g),
        entry_lctx.pcid_needflush_lock_map().dom().is_empty(),
        entry_lctx.cpu_offline_flag_lock_map().dom().is_empty(),
        entry_lctx.endpoint_lock_map().dom().is_empty(),
        entry_lctx.pcid_allocator_lock_map().dom().is_empty(),
        entry_lctx.iommu_table_lock_map().dom().is_empty(),
        entry_lctx.iommu_root_table_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(entry_lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        process_lock_perm.state() is WriteLock,
        process_lock_perm.thread_id() == entry_lctx.thread_id(),
        process_lock_perm.lock_id() == entry_k.prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == entry_lctx.thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == entry_lctx.thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == entry_lctx.thread_id(),
        pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(steps).snapshot_k() == *old(krnl),
        thread_exit_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view() == entry_k.cpu_arr.spec_index(cpu_id).view().view(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == entry_k.cpu_arr.spec_index(cpu_id).view().locking_thread(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == entry_k.cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == entry_k.cpu_arr.spec_index(cpu_id).view().killer_info(),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cr3, pcid),
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr) == entry_k.ctn_mp.spec_index(container_ptr),
        entry_k.ctn_mp.dom().contains(container_ptr),
        entry_k.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
        entry_k.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().contains(thread_ptr),
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).prc_mp.spec_index(process_ptr) == entry_k.prc_mp.spec_index(process_ptr),
        entry_k.prc_mp.dom().contains(process_ptr),
        entry_k.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        entry_k.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() == 1,
        !entry_k.prc_mp.spec_index(process_ptr).view().zombie,
        entry_k.prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
        entry_k.prc_mp.spec_index(process_ptr).view_rodata().view().pcid == pcid,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == entry_k.thr_mp.spec_index(thread_ptr).locking_thread(),
        old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == entry_k.thr_mp.spec_index(thread_ptr).being_killed(),
        entry_k.thr_mp.dom().contains(thread_ptr),
        entry_k.thr_mp.spec_index(thread_ptr).inv(),
        entry_k.thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        entry_k.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        entry_k.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        entry_k.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable,
        entry_k.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        entry_k.thr_mp.spec_index(thread_ptr).view().caller is None,
        forall|j: int| #![trigger entry_k.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j]]
            0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> entry_k.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j] is None,
        entry_k.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        entry_k.thr_mp.spec_index(thread_ptr).view().container_depth <= MAX_CONTAINER_TREE_DEPTH,
        old(krnl).pt_mp.dom().contains(pagetable),
        iommu_table is Some ==> old(krnl).it_mp.dom().contains(iommu_table->Some_0) && old(krnl).it_mp.spec_index(iommu_table->Some_0) == locked_it,
        old(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..entry_k.thr_mp.spec_index(thread_ptr).view() }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: true }),
        0 <= start <= old(steps).view().len(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() is None,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks.dom() =~= Set::<WindowVa>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        forall|l4i: L4Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) is None,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_perms == entry_pt.lower.l2_perms,
        entry_pt.lower.hidden_l1_tables_in_locked_windows(),
        forall|p: PageMapPtr, i: L2Index| #![trigger entry_pt.lower.l2_owner(p, i)]
            entry_pt.lower.l2_perms.dom().contains(p) && pei_valid(i) ==> entry_pt.lower.l2_owner(p, i) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i)] #![trigger entry_pt.spec_held_2m_l2(l4i, l3i, l2i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i) == entry_pt.spec_held_2m_l2(l4i, l3i, l2i),
        entry_pt.kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        entry_pt.mapping_2m().dom() =~= Set::<VAddr>::empty(),
        entry_pt.wf_mapping_2m(),
        forall|l4i: L4Index, l3i: L3Index| #![trigger entry_pt.higher.spec_held_l3(l4i, l3i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && entry_pt.higher.spec_held_l3(l4i, l3i) is Some ==> entry_pt.higher.spec_resolve_mapping_l3(l4i, l3i) is Some,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        iommu_table is Some ==> typed_lock_maps_inserted(&table_lctx, final(lctx), KernelObjId::IommuTable(iommu_table->Some_0), it_entry),
        iommu_table is None ==> typed_lock_maps_unchanged(&table_lctx, final(lctx)),
        final(lctx).cpu_id() == cpu_id,
        final(lctx).thread_id() == entry_lctx.thread_id(),
        cpu_lock_perm.lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        final(steps).snapshot_k() == *final(krnl),
        thread_exit_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == entry_k.cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == entry_k.cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == entry_k.cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == entry_k.cpu_arr.spec_index(cpu_id).view().killer_info(),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cr3, pcid),
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr) == entry_k.ctn_mp.spec_index(container_ptr),
        final(krnl).prc_mp.dom().contains(process_ptr),
        final(krnl).prc_mp.spec_index(process_ptr) == entry_k.prc_mp.spec_index(process_ptr),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == entry_k.thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == entry_k.thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).pt_mp.dom().contains(pagetable),
        iommu_table is Some ==> final(krnl).it_mp.dom().contains(iommu_table->Some_0) && final(krnl).it_mp.spec_index(iommu_table->Some_0) == locked_it,
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..entry_k.thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: true }),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_1g().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks.dom() =~= Set::<WindowVa>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        final(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, l1i) is None,
        forall|l4i: L4Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i)] #![trigger entry_pt.spec_held_2m_l2(l4i, l3i, l2i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i) == entry_pt.spec_held_2m_l2(l4i, l3i, l2i),
{
    let mut indirect = [0usize; MAX_CONTAINER_TREE_DEPTH];
    let mut direct = 0usize;
    proof { assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); }; }
    let stopped_2m = reclaim_held_4k_leaves(krnl, pagetable, thread_ptr, cpu_id, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(pagetable_lock_perm),
        Tracked(thread_lock_perm));
    proof {
        // No user 2M leaf is held at lock time, and hiding and flushing keep the held 2M leaves, so the walk never stops at one.
        if let Some(s) = stopped_2m { entry_pt.higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(s.0, s.1); entry_pt.wf_mapping_2m_at(s.0, s.1, s.2); }
        assert(stopped_2m is None);
    }
    let ghost reclaimed_k = *krnl;
    proof { assert(entry_lctx.container_lock_map().dom().contains(container_ptr) && entry_lctx.process_lock_map().dom().contains(process_ptr) && entry_lctx.cpu_lock_map().dom().contains(cpu_id) && lctx.pagetable_lock_map().dom().contains(pagetable)); }
    let ghost refund_before = steps.view();
    proof { assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); }; }
    refund_unmap_4k_quota(krnl, thread_ptr, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm));
    proof {
        assert(krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() =~= entry_k.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view()) by { thread_perms_wf_at(krnl.thr_mp, thread_ptr); thread_perms_wf_at(old(krnl).thr_mp, thread_ptr); };
        thread_exit_trace_from_refund(&*steps, refund_before, start, pre, cpu_id, thread_ptr, process_ptr, container_ptr);
        assert(krnl.pt_mp.spec_index(pagetable) == reclaimed_k.pt_mp.spec_index(pagetable) && krnl.prc_mp.spec_index(process_ptr) == entry_k.prc_mp.spec_index(process_ptr)
            && krnl.ctn_mp.spec_index(container_ptr) == entry_k.ctn_mp.spec_index(container_ptr) && krnl.cpu_arr.spec_index(cpu_id) == steps.snapshot_k().cpu_arr.spec_index(cpu_id));
        assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable) == whole_pagetable(reclaimed_k.pt_mp, reclaimed_k.pt_lower.view(), pagetable));
    }
}


/// Remove every 4K leaf of the process's write-locked, detached IOMMU table, one IOMMU leaf step per leaf in index
/// order, accumulating the quota of its page as the thread's pending refund, then refund that quota to the thread's
/// container chain. The table has no DID, so no IOTLB entry caches a leaf and no leaf is hidden or flushed first.
pub(super) fn thread_exit_reclaim_iommu_leaves(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, Ghost(container_ptr): Ghost<RwLockContainerPtr>,
    Ghost(process_ptr): Ghost<RwLockProcessPtr>, thread_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot, Ghost(cr3): Ghost<PageTableRoot>, Ghost(pcid): Ghost<Pcid>,
    Ghost(entry_k): Ghost<KernelK>, Ghost(entry_lctx): Ghost<LocalContext>, Ghost(pt_entry): Ghost<TypedHeldLock>,
    Ghost(emptied_pt): Ghost<WholePageTable<PT_TYPE>>, iommu_table: RwLockPageTableRoot, Ghost(table_lctx): Ghost<LocalContext>, Ghost(it_entry): Ghost<TypedHeldLock>,
    Ghost(locked_it): Ghost<LockCell<PageTable<IOMMU_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>>, Tracked(cpu_lock_perm): Tracked<&LockPerm>, Tracked(process_lock_perm): Tracked<&LockPerm>,
    Tracked(thread_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>, Tracked(iommu_table_lock_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>,
    Ghost(pre): Ghost<KernelU>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_inserted(&entry_lctx, &table_lctx, KernelObjId::PageTable(pagetable), pt_entry),
        typed_lock_maps_inserted(&table_lctx, old(lctx), KernelObjId::IommuTable(iommu_table), it_entry),
        pt_entry.mode == TypedLockMode::Write,
        it_entry.mode == TypedLockMode::Write,
        entry_k.prc_mp.spec_index(process_ptr).view().iommu_table == Some(iommu_table),
        locked_it.view().leaves_present(),
        locked_it.view().kernel_l4_end == 0,
        locked_it.view().did is None,
        old(lctx).cpu_id() == cpu_id,
        old(lctx).thread_id() == entry_lctx.thread_id(),
        index_valid(NUM_CPUS, cpu_id),
        entry_lctx.cpu_lock_map().dom() =~= set![cpu_id],
        entry_lctx.container_lock_map().dom() =~= set![container_ptr],
        entry_lctx.process_lock_map().dom() =~= set![process_ptr],
        entry_lctx.thread_lock_map().dom() =~= set![thread_ptr],
        entry_lctx.page_lock_map().dom().is_empty(),
        entry_lctx.scheduler_lock_map().dom().is_empty(),
        entry_lctx.cpu_set_lock_map().dom().is_empty(),
        entry_lctx.pagetable_lock_map().dom().is_empty(),
        entry_lctx.pagetable_window_lock_map().dom().is_empty(),
        entry_lctx.holds_no_allocator_locks(PageSize::SZ4k),
        entry_lctx.holds_no_allocator_locks(PageSize::SZ2m),
        entry_lctx.holds_no_allocator_locks(PageSize::SZ1g),
        entry_lctx.pcid_needflush_lock_map().dom().is_empty(),
        entry_lctx.cpu_offline_flag_lock_map().dom().is_empty(),
        entry_lctx.endpoint_lock_map().dom().is_empty(),
        entry_lctx.pcid_allocator_lock_map().dom().is_empty(),
        entry_lctx.iommu_table_lock_map().dom().is_empty(),
        entry_lctx.iommu_root_table_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(entry_lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        process_lock_perm.state() is WriteLock,
        process_lock_perm.thread_id() == entry_lctx.thread_id(),
        process_lock_perm.lock_id() == entry_k.prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == entry_lctx.thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == entry_lctx.thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == entry_lctx.thread_id(),
        pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(steps).snapshot_k() == *old(krnl),
        thread_exit_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view() == entry_k.cpu_arr.spec_index(cpu_id).view().view(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == entry_k.cpu_arr.spec_index(cpu_id).view().locking_thread(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == entry_k.cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == entry_k.cpu_arr.spec_index(cpu_id).view().killer_info(),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cr3, pcid),
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr) == entry_k.ctn_mp.spec_index(container_ptr),
        entry_k.ctn_mp.dom().contains(container_ptr),
        entry_k.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
        entry_k.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().contains(thread_ptr),
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).prc_mp.spec_index(process_ptr) == entry_k.prc_mp.spec_index(process_ptr),
        entry_k.prc_mp.dom().contains(process_ptr),
        entry_k.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        entry_k.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() == 1,
        !entry_k.prc_mp.spec_index(process_ptr).view().zombie,
        entry_k.prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
        entry_k.prc_mp.spec_index(process_ptr).view_rodata().view().pcid == pcid,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == entry_k.thr_mp.spec_index(thread_ptr).locking_thread(),
        old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == entry_k.thr_mp.spec_index(thread_ptr).being_killed(),
        entry_k.thr_mp.dom().contains(thread_ptr),
        entry_k.thr_mp.spec_index(thread_ptr).inv(),
        entry_k.thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        entry_k.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        entry_k.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        entry_k.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable,
        entry_k.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        entry_k.thr_mp.spec_index(thread_ptr).view().caller is None,
        forall|j: int| #![trigger entry_k.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j]]
            0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> entry_k.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j] is None,
        entry_k.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        entry_k.thr_mp.spec_index(thread_ptr).view().container_depth <= MAX_CONTAINER_TREE_DEPTH,
        old(krnl).pt_mp.dom().contains(pagetable),
        old(krnl).it_mp.dom().contains(iommu_table),
        old(krnl).it_mp.spec_index(iommu_table) == locked_it,
        old(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..entry_k.thr_mp.spec_index(thread_ptr).view() }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: true }),
        0 <= start <= old(steps).view().len(),
        iommu_table_lock_perm.state() is WriteLock,
        iommu_table_lock_perm.thread_id() == entry_lctx.thread_id(),
        iommu_table_lock_perm.lock_id() == locked_it.locking_thread()->Write_lock_id,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() is None,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable) == emptied_pt,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_inserted(&table_lctx, final(lctx), KernelObjId::IommuTable(iommu_table), it_entry),
        final(lctx).cpu_id() == cpu_id,
        final(lctx).thread_id() == entry_lctx.thread_id(),
        cpu_lock_perm.lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        final(steps).snapshot_k() == *final(krnl),
        thread_exit_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == entry_k.cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == entry_k.cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == entry_k.cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == entry_k.cpu_arr.spec_index(cpu_id).view().killer_info(),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cr3, pcid),
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr) == entry_k.ctn_mp.spec_index(container_ptr),
        final(krnl).prc_mp.dom().contains(process_ptr),
        final(krnl).prc_mp.spec_index(process_ptr) == entry_k.prc_mp.spec_index(process_ptr),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == entry_k.thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == entry_k.thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).it_mp.dom().contains(iommu_table),
        final(krnl).it_mp.spec_index(iommu_table).locking_thread() == locked_it.locking_thread(),
        final(krnl).it_mp.spec_index(iommu_table).view().leaves_present(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger final(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> !final(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..entry_k.thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: true }),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable) == emptied_pt,
{
    proof { iommu_table_perms_wf_map(krnl.it_mp); iommu_table_perms_wf_at(krnl.it_mp, iommu_table); }
    let mut indirect = [0usize; MAX_CONTAINER_TREE_DEPTH];
    let mut direct = 0usize;
    let mut cursor: (L4Index, L3Index, L2Index, L1Index) = (0, 0, 0, 0);
    let mut found = krnl.it_mp.borrow_typed(iommu_table, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_table_lock_perm)).next_mapped_4k_from(cursor);
    while found.is_some()
        invariant
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_inserted(&entry_lctx, &table_lctx, KernelObjId::PageTable(pagetable), pt_entry),
            typed_lock_maps_inserted(&table_lctx, lctx, KernelObjId::IommuTable(iommu_table), it_entry),
            pt_entry.mode == TypedLockMode::Write,
            it_entry.mode == TypedLockMode::Write,
            typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
            entry_k.prc_mp.spec_index(process_ptr).view().iommu_table == Some(iommu_table),
            locked_it.view().leaves_present(),
            locked_it.view().kernel_l4_end == 0,
            lctx.cpu_id() == cpu_id,
            lctx.thread_id() == entry_lctx.thread_id(),
            index_valid(NUM_CPUS, cpu_id),
            entry_lctx.cpu_lock_map().dom() =~= set![cpu_id],
            entry_lctx.container_lock_map().dom() =~= set![container_ptr],
            entry_lctx.process_lock_map().dom() =~= set![process_ptr],
            entry_lctx.thread_lock_map().dom() =~= set![thread_ptr],
            entry_lctx.page_lock_map().dom().is_empty(),
            entry_lctx.scheduler_lock_map().dom().is_empty(),
            entry_lctx.cpu_set_lock_map().dom().is_empty(),
            entry_lctx.pagetable_lock_map().dom().is_empty(),
            entry_lctx.pagetable_window_lock_map().dom().is_empty(),
            entry_lctx.holds_no_allocator_locks(PageSize::SZ4k),
            entry_lctx.holds_no_allocator_locks(PageSize::SZ2m),
            entry_lctx.holds_no_allocator_locks(PageSize::SZ1g),
            entry_lctx.pcid_needflush_lock_map().dom().is_empty(),
            entry_lctx.cpu_offline_flag_lock_map().dom().is_empty(),
            entry_lctx.endpoint_lock_map().dom().is_empty(),
            entry_lctx.pcid_allocator_lock_map().dom().is_empty(),
            entry_lctx.iommu_table_lock_map().dom().is_empty(),
            entry_lctx.iommu_root_table_lock_map().dom().is_empty(),
            typed_lock_map_contains_mode(entry_lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
            typed_lock_map_contains_mode(entry_lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(entry_lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(entry_lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
            process_lock_perm.state() is WriteLock,
            process_lock_perm.thread_id() == entry_lctx.thread_id(),
            process_lock_perm.lock_id() == entry_k.prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
            cpu_lock_perm.state() is WriteLock,
            cpu_lock_perm.thread_id() == entry_lctx.thread_id(),
            cpu_lock_perm.lock_id() == krnl.cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == entry_lctx.thread_id(),
            thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            pagetable_lock_perm.state() is WriteLock,
            pagetable_lock_perm.thread_id() == entry_lctx.thread_id(),
            pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
            steps.snapshot_k() == *krnl,
            thread_exit_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id),
            krnl.cpu_arr.spec_index(cpu_id).view().view() == entry_k.cpu_arr.spec_index(cpu_id).view().view(),
            krnl.cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() is None,
            krnl.cpu_arr.spec_index(cpu_id).view().locking_thread() == entry_k.cpu_arr.spec_index(cpu_id).view().locking_thread(),
            krnl.cpu_arr.spec_index(cpu_id).view().being_killed() == entry_k.cpu_arr.spec_index(cpu_id).view().being_killed(),
            krnl.cpu_arr.spec_index(cpu_id).view().killer_info() == entry_k.cpu_arr.spec_index(cpu_id).view().killer_info(),
            entry_k.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
            entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
            entry_k.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
            entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
            entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
            krnl.cpu_hw_cr3_pcid[cpu_id as int].view() == (cr3, pcid),
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            pcid != KERNEL_DEFAULT_PCID,
            krnl.ctn_mp.dom().contains(container_ptr),
            krnl.ctn_mp.spec_index(container_ptr) == entry_k.ctn_mp.spec_index(container_ptr),
            entry_k.ctn_mp.dom().contains(container_ptr),
            entry_k.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
            entry_k.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().contains(thread_ptr),
            krnl.prc_mp.dom().contains(process_ptr),
            krnl.prc_mp.spec_index(process_ptr) == entry_k.prc_mp.spec_index(process_ptr),
            entry_k.prc_mp.dom().contains(process_ptr),
            entry_k.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            entry_k.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() == 1,
            !entry_k.prc_mp.spec_index(process_ptr).view().zombie,
            entry_k.prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
            entry_k.prc_mp.spec_index(process_ptr).view_rodata().view().pcid == pcid,
            krnl.thr_mp.dom().contains(thread_ptr),
            krnl.thr_mp.spec_index(thread_ptr).locking_thread() == entry_k.thr_mp.spec_index(thread_ptr).locking_thread(),
            krnl.thr_mp.spec_index(thread_ptr).being_killed() == entry_k.thr_mp.spec_index(thread_ptr).being_killed(),
            entry_k.thr_mp.dom().contains(thread_ptr),
            entry_k.thr_mp.spec_index(thread_ptr).inv(),
            entry_k.thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
            entry_k.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
            entry_k.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            entry_k.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable,
            entry_k.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            entry_k.thr_mp.spec_index(thread_ptr).view().caller is None,
            forall|j: int| #![trigger entry_k.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j]]
                0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> entry_k.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j] is None,
            entry_k.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            entry_k.thr_mp.spec_index(thread_ptr).view().container_depth <= MAX_CONTAINER_TREE_DEPTH,
            krnl.pt_mp.dom().contains(pagetable),
            krnl.it_mp.dom().contains(iommu_table),
            krnl.thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
            krnl.thr_mp.spec_index(thread_ptr).view() == (Thread {
                direct_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k, indirect_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k,
                syscall_progress: krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..entry_k.thr_mp.spec_index(thread_ptr).view()
            }),
            krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: true }),
            direct == krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
            forall|d: int| #![trigger indirect[d]] #![trigger krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d)] 0 <= d < krnl.thr_mp.spec_index(thread_ptr).view().container_depth
                ==> indirect[d] == krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
            0 <= start <= old(steps).view().len() <= steps.view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            iommu_table_lock_perm.state() is WriteLock,
            iommu_table_lock_perm.thread_id() == entry_lctx.thread_id(),
            iommu_table_lock_perm.lock_id() == locked_it.locking_thread()->Write_lock_id,
            krnl.it_mp.spec_index(iommu_table).locking_thread() == locked_it.locking_thread(),
            krnl.it_mp.spec_index(iommu_table).view().mapping_2m() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_2m(),
            krnl.it_mp.spec_index(iommu_table).view().mapping_1g() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_1g(),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                    ==> krnl.it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
            krnl.it_mp.spec_index(iommu_table).view().kernel_l4_end == 0,
            krnl.it_mp.spec_index(iommu_table).view().did is None,
            pei_valid(cursor.0),
            pei_valid(cursor.1),
            pei_valid(cursor.2),
            cursor.3 <= 512,
            found is Some ==> {
                let next = found->Some_0;
                &&& pei_valid(next.0)
                &&& pei_valid(next.1)
                &&& pei_valid(next.2)
                &&& pei_valid(next.3)
                &&& spec_l4_index_path_le(cursor, next)
                &&& krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va(next))
            },
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && !spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i)) ==> !krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i))
                    && (found is None || !spec_l4_index_path_le(found->Some_0, (l4i, l3i, l2i, l1i))) ==> !krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
            whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable) == emptied_pt,
        decreases 512 - cursor.0, 512 - cursor.1, 512 - cursor.2, 513 - cursor.3,
    {
        let found_next = found.unwrap();
        let next = (found_next.0, found_next.1, found_next.2, found_next.3);
        let ghost leaf_k = *krnl;
        let ghost leaf_before = steps.view();
        proof { assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); }; }
        reclaim_detached_iommu_4k_page(krnl, iommu_table, next, thread_ptr, cpu_id, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(iommu_table_lock_perm),
            Tracked(thread_lock_perm));
        proof {
            let leaf_pre = steps.snapshot_k();
            let leaf_post = *krnl;
            assert(leaf_k.it_mp.spec_index(iommu_table).view().proc_ptr == process_ptr && leaf_post.it_mp.spec_index(iommu_table).view().proc_ptr == process_ptr) by { process_iommu_table_match_process_at(leaf_post.prc_mp, leaf_post.it_mp, process_ptr); };
            thread_exit_iommu_leaf_step_from_k(&leaf_pre, &leaf_post, &*lctx, cpu_id, container_ptr, process_ptr, thread_ptr, pagetable, iommu_table, spec_index2va(next));
            krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
            thread_exit_trace_push(&*steps, leaf_before, start, pre, kernel_k_to_kernel_u(leaf_pre), kernel_k_to_kernel_u(leaf_post), cpu_id);
        }
        cursor = (next.0, next.1, next.2, next.3 + 1);
        proof { index_path_successor_implies_path_le_drops_only_predecessor(next, cursor); iommu_table_perms_wf_map(krnl.it_mp); iommu_table_perms_wf_at(krnl.it_mp, iommu_table); }
        found = krnl.it_mp.borrow_typed(iommu_table, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_table_lock_perm)).next_mapped_4k_from(cursor);
    }
    proof { assert(krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom() =~= Set::<VAddr>::empty()) by { iommu_table_perms_wf_at(krnl.it_mp, iommu_table); broadcast use iova_4k_valid_index_roundtrip; }; }
    let ghost reclaimed_it = krnl.it_mp.spec_index(iommu_table);
    let ghost reclaimed_k = *krnl;
    let ghost refund_before = steps.view();
    proof { assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); }; }
    refund_unmap_4k_quota(krnl, thread_ptr, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm));
    proof {
        assert(krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() =~= entry_k.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view()) by { thread_perms_wf_at(krnl.thr_mp, thread_ptr); thread_perms_wf_at(old(krnl).thr_mp, thread_ptr); };
        thread_exit_trace_from_refund(&*steps, refund_before, start, pre, cpu_id, thread_ptr, process_ptr, container_ptr);
        assert(krnl.pt_mp.spec_index(pagetable) == reclaimed_k.pt_mp.spec_index(pagetable) && krnl.it_mp.spec_index(iommu_table) == reclaimed_it && krnl.prc_mp.spec_index(process_ptr) == entry_k.prc_mp.spec_index(process_ptr)
            && krnl.ctn_mp.spec_index(container_ptr) == entry_k.ctn_mp.spec_index(container_ptr) && krnl.cpu_arr.spec_index(cpu_id) == steps.snapshot_k().cpu_arr.spec_index(cpu_id));
    }
}

/// Return the thread's and the process's quota of every size to their container, then mark the process as having
/// emptied its tables and unlock the reclaimed IOMMU table and page table.
pub(super) fn thread_exit_reclaim_return_quota(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, container_ptr: RwLockContainerPtr,
    process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot, Ghost(cr3): Ghost<PageTableRoot>, Ghost(pcid): Ghost<Pcid>,
    Ghost(entry_k): Ghost<KernelK>, Ghost(entry_lctx): Ghost<LocalContext>,
    Ghost(pt_entry): Ghost<TypedHeldLock>, Ghost(entry_pt): Ghost<WholePageTable<PT_TYPE>>, Ghost(emptied_pt): Ghost<WholePageTable<PT_TYPE>>, iommu_table: Option<RwLockPageTableRoot>, Ghost(table_lctx): Ghost<LocalContext>,
    Ghost(it_entry): Ghost<TypedHeldLock>, Tracked(cpu_lock_perm): Tracked<&LockPerm>, Tracked(process_lock_perm): Tracked<&LockPerm>, Tracked(thread_lock_perm): Tracked<&LockPerm>,
    Tracked(pagetable_lock_perm): Tracked<LockPerm>, Tracked(iommu_table_lock_perm): Tracked<Option<LockPerm>>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_inserted(&entry_lctx, &table_lctx, KernelObjId::PageTable(pagetable), pt_entry),
        iommu_table is Some ==> typed_lock_maps_inserted(&table_lctx, old(lctx), KernelObjId::IommuTable(iommu_table->Some_0), it_entry),
        iommu_table is None ==> typed_lock_maps_unchanged(&table_lctx, old(lctx)),
        pt_entry.mode == TypedLockMode::Write,
        it_entry.mode == TypedLockMode::Write,
        entry_k.prc_mp.spec_index(process_ptr).view().iommu_table == iommu_table,
        old(lctx).cpu_id() == cpu_id,
        old(lctx).thread_id() == entry_lctx.thread_id(),
        index_valid(NUM_CPUS, cpu_id),
        entry_lctx.cpu_lock_map().dom() =~= set![cpu_id],
        entry_lctx.container_lock_map().dom() =~= set![container_ptr],
        entry_lctx.process_lock_map().dom() =~= set![process_ptr],
        entry_lctx.thread_lock_map().dom() =~= set![thread_ptr],
        entry_lctx.page_lock_map().dom().is_empty(),
        entry_lctx.scheduler_lock_map().dom().is_empty(),
        entry_lctx.cpu_set_lock_map().dom().is_empty(),
        entry_lctx.pagetable_lock_map().dom().is_empty(),
        entry_lctx.pagetable_window_lock_map().dom().is_empty(),
        entry_lctx.holds_no_allocator_locks(PageSize::SZ4k),
        entry_lctx.holds_no_allocator_locks(PageSize::SZ2m),
        entry_lctx.holds_no_allocator_locks(PageSize::SZ1g),
        entry_lctx.pcid_needflush_lock_map().dom().is_empty(),
        entry_lctx.cpu_offline_flag_lock_map().dom().is_empty(),
        entry_lctx.endpoint_lock_map().dom().is_empty(),
        entry_lctx.pcid_allocator_lock_map().dom().is_empty(),
        entry_lctx.iommu_table_lock_map().dom().is_empty(),
        entry_lctx.iommu_root_table_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(entry_lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        process_lock_perm.state() is WriteLock,
        process_lock_perm.thread_id() == entry_lctx.thread_id(),
        process_lock_perm.lock_id() == entry_k.prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == entry_lctx.thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == entry_lctx.thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == entry_lctx.thread_id(),
        pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(steps).snapshot_k() == *old(krnl),
        thread_exit_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view() == entry_k.cpu_arr.spec_index(cpu_id).view().view(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == entry_k.cpu_arr.spec_index(cpu_id).view().locking_thread(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == entry_k.cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == entry_k.cpu_arr.spec_index(cpu_id).view().killer_info(),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cr3, pcid),
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr) == entry_k.ctn_mp.spec_index(container_ptr),
        entry_k.ctn_mp.dom().contains(container_ptr),
        entry_k.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
        entry_k.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().contains(thread_ptr),
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).prc_mp.spec_index(process_ptr) == entry_k.prc_mp.spec_index(process_ptr),
        entry_k.prc_mp.dom().contains(process_ptr),
        entry_k.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        entry_k.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() == 1,
        !entry_k.prc_mp.spec_index(process_ptr).view().zombie,
        !entry_k.prc_mp.spec_index(process_ptr).being_killed(),
        entry_k.prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
        entry_k.prc_mp.spec_index(process_ptr).view_rodata().view().pcid == pcid,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == entry_k.thr_mp.spec_index(thread_ptr).locking_thread(),
        old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == entry_k.thr_mp.spec_index(thread_ptr).being_killed(),
        entry_k.thr_mp.dom().contains(thread_ptr),
        entry_k.thr_mp.spec_index(thread_ptr).inv(),
        entry_k.thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        entry_k.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        entry_k.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        entry_k.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable,
        entry_k.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        entry_k.thr_mp.spec_index(thread_ptr).view().caller is None,
        forall|j: int| #![trigger entry_k.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j]]
            0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> entry_k.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j] is None,
        entry_k.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        entry_k.thr_mp.spec_index(thread_ptr).view().container_depth <= MAX_CONTAINER_TREE_DEPTH,
        old(krnl).pt_mp.dom().contains(pagetable),
        old(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..entry_k.thr_mp.spec_index(thread_ptr).view() }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: true }),
        0 <= start <= old(steps).view().len(),
        (iommu_table_lock_perm is Some) == (iommu_table is Some),
        iommu_table is Some ==> {
            let it = old(krnl).it_mp.spec_index(iommu_table->Some_0);
            &&& old(krnl).it_mp.dom().contains(iommu_table->Some_0)
            &&& it.view().leaves_present()
            &&& iommu_table_lock_perm->Some_0.state() is WriteLock
            &&& iommu_table_lock_perm->Some_0.thread_id() == entry_lctx.thread_id()
            &&& iommu_table_lock_perm->Some_0.lock_id() == it.locking_thread()->Write_lock_id
        },
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger old(krnl).it_mp.spec_index(iommu_table->Some_0).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            iommu_table is Some && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> !old(krnl).it_mp.spec_index(iommu_table->Some_0).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() is None,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable) == emptied_pt,
        emptied_pt.mapping_4k().dom() =~= Set::<VAddr>::empty(),
        emptied_pt.mapping_2m().dom() =~= Set::<VAddr>::empty(),
        emptied_pt.mapping_1g().dom() =~= Set::<VAddr>::empty(),
        emptied_pt.lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        emptied_pt.higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
        emptied_pt.kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        emptied_pt.lower.hidden_l1_tables_in_locked_windows(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger emptied_pt.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> emptied_pt.spec_held_4k_l1(l4i, l3i, l2i, l1i) is None,
        forall|l4i: L4Index| #![trigger emptied_pt.spec_resolve_mapping_l4(l4i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) ==> emptied_pt.spec_resolve_mapping_l4(l4i) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger emptied_pt.spec_held_2m_l2(l4i, l3i, l2i)] #![trigger entry_pt.spec_held_2m_l2(l4i, l3i, l2i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> emptied_pt.spec_held_2m_l2(l4i, l3i, l2i) == entry_pt.spec_held_2m_l2(l4i, l3i, l2i),
        entry_pt.kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        entry_pt.mapping_2m().dom() =~= Set::<VAddr>::empty(),
        entry_pt.wf_mapping_2m(),
        forall|l4i: L4Index, l3i: L3Index| #![trigger entry_pt.higher.spec_held_l3(l4i, l3i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && entry_pt.higher.spec_held_l3(l4i, l3i) is Some ==> entry_pt.higher.spec_resolve_mapping_l3(l4i, l3i) is Some,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(&entry_lctx, final(lctx)),
        final(lctx).cpu_id() == cpu_id,
        final(lctx).thread_id() == entry_lctx.thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        thread_exit_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cr3, pcid),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == entry_k.cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == entry_k.cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == entry_k.cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == entry_k.cpu_arr.spec_index(cpu_id).view().killer_info(),
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr) == entry_k.ctn_mp.spec_index(container_ptr),
        final(krnl).prc_mp.dom().contains(process_ptr),
        final(krnl).prc_mp.spec_index(process_ptr).view() == (Process { state: Ghost(ProcessState::TablesEmptied), quota_4k: 0, quota_2m: 0, quota_1g: 0, ..entry_k.prc_mp.spec_index(process_ptr).view() }),
        final(krnl).prc_mp.spec_index(process_ptr).view_rodata() == entry_k.prc_mp.spec_index(process_ptr).view_rodata(),
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost() == entry_k.prc_mp.spec_index(process_ptr).view_ghost(),
        final(krnl).prc_mp.spec_index(process_ptr).locking_thread() == entry_k.prc_mp.spec_index(process_ptr).locking_thread(),
        final(krnl).prc_mp.spec_index(process_ptr).being_killed() == entry_k.prc_mp.spec_index(process_ptr).being_killed(),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { quota_4k: 0, quota_2m: 0, quota_1g: 0, syscall_progress: Ghost(Some(SyscallProgress::ThreadExitZombie)), ..entry_k.thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == entry_k.thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == entry_k.thr_mp.spec_index(thread_ptr).being_killed(),
{
    let ghost reclaimed_it = krnl.it_mp.spec_index(iommu_table->Some_0);
    proof {
        if iommu_table is Some {
            assert(reclaimed_it.view().mapping_4k().dom() =~= Set::<VAddr>::empty()) by {
                iommu_table_perms_wf_at(krnl.it_mp, iommu_table->Some_0);
                broadcast use iova_4k_valid_index_roundtrip;
            };
        }
    }
    thread_exit_reclaim_return_quota_size(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, process_ptr, thread_ptr, pagetable, Ghost(iommu_table), PageSize::SZ4k,
        Tracked(process_lock_perm), Tracked(thread_lock_perm), Ghost(start), Ghost(pre));
    thread_exit_reclaim_return_quota_size(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, process_ptr, thread_ptr, pagetable, Ghost(iommu_table), PageSize::SZ2m,
        Tracked(process_lock_perm), Tracked(thread_lock_perm), Ghost(start), Ghost(pre));
    thread_exit_reclaim_return_quota_size(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, process_ptr, thread_ptr, pagetable, Ghost(iommu_table), PageSize::SZ1g,
        Tracked(process_lock_perm), Tracked(thread_lock_perm), Ghost(start), Ghost(pre));
    thread_exit_reclaim_release_tables(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, process_ptr, thread_ptr, pagetable, iommu_table, Ghost(entry_lctx),
        Ghost(table_lctx), Ghost(pt_entry), Ghost(it_entry), Ghost(entry_pt), Ghost(emptied_pt), Tracked(process_lock_perm), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm),
        Tracked(iommu_table_lock_perm), Ghost(start), Ghost(pre));
}
} // verus!
