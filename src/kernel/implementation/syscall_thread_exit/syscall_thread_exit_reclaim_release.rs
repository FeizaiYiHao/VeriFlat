use vstd::prelude::*;
use crate::*;
use super::syscall_thread_exit_spec::*;
use super::syscall_thread_exit_trace::*;
use super::syscall_thread_exit_quota::thread_exit_return_quota;

verus! {
/// Flush the process's PCID from every cpu once, then record the flush.
pub(super) fn thread_exit_reclaim_flush(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    Ghost(container_ptr): Ghost<RwLockContainerPtr>, Ghost(process_ptr): Ghost<RwLockProcessPtr>, thread_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot,
    cr3: PageTableRoot, pcid: Pcid, Ghost(kernel_l4_end): Ghost<usize>, Ghost(start_l4): Ghost<L4Index>, Ghost(entry_k): Ghost<KernelK>,
    Ghost(entry_lctx): Ghost<LocalContext>, Ghost(pt_entry): Ghost<TypedHeldLock>, Ghost(locked_pt): Ghost<PageTable<PT_TYPE>>,
    Ghost(iommu_table): Ghost<Option<RwLockPageTableRoot>>, Ghost(table_lctx): Ghost<LocalContext>, Ghost(it_entry): Ghost<TypedHeldLock>, Ghost(locked_it): Ghost<RwLock<PageTable<IOMMU_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>>,
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
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        old(krnl).cpu_published[cpu_id as int].view() == (cr3, pcid),
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
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
        old(krnl).pt_mp.spec_index(pagetable).view().mapping_2m() == locked_pt.mapping_2m(),
        old(krnl).pt_mp.spec_index(pagetable).view().mapping_1g() == locked_pt.mapping_1g(),
        locked_pt.leaves_present(),
        kernel_l4_end <= start_l4,
        KERNEL_MEM_END_L4INDEX <= start_l4,
        start_l4 == kernel_l4_end || start_l4 == KERNEL_MEM_END_L4INDEX,
        pei_valid(start_l4),
        forall|va: VAddr| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)]
            old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va) && !old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..entry_k.thr_mp.spec_index(thread_ptr).view() }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: false }),
        0 <= start <= old(steps).view().len(),
        forall|va: VAddr| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)]
            spec_va_4k_valid(va) && kernel_l4_end <= spec_v2l4index(va) && old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va) ==> !old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                ==> !old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
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
        final(krnl).cpu_published[cpu_id as int].view() == (cr3, pcid),
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr) == entry_k.ctn_mp.spec_index(container_ptr),
        final(krnl).prc_mp.dom().contains(process_ptr),
        final(krnl).prc_mp.spec_index(process_ptr) == entry_k.prc_mp.spec_index(process_ptr),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == entry_k.thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == entry_k.thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).pt_mp.dom().contains(pagetable),
        iommu_table is Some ==> final(krnl).it_mp.dom().contains(iommu_table->Some_0) && final(krnl).it_mp.spec_index(iommu_table->Some_0) == locked_it,
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_2m() == locked_pt.mapping_2m(),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_1g() == locked_pt.mapping_1g(),
        forall|va: VAddr| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)]
            final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va) && !final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..entry_k.thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: true }),
        old(steps).view().len() <= final(steps).view().len(),
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pagetable, final(krnl).pt_mp.spec_index(pagetable).view()),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                ==> !final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    let ghost flush_before = steps.view();
    let ghost flush_entry = kernel_k_to_kernel_u(*krnl);
    proof {
        assert(thread_exit_flush_step_pre(flush_entry, cpu_id) && flush_entry.cpu_array[cpu_id as int].current_thread == Some(thread_ptr) && flush_entry.thread_map[thread_ptr].owning_proc == process_ptr
            && flush_entry.thread_map[thread_ptr].owning_container == container_ptr && flush_entry.process_map[process_ptr].pcid == pcid) by {
            kernel_write_held_context_projection(&*krnl, &*lctx, cpu_id, process_ptr, thread_ptr, None);
            kernel_pagetable_user_4k_unmapped_projection_at(&*krnl, process_ptr);
            thread_exit_flush_step_pre_from_u(flush_entry, cpu_id, thread_ptr);
        };
    }
    flush_pagetable_tlbs(krnl, pagetable, cr3, pcid, cpu_id, thread_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(cpu_lock_perm));
    proof {
        thread_exit_trace_from_tlb_flush(&*steps, flush_before, start, pre, flush_entry, cpu_id, thread_ptr, process_ptr, container_ptr, pcid);
        use_type_invariant(&*steps);
        assert(entry_lctx.container_lock_map().dom().contains(container_ptr) && entry_lctx.process_lock_map().dom().contains(process_ptr)
            && entry_lctx.thread_lock_map().dom().contains(thread_ptr) && lctx.pagetable_lock_map().dom().contains(pagetable));
        assert(thread_exit_flush_step_pre(steps.snapshot_u(), cpu_id) && steps.snapshot_u().cpu_array[cpu_id as int].current_thread == Some(thread_ptr)) by {
            kernel_write_held_context_projection(&*krnl, &*lctx, cpu_id, process_ptr, thread_ptr, None);
            kernel_pagetable_user_4k_unmapped_projection_at(&*krnl, process_ptr);
            thread_exit_flush_step_pre_from_u(steps.snapshot_u(), cpu_id, thread_ptr);
        };
    }
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::ThreadExitReclaim { flushed: true })), Tracked(&*lctx), Tracked(thread_lock_perm));
    proof {
        let flushed_before = steps.view();
        let flushed_pre = steps.snapshot_u();
        let flushed_k = *krnl;
        assert(thread_exit_flushed_step(flushed_pre, kernel_k_to_kernel_u(flushed_k), cpu_id)) by {
            kernel_thread_syscall_progress_changed_implies_u_step(&steps.snapshot_k(), &flushed_k, thread_ptr);
            thread_exit_flushed_step_from_u(flushed_pre, kernel_k_to_kernel_u(flushed_k), cpu_id, thread_ptr);
        };
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        thread_exit_trace_push(&*steps, flushed_before, start, pre, flushed_pre, kernel_k_to_kernel_u(flushed_k), cpu_id);
        pagetable_perms_wf_at(krnl.pt_mp, pagetable);
    }
}

/// Unmap every cleared leaf of the locked page table, accumulating the quota of its page as the thread's pending refund,
/// then refund that quota to the thread's container chain.
pub(super) fn thread_exit_reclaim_unmap_leaves(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    Ghost(container_ptr): Ghost<RwLockContainerPtr>, Ghost(process_ptr): Ghost<RwLockProcessPtr>, thread_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot,
    Ghost(cr3): Ghost<PageTableRoot>, Ghost(pcid): Ghost<Pcid>, Ghost(kernel_l4_end): Ghost<usize>, start_l4: L4Index, Ghost(entry_k): Ghost<KernelK>,
    Ghost(entry_lctx): Ghost<LocalContext>, Ghost(pt_entry): Ghost<TypedHeldLock>, Ghost(locked_pt): Ghost<PageTable<PT_TYPE>>,
    Ghost(iommu_table): Ghost<Option<RwLockPageTableRoot>>, Ghost(table_lctx): Ghost<LocalContext>, Ghost(it_entry): Ghost<TypedHeldLock>, Ghost(locked_it): Ghost<RwLock<PageTable<IOMMU_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>>,
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
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        old(krnl).cpu_published[cpu_id as int].view() == (cr3, pcid),
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
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
        old(krnl).pt_mp.spec_index(pagetable).view().mapping_2m() == locked_pt.mapping_2m(),
        old(krnl).pt_mp.spec_index(pagetable).view().mapping_1g() == locked_pt.mapping_1g(),
        locked_pt.leaves_present(),
        kernel_l4_end <= start_l4,
        KERNEL_MEM_END_L4INDEX <= start_l4,
        start_l4 == kernel_l4_end || start_l4 == KERNEL_MEM_END_L4INDEX,
        pei_valid(start_l4),
        forall|va: VAddr| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)]
            old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va) && !old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
        old(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..entry_k.thr_mp.spec_index(thread_ptr).view() }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: true }),
        0 <= start <= old(steps).view().len(),
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pagetable, old(krnl).pt_mp.spec_index(pagetable).view()),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                ==> !old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
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
        final(krnl).cpu_published[cpu_id as int].view() == (cr3, pcid),
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr) == entry_k.ctn_mp.spec_index(container_ptr),
        final(krnl).prc_mp.dom().contains(process_ptr),
        final(krnl).prc_mp.spec_index(process_ptr) == entry_k.prc_mp.spec_index(process_ptr),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == entry_k.thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == entry_k.thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).pt_mp.dom().contains(pagetable),
        iommu_table is Some ==> final(krnl).it_mp.dom().contains(iommu_table->Some_0) && final(krnl).it_mp.spec_index(iommu_table->Some_0) == locked_it,
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_2m() == locked_pt.mapping_2m(),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_1g() == locked_pt.mapping_1g(),
        forall|va: VAddr| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)]
            final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va) && !final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..entry_k.thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: true }),
        old(steps).view().len() <= final(steps).view().len(),
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pagetable, final(krnl).pt_mp.spec_index(pagetable).view()),
        forall|va: VAddr| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)] spec_va_4k_valid(va) && kernel_l4_end <= spec_v2l4index(va) ==> !final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va),
        final(krnl).pt_mp.spec_index(pagetable).view().leaves_present(),
{
    proof { pagetable_perms_wf_at(krnl.pt_mp, pagetable); }
    let mut indirect = [0usize; MAX_CONTAINER_TREE_DEPTH];
    let mut direct = 0usize;
    let mut cursor: (L4Index, L3Index, L2Index, L1Index) = (start_l4, 0, 0, 0);
    let mut found = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(&pagetable_lock_perm)).next_mapped_4k_from(cursor);
    while found.is_some()
        invariant
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_inserted(&entry_lctx, &table_lctx, KernelObjId::PageTable(pagetable), pt_entry),
            iommu_table is Some ==> typed_lock_maps_inserted(&table_lctx, lctx, KernelObjId::IommuTable(iommu_table->Some_0), it_entry),
            iommu_table is None ==> typed_lock_maps_unchanged(&table_lctx, lctx),
            pt_entry.mode == TypedLockMode::Write,
            it_entry.mode == TypedLockMode::Write,
            entry_k.prc_mp.spec_index(process_ptr).view().iommu_table == iommu_table,
            iommu_table is Some ==> locked_it.view().leaves_present() && locked_it.view().proc_ptr == process_ptr && locked_it.view().kernel_l4_end == 0,
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
            krnl.cpu_arr.spec_index(cpu_id).view().locking_thread() == entry_k.cpu_arr.spec_index(cpu_id).view().locking_thread(),
            krnl.cpu_arr.spec_index(cpu_id).view().being_killed() == entry_k.cpu_arr.spec_index(cpu_id).view().being_killed(),
            entry_k.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
            entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
            entry_k.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
            entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
            entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
            krnl.cpu_published[cpu_id as int].view() == (cr3, pcid),
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
            iommu_table is Some ==> krnl.it_mp.dom().contains(iommu_table->Some_0) && krnl.it_mp.spec_index(iommu_table->Some_0) == locked_it,
            krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
            krnl.pt_mp.spec_index(pagetable).view().mapping_2m() == locked_pt.mapping_2m(),
            krnl.pt_mp.spec_index(pagetable).view().mapping_1g() == locked_pt.mapping_1g(),
            locked_pt.leaves_present(),
            kernel_l4_end <= start_l4,
            KERNEL_MEM_END_L4INDEX <= start_l4,
            start_l4 == kernel_l4_end || start_l4 == KERNEL_MEM_END_L4INDEX,
            pei_valid(start_l4),
            forall|va: VAddr| #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)]
                krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va) && !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
            krnl.thr_mp.spec_index(thread_ptr).view() == (Thread {
                direct_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k, indirect_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k,
                syscall_progress: krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..entry_k.thr_mp.spec_index(thread_ptr).view()
            }),
            krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: true }),
            direct == krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
            forall|d: int| #![trigger indirect[d]] #![trigger krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d)] 0 <= d < krnl.thr_mp.spec_index(thread_ptr).view().container_depth
                ==> indirect[d] == krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
            0 <= start <= old(steps).view().len() <= steps.view().len(),
            forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
            pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pagetable, krnl.pt_mp.spec_index(pagetable).view()),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                    ==> !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && !spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i)) ==> !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
            start_l4 <= cursor.0,
            pei_valid(cursor.0),
            pei_valid(cursor.1),
            pei_valid(cursor.2),
            cursor.3 <= 512,
            found is Some ==> {
                let next = found->Some_0;
                &&& kernel_l4_end <= next.0
                &&& pei_valid(next.0)
                &&& pei_valid(next.1)
                &&& pei_valid(next.2)
                &&& pei_valid(next.3)
                &&& spec_l4_index_path_le(cursor, next)
                &&& krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va(next))
            },
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i))
                    && (found is None || !spec_l4_index_path_le(found->Some_0, (l4i, l3i, l2i, l1i))) ==> !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
        decreases 512 - cursor.0, 512 - cursor.1, 512 - cursor.2, 513 - cursor.3,
    {
        let next = found.unwrap();
        let va = index2va(next);
        let ghost iter_pt = krnl.pt_mp.spec_index(pagetable).view();
        proof {
            assert(spec_va_4k_valid(va) && spec_va2index(va) == next) by { spec_va_4k_index_roundtrip_at(va, next.0, next.1, next.2, next.3); };
            kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl);
        }
        reclaim_unmapped_4k_page(krnl, pagetable, va, thread_ptr, cpu_id, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&pagetable_lock_perm), Tracked(thread_lock_perm));
        cursor = (next.0, next.1, next.2, next.3 + 1);
        proof {
            assert forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && !spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i)) implies !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))) by {
                if spec_index2va((l4i, l3i, l2i, l1i)) != va { assert(krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))) == iter_pt.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))); }
            };
            pagetable_perms_wf_at(krnl.pt_mp, pagetable);
        }
        found = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(&pagetable_lock_perm)).next_mapped_4k_from(cursor);
    }
    let ghost reclaimed_pt = krnl.pt_mp.spec_index(pagetable);
    proof {
        assert forall|va: VAddr| #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)] spec_va_4k_valid(va) && kernel_l4_end <= spec_v2l4index(va) implies !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va) by {
            let index = spec_va2index(va);
            spec_va_4k_index_roundtrip_at(va, index.0, index.1, index.2, index.3);
        };
        assert(krnl.pt_mp.spec_index(pagetable).view().leaves_present()) by {
            assert forall|va: VAddr| #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)] krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va) implies krnl.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present by {
                let index = spec_va2index(va);
                if !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present { spec_va_4k_index_roundtrip_at(va, index.0, index.1, index.2, index.3); }
            };
        };
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl);
        assert(entry_lctx.container_lock_map().dom().contains(container_ptr) && entry_lctx.process_lock_map().dom().contains(process_ptr) && entry_lctx.cpu_lock_map().dom().contains(cpu_id)
            && lctx.pagetable_lock_map().dom().contains(pagetable));
    }
    let ghost refund_before = steps.view();
    refund_unmap_4k_quota(krnl, thread_ptr, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm));
    proof {
        assert(krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() =~= entry_k.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view()) by { reveal(thread_perms_wf); };
        thread_exit_trace_from_refund(&*steps, refund_before, start, pre, cpu_id, thread_ptr, process_ptr, container_ptr);
        assert(krnl.pt_mp.spec_index(pagetable) == reclaimed_pt && krnl.prc_mp.spec_index(process_ptr) == entry_k.prc_mp.spec_index(process_ptr)
            && krnl.ctn_mp.spec_index(container_ptr) == entry_k.ctn_mp.spec_index(container_ptr) && krnl.cpu_arr.spec_index(cpu_id) == steps.snapshot_k().cpu_arr.spec_index(cpu_id));
    }
}

/// Clear and unmap every 4K leaf of the process's write-locked IOMMU table, one IOMMU leaf step per leaf in index order,
/// accumulating the quota of its page as the thread's pending refund, then refund that quota to the thread's container
/// chain.
pub(super) fn thread_exit_reclaim_iommu_leaves(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, Ghost(container_ptr): Ghost<RwLockContainerPtr>,
    Ghost(process_ptr): Ghost<RwLockProcessPtr>, thread_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot, Ghost(cr3): Ghost<PageTableRoot>, Ghost(pcid): Ghost<Pcid>,
    Ghost(kernel_l4_end): Ghost<usize>, Ghost(start_l4): Ghost<L4Index>, Ghost(entry_k): Ghost<KernelK>, Ghost(entry_lctx): Ghost<LocalContext>, Ghost(pt_entry): Ghost<TypedHeldLock>,
    Ghost(locked_pt): Ghost<PageTable<PT_TYPE>>, iommu_table: RwLockPageTableRoot, Ghost(table_lctx): Ghost<LocalContext>, Ghost(it_entry): Ghost<TypedHeldLock>,
    Ghost(locked_it): Ghost<RwLock<PageTable<IOMMU_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>>, Tracked(cpu_lock_perm): Tracked<&LockPerm>, Tracked(process_lock_perm): Tracked<&LockPerm>,
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
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        old(krnl).cpu_published[cpu_id as int].view() == (cr3, pcid),
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
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
        old(krnl).pt_mp.spec_index(pagetable).view().mapping_2m() == locked_pt.mapping_2m(),
        old(krnl).pt_mp.spec_index(pagetable).view().mapping_1g() == locked_pt.mapping_1g(),
        locked_pt.leaves_present(),
        kernel_l4_end <= start_l4,
        KERNEL_MEM_END_L4INDEX <= start_l4,
        start_l4 == kernel_l4_end || start_l4 == KERNEL_MEM_END_L4INDEX,
        pei_valid(start_l4),
        forall|va: VAddr| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)]
            old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va) && !old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
        old(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..entry_k.thr_mp.spec_index(thread_ptr).view() }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: true }),
        0 <= start <= old(steps).view().len(),
        forall|va: VAddr| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)] spec_va_4k_valid(va) && kernel_l4_end <= spec_v2l4index(va) ==> !old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va),
        old(krnl).pt_mp.spec_index(pagetable).view().leaves_present(),
        iommu_table_lock_perm.state() is WriteLock,
        iommu_table_lock_perm.thread_id() == entry_lctx.thread_id(),
        iommu_table_lock_perm.lock_id() == locked_it.locking_thread()->Write_lock_id,
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
        final(krnl).cpu_published[cpu_id as int].view() == (cr3, pcid),
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
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_2m() == locked_pt.mapping_2m(),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_1g() == locked_pt.mapping_1g(),
        forall|va: VAddr| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)]
            final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va) && !final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..entry_k.thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: true }),
        old(steps).view().len() <= final(steps).view().len(),
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|va: VAddr| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)] spec_va_4k_valid(va) && kernel_l4_end <= spec_v2l4index(va) ==> !final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va),
        final(krnl).pt_mp.spec_index(pagetable).view().leaves_present(),
{
    proof { iommu_table_perms_wf_at(krnl.it_mp, iommu_table); }
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
            krnl.cpu_arr.spec_index(cpu_id).view().locking_thread() == entry_k.cpu_arr.spec_index(cpu_id).view().locking_thread(),
            krnl.cpu_arr.spec_index(cpu_id).view().being_killed() == entry_k.cpu_arr.spec_index(cpu_id).view().being_killed(),
            entry_k.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
            entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
            entry_k.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
            entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
            entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
            krnl.cpu_published[cpu_id as int].view() == (cr3, pcid),
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
            krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
            krnl.pt_mp.spec_index(pagetable).view().mapping_2m() == locked_pt.mapping_2m(),
            krnl.pt_mp.spec_index(pagetable).view().mapping_1g() == locked_pt.mapping_1g(),
            locked_pt.leaves_present(),
            kernel_l4_end <= start_l4,
            KERNEL_MEM_END_L4INDEX <= start_l4,
            start_l4 == kernel_l4_end || start_l4 == KERNEL_MEM_END_L4INDEX,
            pei_valid(start_l4),
            forall|va: VAddr| #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)]
                krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va) && !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
            krnl.thr_mp.spec_index(thread_ptr).view() == (Thread {
                direct_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k, indirect_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k,
                syscall_progress: krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..entry_k.thr_mp.spec_index(thread_ptr).view()
            }),
            krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: true }),
            direct == krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
            forall|d: int| #![trigger indirect[d]] #![trigger krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d)] 0 <= d < krnl.thr_mp.spec_index(thread_ptr).view().container_depth
                ==> indirect[d] == krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
            0 <= start <= old(steps).view().len() <= steps.view().len(),
            forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
            forall|va: VAddr| #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)]
                spec_va_4k_valid(va) && kernel_l4_end <= spec_v2l4index(va) ==> !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va),
            krnl.pt_mp.spec_index(pagetable).view().leaves_present(),
            iommu_table_lock_perm.state() is WriteLock,
            iommu_table_lock_perm.thread_id() == entry_lctx.thread_id(),
            iommu_table_lock_perm.lock_id() == locked_it.locking_thread()->Write_lock_id,
            krnl.it_mp.spec_index(iommu_table).locking_thread() == locked_it.locking_thread(),
            krnl.it_mp.spec_index(iommu_table).view().leaves_present(),
            krnl.it_mp.spec_index(iommu_table).view().kernel_l4_end == 0,
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
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && !spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i))
                    ==> !krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i))
                    && (found is None || !spec_l4_index_path_le(found->Some_0, (l4i, l3i, l2i, l1i))) ==> !krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
        decreases 512 - cursor.0, 512 - cursor.1, 512 - cursor.2, 513 - cursor.3,
    {
        let next = found.unwrap();
        let iova = index2va(next);
        let ghost leaf_k = *krnl;
        let ghost leaf_lctx = *lctx;
        let ghost leaf_before = steps.view();
        let ghost leaf_it = krnl.it_mp.spec_index(iommu_table).view();
        proof { assert(lctx.iommu_table_lock_map().dom().contains(iommu_table) && lctx.pagetable_lock_map().dom().contains(pagetable) && lctx.thread_lock_map().dom().contains(thread_ptr)); }
        clear_iommu_4k_mapping_present(krnl, iommu_table, next, Tracked(&mut *lctx), Tracked(iommu_table_lock_perm));
        proof {
            let leaf_post = *krnl;
            assert(leaf_k.it_mp.spec_index(iommu_table).view().proc_ptr == process_ptr) by { reveal(process_iommu_table_match); };
            assert(thread_exit_reclaim_step_pre(kernel_k_to_kernel_u(leaf_k), cpu_id, true)
                && thread_exit_iommu_leaf_step(kernel_k_to_kernel_u(leaf_k), kernel_k_to_kernel_u(leaf_post), cpu_id)
                && kernel_k_to_kernel_u(leaf_k) != kernel_k_to_kernel_u(leaf_post) && kernel_k_to_nonlock_kernel_u(leaf_k) != kernel_k_to_nonlock_kernel_u(leaf_post)) by {
                kernel_write_held_context_projection(&leaf_k, &leaf_lctx, cpu_id, process_ptr, thread_ptr, None);
                leaf_k.it_mp.typed_lock_map_aligned_write_at(leaf_lctx.iommu_table_lock_map(), leaf_lctx.thread_id(), iommu_table);
                kernel_iommu_table_mappings_projection_at(&leaf_k, process_ptr);
                kernel_iommu_table_4k_present_cleared_implies_u_step(&leaf_k, &leaf_post, iommu_table, iova);
                thread_exit_iommu_leaf_step_from_u(kernel_k_to_kernel_u(leaf_k), kernel_k_to_kernel_u(leaf_post), cpu_id, process_ptr, thread_ptr, iova);
            };
            krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
            thread_exit_trace_push(&*steps, leaf_before, start, pre, kernel_k_to_kernel_u(leaf_k), kernel_k_to_kernel_u(leaf_post), cpu_id);
            kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl);
        }
        reclaim_unmapped_iommu_4k_page(krnl, iommu_table, next, thread_ptr, cpu_id, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(iommu_table_lock_perm),
            Tracked(thread_lock_perm));
        cursor = (next.0, next.1, next.2, next.3 + 1);
        proof {
            assert forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && !spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i))
                    implies !krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))) by {
                if spec_index2va((l4i, l3i, l2i, l1i)) != iova { assert(krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))) == leaf_it.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))); }
            };
            iommu_table_perms_wf_at(krnl.it_mp, iommu_table);
        }
        found = krnl.it_mp.borrow_typed(iommu_table, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_table_lock_perm)).next_mapped_4k_from(cursor);
    }
    let ghost reclaimed_it = krnl.it_mp.spec_index(iommu_table);
    let ghost reclaimed_pt = krnl.pt_mp.spec_index(pagetable);
    proof {
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl);
        assert(entry_lctx.container_lock_map().dom().contains(container_ptr) && entry_lctx.process_lock_map().dom().contains(process_ptr) && entry_lctx.cpu_lock_map().dom().contains(cpu_id)
            && lctx.pagetable_lock_map().dom().contains(pagetable) && lctx.iommu_table_lock_map().dom().contains(iommu_table));
    }
    let ghost refund_before = steps.view();
    refund_unmap_4k_quota(krnl, thread_ptr, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm));
    proof {
        assert(krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() =~= entry_k.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view()) by { reveal(thread_perms_wf); };
        thread_exit_trace_from_refund(&*steps, refund_before, start, pre, cpu_id, thread_ptr, process_ptr, container_ptr);
        assert(krnl.pt_mp.spec_index(pagetable) == reclaimed_pt && krnl.it_mp.spec_index(iommu_table) == reclaimed_it && krnl.prc_mp.spec_index(process_ptr) == entry_k.prc_mp.spec_index(process_ptr)
            && krnl.ctn_mp.spec_index(container_ptr) == entry_k.ctn_mp.spec_index(container_ptr) && krnl.cpu_arr.spec_index(cpu_id) == steps.snapshot_k().cpu_arr.spec_index(cpu_id));
    }
}

/// Return the thread's and the process's quota of every size to their container, then unlock the reclaimed IOMMU table and
/// page table.
pub(super) fn thread_exit_reclaim_return_quota(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, container_ptr: RwLockContainerPtr,
    process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot, Ghost(cr3): Ghost<PageTableRoot>, Ghost(pcid): Ghost<Pcid>,
    Ghost(kernel_l4_end): Ghost<usize>, Ghost(start_l4): Ghost<L4Index>, Ghost(entry_k): Ghost<KernelK>, Ghost(entry_lctx): Ghost<LocalContext>,
    Ghost(pt_entry): Ghost<TypedHeldLock>, Ghost(locked_pt): Ghost<PageTable<PT_TYPE>>, iommu_table: Option<RwLockPageTableRoot>, Ghost(table_lctx): Ghost<LocalContext>,
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
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        old(krnl).cpu_published[cpu_id as int].view() == (cr3, pcid),
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
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
        old(krnl).pt_mp.spec_index(pagetable).view().mapping_2m() == locked_pt.mapping_2m(),
        old(krnl).pt_mp.spec_index(pagetable).view().mapping_1g() == locked_pt.mapping_1g(),
        locked_pt.leaves_present(),
        kernel_l4_end <= start_l4,
        KERNEL_MEM_END_L4INDEX <= start_l4,
        start_l4 == kernel_l4_end || start_l4 == KERNEL_MEM_END_L4INDEX,
        pei_valid(start_l4),
        forall|va: VAddr| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)]
            old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va) && !old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
        old(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..entry_k.thr_mp.spec_index(thread_ptr).view() }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: true }),
        0 <= start <= old(steps).view().len(),
        forall|va: VAddr| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)] spec_va_4k_valid(va) && kernel_l4_end <= spec_v2l4index(va) ==> !old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va),
        old(krnl).pt_mp.spec_index(pagetable).view().leaves_present(),
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
            iommu_table is Some && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                ==> !old(krnl).it_mp.spec_index(iommu_table->Some_0).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(&entry_lctx, final(lctx)),
        final(lctx).cpu_id() == cpu_id,
        final(lctx).thread_id() == entry_lctx.thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        thread_exit_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id),
        final(krnl).cpu_published[cpu_id as int].view() == (cr3, pcid),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == entry_k.cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == entry_k.cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == entry_k.cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr) == entry_k.ctn_mp.spec_index(container_ptr),
        final(krnl).prc_mp.dom().contains(process_ptr),
        final(krnl).prc_mp.spec_index(process_ptr).view() == (Process { quota_4k: 0, quota_2m: 0, quota_1g: 0, ..entry_k.prc_mp.spec_index(process_ptr).view() }),
        final(krnl).prc_mp.spec_index(process_ptr).view_rodata() == entry_k.prc_mp.spec_index(process_ptr).view_rodata(),
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost() == entry_k.prc_mp.spec_index(process_ptr).view_ghost(),
        final(krnl).prc_mp.spec_index(process_ptr).locking_thread() == entry_k.prc_mp.spec_index(process_ptr).locking_thread(),
        final(krnl).prc_mp.spec_index(process_ptr).being_killed() == entry_k.prc_mp.spec_index(process_ptr).being_killed(),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view()
            == (Thread { quota_4k: 0, quota_2m: 0, quota_1g: 0, syscall_progress: Ghost(Some(SyscallProgress::ThreadExitZombie)), ..entry_k.thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == entry_k.thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == entry_k.thr_mp.spec_index(thread_ptr).being_killed(),
{
    let ghost reclaimed_pt = krnl.pt_mp.spec_index(pagetable);
    let ghost reclaimed_it = krnl.it_mp.spec_index(iommu_table->Some_0);
    let ghost sz4k_before = steps.view();
    let ghost sz4k_k = *krnl;
    let ghost sz4k_lctx = *lctx;
    thread_exit_return_quota(krnl, Tracked(&mut *lctx), container_ptr, process_ptr, thread_ptr, PageSize::SZ4k, Tracked(process_lock_perm), Tracked(thread_lock_perm));
    proof {
        let returned_k = *krnl;
        assert(thread_exit_quota_step_pre(kernel_k_to_kernel_u(sz4k_k), cpu_id) && thread_exit_quota_step(kernel_k_to_kernel_u(sz4k_k), kernel_k_to_kernel_u(returned_k), cpu_id)) by {
            kernel_write_held_context_projection(&sz4k_k, &sz4k_lctx, cpu_id, process_ptr, thread_ptr, None);
            kernel_thread_exit_quota_returned_implies_u_step(&sz4k_k, &returned_k, thread_ptr, PageSize::SZ4k);
            thread_exit_quota_step_from_u(kernel_k_to_kernel_u(sz4k_k), kernel_k_to_kernel_u(returned_k), cpu_id, thread_ptr, PageSize::SZ4k);
        };
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        thread_exit_trace_push(&*steps, sz4k_before, start, pre, kernel_k_to_kernel_u(sz4k_k), kernel_k_to_kernel_u(returned_k), cpu_id);
        assert(entry_lctx.container_lock_map().dom().contains(container_ptr) && entry_lctx.process_lock_map().dom().contains(process_ptr) && entry_lctx.cpu_lock_map().dom().contains(cpu_id)
            && entry_lctx.thread_lock_map().dom().contains(thread_ptr) && lctx.pagetable_lock_map().dom().contains(pagetable)
            && (iommu_table is Some ==> lctx.iommu_table_lock_map().dom().contains(iommu_table->Some_0)));
    }
    // Return the thread's and the process's 2m quota to their container.
    let ghost sz2m_before = steps.view();
    let ghost sz2m_k = *krnl;
    let ghost sz2m_lctx = *lctx;
    thread_exit_return_quota(krnl, Tracked(&mut *lctx), container_ptr, process_ptr, thread_ptr, PageSize::SZ2m, Tracked(process_lock_perm), Tracked(thread_lock_perm));
    proof {
        let returned_k = *krnl;
        assert(thread_exit_quota_step_pre(kernel_k_to_kernel_u(sz2m_k), cpu_id) && thread_exit_quota_step(kernel_k_to_kernel_u(sz2m_k), kernel_k_to_kernel_u(returned_k), cpu_id)) by {
            kernel_write_held_context_projection(&sz2m_k, &sz2m_lctx, cpu_id, process_ptr, thread_ptr, None);
            kernel_thread_exit_quota_returned_implies_u_step(&sz2m_k, &returned_k, thread_ptr, PageSize::SZ2m);
            thread_exit_quota_step_from_u(kernel_k_to_kernel_u(sz2m_k), kernel_k_to_kernel_u(returned_k), cpu_id, thread_ptr, PageSize::SZ2m);
        };
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        thread_exit_trace_push(&*steps, sz2m_before, start, pre, kernel_k_to_kernel_u(sz2m_k), kernel_k_to_kernel_u(returned_k), cpu_id);
        assert(entry_lctx.container_lock_map().dom().contains(container_ptr) && entry_lctx.process_lock_map().dom().contains(process_ptr) && entry_lctx.cpu_lock_map().dom().contains(cpu_id)
            && entry_lctx.thread_lock_map().dom().contains(thread_ptr) && lctx.pagetable_lock_map().dom().contains(pagetable)
            && (iommu_table is Some ==> lctx.iommu_table_lock_map().dom().contains(iommu_table->Some_0)));
    }
    // Return the thread's and the process's 1g quota to their container.
    let ghost sz1g_before = steps.view();
    let ghost sz1g_k = *krnl;
    let ghost sz1g_lctx = *lctx;
    thread_exit_return_quota(krnl, Tracked(&mut *lctx), container_ptr, process_ptr, thread_ptr, PageSize::SZ1g, Tracked(process_lock_perm), Tracked(thread_lock_perm));
    proof {
        let returned_k = *krnl;
        assert(thread_exit_quota_step_pre(kernel_k_to_kernel_u(sz1g_k), cpu_id) && thread_exit_quota_step(kernel_k_to_kernel_u(sz1g_k), kernel_k_to_kernel_u(returned_k), cpu_id)) by {
            kernel_write_held_context_projection(&sz1g_k, &sz1g_lctx, cpu_id, process_ptr, thread_ptr, None);
            kernel_thread_exit_quota_returned_implies_u_step(&sz1g_k, &returned_k, thread_ptr, PageSize::SZ1g);
            thread_exit_quota_step_from_u(kernel_k_to_kernel_u(sz1g_k), kernel_k_to_kernel_u(returned_k), cpu_id, thread_ptr, PageSize::SZ1g);
        };
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        thread_exit_trace_push(&*steps, sz1g_before, start, pre, kernel_k_to_kernel_u(sz1g_k), kernel_k_to_kernel_u(returned_k), cpu_id);
        assert(entry_lctx.container_lock_map().dom().contains(container_ptr) && entry_lctx.process_lock_map().dom().contains(process_ptr) && entry_lctx.cpu_lock_map().dom().contains(cpu_id)
            && entry_lctx.thread_lock_map().dom().contains(thread_ptr) && lctx.pagetable_lock_map().dom().contains(pagetable)
            && (iommu_table is Some ==> lctx.iommu_table_lock_map().dom().contains(iommu_table->Some_0)));
    }
    // Unlock the reclaimed IOMMU table and page table.
    let ghost unlock_before = steps.view();
    let ghost unlock_k = *krnl;
    let ghost unlock_lctx = *lctx;
    proof { assert(krnl.pt_mp.spec_index(pagetable) == reclaimed_pt && (iommu_table is Some ==> krnl.it_mp.spec_index(iommu_table->Some_0) == reclaimed_it)); }
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::ThreadExitZombie)), Tracked(&*lctx), Tracked(thread_lock_perm));
    if let Some(it) = iommu_table {
        krnl.wunlock_iommu_table(it, Tracked(&mut *lctx), Tracked(iommu_table_lock_perm.tracked_unwrap()));
    }
    proof {
        let pt = krnl.pt_mp.spec_index(pagetable).view();
        assert(pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pagetable, pt)) by {
            reveal(tlb_wf_spec);
            assert forall|c: CpuId, p: Pcid| #![trigger krnl.cpu_tlb.spec_index((c, p))]
                index_valid(NUM_CPUS, c) && pcid_valid(p) && p != KERNEL_DEFAULT_PCID
                && (!krnl.pcid_needflush.spec_index(c, p).view().needflush || krnl.cpu_arr.spec_index(c).view().view().view().current_pcid == p)
                && krnl.cpu_arr.spec_index(c).view().view().tlb_dirty_bitmap().spec_index(p) is Some && krnl.cpu_arr.spec_index(c).view().view().tlb_dirty_bitmap().spec_index(p).unwrap().pagetable_ptr == pagetable
                implies single_cpu_single_pcid_tlb_subset_of_present_pagetable(krnl.cpu_tlb.spec_index((c, p)), pt) by {
                let tlb = krnl.cpu_tlb.spec_index((c, p));
                if !tlb.is_empty() {
                    assert forall|va: VAddr| #![trigger tlb.tlb_4k().spec_index(va)] #![trigger pt.mapping_4k().spec_index(va)] tlb.tlb_4k().dom().contains(va) implies pt.mapping_4k().spec_index(va).present by { assert(pt.mapping_4k().dom().contains(va)); };
                    assert forall|va: VAddr| #![trigger tlb.tlb_2m().spec_index(va)] #![trigger pt.mapping_2m().spec_index(va)] tlb.tlb_2m().dom().contains(va) implies pt.mapping_2m().spec_index(va).present by { assert(pt.mapping_2m().dom().contains(va)); };
                    assert forall|va: VAddr| #![trigger tlb.tlb_1g().spec_index(va)] #![trigger pt.mapping_1g().spec_index(va)] tlb.tlb_1g().dom().contains(va) implies pt.mapping_1g().spec_index(va).present by { assert(pt.mapping_1g().dom().contains(va)); };
                }
            };
        };
    }
    krnl.wunlock_pagetable(pagetable, Tracked(&mut *lctx), Tracked(pagetable_lock_perm));
    proof {
        let unlocked_k = *krnl;
        assert(thread_exit_unlock_table_step_pre(kernel_k_to_kernel_u(unlock_k), cpu_id) && thread_exit_unlock_table_step(kernel_k_to_kernel_u(unlock_k), kernel_k_to_kernel_u(unlocked_k), cpu_id)) by {
            kernel_write_held_context_projection(&unlock_k, &unlock_lctx, cpu_id, process_ptr, thread_ptr, None);
            kernel_pagetable_user_4k_unmapped_projection_at(&unlock_k, process_ptr);
            if iommu_table is Some { kernel_iommu_table_4k_unmapped_projection_at(&unlock_k, process_ptr); }
            kernel_process_tables_lock_state_and_progress_changed_implies_u_step(&unlock_k, &unlocked_k, &*lctx, process_ptr, pagetable, thread_ptr, false);
            thread_exit_unlock_table_step_from_u(kernel_k_to_kernel_u(unlock_k), kernel_k_to_kernel_u(unlocked_k), cpu_id, thread_ptr);
        };
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        thread_exit_trace_push(&*steps, unlock_before, start, pre, kernel_k_to_kernel_u(unlock_k), kernel_k_to_kernel_u(unlocked_k), cpu_id);
        assert(lctx.pagetable_lock_map() =~= entry_lctx.pagetable_lock_map());
        assert(lctx.iommu_table_lock_map() =~= entry_lctx.iommu_table_lock_map());
        assert(entry_lctx.container_lock_map().dom().contains(container_ptr) && entry_lctx.process_lock_map().dom().contains(process_ptr) && entry_lctx.cpu_lock_map().dom().contains(cpu_id)
            && entry_lctx.thread_lock_map().dom().contains(thread_ptr));
    }
}
} // verus!
