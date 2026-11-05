use vstd::prelude::*;
use crate::*;
use super::syscall_thread_exit_spec::*;
use super::syscall_thread_exit_trace::*;
use super::syscall_thread_exit_quota::thread_exit_return_quota;
#[cfg(verus_keep_ghost)]
use super::syscall_thread_exit_reclaim_spec::thread_exit_tables_emptied_eof_transition_framing;
#[cfg(verus_keep_ghost)]
use super::syscall_thread_exit_reclaim_eof::{thread_exit_tables_emptied_eof, thread_exit_mark_exited_eof};

verus! {
/// Return the `size` quota of the exiting last thread and of its process to their container as one recorded step,
/// while the reclaimed page table and IOMMU table stay write-held.
pub(super) fn thread_exit_reclaim_return_quota_size(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr,
    prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot, Ghost(iommu_table): Ghost<Option<RwLockPageTableRoot>>, size: PageSize,
    Tracked(process_lock_perm): Tracked<&LockPerm>, Tracked(thread_lock_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).cpu_id() == cpu_id,
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), ctn_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        iommu_table is Some ==> old(lctx).iommu_table_lock_map().dom().contains(iommu_table->Some_0),
        process_lock_perm.state() is WriteLock,
        process_lock_perm.thread_id() == old(lctx).thread_id(),
        process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(prc_ptr).locking_thread()->Write_lock_id,
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        thread_exit_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).ctn_mp.dom().contains(ctn_ptr),
        old(krnl).ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view().contains(prc_ptr),
        old(krnl).ctn_mp.spec_index(ctn_ptr).view_ghost().owned_threads.view().contains(thrd_ptr),
        old(krnl).prc_mp.dom().contains(prc_ptr),
        old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == ctn_ptr,
        !old(krnl).prc_mp.spec_index(prc_ptr).being_killed(),
        !old(krnl).prc_mp.spec_index(prc_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is Some,
        thread_exit_quota_progress_after(old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()->Some_0) == Some(SyscallProgress::ThreadExitQuota { returned: size }),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() is None,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == cpu_id,
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        thread_exit_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        final(krnl).ctn_mp.dom().contains(ctn_ptr),
        final(krnl).ctn_mp.spec_index(ctn_ptr) == old(krnl).ctn_mp.spec_index(ctn_ptr),
        final(krnl).prc_mp.dom().contains(prc_ptr),
        final(krnl).prc_mp.spec_index(prc_ptr).view() == match size {
            PageSize::SZ4k => Process { quota_4k: 0, ..old(krnl).prc_mp.spec_index(prc_ptr).view() },
            PageSize::SZ2m => Process { quota_2m: 0, ..old(krnl).prc_mp.spec_index(prc_ptr).view() },
            PageSize::SZ1g => Process { quota_1g: 0, ..old(krnl).prc_mp.spec_index(prc_ptr).view() },
        },
        final(krnl).prc_mp.spec_index(prc_ptr).view_rodata() == old(krnl).prc_mp.spec_index(prc_ptr).view_rodata(),
        final(krnl).prc_mp.spec_index(prc_ptr).view_ghost() == old(krnl).prc_mp.spec_index(prc_ptr).view_ghost(),
        final(krnl).prc_mp.spec_index(prc_ptr).locking_thread() == old(krnl).prc_mp.spec_index(prc_ptr).locking_thread(),
        final(krnl).prc_mp.spec_index(prc_ptr).being_killed() == old(krnl).prc_mp.spec_index(prc_ptr).being_killed(),
        final(krnl).thrd_mp.dom().contains(thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == match size {
            PageSize::SZ4k => Thread { quota_4k: 0, syscall_progress: Ghost(Some(SyscallProgress::ThreadExitQuota { returned: size })), ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() },
            PageSize::SZ2m => Thread { quota_2m: 0, syscall_progress: Ghost(Some(SyscallProgress::ThreadExitQuota { returned: size })), ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() },
            PageSize::SZ1g => Thread { quota_1g: 0, syscall_progress: Ghost(Some(SyscallProgress::ThreadExitQuota { returned: size })), ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() },
        },
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable) == old(krnl).pt_mp.spec_index(pagetable),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable),
        iommu_table is Some ==> final(krnl).it_mp.dom().contains(iommu_table->Some_0) && final(krnl).it_mp.spec_index(iommu_table->Some_0) == old(krnl).it_mp.spec_index(iommu_table->Some_0),
{
    let ghost before = steps.view();
    let ghost size_k = *krnl;
    let ghost size_lctx = *lctx;
    thread_exit_return_quota(krnl, Tracked(&mut *lctx), ctn_ptr, prc_ptr, thrd_ptr, size, Tracked(process_lock_perm), Tracked(thread_lock_perm));
    proof {
        let returned_k = *krnl;
        assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thrd_ptr);
        assert(thread_exit_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id)) by {
            thread_exit_quota_step_pre_from_k(&size_k, &size_lctx, cpu_id, ctn_ptr, prc_ptr, thrd_ptr, pagetable, size);
            kernel_thread_exit_quota_returned_implies_u_step(&size_k, &returned_k, thrd_ptr, size);
            thread_exit_quota_step_from_u(kernel_k_to_kernel_u(size_k), kernel_k_to_kernel_u(returned_k), cpu_id, thrd_ptr, size);
            thread_exit_trace_push(&*steps, before, start, pre, kernel_k_to_kernel_u(size_k), kernel_k_to_kernel_u(returned_k), cpu_id);
        };
    }
}

/// Park the exiting last thread as a zombie, mark its process as having emptied its tables, and unlock the reclaimed
/// IOMMU table and page table as one recorded step.
pub(super) fn thread_exit_reclaim_release_tables(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr,
    prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot, iommu_table: Option<RwLockPageTableRoot>, Ghost(entry_lctx): Ghost<LocalContext>,
    Ghost(table_lctx): Ghost<LocalContext>, Ghost(pt_entry): Ghost<TypedHeldLock>, Ghost(it_entry): Ghost<TypedHeldLock>,
    Ghost(emptied_pt): Ghost<WholePageTable<PT_TYPE>>, Tracked(process_lock_perm): Tracked<&LockPerm>, Tracked(thread_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_lock_perm): Tracked<LockPerm>,
    Tracked(iommu_table_lock_perm): Tracked<Option<LockPerm>>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        typed_lock_maps_inserted(&entry_lctx, &table_lctx, KernelObjId::PageTable(pagetable), pt_entry),
        iommu_table is Some ==> typed_lock_maps_inserted(&table_lctx, old(lctx), KernelObjId::IommuTable(iommu_table->Some_0), it_entry),
        iommu_table is None ==> typed_lock_maps_unchanged(&table_lctx, old(lctx)),
        pt_entry.mode == TypedLockMode::Write,
        it_entry.mode == TypedLockMode::Write,
        entry_lctx.pagetable_lock_map().dom().is_empty(),
        entry_lctx.pagetable_window_lock_map().dom().is_empty(),
        entry_lctx.iommu_table_lock_map().dom().is_empty(),
        old(lctx).cpu_id() == cpu_id,
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(entry_lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.container_lock_map(), ctn_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        process_lock_perm.state() is WriteLock,
        process_lock_perm.thread_id() == old(lctx).thread_id(),
        process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(prc_ptr).locking_thread()->Write_lock_id,
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        thread_exit_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).prc_mp.dom().contains(prc_ptr),
        !old(krnl).prc_mp.spec_index(prc_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        old(krnl).prc_mp.spec_index(prc_ptr).view().iommu_table == iommu_table,
        old(krnl).prc_mp.spec_index(prc_ptr).view().owned_threads.view().len() == 1,
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitQuota { returned: PageSize::SZ1g }),
        old(krnl).pt_mp.dom().contains(pagetable),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable) == emptied_pt,
        emptied_pt.mapping_4k().dom() =~= Set::<VAddr>::empty(),
        emptied_pt.mapping_2m().dom() =~= Set::<VAddr>::empty(),
        emptied_pt.mapping_1g().dom() =~= Set::<VAddr>::empty(),
        emptied_pt.lower.pagetable_window_locks.dom() =~= Set::<WindowVa>::empty(),
        emptied_pt.lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        emptied_pt.higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
        emptied_pt.kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        emptied_pt.lower.hidden_l1_tables_in_locked_windows(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger emptied_pt.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> emptied_pt.spec_held_4k_l1(l4i, l3i, l2i, l1i) is None,
        forall|l4i: L4Index| #![trigger emptied_pt.spec_resolve_mapping_l4(l4i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) ==> emptied_pt.spec_resolve_mapping_l4(l4i) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger emptied_pt.spec_held_2m_l2(l4i, l3i, l2i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> emptied_pt.spec_held_2m_l2(l4i, l3i, l2i) is None,
        (iommu_table_lock_perm is Some) == (iommu_table is Some),
        iommu_table is Some ==> {
            let it = old(krnl).it_mp.spec_index(iommu_table->Some_0);
            &&& old(krnl).it_mp.dom().contains(iommu_table->Some_0)
            &&& it.view().leaves_present()
            &&& it.view().mapping_4k().dom() =~= Set::<VAddr>::empty()
            &&& iommu_table_lock_perm->Some_0.state() is WriteLock
            &&& iommu_table_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
            &&& iommu_table_lock_perm->Some_0.lock_id() == it.locking_thread()->Write_lock_id
        },
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() is None,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(&entry_lctx, final(lctx)),
        final(lctx).cpu_id() == cpu_id,
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        thread_exit_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        final(krnl).ctn_mp.dom().contains(ctn_ptr),
        final(krnl).ctn_mp.spec_index(ctn_ptr) == old(krnl).ctn_mp.spec_index(ctn_ptr),
        final(krnl).prc_mp.dom().contains(prc_ptr),
        final(krnl).prc_mp.spec_index(prc_ptr).view() == (Process { state: Ghost(ProcessState::TablesEmptied), ..old(krnl).prc_mp.spec_index(prc_ptr).view() }),
        final(krnl).prc_mp.spec_index(prc_ptr).view_rodata() == old(krnl).prc_mp.spec_index(prc_ptr).view_rodata(),
        final(krnl).prc_mp.spec_index(prc_ptr).view_ghost() == old(krnl).prc_mp.spec_index(prc_ptr).view_ghost(),
        final(krnl).prc_mp.spec_index(prc_ptr).locking_thread() == old(krnl).prc_mp.spec_index(prc_ptr).locking_thread(),
        final(krnl).prc_mp.spec_index(prc_ptr).being_killed() == old(krnl).prc_mp.spec_index(prc_ptr).being_killed(),
        final(krnl).thrd_mp.dom().contains(thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: Ghost(Some(SyscallProgress::ThreadExitZombie)), ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
{
    let ghost unlock_before = steps.view();
    let ghost unlock_k = *krnl;
    let ghost unlock_lctx = *lctx;
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(Some(SyscallProgress::ThreadExitZombie)), Tracked(&*lctx), Tracked(thread_lock_perm));
    proof {
        let zombie = *krnl;
        krnl.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr); thread_perms_wf_map(krnl.thrd_mp);
        krnl.thrd_mp.update_ghost(thrd_ptr, ThreadGhost { exited: true, ..zombie.thrd_mp.spec_index(thrd_ptr).view_ghost() });
        thread_exit_mark_exited_eof(zombie, *krnl, thrd_ptr);
        assert(typed_lock_maps_aligned(&*krnl, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    let ghost progressed = *krnl;
    proof { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, prc_ptr); }
    {
        let process = krnl.prc_mp.borrow_mut_typed(prc_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(process_lock_perm));
        process.state = Ghost(ProcessState::TablesEmptied);
    }
    proof {
        process_thread_wf_thread_at(progressed.prc_mp, progressed.thrd_mp, thrd_ptr);
        assert(thread_exit_tables_emptied_eof_transition_framing(progressed, *krnl, prc_ptr)) by { reveal(thread_exit_tables_emptied_eof_transition_framing); };
        thread_exit_tables_emptied_eof(progressed, *krnl, prc_ptr, thrd_ptr, pagetable);
    }
    if let Some(it) = iommu_table {
        krnl.wunlock_iommu_table(it, Tracked(&mut *lctx), Tracked(iommu_table_lock_perm.tracked_unwrap()));
    }
    proof { process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr); }
    krnl.wunlock_pagetable(pagetable, Tracked(&mut *lctx), Tracked(pagetable_lock_perm));
    proof {
        let unlocked_k = *krnl;
        let unlocked_lctx = *lctx;
        assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thrd_ptr);
        assert(thread_exit_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id)) by {
            thread_exit_unlock_table_step_pre_from_k(&unlock_k, &unlock_lctx, cpu_id, ctn_ptr, prc_ptr, thrd_ptr, pagetable, iommu_table);
            kernel_process_tables_lock_state_and_progress_changed_implies_u_step(&unlock_k, &unlocked_k, &unlocked_lctx, prc_ptr, pagetable, thrd_ptr, false);
            thread_exit_unlock_table_step_from_u(kernel_k_to_kernel_u(unlock_k), kernel_k_to_kernel_u(unlocked_k), cpu_id, thrd_ptr);
            thread_exit_trace_push(&*steps, unlock_before, start, pre, kernel_k_to_kernel_u(unlock_k), kernel_k_to_kernel_u(unlocked_k), cpu_id);
        };
        assert(lctx.pagetable_lock_map() =~= entry_lctx.pagetable_lock_map());
        assert(lctx.iommu_table_lock_map() =~= entry_lctx.iommu_table_lock_map());
    }
}
} // verus!
