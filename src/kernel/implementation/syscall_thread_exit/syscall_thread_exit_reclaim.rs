use vstd::prelude::*;
use crate::*;
use super::syscall_thread_exit_spec::*;
use super::syscall_thread_exit_trace::*;
use super::syscall_thread_exit_reclaim_release::*;
use super::syscall_thread_exit_reclaim_leaf::thread_exit_reclaim_clear_leaf;
#[cfg(verus_keep_ghost)]
use super::syscall_thread_exit_reclaim_spec::thread_exit_detach_process_functions_eof_transition_framing;
#[cfg(verus_keep_ghost)]
use super::syscall_thread_exit_reclaim_eof::thread_exit_detach_process_functions_eof;

verus! {
/// Reclaim the user memory of the running last thread's process inside its exit: write-lock the process's page table,
/// detach the process's attached functions and write-lock its IOMMU table, clear every user 4K leaf, flush the
/// process's PCID from every cpu once, unmap the cleared pages and then every IOMMU 4K leaf while refunding their quota
/// to the thread's container chain, return the thread's and the process's quota of every size to their container, and
/// unlock the tables. Each change is one middle step of the partial trace that starts at `start`.
pub(super) fn thread_exit_reclaim(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, container_ptr: RwLockContainerPtr,
    process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, Tracked(cpu_lock_perm): Tracked<&LockPerm>, Tracked(process_lock_perm): Tracked<&LockPerm>,
    Tracked(thread_lock_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        thread_exit_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom() =~= set![container_ptr],
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        process_lock_perm.state() is WriteLock,
        process_lock_perm.thread_id() == old(lctx).thread_id(),
        process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        old(krnl).cpu_published[cpu_id as int].view()
            == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() == 1,
        !old(krnl).prc_mp.spec_index(process_ptr).being_killed(),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().caller is None,
        forall|j: int| #![trigger old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j]]
            0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j] is None,
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() matches Some(SyscallProgress::ThreadExit { .. }),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        thread_exit_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info(),
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr) == old(krnl).ctn_mp.spec_index(container_ptr),
        final(krnl).prc_mp.dom().contains(process_ptr),
        final(krnl).prc_mp.spec_index(process_ptr).view() == (Process { state: Ghost(ProcessState::TablesEmptied), quota_4k: 0, quota_2m: 0, quota_1g: 0, ..old(krnl).prc_mp.spec_index(process_ptr).view() }),
        final(krnl).prc_mp.spec_index(process_ptr).view_rodata() == old(krnl).prc_mp.spec_index(process_ptr).view_rodata(),
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost() == old(krnl).prc_mp.spec_index(process_ptr).view_ghost(),
        final(krnl).prc_mp.spec_index(process_ptr).locking_thread() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread(),
        final(krnl).prc_mp.spec_index(process_ptr).being_killed() == old(krnl).prc_mp.spec_index(process_ptr).being_killed(),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view()
            == (Thread { quota_4k: 0, quota_2m: 0, quota_1g: 0, syscall_progress: Ghost(Some(SyscallProgress::ThreadExitZombie)), ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
{
    proof { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, process_ptr); }
    let process = krnl.prc_mp.borrow_rodata(process_ptr).borrow();
    let pagetable = process.pagetable;
    let cr3 = process.cr3;
    let pcid = process.pcid;
    let iommu_table = krnl.prc_mp.borrow_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(process_lock_perm)).iommu_table;
    let ghost entry_k = *krnl;
    let ghost entry_lctx = *lctx;
    let (Tracked(pagetable_lock_perm), Tracked(iommu_table_lock_perm), Ghost(table_lctx)) = thread_exit_reclaim_lock_table(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), Ghost(cpu_id),
        Ghost(container_ptr), process_ptr, thread_ptr, pagetable, iommu_table, Ghost(cr3), Ghost(pcid), Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(thread_lock_perm),
        Ghost(start), Ghost(pre));
    proof { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); }
    let kernel_l4_end = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(&pagetable_lock_perm)).kernel_l4_end;
    let start_l4 = if kernel_l4_end < KERNEL_MEM_END_L4INDEX { KERNEL_MEM_END_L4INDEX } else { kernel_l4_end };
    let ghost pt_entry = TypedHeldLock { lock_id: krnl.pt_mp.lock_id_by_key(pagetable), mode: TypedLockMode::Write };
    let ghost locked_pt = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
    let ghost it_entry = TypedHeldLock { lock_id: krnl.it_mp.lock_id_by_key(iommu_table->Some_0), mode: TypedLockMode::Write };
    let ghost locked_it = krnl.it_mp.spec_index(iommu_table->Some_0);
    thread_exit_reclaim_clear_leaves(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), Ghost(cpu_id), Ghost(container_ptr), Ghost(process_ptr), Ghost(thread_ptr), pagetable, Ghost(cr3), Ghost(pcid),
        Ghost(kernel_l4_end), start_l4, Ghost(entry_k), Ghost(entry_lctx), Ghost(pt_entry), Ghost(locked_pt), Ghost(iommu_table), Ghost(table_lctx), Ghost(it_entry), Ghost(locked_it),
        Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(thread_lock_perm), Tracked(&pagetable_lock_perm), Ghost(start), Ghost(pre));
    thread_exit_reclaim_flush(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Ghost(container_ptr), Ghost(process_ptr), thread_ptr, pagetable, cr3, pcid, Ghost(kernel_l4_end),
        Ghost(start_l4), Ghost(entry_k), Ghost(entry_lctx), Ghost(pt_entry), Ghost(locked_pt), Ghost(iommu_table), Ghost(table_lctx), Ghost(it_entry), Ghost(locked_it),
        Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(thread_lock_perm), Tracked(&pagetable_lock_perm), Ghost(start), Ghost(pre));
    thread_exit_reclaim_unmap_leaves(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Ghost(container_ptr), Ghost(process_ptr), thread_ptr, pagetable, Ghost(cr3), Ghost(pcid),
        Ghost(kernel_l4_end), start_l4, Ghost(entry_k), Ghost(entry_lctx), Ghost(pt_entry), Ghost(locked_pt), Ghost(iommu_table), Ghost(table_lctx), Ghost(it_entry), Ghost(locked_it),
        Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(thread_lock_perm), Tracked(&pagetable_lock_perm), Ghost(start), Ghost(pre));
    if let Some(it) = iommu_table {
        thread_exit_reclaim_iommu_leaves(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Ghost(container_ptr), Ghost(process_ptr), thread_ptr, pagetable, Ghost(cr3), Ghost(pcid),
            Ghost(kernel_l4_end), Ghost(start_l4), Ghost(entry_k), Ghost(entry_lctx), Ghost(pt_entry), Ghost(locked_pt), it, Ghost(table_lctx), Ghost(it_entry), Ghost(locked_it),
            Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(thread_lock_perm), Tracked(&pagetable_lock_perm), Tracked(iommu_table_lock_perm.tracked_borrow()), Ghost(start),
            Ghost(pre));
    }
    thread_exit_reclaim_return_quota(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, process_ptr, thread_ptr, pagetable, Ghost(cr3), Ghost(pcid), Ghost(kernel_l4_end),
        Ghost(start_l4), Ghost(entry_k), Ghost(entry_lctx), Ghost(pt_entry), Ghost(locked_pt), iommu_table, Ghost(table_lctx), Ghost(it_entry), Tracked(cpu_lock_perm),
        Tracked(process_lock_perm), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(iommu_table_lock_perm), Ghost(start), Ghost(pre));
}

/// Write-lock the process's page table, detach the process's attached functions with their IOTLB domains emptied,
/// write-lock its IOMMU table, and record that nothing is flushed yet.
fn thread_exit_reclaim_lock_table(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Ghost(cpu_id): Ghost<CpuId>,
    Ghost(container_ptr): Ghost<RwLockContainerPtr>, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>, Ghost(cr3): Ghost<PageTableRoot>, Ghost(pcid): Ghost<Pcid>, Tracked(cpu_lock_perm): Tracked<&LockPerm>,
    Tracked(process_lock_perm): Tracked<&LockPerm>, Tracked(thread_lock_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
) -> (ret: (Tracked<LockPerm>, Tracked<Option<LockPerm>>, Ghost<LocalContext>))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        thread_exit_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom() =~= set![container_ptr],
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        process_lock_perm.state() is WriteLock,
        process_lock_perm.thread_id() == old(lctx).thread_id(),
        process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        old(krnl).cpu_published[cpu_id as int].view()
            == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() == 1,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().caller is None,
        forall|j: int| #![trigger old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j]]
            0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j] is None,
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() matches Some(SyscallProgress::ThreadExit { .. }),
        pagetable == old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable,
        cr3 == old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().cr3,
        pcid == old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pcid,
        iommu_table == old(krnl).prc_mp.spec_index(process_ptr).view().iommu_table,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).cpu_id() == cpu_id,
        final(lctx).thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == old(lctx).thread_id(),
        ret.0.view().lock_id() == final(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        final(steps).snapshot_k() == *final(krnl),
        thread_exit_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        final(krnl).cpu_published[cpu_id as int].view() == (cr3, pcid),
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr) == old(krnl).ctn_mp.spec_index(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().contains(thread_ptr),
        final(krnl).prc_mp.dom().contains(process_ptr),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        !old(krnl).prc_mp.spec_index(process_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
        old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pcid == pcid,
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(thread_ptr).inv(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable,
        old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth <= MAX_CONTAINER_TREE_DEPTH,
        final(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_maps_inserted(old(lctx), &ret.2.view(), KernelObjId::PageTable(pagetable), TypedHeldLock { lock_id: final(krnl).pt_mp.lock_id_by_key(pagetable), mode: TypedLockMode::Write }),
        iommu_table is Some ==> typed_lock_maps_inserted(&ret.2.view(), final(lctx), KernelObjId::IommuTable(iommu_table->Some_0),
            TypedHeldLock { lock_id: final(krnl).it_mp.lock_id_by_key(iommu_table->Some_0), mode: TypedLockMode::Write }),
        iommu_table is None ==> typed_lock_maps_unchanged(&ret.2.view(), final(lctx)),
        (ret.1.view() is Some) == (iommu_table is Some),
        iommu_table is Some ==> {
            let it = final(krnl).it_mp.spec_index(iommu_table->Some_0);
            &&& final(krnl).it_mp.dom().contains(iommu_table->Some_0)
            &&& it.view().leaves_present()
            &&& it.view().proc_ptr == process_ptr
            &&& it.view().kernel_l4_end == 0
            &&& ret.1.view().unwrap().state() is WriteLock
            &&& ret.1.view().unwrap().thread_id() == old(lctx).thread_id()
            &&& ret.1.view().unwrap().lock_id() == it.locking_thread()->Write_lock_id
        },
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).leaves_present(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        pei_valid(final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end),
        final(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        final(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        final(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == process_ptr,
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: false }),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
{
    proof {
        thread_perms_wf_at(krnl.thr_mp, thread_ptr); process_perms_wf_at(krnl.prc_mp, process_ptr);
    }
    assert({
        &&& krnl.pt_mp.dom().contains(pagetable)
        &&& old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable
        &&& krnl.pt_mp.spec_index(pagetable).view().cr3 == cr3
        &&& krnl.pt_mp.spec_index(pagetable).view().pcid == Some(pcid)
        &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3
        &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid
        &&& page_ptr_valid(cr3)
        &&& pcid_valid(pcid)
        &&& pcid != KERNEL_DEFAULT_PCID
    }) by {
        process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, process_ptr);
        process_pcid_allocator_wf_process_at(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp, process_ptr); pagetable_perms_wf_at(krnl.pt_mp, pagetable); krnl.pt_mp.spec_index(pagetable).view().table_pages_wf_cr3_at();
    };
    assert({
        &&& !krnl.prc_mp.spec_index(process_ptr).view().zombie
        &&& krnl.prc_mp.spec_index(process_ptr).view().pagetable == pagetable
        &&& krnl.pt_mp.spec_index(pagetable).view().proc_ptr == process_ptr
    }) by { process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, process_ptr); };
    assert({
        &&& krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr)
        &&& krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().contains(thread_ptr)
        &&& krnl.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr
    }) by { process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, process_ptr); container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr); };
    assert(old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth <= MAX_CONTAINER_TREE_DEPTH) by {
        container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr); container_perms_wf_at(krnl.ctn_mp, container_ptr);
    };
    let ghost lock_k = *krnl;
    let ghost lock_lctx = *lctx;
    let ghost lock_before = steps.view();
    let Tracked(pagetable_lock_perm) = krnl.wlock_pagetable(pagetable, Tracked(&mut *lctx));
    let ghost table_lctx = *lctx;
    proof { assert(lctx.held_lock_majors_lt(IOMMU_ROOT_TABLE_LOCK_MAJOR)) by { reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); }; }
    let Tracked(irt_lock_perm) = krnl.wlock_iommu_root_table(Tracked(&mut *lctx));
    thread_exit_detach_process_functions(krnl, process_ptr, Tracked(&*lctx), Tracked(&irt_lock_perm));
    let iommu_table_lock_perm = match iommu_table {
        Some(it) => {
            proof { assert(krnl.it_mp.dom().contains(it) && krnl.it_mp.spec_index(it).view().proc_ptr == process_ptr) by { process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, process_ptr); }; }
            let Tracked(perm) = krnl.wlock_iommu_table(it, Tracked(&mut *lctx));
            Tracked(Some(perm))
        },
        None => Tracked(None),
    };
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::ThreadExitReclaim { flushed: false })), Tracked(&*lctx), Tracked(thread_lock_perm));
    krnl.wunlock_iommu_root_table(Tracked(&mut *lctx), Tracked(irt_lock_perm));
    proof {
        let locked_k = *krnl;
        assert(lctx.iommu_root_table_lock_map() =~= table_lctx.iommu_root_table_lock_map());
        let locked_lctx = *lctx;
        assert(lctx.pagetable_lock_map().dom().contains(pagetable));
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        assert(thread_exit_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id)) by {
            thread_exit_lock_table_step_pre_from_k(&lock_k, &lock_lctx, cpu_id, container_ptr, process_ptr, thread_ptr, pagetable);
            kernel_process_tables_lock_state_and_progress_changed_implies_u_step(&lock_k, &locked_k, &locked_lctx, process_ptr, pagetable, thread_ptr, true);
            kernel_iommu_root_table_process_detached_implies_u(&lock_k, &locked_k, process_ptr);
            thread_exit_lock_table_step_from_u(kernel_k_to_kernel_u(lock_k), kernel_k_to_kernel_u(locked_k), cpu_id, process_ptr, thread_ptr);
            thread_exit_trace_push(&*steps, lock_before, start, pre, kernel_k_to_kernel_u(lock_k), kernel_k_to_kernel_u(locked_k), cpu_id);
        };
        pagetable_perms_wf_at(krnl.pt_mp, pagetable); krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end_valid();
        if iommu_table is Some {
            iommu_table_perms_wf_at(krnl.it_mp, iommu_table->Some_0); iommu_table_perms_wf_at(locked_k.it_mp, iommu_table->Some_0);
            assert(krnl.it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0) by { krnl.it_mp.spec_index(iommu_table->Some_0).view().kernel_entries_wf_l4_end_at(); };
        }
    }
    (Tracked(pagetable_lock_perm), iommu_table_lock_perm, Ghost(table_lctx))
}

/// Detach every attached function that `process_ptr` owns under the held root-table lock and empty its IOTLB domain,
/// scanning every B/D/F.
fn thread_exit_detach_process_functions(krnl: &mut KernelK, process_ptr: RwLockProcessPtr, Tracked(lctx): Tracked<&LocalContext>, Tracked(irt_lock_perm): Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), lctx),
        old(krnl).irt.wlocked_by(lctx),
        typed_lock_map_contains_mode(lctx.iommu_root_table_lock_map(), old(krnl).irt.view().table_base(), TypedLockMode::Write),
        irt_lock_perm.state() is WriteLock,
        irt_lock_perm.thread_id() == lctx.thread_id(),
        irt_lock_perm.lock_id() == old(krnl).irt.locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), lctx),
        *final(krnl) == (KernelK { irt: final(krnl).irt, iommu_tlb: final(krnl).iommu_tlb, ..*old(krnl) }),
        final(krnl).irt.locking_thread() == old(krnl).irt.locking_thread(),
        final(krnl).irt.view().table_base() == old(krnl).irt.view().table_base(),
        final(krnl).irt.view().owners() == old(krnl).irt.view().owners(),
        final(krnl).iommu_tlb.view().dom() == old(krnl).iommu_tlb.view().dom(),
        forall|b: usize, d: usize, f: usize| #![trigger final(krnl).irt.view().spec_index_iommu_root(b, d, f)] pci_bdf_valid(b, d, f)
            ==> final(krnl).irt.view().spec_index_iommu_root(b, d, f) == if old(krnl).irt.view().spec_index_owner(b, d, f) == process_ptr { None } else { old(krnl).irt.view().spec_index_iommu_root(b, d, f) },
        forall|b: usize, d: usize, f: usize| #![trigger final(krnl).iommu_tlb.view()[pci_bdf_did(b, d, f)]] pci_bdf_valid(b, d, f)
            ==> final(krnl).iommu_tlb.view()[pci_bdf_did(b, d, f)] == if old(krnl).irt.view().spec_index_owner(b, d, f) == process_ptr && old(krnl).irt.view().spec_index_iommu_root(b, d, f) is Some {
                SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }
            } else { old(krnl).iommu_tlb.view()[pci_bdf_did(b, d, f)] },
{
    let mut bus: usize = 0;
    let mut device: usize = 0;
    let mut function: usize = 0;
    while bus < PCI_BUS_COUNT
        invariant
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            *krnl == (KernelK { irt: krnl.irt, iommu_tlb: krnl.iommu_tlb, ..*old(krnl) }),
            krnl.irt.locking_thread() == old(krnl).irt.locking_thread(),
            krnl.irt.view().table_base() == old(krnl).irt.view().table_base(),
            krnl.irt.view().owners() == old(krnl).irt.view().owners(),
            krnl.iommu_tlb.view().dom() == old(krnl).iommu_tlb.view().dom(),
            old(krnl).irt.wlocked_by(lctx),
            typed_lock_map_contains_mode(lctx.iommu_root_table_lock_map(), old(krnl).irt.view().table_base(), TypedLockMode::Write),
            irt_lock_perm.state() is WriteLock,
            irt_lock_perm.thread_id() == lctx.thread_id(),
            irt_lock_perm.lock_id() == old(krnl).irt.locking_thread()->Write_lock_id,
            bus <= PCI_BUS_COUNT,
            device < PCI_DEVICE_COUNT,
            function < PCI_FUNCTION_COUNT,
            bus == PCI_BUS_COUNT ==> device == 0 && function == 0,
            forall|b: usize, d: usize, f: usize| #![trigger krnl.irt.view().spec_index_iommu_root(b, d, f)] pci_bdf_valid(b, d, f)
                ==> krnl.irt.view().spec_index_iommu_root(b, d, f) == if (b < bus || (b == bus && (d < device || (d == device && f < function)))) && old(krnl).irt.view().spec_index_owner(b, d, f) == process_ptr {
                    None
                } else { old(krnl).irt.view().spec_index_iommu_root(b, d, f) },
            forall|b: usize, d: usize, f: usize| #![trigger krnl.iommu_tlb.view()[pci_bdf_did(b, d, f)]] pci_bdf_valid(b, d, f)
                ==> krnl.iommu_tlb.view()[pci_bdf_did(b, d, f)] == if (b < bus || (b == bus && (d < device || (d == device && f < function))))
                    && old(krnl).irt.view().spec_index_owner(b, d, f) == process_ptr && old(krnl).irt.view().spec_index_iommu_root(b, d, f) is Some {
                    SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }
                } else { old(krnl).iommu_tlb.view()[pci_bdf_did(b, d, f)] },
        decreases PCI_BUS_COUNT - bus, PCI_DEVICE_COUNT - device, PCI_FUNCTION_COUNT - function,
    {
        let owner = krnl.irt.borrow(Tracked(irt_lock_perm)).owner(bus, device, function);
        let attached = krnl.irt.borrow(Tracked(irt_lock_perm)).is_attached(bus, device, function);
        if owner == process_ptr && attached {
            let ghost detach_k = *krnl;
            iommu_root_table_detach(&mut krnl.irt, &mut krnl.iommu_tlb, bus, device, function, Tracked(lctx), Tracked(irt_lock_perm));
            proof {
                assert(thread_exit_detach_process_functions_eof_transition_framing(detach_k, *krnl, bus, device, function)) by { reveal(thread_exit_detach_process_functions_eof_transition_framing); };
                thread_exit_detach_process_functions_eof(detach_k, *krnl, bus, device, function);
            }
        }
        if function + 1 < PCI_FUNCTION_COUNT {
            function = function + 1;
        } else if device + 1 < PCI_DEVICE_COUNT {
            function = 0;
            device = device + 1;
        } else {
            function = 0;
            device = 0;
            bus = bus + 1;
        }
    }
}

/// Clear every user 4K leaf of the locked page table, one leaf step each, walking the mapped VAs in index order.
fn thread_exit_reclaim_clear_leaves(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Ghost(cpu_id): Ghost<CpuId>,
    Ghost(container_ptr): Ghost<RwLockContainerPtr>, Ghost(process_ptr): Ghost<RwLockProcessPtr>, Ghost(thread_ptr): Ghost<RwLockThreadPtr>,
    pagetable: RwLockPageTableRoot, Ghost(cr3): Ghost<PageTableRoot>, Ghost(pcid): Ghost<Pcid>, Ghost(kernel_l4_end): Ghost<usize>, start_l4: L4Index,
    Ghost(entry_k): Ghost<KernelK>, Ghost(entry_lctx): Ghost<LocalContext>, Ghost(pt_entry): Ghost<TypedHeldLock>, Ghost(locked_pt): Ghost<PageTableC<PT_TYPE>>,
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
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m() == locked_pt.mapping_2m(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g() == locked_pt.mapping_1g(),
        locked_pt.leaves_present(),
        forall|k: (PageMapPtr, L2Index)| #![trigger pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)]
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k) ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index(k) == Set::range(0usize, NUM_CPUS),
        kernel_l4_end <= start_l4,
        KERNEL_MEM_END_L4INDEX <= start_l4,
        start_l4 == kernel_l4_end || start_l4 == KERNEL_MEM_END_L4INDEX,
        pei_valid(start_l4),
        forall|va: VAddr| #![trigger pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va)]
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va) && !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..entry_k.thr_mp.spec_index(thread_ptr).view() }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: false }),
        0 <= start <= old(steps).view().len(),
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
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m() == locked_pt.mapping_2m(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_1g() == locked_pt.mapping_1g(),
        forall|k: (PageMapPtr, L2Index)| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)]
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k) ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index(k) == Set::range(0usize, NUM_CPUS),
        forall|va: VAddr| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va)]
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va) && !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
        final(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        final(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        final(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == process_ptr,
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..entry_k.thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: false }),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                ==> !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
{
    proof { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable); }
    let mut cursor: (L4Index, L3Index, L2Index, L1Index) = (start_l4, 0, 0, 0);
    let mut found = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(&pagetable_lock_perm)).next_mapped_4k_from(Tracked(krnl.pt_lower.borrow().tracked_borrow(pagetable)), cursor);
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
            krnl.cpu_arr.spec_index(cpu_id).view().locking_thread() == entry_k.cpu_arr.spec_index(cpu_id).view().locking_thread(),
            krnl.cpu_arr.spec_index(cpu_id).view().being_killed() == entry_k.cpu_arr.spec_index(cpu_id).view().being_killed(),
            krnl.cpu_arr.spec_index(cpu_id).view().killer_info() == entry_k.cpu_arr.spec_index(cpu_id).view().killer_info(),
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
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m() == locked_pt.mapping_2m(),
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_1g() == locked_pt.mapping_1g(),
            locked_pt.leaves_present(),
            forall|k: (PageMapPtr, L2Index)| #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)]
                pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k) ==> pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index(k) == Set::range(0usize, NUM_CPUS),
            kernel_l4_end <= start_l4,
            KERNEL_MEM_END_L4INDEX <= start_l4,
            start_l4 == kernel_l4_end || start_l4 == KERNEL_MEM_END_L4INDEX,
            pei_valid(start_l4),
            forall|va: VAddr| #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(va)]
                pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(va) && !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
            krnl.pt_mp.spec_index(pagetable).view().cr3 == cr3,
            krnl.pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
            krnl.pt_mp.spec_index(pagetable).view().proc_ptr == process_ptr,
            krnl.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..entry_k.thr_mp.spec_index(thread_ptr).view() }),
            krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: false }),
            0 <= start <= old(steps).view().len() <= steps.view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
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
                &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va(next))
            },
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i))
                    && (found is None || !spec_l4_index_path_le(found->Some_0, (l4i, l3i, l2i, l1i))) ==> !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && !spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i)) && pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                    ==> !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
        decreases 512 - cursor.0, 512 - cursor.1, 512 - cursor.2, 513 - cursor.3,
    {
        let next = found.unwrap();
        let va = index2va(next);
        let ghost iter_pt = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        proof {
            pagetable_perms_wf_map(krnl.pt_mp);
            pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
            assert(spec_va_4k_valid(va) && spec_va2index(va) == next) by { spec_va_4k_index_roundtrip_at(va, next.0, next.1, next.2, next.3); };
        }
        let resolved = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(&pagetable_lock_perm)).resolve_mapping_4k_l1(Tracked(krnl.pt_lower.borrow().tracked_borrow(pagetable)), next.0, next.1, next.2, next.3);
        if resolved.2.is_some() && resolved.2.unwrap().present {
            thread_exit_reclaim_clear_leaf(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), Ghost(cpu_id), Ghost(container_ptr), Ghost(process_ptr), Ghost(thread_ptr), pagetable, va,
                Ghost(iommu_table), Tracked(pagetable_lock_perm), Ghost(start), Ghost(pre));
        } else {
            proof {
                assert(!pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(va) || !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(va).present) by {
                    pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).wf_mapping_4k_at(next.0, next.1, next.2, next.3);
                };
            }
        }
        cursor = (next.0, next.1, next.2, next.3 + 1);
        proof {
            assert forall|key: VAddr| #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(key)]
                pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(key) && !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(key).present
                implies spec_va_4k_valid(key) && start_l4 <= spec_v2l4index(key) by {
                if key != va { assert(iter_pt.mapping_4k().dom().contains(key) && iter_pt.mapping_4k().spec_index(key) == pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(key)); }
            };
            pagetable_perms_wf_map(krnl.pt_mp);
            pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        }
        found = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(&pagetable_lock_perm)).next_mapped_4k_from(Tracked(krnl.pt_lower.borrow().tracked_borrow(pagetable)), cursor);
    }
}
} // verus!
