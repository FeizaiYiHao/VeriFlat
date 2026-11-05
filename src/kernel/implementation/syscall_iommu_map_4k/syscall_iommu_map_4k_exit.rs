use vstd::prelude::*;
use crate::*;
use super::syscall_iommu_map_4k_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_iommu_map_4k_trace::*;

verus! {
/// After the whole range is mapped, clear progress, release the windows and every IOMMU-map lock, and record the exit step;
/// `k0` and `lctx0` are the state and lock context at the start of the range.
pub(super) fn iommu_map_4k_exit(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va_range: &VaRange4K, iova_range: &VaRange4K,
    thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot, iommu_table_ptr: RwLockPageTableRoot, Ghost(k0): Ghost<KernelK>,
    Ghost(lctx0): Ghost<LocalContext>, Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(process_lock_perm): Tracked<LockPerm>, Tracked(thread_lock_perm): Tracked<LockPerm>,
    Tracked(pagetable_lock_perm): Tracked<LockPerm>, Tracked(iommu_table_lock_perm): Tracked<LockPerm>, Tracked(window_perms): Tracked<Map<WindowVa, LockPerm>>,
)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        typed_lock_maps_unchanged(&lctx0, old(lctx)),
        old(lctx).cpu_id() == lctx0.cpu_id(),
        old(lctx).thread_id() == lctx0.thread_id(),
        old(steps).snapshot_k() == *old(krnl),
        va_range.len + 1 <= old(steps).view().len() <= 4 * va_range.len + 1,
        iommu_map_4k_enter_step_pre(old(steps).view()[0].old_u, cpu_id, *va_range, *iova_range),
        iommu_map_4k_enter_step(old(steps).view()[0].old_u, old(steps).view()[0].new_u, cpu_id, *va_range, *iova_range),
        forall|j: int| #![trigger old(steps).view()[j]] 0 < j < old(steps).view().len() ==> iommu_map_4k_range_step(old(steps).view()[j], cpu_id),
        index_valid(NUM_CPUS, cpu_id) && cpu_id == lctx0.cpu_id(),
        typed_lock_map_contains_mode(lctx0.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx0.process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx0.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx0.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        typed_lock_map_contains_mode(lctx0.iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        lctx0.cpu_lock_map().dom() == set![cpu_id],
        lctx0.process_lock_map().dom() == set![prc_ptr],
        lctx0.thread_lock_map().dom() == set![thrd_ptr],
        lctx0.pagetable_lock_map().dom() == set![pagetable_ptr],
        lctx0.iommu_table_lock_map().dom() == set![iommu_table_ptr],
        lctx0.page_lock_map().dom().is_empty() && lctx0.container_lock_map().dom().is_empty() && lctx0.endpoint_lock_map().dom().is_empty(),
        lctx0.pcid_allocator_lock_map().dom().is_empty() && lctx0.iommu_root_table_lock_map().dom().is_empty(),
        lctx0.pcid_needflush_lock_map().dom().is_empty() && lctx0.cpu_offline_flag_lock_map().dom().is_empty(),
        lctx0.scheduler_lock_map().dom().is_empty() && lctx0.cpu_set_lock_map().dom().is_empty(),
        lctx0.holds_no_allocator_locks(PageSize::SZ4k) && lctx0.holds_no_allocator_locks(PageSize::SZ2m) && lctx0.holds_no_allocator_locks(PageSize::SZ1g),
        va_range.wf() && iova_range.wf() && va_range.len > 0 && iova_range.len == va_range.len,
        *va_range == spec_va_range_4k(va_range.start, va_range.len) && *iova_range == spec_va_range_4k(iova_range.start, iova_range.len),
        whole_pagetable(k0.pt_mp, k0.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va_range.start),
        k0.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        k0.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        k0.thrd_mp.dom().contains(thrd_ptr) && !thread_is_dangling(k0.thrd_mp.spec_index(thrd_ptr)),
        k0.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        k0.thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        !k0.cpu_arr.spec_index(cpu_id).view().being_killed(),
        k0.cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() is None,
        !k0.prc_mp.spec_index(prc_ptr).being_killed() && !k0.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        k0.prc_mp.spec_index(prc_ptr).view().state.view() is Running || k0.prc_mp.spec_index(prc_ptr).view().state.view() is Zombie,
        !(k0.thrd_mp.spec_index(thrd_ptr).view().state is IPC_TRANSIT) && !(k0.thrd_mp.spec_index(thrd_ptr).view().state is KILLED),
        k0.cpu_hw_cr3_pcid[cpu_id as int].view() == (k0.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, k0.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == k0.cpu_hw_cr3_pcid[cpu_id as int].view(),
        k0.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr,
        k0.prc_mp.spec_index(prc_ptr).view().iommu_table == Some(iommu_table_ptr),
        cpu_lock_perm.state() is WriteLock && cpu_lock_perm.thread_id() == lctx0.thread_id(),
        cpu_lock_perm.lock_id() == k0.cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        process_lock_perm.state() is WriteLock && process_lock_perm.thread_id() == lctx0.thread_id(),
        process_lock_perm.lock_id() == k0.prc_mp.spec_index(prc_ptr).locking_thread()->Write_lock_id,
        thread_lock_perm.state() is WriteLock && thread_lock_perm.thread_id() == lctx0.thread_id(),
        pagetable_lock_perm.state() is ReadLock && pagetable_lock_perm.thread_id() == lctx0.thread_id(),
        k0.pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(lctx0.thread_id(), pagetable_lock_perm.lock_id()),
        iommu_table_lock_perm.state() is WriteLock && iommu_table_lock_perm.thread_id() == lctx0.thread_id(),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger lctx0.pagetable_window_lock_map().dom().contains((p, w))]
            lctx0.pagetable_window_lock_map().dom().contains((p, w)) == (p == pagetable_ptr && window_perms.dom().contains(w)),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*va_range).contains(w)]
            va_range_2m_windows(*va_range).contains(w) && whole_pagetable(k0.pt_mp, k0.pt_lower.view(), pagetable_ptr).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
            ==> window_perms.dom().contains(w),
        forall|w: WindowVa| #![trigger window_perms.dom().contains(w)]
            window_perms.dom().contains(w) ==> {
                &&& va_range_2m_windows(*va_range).contains(w)
                &&& whole_pagetable(k0.pt_mp, k0.pt_lower.view(), pagetable_ptr).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(lctx0.pagetable_window_lock_map(), (pagetable_ptr, w), TypedLockMode::Write)
                &&& window_perms.index(w).state() is WriteLock
                &&& window_perms.index(w).thread_id() == lctx0.thread_id()
                &&& whole_pagetable(k0.pt_mp, k0.pt_lower.view(), pagetable_ptr).lower.l2_owner(whole_pagetable(k0.pt_mp, k0.pt_lower.view(), pagetable_ptr).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
                    == (RwLockState::Write { thread_id: window_perms.index(w).thread_id(), lock_id: window_perms.index(w).lock_id() })
                &&& whole_pagetable(k0.pt_mp, k0.pt_lower.view(), pagetable_ptr).window_leaves_present(w)
                &&& !whole_pagetable(k0.pt_mp, k0.pt_lower.view(), pagetable_ptr).lower.window_stale_cpus.dom().contains((whole_pagetable(k0.pt_mp, k0.pt_lower.view(), pagetable_ptr).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
                &&& !whole_pagetable(k0.pt_mp, k0.pt_lower.view(), pagetable_ptr).lower.l2_entry_hides_l1(whole_pagetable(k0.pt_mp, k0.pt_lower.view(), pagetable_ptr).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
            },
        old(krnl).cpu_arr.spec_index(cpu_id).view() == k0.cpu_arr.spec_index(cpu_id).view(),
        old(krnl).prc_mp.dom().contains(prc_ptr),
        old(krnl).prc_mp.spec_index(prc_ptr) == k0.prc_mp.spec_index(prc_ptr),
        held_pagetables_unchanged(k0.pt_mp, old(krnl).pt_mp, &lctx0),
        held_pagetable_windows_unchanged(k0.pt_mp, k0.pt_lower.view(), old(krnl).pt_mp, old(krnl).pt_lower.view(), &lctx0),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread {
            quota_4k: old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k, temp_alloc_cache_4k: old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k,
            syscall_progress: old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..k0.thrd_mp.spec_index(thrd_ptr).view()
        }),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == k0.thrd_mp.spec_index(thrd_ptr).view_ghost(),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()
            == Some(SyscallProgress::IommuMap4k { va_range: *va_range, iova_range: *iova_range, mapped: va_range.len, directory: Mmap4kDirectory::None }),
        thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        iommu_table_lock_perm.lock_id() == old(krnl).it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
        old(krnl).it_mp.dom().contains(iommu_table_ptr),
        old(krnl).it_mp.spec_index(iommu_table_ptr).view().leaves_present(),
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view()[0] == old(steps).view()[0],
        iommu_map_4k_syscall_trace(final(steps).view(), cpu_id, va_range.start, iova_range.start, va_range.len),
        va_range.len + 2 <= final(steps).view().len() <= 4 * va_range.len + 2,
{
    let ghost exit_start = *krnl;
    let ghost exit_steps = steps.view();
    let ghost exit_lctx = *lctx;
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(None), Tracked(&*lctx), Tracked(&thread_lock_perm));
    krnl.unlock_pagetable_range_existing_windows(pagetable_ptr, va_range, Tracked(&pagetable_lock_perm), Tracked(&mut *lctx), Tracked(window_perms));
    krnl.wunlock_iommu_table(iommu_table_ptr, Tracked(&mut *lctx), Tracked(iommu_table_lock_perm));
    let ghost pt_before_runlock = krnl.pt_mp.spec_index(pagetable_ptr).locking_thread();
    krnl.runlock_pagetable(cpu_id, pagetable_ptr, Tracked(&mut *lctx), Tracked(pagetable_lock_perm));
    proof { assert(pt_before_runlock->Read_reader_map.remove(cpu_id).dom() =~= pt_before_runlock->Read_reader_map.dom().remove(cpu_id)); }
    krnl.wunlock_thread(thrd_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
    krnl.wunlock_process(prc_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
    proof { assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); }; }
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        process_thread_wf_thread_at(exit_start.prc_mp, exit_start.thrd_mp, thrd_ptr);
        process_pagetable_wf_process_at(exit_start.prc_mp, exit_start.pt_mp, prc_ptr); process_iommu_table_wf_process_at(exit_start.prc_mp, exit_start.it_mp, prc_ptr);
        iommu_map_4k_exit_step_from_k(&exit_start, &*krnl, &exit_lctx, cpu_id, prc_ptr, thrd_ptr, pagetable_ptr, iommu_table_ptr);
        steps.end_kernel_step_thread_syscall_progress_changed(&*krnl, &*lctx, thrd_ptr);
        iommu_map_4k_trace_exit(steps.view(), exit_steps, kernel_k_to_kernel_u(exit_start), kernel_k_to_kernel_u(*krnl), cpu_id, *va_range, *iova_range);
    }
}
} // verus!
