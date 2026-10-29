use vstd::prelude::*;
use crate::*;
use super::syscall_iommu_map_4k_spec::*;
use super::iommu_map_4k_directory_step::iommu_map_4k_ensure_l1;
#[cfg(verus_keep_ghost)]
use super::syscall_iommu_map_4k_trace::*;

verus! {
/// Map page `i` of `va_range` at page `i` of `iova_range`, installing each missing IOMMU directory level first; `k0` and `lctx0`
/// are the state and lock context at the start of the range. Records one leaf step and at most three directory steps.
pub(super) fn iommu_map_4k_map_one_page(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va_range: &VaRange4K, iova_range: &VaRange4K, i: usize,
    thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, pagetable_ptr: RwLockPageTableRoot, iommu_table_ptr: RwLockPageTableRoot,
    Ghost(k0): Ghost<KernelK>, Ghost(lctx0): Ghost<LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>, Tracked(thread_lock_perm): Tracked<&LockPerm>,
    Tracked(iommu_table_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        typed_lock_maps_unchanged(&lctx0, old(lctx)),
        old(lctx).cpu_id() == lctx0.cpu_id(),
        old(lctx).thread_id() == lctx0.thread_id(),
        old(steps).snapshot_k() == *old(krnl),
        i < va_range.len,
        i + 1 <= old(steps).view().len() <= 4 * i + 1,
        iommu_map_4k_enter_step_pre(old(steps).view()[0].old_u, cpu_id, *va_range, *iova_range),
        iommu_map_4k_enter_step(old(steps).view()[0].old_u, old(steps).view()[0].new_u, cpu_id, *va_range, *iova_range),
        forall|j: int| #![trigger old(steps).view()[j]] 0 < j < old(steps).view().len() ==> iommu_map_4k_range_step(old(steps).view()[j], cpu_id),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        index_valid(NUM_CPUS, cpu_id) && cpu_id == lctx0.cpu_id(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        typed_lock_map_contains_mode(lctx0.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx0.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx0.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx0.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        typed_lock_map_contains_mode(lctx0.iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        lctx0.cpu_lock_map().dom() == set![cpu_id] && lctx0.thread_lock_map().dom() == set![thread_ptr],
        lctx0.page_lock_map().dom().is_empty(),
        lctx0.pcid_needflush_lock_map().dom().is_empty() && lctx0.cpu_offline_flag_lock_map().dom().is_empty(),
        lctx0.scheduler_lock_map().dom().is_empty() && lctx0.cpu_set_lock_map().dom().is_empty(),
        lctx0.holds_no_allocator_locks(PageSize::SZ4k) && lctx0.holds_no_allocator_locks(PageSize::SZ2m) && lctx0.holds_no_allocator_locks(PageSize::SZ1g),
        va_range.wf() && iova_range.wf() && iova_range.len == va_range.len,
        va_4k_valid(va_range.view()[i as int]) && va_4k_valid(iova_range.view()[i as int]),
        lctx0.pagetable_window_lock_map().dom().contains((pagetable_ptr, window_of(va_range.view()[i as int]))),
        pagetable_c(k0.pt_mp, k0.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va_range.start),
        pagetable_c(k0.pt_mp, k0.pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(va_range.view()[i as int]),
        pagetable_c(k0.pt_mp, k0.pt_lower.view(), pagetable_ptr).mapping_4k()[va_range.view()[i as int]].present,
        k0.thr_mp.dom().contains(thread_ptr) && !thread_is_dangling(k0.thr_mp.spec_index(thread_ptr)),
        k0.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        k0.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        k0.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        k0.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        k0.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        forall|held_thread: RwLockThreadPtr| #![trigger lctx0.thread_lock_map().dom().contains(held_thread)] lctx0.thread_lock_map().dom().contains(held_thread)
            ==> k0.thr_mp.spec_index(held_thread).being_killed() || !(k0.thr_mp.spec_index(held_thread).view().state is SCHEDULED),
        !k0.thr_mp.spec_index(thread_ptr).view_ghost().exited,
        k0.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr,
        k0.prc_mp.spec_index(process_ptr).view().iommu_table == Some(iommu_table_ptr),
        !(k0.cpu_arr.spec_index(cpu_id).view().view().view().state is Off),
        pagetable_lock_perm.state() is ReadLock && pagetable_lock_perm.thread_id() == lctx0.thread_id(),
        k0.pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(lctx0.thread_id(), pagetable_lock_perm.lock_id()),
        thread_lock_perm.state() is WriteLock && thread_lock_perm.thread_id() == lctx0.thread_id(),
        iommu_table_lock_perm.state() is WriteLock && iommu_table_lock_perm.thread_id() == lctx0.thread_id(),
        old(krnl).cpu_arr.spec_index(cpu_id).view() == k0.cpu_arr.spec_index(cpu_id).view(),
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == k0.cpu_hw_cr3_pcid[cpu_id as int].view(),
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).prc_mp.spec_index(process_ptr) == k0.prc_mp.spec_index(process_ptr),
        held_pagetables_unchanged(k0.pt_mp, old(krnl).pt_mp, &lctx0),
        held_pagetable_windows_unchanged(k0.pt_mp, k0.pt_lower.view(), old(krnl).pt_mp, old(krnl).pt_lower.view(), &lctx0),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread {
            quota_4k: old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k, temp_alloc_cache_4k: old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k,
            syscall_progress: old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..k0.thr_mp.spec_index(thread_ptr).view()
        }),
        old(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == k0.thr_mp.spec_index(thread_ptr).view_ghost(),
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= 3 * (va_range.len - i),
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()
            == Some(SyscallProgress::IommuMap4k { va_range: *va_range, iova_range: *iova_range, mapped: i, directory: Mmap4kDirectory::None }),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        iommu_table_lock_perm.lock_id() == old(krnl).it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
        old(krnl).it_mp.dom().contains(iommu_table_ptr),
        old(krnl).it_mp.spec_index(iommu_table_ptr).view().proc_ptr == k0.it_mp.spec_index(iommu_table_ptr).view().proc_ptr,
        old(krnl).it_mp.spec_index(iommu_table_ptr).view().leaves_present(),
        forall|j: int| #![trigger iova_range.view()[j]] i <= j < va_range.len ==> !old(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_4k().dom().contains(iova_range.view()[j]),
    ensures
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(&lctx0, final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(steps).snapshot_k() == *final(krnl),
        i + 2 <= final(steps).view().len() <= 4 * i + 5,
        final(steps).view()[0] == old(steps).view()[0],
        forall|j: int| #![trigger final(steps).view()[j]] 0 < j < final(steps).view().len() ==> iommu_map_4k_range_step(final(steps).view()[j], cpu_id),
        held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == k0.cpu_arr.spec_index(cpu_id).view(),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == k0.cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).prc_mp.dom().contains(process_ptr),
        final(krnl).prc_mp.spec_index(process_ptr) == k0.prc_mp.spec_index(process_ptr),
        held_pagetables_unchanged(k0.pt_mp, final(krnl).pt_mp, &lctx0),
        held_pagetable_windows_unchanged(k0.pt_mp, k0.pt_lower.view(), final(krnl).pt_mp, final(krnl).pt_lower.view(), &lctx0),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread {
            quota_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k, temp_alloc_cache_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k,
            syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..k0.thr_mp.spec_index(thread_ptr).view()
        }),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == k0.thr_mp.spec_index(thread_ptr).view_ghost(),
        !final(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= 3 * (va_range.len - (i + 1)),
        final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()
            == Some(SyscallProgress::IommuMap4k { va_range: *va_range, iova_range: *iova_range, mapped: (i + 1) as usize, directory: Mmap4kDirectory::None }),
        thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        iommu_table_lock_perm.lock_id() == final(krnl).it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
        final(krnl).it_mp.dom().contains(iommu_table_ptr),
        final(krnl).it_mp.spec_index(iommu_table_ptr).view().proc_ptr == k0.it_mp.spec_index(iommu_table_ptr).view().proc_ptr,
        final(krnl).it_mp.spec_index(iommu_table_ptr).view().leaves_present(),
        forall|j: int| #![trigger iova_range.view()[j]] i + 1 <= j < va_range.len ==> !final(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_4k().dom().contains(iova_range.view()[j]),
{
    let va = va_range.index(i);
    let iova = iova_range.index(i);
    iommu_map_4k_ensure_l1(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va_range, iova_range, i, thread_ptr, process_ptr, container_ptr, pagetable_ptr, iommu_table_ptr,
        Ghost(k0), Ghost(lctx0), Tracked(thread_lock_perm), Tracked(iommu_table_lock_perm));
    let ghost leaf_start = *krnl;
    let ghost leaf_lctx = *lctx;
    let ghost leaf_steps = steps.view();
    proof {
        spec_va_4k_index_roundtrip_at(va, spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
        spec_va_4k_index_roundtrip_at(window_of(va).va, spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), 0);
        held_pagetable_window_mapping_4k_unchanged_at(k0.pt_mp, k0.pt_lower.view(), krnl.pt_mp, krnl.pt_lower.view(), &lctx0, pagetable_ptr, window_of(va), va);
        va_range.va_range_lemma(); spec_v2l4index_monotonic(va_range.start, va);
        krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
        process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, process_ptr); process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, process_ptr);
    }
    map_shared_page_into_iommu_4k(krnl, process_ptr, thread_ptr, pagetable_ptr, iommu_table_ptr, va, iova, Tracked(&mut *lctx), Tracked(pagetable_lock_perm), Tracked(iommu_table_lock_perm));
    let ghost mapped_k = *krnl;
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(iommu_map_4k_progress_after_leaf(krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view())), Tracked(&*lctx),
        Tracked(thread_lock_perm));
    proof {
        let leaf_k = *krnl;
        process_thread_wf_at(leaf_start.prc_mp, leaf_start.thr_mp, thread_ptr);
        iommu_map_4k_leaf_step_from_k(&leaf_start, &mapped_k, &leaf_k, &leaf_lctx, cpu_id, process_ptr, thread_ptr, pagetable_ptr, iommu_table_ptr);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        iommu_map_4k_trace_push_range_step(steps.view(), leaf_steps, kernel_k_to_kernel_u(leaf_start), kernel_k_to_kernel_u(leaf_k), cpu_id, *va_range, *iova_range);
    }
}
} // verus!
