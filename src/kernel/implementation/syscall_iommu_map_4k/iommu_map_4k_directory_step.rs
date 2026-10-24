use vstd::prelude::*;
use crate::*;
use super::syscall_iommu_map_4k_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_iommu_map_4k_trace::*;

verus! {
/// Install the missing IOMMU directory page `level` on the path of `indices` from a freshly allocated 4K page, charged to the
/// running thread's quota; the section is one directory step.
pub(super) fn iommu_map_4k_install_directory(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, level: MissingPageTableLevel, cpu_id: CpuId,
    va_range: Ghost<VaRange4K>, iova_range: Ghost<VaRange4K>, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr,
    pagetable_ptr: RwLockPageTableRoot, iommu_table_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index), Tracked(thread_lock_perm): Tracked<&LockPerm>,
    Tracked(iommu_table_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        !thread_is_dangling(old(krnl).thr_mp.spec_index(thread_ptr)),
        old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= 1,
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        thread_lock_perm.state() is WriteLock && thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr,
        old(krnl).prc_mp.spec_index(process_ptr).view().iommu_table == Some(iommu_table_ptr),
        iommu_table_lock_perm.state() is WriteLock && iommu_table_lock_perm.thread_id() == old(lctx).thread_id(),
        iommu_table_lock_perm.lock_id() == old(krnl).it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        pei_valid(indices.0) && pei_valid(indices.1) && pei_valid(indices.2),
        ({
            let progress = old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view();
            &&& progress is Some && progress->Some_0 is IommuMap4k
            &&& progress->Some_0->IommuMap4k_va_range == va_range.view() && progress->Some_0->IommuMap4k_iova_range == iova_range.view()
            &&& progress->Some_0->IommuMap4k_mapped < progress->Some_0->IommuMap4k_iova_range.len
            &&& mmap_4k_directory_rank(progress->Some_0->IommuMap4k_directory) < mmap_4k_directory_rank(mmap_4k_installed_directory(level))
        }),
        match level {
            MissingPageTableLevel::L4 => old(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_l4(indices.0) is None,
            MissingPageTableLevel::L3 => {
                &&& old(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_l4(indices.0) is Some
                &&& old(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) is None
            },
            MissingPageTableLevel::L2 => {
                &&& old(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) is Some
                &&& old(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None
            },
        },
        old(steps).view().len() >= 1,
        iommu_map_4k_enter_step_pre(old(steps).view()[0].old_u, cpu_id, va_range.view(), iova_range.view()),
        iommu_map_4k_enter_step(old(steps).view()[0].old_u, old(steps).view()[0].new_u, cpu_id, va_range.view(), iova_range.view()),
        forall|j: int| #![trigger old(steps).view()[j]] 0 < j < old(steps).view().len() ==> iommu_map_4k_range_step(old(steps).view()[j], cpu_id),
    ensures
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view().len() == old(steps).view().len() + 1,
        final(steps).view()[0] == old(steps).view()[0],
        forall|j: int| #![trigger final(steps).view()[j]] 0 < j < final(steps).view().len() ==> iommu_map_4k_range_step(final(steps).view()[j], cpu_id),
        held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        held_pagetable_windows_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), final(krnl).pt_mp, final(krnl).pt_lower.view(), old(lctx)),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread {
            quota_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k, temp_alloc_cache_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k,
            syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view()
        }),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        !final(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k - 1,
        final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()
            == iommu_map_4k_progress_after_directory(old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), level),
        thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        iommu_table_lock_perm.lock_id() == final(krnl).it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
        final(krnl).it_mp.dom().contains(iommu_table_ptr),
        final(krnl).it_mp.spec_index(iommu_table_ptr).view().proc_ptr == old(krnl).it_mp.spec_index(iommu_table_ptr).view().proc_ptr,
        final(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_4k() == old(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_4k(),
        final(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_2m() == old(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_2m(),
        final(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_1g() == old(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_1g(),
        final(krnl).prc_mp.dom().contains(process_ptr),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        match level {
            MissingPageTableLevel::L4 => final(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_l4(indices.0) is Some,
            MissingPageTableLevel::L3 => final(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) is Some,
            MissingPageTableLevel::L2 => final(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        },
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    let ghost entry_lctx = *lctx;
    let (page_ptr, Tracked(page_lock_perm)) = allocate_free_4k_page(krnl, thread_ptr, container_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm));
    let page_index = page_ptr2page_index(page_ptr);
    let ghost staged_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
    let ghost section_start = *krnl;
    let ghost section_lctx = *lctx;
    let ghost before_steps = steps.view();
    proof {
        let it = krnl.it_mp.spec_index(iommu_table_ptr).view();
        process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr); process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, process_ptr);
        assert(it.spec_resolve_mapping_1g_l3(indices.0, indices.1) is None && it.spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None) by {
            iommu_table_perms_wf_map(krnl.it_mp); iommu_table_perms_wf_at(krnl.it_mp, iommu_table_ptr); iommu_table_perms_wf_kernel_l4_end_at(krnl.it_mp, iommu_table_ptr);
            pagetable_no_huge_leaf_wf_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.it_mp, iommu_table_ptr); it.wf_mapping_1g_at(indices.0, indices.1); it.wf_mapping_2m_at(indices.0, indices.1, indices.2);
        };
    }
    install_staged_4k_iommu_table_page(krnl, level, page_ptr, thread_ptr, process_ptr, container_ptr, iommu_table_ptr, indices, Tracked(&mut *lctx), Tracked(&page_lock_perm),
        Tracked(thread_lock_perm), Tracked(iommu_table_lock_perm));
    krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
    proof {
        let installed_k = *krnl;
        assert(typed_lock_maps_unchanged(&entry_lctx, lctx)) by {
            map_insert_overwrite_lemma(entry_lctx.page_lock_map(), page_index, TypedHeldLock { lock_id: staged_page_lock_id, mode: TypedLockMode::Write },
                TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
            map_insert_remove_absent_lemma(entry_lctx.page_lock_map(), page_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
        };
        section_start.thr_mp.typed_lock_map_aligned_write_at(section_lctx.thread_lock_map(), section_lctx.thread_id(), thread_ptr);
        installed_k.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr);
        assert(kernel_thread_quota_4k_changed(&section_start, krnl, thread_ptr, -1)) by { reveal(kernel_thread_quota_4k_changed); };
        krnl.kernel_step_boundary_thread_quota_4k_changed(&mut *lctx, &mut *steps, thread_ptr, -1);
        iommu_map_4k_directory_step_from_k(&section_start, &installed_k, &section_lctx, cpu_id, process_ptr, thread_ptr, pagetable_ptr, iommu_table_ptr, level);
        iommu_map_4k_trace_push_range_step(steps.view(), before_steps, kernel_k_to_kernel_u(section_start), kernel_k_to_kernel_u(installed_k), cpu_id, va_range.view(), iova_range.view());
    }
}

/// Install every missing IOMMU directory level on the path of page `i` of `iova_range` so its L1 page is linked; `k0` and
/// `lctx0` are the state and lock context at the start of the range. Records at most three directory steps.
pub(super) fn iommu_map_4k_ensure_l1(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va_range: &VaRange4K, iova_range: &VaRange4K, i: usize,
    thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, pagetable_ptr: RwLockPageTableRoot, iommu_table_ptr: RwLockPageTableRoot,
    Ghost(k0): Ghost<KernelK>, Ghost(lctx0): Ghost<LocalContext>, Tracked(thread_lock_perm): Tracked<&LockPerm>, Tracked(iommu_table_lock_perm): Tracked<&LockPerm>,
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
        typed_lock_map_contains_mode(lctx0.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx0.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx0.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx0.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        typed_lock_map_contains_mode(lctx0.iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        lctx0.page_lock_map().dom().is_empty(),
        va_range.wf() && iova_range.wf() && iova_range.len == va_range.len,
        va_4k_valid(iova_range.view()[i as int]),
        k0.thr_mp.dom().contains(thread_ptr) && !thread_is_dangling(k0.thr_mp.spec_index(thread_ptr)),
        k0.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        k0.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        k0.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        k0.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        k0.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        k0.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr,
        k0.prc_mp.spec_index(process_ptr).view().iommu_table == Some(iommu_table_ptr),
        thread_lock_perm.state() is WriteLock && thread_lock_perm.thread_id() == lctx0.thread_id(),
        iommu_table_lock_perm.state() is WriteLock && iommu_table_lock_perm.thread_id() == lctx0.thread_id(),
        old(krnl).cpu_arr.spec_index(cpu_id).view() == k0.cpu_arr.spec_index(cpu_id).view(),
        old(krnl).cpu_published[cpu_id as int].view() == k0.cpu_published[cpu_id as int].view(),
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
    ensures
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(&lctx0, final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(steps).snapshot_k() == *final(krnl),
        i + 1 <= final(steps).view().len() <= 4 * i + 4,
        final(steps).view()[0] == old(steps).view()[0],
        forall|j: int| #![trigger final(steps).view()[j]] 0 < j < final(steps).view().len() ==> iommu_map_4k_range_step(final(steps).view()[j], cpu_id),
        held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == k0.cpu_arr.spec_index(cpu_id).view(),
        final(krnl).cpu_published[cpu_id as int].view() == k0.cpu_published[cpu_id as int].view(),
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
        ({
            let progress = final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view();
            &&& progress is Some && progress->Some_0 is IommuMap4k
            &&& progress->Some_0->IommuMap4k_va_range == *va_range && progress->Some_0->IommuMap4k_iova_range == *iova_range && progress->Some_0->IommuMap4k_mapped == i
        }),
        thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        iommu_table_lock_perm.lock_id() == final(krnl).it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
        final(krnl).it_mp.dom().contains(iommu_table_ptr),
        final(krnl).it_mp.spec_index(iommu_table_ptr).view().proc_ptr == k0.it_mp.spec_index(iommu_table_ptr).view().proc_ptr,
        final(krnl).it_mp.spec_index(iommu_table_ptr).view().leaves_present(),
        final(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_4k() == old(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_4k(),
        final(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(spec_va2index(iova_range.view()[i as int]).0, spec_va2index(iova_range.view()[i as int]).1,
            spec_va2index(iova_range.view()[i as int]).2) is Some,
{
    let iova = iova_range.index(i);
    let indices = va2index(iova);
    proof {
        krnl.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), process_ptr); krnl.it_mp.typed_lock_map_aligned_write_at(lctx.iommu_table_lock_map(), lctx.thread_id(), iommu_table_ptr);
        krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
        iommu_table_perms_wf_map(krnl.it_mp); iommu_table_perms_wf_at(krnl.it_mp, iommu_table_ptr); iommu_table_perms_wf_kernel_l4_end_at(krnl.it_mp, iommu_table_ptr);
    }
    let code = krnl.it_mp.borrow_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_table_lock_perm)).resolve_mapping_4k_l2(indices.0, indices.1, indices.2).1;
    if let PageTableErrorCode::L4EntryNotExist = code {
        iommu_map_4k_install_directory(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), MissingPageTableLevel::L4, cpu_id, Ghost(*va_range), Ghost(*iova_range), thread_ptr, process_ptr,
            container_ptr, pagetable_ptr, iommu_table_ptr, (indices.0, indices.1, indices.2), Tracked(thread_lock_perm), Tracked(iommu_table_lock_perm));
    }
    proof {
        let it = krnl.it_mp.spec_index(iommu_table_ptr).view();
        iommu_table_perms_wf_map(krnl.it_mp); iommu_table_perms_wf_at(krnl.it_mp, iommu_table_ptr); iommu_table_perms_wf_kernel_l4_end_at(krnl.it_mp, iommu_table_ptr);
        pagetable_no_huge_leaf_wf_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.it_mp, iommu_table_ptr); it.wf_mapping_1g_at(indices.0, indices.1);
    }
    let code = krnl.it_mp.borrow_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_table_lock_perm)).resolve_mapping_4k_l2(indices.0, indices.1, indices.2).1;
    if let PageTableErrorCode::L3EntryNotExist = code {
        iommu_map_4k_install_directory(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), MissingPageTableLevel::L3, cpu_id, Ghost(*va_range), Ghost(*iova_range), thread_ptr, process_ptr,
            container_ptr, pagetable_ptr, iommu_table_ptr, (indices.0, indices.1, indices.2), Tracked(thread_lock_perm), Tracked(iommu_table_lock_perm));
    }
    proof {
        let it = krnl.it_mp.spec_index(iommu_table_ptr).view();
        iommu_table_perms_wf_map(krnl.it_mp); iommu_table_perms_wf_at(krnl.it_mp, iommu_table_ptr); iommu_table_perms_wf_kernel_l4_end_at(krnl.it_mp, iommu_table_ptr);
        pagetable_no_huge_leaf_wf_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.it_mp, iommu_table_ptr); it.wf_mapping_1g_at(indices.0, indices.1); it.wf_mapping_2m_at(indices.0, indices.1, indices.2);
    }
    let code = krnl.it_mp.borrow_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_table_lock_perm)).resolve_mapping_4k_l2(indices.0, indices.1, indices.2).1;
    if let PageTableErrorCode::L2EntryNotExist = code {
        iommu_map_4k_install_directory(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), MissingPageTableLevel::L2, cpu_id, Ghost(*va_range), Ghost(*iova_range), thread_ptr, process_ptr,
            container_ptr, pagetable_ptr, iommu_table_ptr, (indices.0, indices.1, indices.2), Tracked(thread_lock_perm), Tracked(iommu_table_lock_perm));
    }
}
} // verus!
