use vstd::prelude::*;
use crate::*;
use super::syscall_iommu_unmap_4k_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_iommu_unmap_4k_trace::*;

verus! {
/// Hides every iova of `iova_range` in the write-held IOMMU table of the running thread's process, recording one leaf step
/// per iova and advancing the thread's progress to the whole range.
pub(super) fn iommu_unmap_4k_hide_range(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr,
    prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, iommu_table: RwLockPageTableRoot, iova_range: &VaRange4K, Tracked(iommu_table_perm): Tracked<&LockPerm>,
    Tracked(thread_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).cpu_id() == cpu_id,
        iova_range.wf(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), ctn_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table, TypedLockMode::Write),
        thread_perm.state() is WriteLock,
        thread_perm.thread_id() == old(lctx).thread_id(),
        thread_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        iommu_table_perm.state() is WriteLock,
        iommu_table_perm.thread_id() == old(lctx).thread_id(),
        iommu_table_perm.lock_id() == old(krnl).it_mp.spec_index(iommu_table).locking_thread()->Write_lock_id,
        old(krnl).cpu_arr.spec_index(cpu_id).value.locking_thread() is Write,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).ctn_mp.dom().contains(ctn_ptr),
        old(krnl).ctn_mp.spec_index(ctn_ptr).locking_thread() is Write,
        old(krnl).prc_mp.dom().contains(prc_ptr),
        !old(krnl).prc_mp.spec_index(prc_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(prc_ptr).locking_thread() is Write,
        old(krnl).prc_mp.spec_index(prc_ptr).view().iommu_table == Some(iommu_table),
        old(krnl).it_mp.dom().contains(iommu_table),
        old(krnl).it_mp.spec_index(iommu_table).locking_thread() is Write,
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::IommuUnmap4k { iova_range: *iova_range, unmapped: 0, flushed: false }),
        forall|j: int| #![trigger iova_range.view()[j]] 0 <= j < iova_range.len
            ==> old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(iova_range.view()[j]) && old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k()[iova_range.view()[j]].present,
        forall|v: VAddr| #![trigger old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(v)]
            old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(v) && !iova_range.view().contains(v) ==> old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k()[v].present,
        forall|v: VAddr| #![trigger old(krnl).it_mp.spec_index(iommu_table).view().mapping_2m().dom().contains(v)]
            old(krnl).it_mp.spec_index(iommu_table).view().mapping_2m().dom().contains(v) ==> old(krnl).it_mp.spec_index(iommu_table).view().mapping_2m()[v].present,
        forall|v: VAddr| #![trigger old(krnl).it_mp.spec_index(iommu_table).view().mapping_1g().dom().contains(v)]
            old(krnl).it_mp.spec_index(iommu_table).view().mapping_1g().dom().contains(v) ==> old(krnl).it_mp.spec_index(iommu_table).view().mapping_1g()[v].present,
        iommu_unmap_4k_partial_trace(old(steps).view(), cpu_id, *iova_range),
        1 <= old(steps).view().len(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).ctn_mp.dom().contains(ctn_ptr),
        final(krnl).ctn_mp.spec_index(ctn_ptr) == old(krnl).ctn_mp.spec_index(ctn_ptr),
        final(krnl).prc_mp.dom().contains(prc_ptr),
        final(krnl).prc_mp.spec_index(prc_ptr) == old(krnl).prc_mp.spec_index(prc_ptr),
        final(krnl).thrd_mp.dom().contains(thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::IommuUnmap4k { iova_range: *iova_range, unmapped: iova_range.len, flushed: false }),
        final(krnl).it_mp.dom().contains(iommu_table),
        final(krnl).it_mp.spec_index(iommu_table).locking_thread() == old(krnl).it_mp.spec_index(iommu_table).locking_thread(),
        forall|j: int| #![trigger iova_range.view()[j]] 0 <= j < iova_range.len
            ==> final(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(iova_range.view()[j]) && !final(krnl).it_mp.spec_index(iommu_table).view().mapping_4k()[iova_range.view()[j]].present,
        forall|v: VAddr| #![trigger final(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(v)]
            final(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(v) && !iova_range.view().contains(v) ==> final(krnl).it_mp.spec_index(iommu_table).view().mapping_4k()[v].present,
        forall|v: VAddr| #![trigger final(krnl).it_mp.spec_index(iommu_table).view().mapping_2m().dom().contains(v)]
            final(krnl).it_mp.spec_index(iommu_table).view().mapping_2m().dom().contains(v) ==> final(krnl).it_mp.spec_index(iommu_table).view().mapping_2m()[v].present,
        forall|v: VAddr| #![trigger final(krnl).it_mp.spec_index(iommu_table).view().mapping_1g().dom().contains(v)]
            final(krnl).it_mp.spec_index(iommu_table).view().mapping_1g().dom().contains(v) ==> final(krnl).it_mp.spec_index(iommu_table).view().mapping_1g()[v].present,
        iommu_unmap_4k_partial_trace(final(steps).view(), cpu_id, *iova_range),
        final(steps).view().len() == old(steps).view().len() + iova_range.len,
        final(steps).view()[0] == old(steps).view()[0],
{
    let ghost r = *iova_range;
    let mut k = 0usize;
    while k < iova_range.len
        invariant
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            steps.snapshot_k() == *krnl,
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.cpu_id() == cpu_id,
            lctx.thread_id() == old(lctx).thread_id(),
            index_valid(NUM_CPUS, cpu_id),
            0 <= k <= iova_range.len,
            r == *iova_range,
            r.wf(),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).container_lock_map(), ctn_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), prc_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table, TypedLockMode::Write),
            old(krnl).ctn_mp.dom().contains(ctn_ptr),
            old(krnl).prc_mp.dom().contains(prc_ptr),
            old(krnl).thrd_mp.dom().contains(thrd_ptr),
            old(krnl).it_mp.dom().contains(iommu_table),
            1 <= old(steps).view().len(),
            thread_perm.state() is WriteLock,
            thread_perm.thread_id() == old(lctx).thread_id(),
            thread_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            iommu_table_perm.state() is WriteLock,
            iommu_table_perm.thread_id() == old(lctx).thread_id(),
            iommu_table_perm.lock_id() == old(krnl).it_mp.spec_index(iommu_table).locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).value.locking_thread() is Write,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
            old(krnl).ctn_mp.spec_index(ctn_ptr).locking_thread() is Write,
            !old(krnl).prc_mp.spec_index(prc_ptr).view().zombie,
            old(krnl).prc_mp.spec_index(prc_ptr).locking_thread() is Write,
            old(krnl).prc_mp.spec_index(prc_ptr).view().iommu_table == Some(iommu_table),
            old(krnl).it_mp.spec_index(iommu_table).locking_thread() is Write,
            old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
            krnl.cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            krnl.cpu_op.view().view()[cpu_id as int] is InStep,
            krnl.cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
            krnl.ctn_mp.dom().contains(ctn_ptr),
            krnl.ctn_mp.spec_index(ctn_ptr) == old(krnl).ctn_mp.spec_index(ctn_ptr),
            krnl.prc_mp.dom().contains(prc_ptr),
            krnl.prc_mp.spec_index(prc_ptr) == old(krnl).prc_mp.spec_index(prc_ptr),
            krnl.thrd_mp.dom().contains(thrd_ptr),
            krnl.thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
            krnl.thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
            krnl.thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
            krnl.thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
            krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::IommuUnmap4k { iova_range: r, unmapped: k, flushed: false }),
            krnl.it_mp.dom().contains(iommu_table),
            krnl.it_mp.spec_index(iommu_table).locking_thread() == old(krnl).it_mp.spec_index(iommu_table).locking_thread(),
            forall|j: int| #![trigger r.view()[j]] 0 <= j < r.len
                ==> krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(r.view()[j]) && krnl.it_mp.spec_index(iommu_table).view().mapping_4k()[r.view()[j]].present == (k <= j),
            forall|v: VAddr| #![trigger krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(v)]
                krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(v) && !r.view().contains(v) ==> krnl.it_mp.spec_index(iommu_table).view().mapping_4k()[v].present,
            forall|v: VAddr| #![trigger krnl.it_mp.spec_index(iommu_table).view().mapping_2m().dom().contains(v)]
                krnl.it_mp.spec_index(iommu_table).view().mapping_2m().dom().contains(v) ==> krnl.it_mp.spec_index(iommu_table).view().mapping_2m()[v].present,
            forall|v: VAddr| #![trigger krnl.it_mp.spec_index(iommu_table).view().mapping_1g().dom().contains(v)]
                krnl.it_mp.spec_index(iommu_table).view().mapping_1g().dom().contains(v) ==> krnl.it_mp.spec_index(iommu_table).view().mapping_1g()[v].present,

            iommu_unmap_4k_partial_trace(steps.view(), cpu_id, r),
            steps.view().len() == old(steps).view().len() + k,
            steps.view()[0] == old(steps).view()[0],
        decreases iova_range.len - k,
    {
        let v = iova_range.index(k);
        let indices = va2index(v);
        proof { spec_va_4k_index_roundtrip_at(v, indices.0, indices.1, indices.2, indices.3); }
        let ghost leaf_pre = *krnl;
        krnl.set_thread_syscall_progress(thrd_ptr, Ghost(Some(SyscallProgress::IommuUnmap4k { iova_range: r, unmapped: (k + 1) as usize, flushed: false })), Tracked(&*lctx), Tracked(thread_perm));
        let ghost leaf_mid = *krnl;
        clear_iommu_4k_mapping_present(krnl, iommu_table, indices, Tracked(&mut *lctx), Tracked(iommu_table_perm));
        proof {
            let leaf_post = *krnl;
            let before = steps.view();
            krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thrd_ptr);
            iommu_unmap_4k_leaf_step_from_k(&leaf_pre, &leaf_mid, &leaf_post, cpu_id, ctn_ptr, prc_ptr, thrd_ptr, iommu_table, r, k);
            iommu_unmap_4k_trace_range_steps(before, steps.view(), cpu_id, r);
        }
        k = k + 1;
    }
}

/// Unmaps every hidden iova of `iova_range` from the write-held IOMMU table of the running thread's process, freeing each
/// page whose last mapping it was and crediting its 4K quota to the thread's pending counters `indirect` and `direct`.
pub(super) fn iommu_unmap_4k_reclaim_range(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr,
    prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, iommu_table: RwLockPageTableRoot, iova_range: &VaRange4K, indirect: &mut [usize; MAX_CONTAINER_TREE_DEPTH],
    direct: &mut usize, Tracked(iommu_table_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() == set![cpu_id],
        old(lctx).thread_lock_map().dom() == set![thrd_ptr],
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).cpu_id() == cpu_id,
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        iova_range.wf(),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), ctn_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table, TypedLockMode::Write),
        thread_perm.state() is WriteLock,
        thread_perm.thread_id() == old(lctx).thread_id(),
        thread_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        iommu_table_perm.state() is WriteLock,
        iommu_table_perm.thread_id() == old(lctx).thread_id(),
        iommu_table_perm.lock_id() == old(krnl).it_mp.spec_index(iommu_table).locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(ctn_ptr),
        old(krnl).prc_mp.dom().contains(prc_ptr),
        old(krnl).prc_mp.spec_index(prc_ptr).view().iommu_table == Some(iommu_table),
        old(krnl).it_mp.dom().contains(iommu_table),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        *old(direct) == old(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
        forall|d: int| #![trigger old(indirect)[d]] 0 <= d < old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth
            ==> old(indirect)[d] == old(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
        iommu_table_tlb_entries_present(old(krnl).iommu_tlb, old(krnl).irt.view(), old(krnl).it_mp, iommu_table),
        forall|v: VAddr| #![trigger old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(v)]
            old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(v) && !iova_range.view().contains(v) ==> old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k()[v].present,
        forall|v: VAddr| #![trigger old(krnl).it_mp.spec_index(iommu_table).view().mapping_2m().dom().contains(v)]
            old(krnl).it_mp.spec_index(iommu_table).view().mapping_2m().dom().contains(v) ==> old(krnl).it_mp.spec_index(iommu_table).view().mapping_2m()[v].present,
        forall|v: VAddr| #![trigger old(krnl).it_mp.spec_index(iommu_table).view().mapping_1g().dom().contains(v)]
            old(krnl).it_mp.spec_index(iommu_table).view().mapping_1g().dom().contains(v) ==> old(krnl).it_mp.spec_index(iommu_table).view().mapping_1g()[v].present,
        forall|j: int| #![trigger iova_range.view()[j]] 0 <= j < iova_range.len
            ==> old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(iova_range.view()[j]) && !old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k()[iova_range.view()[j]].present,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == old(steps).view(),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).ctn_mp.dom().contains(ctn_ptr),
        final(krnl).ctn_mp.spec_index(ctn_ptr) == old(krnl).ctn_mp.spec_index(ctn_ptr),
        final(krnl).prc_mp.dom().contains(prc_ptr),
        final(krnl).prc_mp.spec_index(prc_ptr) == old(krnl).prc_mp.spec_index(prc_ptr),
        final(krnl).thrd_mp.dom().contains(thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread {
            direct_free_quota_pending_4k: final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view()
        }),
        *final(direct) == final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
        forall|d: int| #![trigger final(indirect)[d]] 0 <= d < final(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth
            ==> final(indirect)[d] == final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
        final(krnl).it_mp.dom().contains(iommu_table),
        final(krnl).it_mp.spec_index(iommu_table).locking_thread() == old(krnl).it_mp.spec_index(iommu_table).locking_thread(),
        final(krnl).it_mp.spec_index(iommu_table).view().leaves_present(),
{
    let ghost r = *iova_range;
    let mut k = 0usize;
    while k < iova_range.len
        invariant
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            steps.snapshot_k() == *krnl,
            steps.view() == old(steps).view(),
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.cpu_id() == cpu_id,
            lctx.thread_id() == old(lctx).thread_id(),
            old(lctx).page_lock_map().dom().is_empty(),
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_4K_MAJOR),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() == set![cpu_id],
            old(lctx).thread_lock_map().dom() == set![thrd_ptr],
            index_valid(NUM_CPUS, cpu_id),
            0 <= k <= iova_range.len,
            r == *iova_range,
            r.wf(),
            typed_lock_map_contains_mode(old(lctx).container_lock_map(), ctn_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), prc_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table, TypedLockMode::Write),
            thread_perm.state() is WriteLock,
            thread_perm.thread_id() == old(lctx).thread_id(),
            thread_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            iommu_table_perm.state() is WriteLock,
            iommu_table_perm.thread_id() == old(lctx).thread_id(),
            iommu_table_perm.lock_id() == old(krnl).it_mp.spec_index(iommu_table).locking_thread()->Write_lock_id,
            old(krnl).prc_mp.spec_index(prc_ptr).view().iommu_table == Some(iommu_table),
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
            krnl.cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            krnl.cpu_op.view().view()[cpu_id as int] is InStep,
            krnl.cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
            krnl.ctn_mp.dom().contains(ctn_ptr),
            krnl.ctn_mp.spec_index(ctn_ptr) == old(krnl).ctn_mp.spec_index(ctn_ptr),
            krnl.prc_mp.dom().contains(prc_ptr),
            krnl.prc_mp.spec_index(prc_ptr) == old(krnl).prc_mp.spec_index(prc_ptr),
            krnl.thrd_mp.dom().contains(thrd_ptr),
            !thread_is_dangling(krnl.thrd_mp.spec_index(thrd_ptr)),
            krnl.thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
            krnl.thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
            krnl.thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
            krnl.thrd_mp.spec_index(thrd_ptr).view() == (Thread {
                direct_free_quota_pending_4k: krnl.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k,
                indirect_free_quota_pending_4k: krnl.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view()
            }),
            *direct == krnl.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
            forall|d: int| #![trigger indirect[d]] 0 <= d < krnl.thrd_mp.spec_index(thrd_ptr).view().container_depth
                ==> indirect[d] == krnl.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
            krnl.it_mp.dom().contains(iommu_table),
            krnl.it_mp.spec_index(iommu_table).locking_thread() == old(krnl).it_mp.spec_index(iommu_table).locking_thread(),
            iommu_table_tlb_entries_present(krnl.iommu_tlb, krnl.irt.view(), krnl.it_mp, iommu_table),
            forall|v: VAddr| #![trigger krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(v)]
                krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(v) && !r.view().contains(v) ==> krnl.it_mp.spec_index(iommu_table).view().mapping_4k()[v].present,
            forall|v: VAddr| #![trigger krnl.it_mp.spec_index(iommu_table).view().mapping_2m().dom().contains(v)]
                krnl.it_mp.spec_index(iommu_table).view().mapping_2m().dom().contains(v) ==> krnl.it_mp.spec_index(iommu_table).view().mapping_2m()[v].present,
            forall|v: VAddr| #![trigger krnl.it_mp.spec_index(iommu_table).view().mapping_1g().dom().contains(v)]
                krnl.it_mp.spec_index(iommu_table).view().mapping_1g().dom().contains(v) ==> krnl.it_mp.spec_index(iommu_table).view().mapping_1g()[v].present,

            forall|j: int| #![trigger r.view()[j]] 0 <= j < r.len
                ==> krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(r.view()[j]) == (k <= j) && (k <= j ==> !krnl.it_mp.spec_index(iommu_table).view().mapping_4k()[r.view()[j]].present),
        decreases iova_range.len - k,
    {
        let v = iova_range.index(k);
        let indices = va2index(v);
        proof { spec_va_4k_index_roundtrip_at(v, indices.0, indices.1, indices.2, indices.3); }
        reclaim_unmapped_iommu_4k_page(krnl, iommu_table, indices, thrd_ptr, cpu_id, indirect, direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(iommu_table_perm),
            Tracked(thread_perm));
        k = k + 1;
    }
}
} // verus!
