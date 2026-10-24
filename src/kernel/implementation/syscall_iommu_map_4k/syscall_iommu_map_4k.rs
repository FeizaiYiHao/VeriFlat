use vstd::prelude::*;
use crate::*;
use super::syscall_iommu_map_4k_spec::*;
use super::iommu_map_4k_range::iommu_map_4k_map_range_and_exit;
use super::syscall_iommu_map_4k_check::iommu_map_4k_lock_and_check;
#[cfg(verus_keep_ghost)]
use super::syscall_iommu_map_4k_trace::*;

verus! {
/// Map the 4K pages `va..va + range * 4K` of the running process's page table at `iova..iova + range * 4K` of its IOMMU
/// table. The call write-locks the cpu, its running process and thread, read-locks the page table, write-locks the IOMMU table, and
/// holds the existing 2M windows of the va range for the whole call. Success records an entering step, one step per
/// installed IOMMU directory page or published IOMMU leaf, and an exiting step; failure records no step. The result is
/// `iommu_map_4k_syscall_result` of the state at entry.
pub fn syscall_iommu_map_4k(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, iova: VAddr, range: usize)
    -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).nonlock_view().len() == 0,
        old(steps).view().len() == 0,
        old(steps).snapshot_k() == *old(krnl),
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        ret == iommu_map_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, iova, range),
        ret is Success ==> range + 2 <= final(steps).view().len() <= 4 * range + 2,
        ret is Success ==> final(steps).view()[0].old_u == kernel_k_to_kernel_u(*old(krnl)),
        ret is Success ==> iommu_map_4k_syscall_trace(final(steps).view(), cpu_id, iommu_map_4k_syscall_range(va, range), iommu_map_4k_syscall_range(iova, range)),
        !(ret is Success) ==> final(steps).nonlock_view().len() == 0 && final(steps).view().len() == 0,
{
    let (locked, va_range, iova_range) = match iommu_map_4k_lock_and_check(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, iova, range) {
        Ok(e) => e,
        Err(r) => { return r; },
    };
    let Tracked(cpu_lock_perm) = locked.cpu_lock_perm;
    let Tracked(process_lock_perm) = locked.process_lock_perm;
    let Tracked(thread_lock_perm) = locked.thread_lock_perm;
    let Tracked(pagetable_lock_perm) = locked.pagetable_lock_perm;
    let Tracked(iommu_table_lock_perm) = locked.iommu_table_lock_perm;
    let Tracked(window_perms) = locked.window_perms;
    let (container_ptr, process_ptr, thread_ptr, pagetable_ptr, iommu_table_ptr) = (locked.container_ptr, locked.process_ptr, locked.thread_ptr, locked.pagetable_ptr, locked.iommu_table_ptr);
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::IommuMap4k { va_range, iova_range, mapped: 0, directory: Mmap4kDirectory::None })), Tracked(&*lctx),
        Tracked(&thread_lock_perm));
    let ghost entered_k = *krnl;
    proof {
        iommu_map_4k_enter_step_from_k(&*old(krnl), &entered_k, cpu_id, process_ptr, thread_ptr, pagetable_ptr, iommu_table_ptr, va, iova, range);
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        iommu_map_4k_trace_enter(steps.view(), old(steps).view(), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(entered_k), cpu_id, va_range, iova_range);
    }
    proof {
        va_range.va_range_lemma(); iova_range.va_range_lemma(); va_range_2m_windows_contains_window_of_first_n_pages(va_range, range as int);
        thread_perms_wf_at(krnl.thr_mp, thread_ptr); thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id);
    }
    iommu_map_4k_map_range_and_exit(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, &va_range, &iova_range, thread_ptr, process_ptr, container_ptr, pagetable_ptr, iommu_table_ptr,
        Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(iommu_table_lock_perm), Tracked(window_perms));
    RetValueType::Success
}
} // verus!
