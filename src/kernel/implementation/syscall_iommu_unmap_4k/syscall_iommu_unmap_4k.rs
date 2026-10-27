use vstd::prelude::*;
use crate::*;
use super::syscall_iommu_unmap_4k_spec::*;
use super::syscall_iommu_unmap_4k_check::iommu_unmap_4k_lock_and_check;
use super::syscall_iommu_unmap_4k_range::{iommu_unmap_4k_hide_range, iommu_unmap_4k_reclaim_range};
#[cfg(verus_keep_ghost)]
use super::syscall_iommu_unmap_4k_trace::*;

verus! {
/// Unmap the 4K pages `iova..iova + range * 4K` from the running process's IOMMU table. Success records an entering step that
/// write-locks the cpu, container, process, thread, and IOMMU table; one step per hidden leaf; one IOTLB flush step; one step
/// per quota refund; and an exiting step that releases all five. Failure records no step. The result is
/// `iommu_unmap_4k_syscall_result` of the state at entry.
pub fn syscall_iommu_unmap_4k(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, iova: VAddr, range: usize)
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
        ret == iommu_unmap_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, iova, range),
        ret is Success ==> final(steps).view()[0].old_u == kernel_k_to_kernel_u(*old(krnl)),
        ret is Success ==> iommu_unmap_4k_syscall_trace(final(steps).view(), cpu_id, iova, range),
        !(ret is Success) ==> final(steps).nonlock_view().len() == 0 && final(steps).view().len() == 0,
        !(ret is Success) ==> kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(*old(krnl)),
{
    let (locked, iommu_table, Tracked(iommu_table_perm)) = match iommu_unmap_4k_lock_and_check(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, iova, range) {
        Ok(e) => e,
        Err(r) => { return r; },
    };
    let Tracked(cpu_perm) = locked.cpu_lock_perm;
    let Tracked(container_perm) = locked.container_lock_perm;
    let Tracked(process_perm) = locked.process_lock_perm;
    let Tracked(thread_perm) = locked.thread_lock_perm;
    let (container_ptr, process_ptr, thread_ptr) = (locked.container_ptr, locked.process_ptr, locked.thread_ptr);
    let iova_range = VaRange4K::new(iova, range);
    let ghost r = iommu_unmap_4k_iova_range(iova, range);
    proof { assert(iova_range == r) by { iova_range.va_range_lemma(); }; }
    iommu_unmap_4k_hide_range(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, process_ptr, thread_ptr, iommu_table, &iova_range, Tracked(&iommu_table_perm),
        Tracked(&thread_perm));
    let ghost flush_pre = *krnl;
    proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); }
    flush_iommu_tlb_for_table(krnl, iommu_table, Tracked(&*lctx), Tracked(&iommu_table_perm));
    let ghost flush_mid = *krnl;
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::IommuUnmap4k { iova_range: r, unmapped: range, flushed: true })), Tracked(&*lctx), Tracked(&thread_perm));
    proof {
        let flush_post = *krnl;
        let before = steps.view();
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        iommu_unmap_4k_flush_step_from_k(&flush_pre, &flush_mid, &flush_post, cpu_id, container_ptr, process_ptr, thread_ptr, iommu_table, r);
        iommu_unmap_4k_trace_range_steps(before, steps.view(), cpu_id, r);
    }
    proof { thread_perms_wf_at(krnl.thr_mp, thread_ptr); container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr); container_perms_wf_at(krnl.ctn_mp, container_ptr); }
    let mut indirect = [0usize; MAX_CONTAINER_TREE_DEPTH];
    let mut direct = 0usize;
    iommu_unmap_4k_reclaim_range(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, process_ptr, thread_ptr, iommu_table, &iova_range, &mut indirect, &mut direct,
        Tracked(&iommu_table_perm), Tracked(&thread_perm));
    let ghost refund_before = steps.view();
    let ghost refund_k = *krnl;
    let ghost refund_lctx = *lctx;
    refund_unmap_4k_quota(krnl, thread_ptr, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&thread_perm));
    proof { iommu_unmap_4k_trace_refund_steps(refund_before, steps.view(), &refund_k, &refund_lctx, cpu_id, thread_ptr, r); }
    let ghost exit_start = *krnl;
    let ghost exit_before = steps.view();
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(None), Tracked(&*lctx), Tracked(&thread_perm));
    krnl.wunlock_iommu_table(iommu_table, Tracked(&mut *lctx), Tracked(iommu_table_perm));
    krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_perm));
    krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_perm));
    krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
    proof {
        let exit_k = *krnl;
        steps.end_kernel_step_thread_syscall_progress_changed(&*krnl, &*lctx, thread_ptr);
        iommu_unmap_4k_exit_step_from_k(&exit_start, &exit_k, cpu_id, container_ptr, process_ptr, thread_ptr, iommu_table);
        iommu_unmap_4k_trace_exit_step(exit_before, steps.view(), kernel_k_to_kernel_u(exit_start), kernel_k_to_kernel_u(exit_k), cpu_id, iova, range);
    }
    RetValueType::Success
}
} // verus!
