use vstd::prelude::*;
use crate::*;
use super::syscall_iommu_unmap_4k_spec::*;
use super::syscall_iommu_unmap_4k_check::iommu_unmap_4k_lock_and_check;
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
    let ghost lk = *krnl;
    let ghost lctx0 = *lctx;
    let ghost th0 = krnl.thr_mp.spec_index(thread_ptr).view();
    let ghost t0 = krnl.it_mp.spec_index(iommu_table).view();
    proof { assert(iova_range == r) by { iova_range.va_range_lemma(); }; }
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::IommuUnmap4k { iova_range: r, unmapped: 0, flushed: false })), Tracked(&*lctx), Tracked(&thread_perm));
    proof {
        let entered_k = *krnl;
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        iommu_unmap_4k_enter_step_from_k(&old(steps).snapshot_k(), &entered_k, cpu_id, container_ptr, process_ptr, thread_ptr, iommu_table, iova, range);
        iommu_unmap_4k_trace_enter_step(old(steps).view(), steps.view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(entered_k), cpu_id, r);
    }
    let mut k = 0usize;
    #[verifier::loop_isolation(false)]
    while k < range
        invariant
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            steps.snapshot_k() == *krnl,
            typed_lock_maps_unchanged(&lctx0, lctx),
            lctx.cpu_id() == cpu_id,
            lctx.thread_id() == lctx0.thread_id(),
            0 <= k <= range,
            iova_range == r,
            r.wf(),
            r.len == range,
            krnl.cpu_arr.spec_index(cpu_id).view() == lk.cpu_arr.spec_index(cpu_id).view(),
            krnl.cpu_published[cpu_id as int].view() == lk.cpu_published[cpu_id as int].view(),
            krnl.ctn_mp.dom().contains(container_ptr),
            krnl.ctn_mp.spec_index(container_ptr) == lk.ctn_mp.spec_index(container_ptr),
            krnl.prc_mp.dom().contains(process_ptr),
            krnl.prc_mp.spec_index(process_ptr) == lk.prc_mp.spec_index(process_ptr),
            krnl.thr_mp.dom().contains(thread_ptr),
            krnl.thr_mp.spec_index(thread_ptr).locking_thread() == lk.thr_mp.spec_index(thread_ptr).locking_thread(),
            krnl.thr_mp.spec_index(thread_ptr).being_killed() == lk.thr_mp.spec_index(thread_ptr).being_killed(),
            krnl.thr_mp.spec_index(thread_ptr).view_ghost() == lk.thr_mp.spec_index(thread_ptr).view_ghost(),
            krnl.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: Ghost(Some(SyscallProgress::IommuUnmap4k { iova_range: r, unmapped: k, flushed: false })), ..th0 }),
            krnl.it_mp.dom().contains(iommu_table),
            krnl.it_mp.spec_index(iommu_table).locking_thread() == lk.it_mp.spec_index(iommu_table).locking_thread(),
            krnl.it_mp.spec_index(iommu_table).view().proc_ptr == t0.proc_ptr,
            krnl.it_mp.spec_index(iommu_table).view().mapping_2m() == t0.mapping_2m(),
            krnl.it_mp.spec_index(iommu_table).view().mapping_1g() == t0.mapping_1g(),
            forall|j: int| #![trigger r.view()[j]] 0 <= j < range ==> {
                &&& krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(r.view()[j])
                &&& krnl.it_mp.spec_index(iommu_table).view().mapping_4k()[r.view()[j]] == (MapEntry { present: k <= j, ..t0.mapping_4k()[r.view()[j]] })
            },
            forall|v: VAddr| #![trigger krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(v)] #![trigger t0.mapping_4k().dom().contains(v)] !r.view().contains(v) ==> {
                &&& krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(v) == t0.mapping_4k().dom().contains(v)
                &&& t0.mapping_4k().dom().contains(v) ==> krnl.it_mp.spec_index(iommu_table).view().mapping_4k()[v] == t0.mapping_4k()[v]
            },
            iommu_unmap_4k_partial_trace(steps.view(), cpu_id, r),
            steps.view()[0].old_u == kernel_k_to_kernel_u(*old(krnl)),
            steps.view().len() == 1 + k,
        decreases range - k,
    {
        let v = iova_range.index(k);
        let indices = va2index(v);
        proof { spec_va_4k_index_roundtrip_at(v, indices.0, indices.1, indices.2, indices.3); }
        let ghost leaf_pre = *krnl;
        krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::IommuUnmap4k { iova_range: r, unmapped: (k + 1) as usize, flushed: false })), Tracked(&*lctx),
            Tracked(&thread_perm));
        let ghost leaf_mid = *krnl;
        clear_iommu_4k_mapping_present(krnl, iommu_table, indices, Tracked(&mut *lctx), Tracked(&iommu_table_perm));
        proof {
            let leaf_post = *krnl;
            let before = steps.view();
            krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
            iommu_unmap_4k_leaf_step_from_k(&leaf_pre, &leaf_mid, &leaf_post, cpu_id, container_ptr, process_ptr, thread_ptr, iommu_table, r, k);
            iommu_unmap_4k_trace_range_steps(before, steps.view(), cpu_id, r);
        }
        k = k + 1;
    }
    let ghost flush_pre = *krnl;
    proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); }
    flush_iommu_tlb_for_table(krnl, iommu_table, Tracked(&*lctx));
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
    let mut k = 0usize;
    #[verifier::loop_isolation(false)]
    while k < range
        invariant
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            steps.snapshot_k() == *krnl,
            typed_lock_maps_unchanged(&lctx0, lctx),
            lctx.cpu_id() == cpu_id,
            lctx.thread_id() == lctx0.thread_id(),
            0 <= k <= range,
            iova_range == r,
            r.wf(),
            r.len == range,
            krnl.cpu_arr.spec_index(cpu_id).view() == lk.cpu_arr.spec_index(cpu_id).view(),
            krnl.cpu_published[cpu_id as int].view() == lk.cpu_published[cpu_id as int].view(),
            krnl.ctn_mp.dom().contains(container_ptr),
            krnl.ctn_mp.spec_index(container_ptr) == lk.ctn_mp.spec_index(container_ptr),
            krnl.prc_mp.dom().contains(process_ptr),
            krnl.prc_mp.spec_index(process_ptr) == lk.prc_mp.spec_index(process_ptr),
            krnl.thr_mp.dom().contains(thread_ptr),
            krnl.thr_mp.spec_index(thread_ptr).locking_thread() == lk.thr_mp.spec_index(thread_ptr).locking_thread(),
            krnl.thr_mp.spec_index(thread_ptr).being_killed() == lk.thr_mp.spec_index(thread_ptr).being_killed(),
            krnl.thr_mp.spec_index(thread_ptr).view_ghost() == lk.thr_mp.spec_index(thread_ptr).view_ghost(),
            krnl.thr_mp.spec_index(thread_ptr).view() == (Thread {
                direct_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
                indirect_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k,
                syscall_progress: Ghost(Some(SyscallProgress::IommuUnmap4k { iova_range: r, unmapped: range, flushed: true })), ..th0
            }),
            direct == krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
            forall|d: int| #![trigger indirect[d]] #![trigger krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d)] 0 <= d < krnl.thr_mp.spec_index(thread_ptr).view().container_depth
                ==> indirect[d] == krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
            krnl.it_mp.dom().contains(iommu_table),
            krnl.it_mp.spec_index(iommu_table).locking_thread() == lk.it_mp.spec_index(iommu_table).locking_thread(),
            krnl.it_mp.spec_index(iommu_table).view().mapping_2m() == t0.mapping_2m(),
            krnl.it_mp.spec_index(iommu_table).view().mapping_1g() == t0.mapping_1g(),
            iommu_table_tlb_entries_present(krnl.iommu_tlb, krnl.irt.view(), krnl.it_mp, iommu_table),
            forall|j: int| #![trigger r.view()[j]] 0 <= j < range ==> {
                &&& krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(r.view()[j]) == (k <= j)
                &&& k <= j ==> krnl.it_mp.spec_index(iommu_table).view().mapping_4k()[r.view()[j]] == (MapEntry { present: false, ..t0.mapping_4k()[r.view()[j]] })
            },
            forall|v: VAddr| #![trigger krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(v)] #![trigger t0.mapping_4k().dom().contains(v)] !r.view().contains(v) ==> {
                &&& krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(v) == t0.mapping_4k().dom().contains(v)
                &&& t0.mapping_4k().dom().contains(v) ==> krnl.it_mp.spec_index(iommu_table).view().mapping_4k()[v] == t0.mapping_4k()[v]
            },
            iommu_unmap_4k_partial_trace(steps.view(), cpu_id, r),
            steps.view()[0].old_u == kernel_k_to_kernel_u(*old(krnl)),
            steps.view().len() == range + 2,
        decreases range - k,
    {
        let v = iova_range.index(k);
        let indices = va2index(v);
        proof {
            spec_va_4k_index_roundtrip_at(v, indices.0, indices.1, indices.2, indices.3);
            thread_perms_wf_at(krnl.thr_mp, thread_ptr); thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id);
        }
        reclaim_unmapped_iommu_4k_page(krnl, iommu_table, indices, thread_ptr, cpu_id, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&iommu_table_perm),
            Tracked(&thread_perm));
        k = k + 1;
    }
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
