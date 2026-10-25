use vstd::prelude::*;
use crate::*;
use super::syscall_iommu_map_4k_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_iommu_map_4k_trace::*;

verus! {
pub(super) struct IommuMap4kThreadLocked {
    pub container_ptr: RwLockContainerPtr, pub process_ptr: RwLockProcessPtr, pub thread_ptr: RwLockThreadPtr,
    pub cpu_lock_perm: Tracked<LockPerm>, pub process_lock_perm: Tracked<LockPerm>, pub thread_lock_perm: Tracked<LockPerm>,
}

/// Write-locks cpu `cpu_id` and its running process and thread, rejecting an idle cpu and a killed process or thread with every
/// lock released and no step; otherwise returns the three locks held.
pub(super) fn iommu_map_4k_lock_running_thread(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr,
    iova: VAddr, range: usize) -> (ret: Result<IommuMap4kThreadLocked, RetValueType>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        !(range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range) || !spec_va_4k_valid(iova)
            || iova >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(iova, range)),
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        ret is Err ==> ({
            &&& ret->Err_0 == iommu_map_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, iova, range)
            &&& !(ret->Err_0 is Success)
            &&& final(lctx).kernel_view_locking_state() is Release
            &&& final(lctx).no_locks_held()
            &&& final(krnl).all_objects_unlocked(final(lctx))
            &&& final(steps).snapshot_k() == *final(krnl)
            &&& final(steps).view() == old(steps).view()
            &&& final(steps).nonlock_view() == old(steps).nonlock_view()
        }),
        ret is Ok ==> ({
            let e = ret->Ok_0;
            let cpu = final(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            let thread = final(krnl).thr_mp.spec_index(e.thread_ptr).view();
            &&& *final(steps) == *old(steps)
            &&& final(lctx).kernel_view_locking_state() is Acquire
            &&& final(lctx).cpu_lock_map().dom() =~= set![cpu_id]
            &&& final(lctx).process_lock_map().dom() =~= set![e.process_ptr]
            &&& final(lctx).thread_lock_map().dom() =~= set![e.thread_ptr]
            &&& final(lctx).container_lock_map().dom().is_empty()
            &&& final(lctx).page_lock_map().dom().is_empty()
            &&& final(lctx).endpoint_lock_map().dom().is_empty()
            &&& final(lctx).scheduler_lock_map().dom().is_empty()
            &&& final(lctx).pcid_allocator_lock_map().dom().is_empty()
            &&& final(lctx).cpu_set_lock_map().dom().is_empty()
            &&& final(lctx).pagetable_lock_map().dom().is_empty()
            &&& final(lctx).iommu_table_lock_map().dom().is_empty()
            &&& final(lctx).iommu_root_table_lock_map().dom().is_empty()
            &&& final(lctx).pagetable_window_lock_map().dom().is_empty()
            &&& final(lctx).holds_no_allocator_locks(PageSize::SZ4k)
            &&& final(lctx).holds_no_allocator_locks(PageSize::SZ2m)
            &&& final(lctx).holds_no_allocator_locks(PageSize::SZ1g)
            &&& final(lctx).pcid_needflush_lock_map().dom().is_empty()
            &&& final(lctx).cpu_offline_flag_lock_map().dom().is_empty()
            &&& typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(final(lctx).process_lock_map(), e.process_ptr, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(final(lctx).thread_lock_map(), e.thread_ptr, TypedLockMode::Write)
            &&& wlock_ensures(old(krnl).cpu_arr.spec_index(cpu_id).view(), final(krnl).cpu_arr.spec_index(cpu_id).view(), old(krnl).cpu_arr.lock_id_by_index(cpu_id), final(lctx), e.cpu_lock_perm.view())
            &&& wlock_ensures(old(krnl).prc_mp.spec_index(e.process_ptr), final(krnl).prc_mp.spec_index(e.process_ptr), old(krnl).prc_mp.lock_id_by_key(e.process_ptr), final(lctx), e.process_lock_perm.view())
            &&& wlock_ensures(old(krnl).thr_mp.spec_index(e.thread_ptr), final(krnl).thr_mp.spec_index(e.thread_ptr), old(krnl).thr_mp.lock_id_by_key(e.thread_ptr), final(lctx), e.thread_lock_perm.view())
            &&& cpu.state is Running && !final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& cpu.current_process == Some(e.process_ptr) && cpu.current_thread == Some(e.thread_ptr) && cpu.owning_container == e.container_ptr
            &&& final(krnl).cpu_published[cpu_id as int].view() == (cpu.current_cr3, cpu.current_pcid)
            &&& final(krnl).ctn_mp.dom().contains(e.container_ptr)
            &&& final(krnl).prc_mp.dom().contains(e.process_ptr) && !final(krnl).prc_mp.spec_index(e.process_ptr).being_killed()
            &&& final(krnl).prc_mp.spec_index(e.process_ptr).view().state.view() is Running || final(krnl).prc_mp.spec_index(e.process_ptr).view().state.view() is Zombie
            &&& final(krnl).thr_mp.dom().contains(e.thread_ptr) && !final(krnl).thr_mp.spec_index(e.thread_ptr).being_killed()
            &&& thread.state == (ThreadState::RUNNING { cpu_id }) && thread.owning_proc == e.process_ptr && thread.owning_container == e.container_ptr
            &&& thread.syscall_progress.view() is None && thread.free_quota_pending_clean() && thread.temp_alloc_clean()
            &&& !final(krnl).thr_mp.spec_index(e.thread_ptr).view_ghost().exited
            &&& *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, prc_mp: final(krnl).prc_mp, thr_mp: final(krnl).thr_mp, ..*old(krnl) })
            &&& final(krnl).cpu_arr.unchanged_except(&old(krnl).cpu_arr, cpu_id)
            &&& final(krnl).prc_mp.unchanged_except(&old(krnl).prc_mp, e.process_ptr)
            &&& final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, e.thread_ptr)
        }),
{
    let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
    if cpu_lock_res.is_none() {
        proof { iommu_map_4k_result_from_k(&*old(krnl), cpu_id, va, iova, range, RetValueType::CpuIdle); }
        return Err(RetValueType::CpuIdle);
    }
    let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
    proof {
        container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id); thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id);
    }
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let process_ptr = cpu.current_process().unwrap();
    let thread_ptr = cpu.current_thread().unwrap();
    let container_ptr = cpu.owning_container();
    proof { process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, process_ptr); }
    let process_res = krnl.wlock_process_unless_killed(process_ptr, Ghost(cpu_id), Tracked(&mut *lctx));
    if process_res.is_none() {
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(process_ptr), None, None, None, None);
            iommu_map_4k_result_from_k(&*old(krnl), cpu_id, va, iova, range, RetValueType::ErrorProcessKilled);
        }
        return Err(RetValueType::ErrorProcessKilled);
    }
    let Tracked(process_lock_perm) = process_res.unwrap();
    let thread_res = krnl.wlock_current_running_thread_unless_killed(thread_ptr, Tracked(&mut *lctx));
    if thread_res.is_none() {
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(process_ptr), Some(thread_ptr), None, None, None);
            iommu_map_4k_result_from_k(&*old(krnl), cpu_id, va, iova, range, RetValueType::ErrorThreadKilled);
        }
        return Err(RetValueType::ErrorThreadKilled);
    }
    let Tracked(thread_lock_perm) = thread_res.unwrap();
    Ok(IommuMap4kThreadLocked {
        container_ptr, process_ptr, thread_ptr, cpu_lock_perm: Tracked(cpu_lock_perm), process_lock_perm: Tracked(process_lock_perm), thread_lock_perm: Tracked(thread_lock_perm),
    })
}
} // verus!
