use vstd::prelude::*;
use crate::*;
use super::syscall_mmap_1g_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_1g_trace::mmap_1g_result_from_k;
use super::syscall_mmap_1g_precheck::mmap_1g_precheck;
use super::syscall_mmap_1g_helpers::mmap_1g_map_and_finish;

verus! {
/// With `cpu_id` and its current `thrd_ptr` write-held since the entry snapshot and otherwise unchanged: releases both and finishes the call without recording a step.
fn mmap_1g_unlock_and_finish(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr,
    Tracked(thread_lock_perm): Tracked<LockPerm>, Tracked(cpu_lock_perm): Tracked<LockPerm>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        cpu_id == old(lctx).cpu_id(),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, thrd_mp: old(krnl).thrd_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view(),
        !old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().locked(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cpu_lock_perm.lock_id() }),
        old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().killer_info(),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        old(krnl).thrd_mp.unchanged_except(&old(steps).snapshot_k().thrd_mp, thrd_ptr),
        wlock_ensures(old(steps).snapshot_k().thrd_mp.spec_index(thrd_ptr), old(krnl).thrd_mp.spec_index(thrd_ptr), old(steps).snapshot_k().thrd_mp.lock_id_by_key(thrd_ptr), old(lctx), thread_lock_perm),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is None,
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        old(lctx).pagetable_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).thread_lock_map().dom() =~= set![thrd_ptr],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).view() == old(steps).view(),
        final(steps).snapshot_k() == *final(krnl),
{
    krnl.wunlock_thread(thrd_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        assert(krnl.cpu_op.view().view() =~= old(steps).snapshot_k().cpu_op.view().view());
        steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, Some(thrd_ptr), None, None, None);
    }
}

/// Write-locks `cpu_id` while it runs a live thread, then that thread, and with one 1G quota and one 4K quota per page maps `va_range` through `mmap_1g_lock_pagetable_and_map`. Every failure releases the locks it took and records no step.
pub(super) fn mmap_1g_attempt(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, len: usize, va_range: &VaRange1G)
    -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).view().len() == 0,
        old(steps).snapshot_k() == *old(krnl),
        !(len == 0 || len > usize::MAX / 0x40000000 || !spec_va_1g_valid(va) || va >= usize::MAX - len * 0x40000000 || !spec_va_1g_range_valid(va, len)),
        *va_range == spec_va_range_1g(va, len),
        va_range.wf(),
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        ret == mmap_1g_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, len),
        !(ret is Success) ==> final(steps).view().len() == 0,
        ret is Success ==> mmap_1g_syscall_trace(final(steps).view(), cpu_id, va, len),
        ret is Success ==> mmap_1g_syscall_success_mapped(final(krnl), cpu_id, va, len),
{
    let ghost entry_lctx = *lctx;
    let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
    if cpu_lock_res.is_none() {
        proof { mmap_1g_result_from_k(&*old(krnl), cpu_id, va, len, RetValueType::CpuIdle, 0, None, None); }
        return RetValueType::CpuIdle;
    }
    let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
    let locked = mmap_4k_lock_current_thread(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Tracked(cpu_lock_perm));
    if locked.is_none() {
        proof { mmap_1g_result_from_k(&*old(krnl), cpu_id, va, len, RetValueType::ErrorThreadKilled, 0, None, None); }
        return RetValueType::ErrorThreadKilled;
    }
    let (prc_ptr, thrd_ptr, ctn_ptr, _alloc_ptr_4k, pagetable, quota_4k, Tracked(thread_perm), Tracked(cpu_perm)) = locked.unwrap();
    proof { thread_perms_wf_map(krnl.thrd_mp); }
    let quota_1g = krnl.thrd_mp.borrow_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_perm)).quota_1g;
    if quota_1g < len || quota_4k < len {
        proof { mmap_1g_result_from_k(&*old(krnl), cpu_id, va, len, RetValueType::ErrorNoQuota, 0, None, None); }
        mmap_1g_unlock_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, thrd_ptr, Tracked(thread_perm), Tracked(cpu_perm));
        return RetValueType::ErrorNoQuota;
    }
    mmap_1g_lock_pagetable_and_map(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, len, va_range, prc_ptr, thrd_ptr, ctn_ptr, pagetable, Ghost(entry_lctx),
        Tracked(cpu_perm), Tracked(thread_perm))
}

/// With cpu `cpu_id` and its running thread write-held since the entry snapshot `entry_lctx` was aligned with: write-locks the pagetable of the thread's process and maps the range when no leaf maps inside a 1G slot of it; otherwise releases every lock with no step and returns
/// ErrorVaInUse.
fn mmap_1g_lock_pagetable_and_map(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, len: usize, va_range: &VaRange1G,
    prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot, Ghost(entry_lctx): Ghost<LocalContext>,
    Tracked(cpu_perm): Tracked<LockPerm>, Tracked(thread_perm): Tracked<LockPerm>,
) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).view().len() == 0,
        *va_range == spec_va_range_1g(va, len),
        va_range.wf(),
        old(steps).snapshot_k().inv(),
        typed_lock_maps_aligned(&old(steps).snapshot_k(), &entry_lctx),
        !(len == 0 || len > usize::MAX / 0x40000000 || !spec_va_1g_valid(va) || va >= usize::MAX - len * 0x40000000 || !spec_va_1g_range_valid(va, len)),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![thrd_ptr],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        ({
            let pre = old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view();
            let post = old(krnl).cpu_arr.spec_index(cpu_id).view();
            &&& !pre.locked()
            &&& post.locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cpu_perm.lock_id() })
            &&& post.view().view() == pre.view().view()
            &&& post.view().kernel_call_perm() is None
            &&& post.being_killed() == pre.being_killed()
            &&& post.killer_info() == pre.killer_info()
            &&& cpu_perm.state() is WriteLock
            &&& cpu_perm.thread_id() == old(lctx).thread_id()
        }),
        wlock_ensures(old(steps).snapshot_k().thrd_mp.spec_index(thrd_ptr), old(krnl).thrd_mp.spec_index(thrd_ptr), old(steps).snapshot_k().thrd_mp.lock_id_by_key(thrd_ptr), old(lctx), thread_perm),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).prc_mp.dom().contains(prc_ptr),
        !old(krnl).prc_mp.spec_index(prc_ptr).view().zombie,
        old(krnl).ctn_mp.dom().contains(ctn_ptr),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_1g >= len,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k >= len,
        old(krnl).prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        old(krnl).pt_mp.dom().contains(pagetable),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is None,
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, thrd_mp: old(krnl).thrd_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).thrd_mp.unchanged_except(&old(steps).snapshot_k().thrd_mp, thrd_ptr),
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        ret == mmap_1g_syscall_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, va, len),
        !(ret is Success) ==> final(steps).view().len() == 0,
        ret is Success ==> mmap_1g_syscall_trace(final(steps).view(), cpu_id, va, len),
        ret is Success ==> mmap_1g_syscall_success_mapped(final(krnl), cpu_id, va, len),
{
    assert(krnl.prc_mp.view().spec_index(prc_ptr).is_init() && krnl.prc_mp.view().spec_index(prc_ptr).addr() == prc_ptr) by { process_perms_wf_at(krnl.prc_mp, prc_ptr); };
    let process = krnl.prc_mp.borrow_rodata(prc_ptr).borrow();
    let cr3 = process.cr3;
    let pcid = process.pcid;
    assert({
        &&& krnl.pt_mp.spec_index(pagetable).view().cr3 == cr3
        &&& krnl.pt_mp.spec_index(pagetable).view().pcid == Some(pcid)
        &&& krnl.pt_mp.spec_index(pagetable).view().proc_ptr == prc_ptr
        &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3
        &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid
        &&& page_ptr_valid(cr3)
        &&& pcid_valid(pcid)
        &&& pcid != KERNEL_DEFAULT_PCID
    }) by {
        process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr); process_perms_wf_at(krnl.prc_mp, prc_ptr);
        process_pcid_allocator_wf_process_at(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp, prc_ptr); pagetable_perms_wf_at(krnl.pt_mp, pagetable);
        krnl.pt_mp.spec_index(pagetable).view().table_pages_wf_cr3_at();
    };
    proof { krnl.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr); }
    let Tracked(pagetable_perm) = krnl.wlock_pagetable(pagetable, Tracked(&mut *lctx));
    proof {
        assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable) == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable));
        krnl.default_pagetable_wf_at(pagetable);
    }
    let (free, Ghost(at), Ghost(found_2m), Ghost(found_4k)) = mmap_1g_precheck(krnl, va_range, pagetable, Tracked(&*lctx), Tracked(&pagetable_perm));
    if free {
        mmap_1g_map_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, len, va_range, prc_ptr, thrd_ptr, ctn_ptr, pagetable, cr3, pcid, Ghost(entry_lctx),
            Tracked(cpu_perm), Tracked(thread_perm), Tracked(pagetable_perm));
        RetValueType::Success
    } else {
        proof { mmap_1g_result_from_k(&old(steps).snapshot_k(), cpu_id, va, len, RetValueType::ErrorVaInUse, at, found_2m, found_4k); }
        mmap_1g_unlock_all_rejected(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, thrd_ptr, pagetable, Ghost(entry_lctx), Tracked(cpu_perm), Tracked(thread_perm),
            Tracked(pagetable_perm));
        RetValueType::ErrorVaInUse
    }
}

/// With cpu `cpu_id` and its running thread write-held and the pagetable `pagetable` of the thread's process write-held since the entry snapshot `entry_lctx` was aligned with, and nothing else changed: releases all three locks and records no step.
fn mmap_1g_unlock_all_rejected(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot,
    Ghost(entry_lctx): Ghost<LocalContext>, Tracked(cpu_perm): Tracked<LockPerm>, Tracked(thread_perm): Tracked<LockPerm>, Tracked(pagetable_perm): Tracked<LockPerm>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k().inv(),
        typed_lock_maps_aligned(&old(steps).snapshot_k(), &entry_lctx),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, thrd_mp: old(krnl).thrd_mp, pt_mp: old(krnl).pt_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).thrd_mp.unchanged_except(&old(steps).snapshot_k().thrd_mp, thrd_ptr),
        old(krnl).pt_mp.unchanged_except(&old(steps).snapshot_k().pt_mp, pagetable),
        ({
            let pre = old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view();
            let post = old(krnl).cpu_arr.spec_index(cpu_id).view();
            &&& !pre.locked()
            &&& post.locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cpu_perm.lock_id() })
            &&& post.view().view() == pre.view().view()
            &&& post.being_killed() == pre.being_killed()
            &&& post.killer_info() == pre.killer_info()
            &&& cpu_perm.state() is WriteLock
            &&& cpu_perm.thread_id() == old(lctx).thread_id()
        }),
        wlock_ensures(old(steps).snapshot_k().thrd_mp.spec_index(thrd_ptr), old(krnl).thrd_mp.spec_index(thrd_ptr), old(steps).snapshot_k().thrd_mp.lock_id_by_key(thrd_ptr), old(lctx), thread_perm),
        !old(steps).snapshot_k().pt_mp.spec_index(pagetable).locked(),
        old(krnl).pt_mp.spec_index(pagetable).locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: pagetable_perm.lock_id() }),
        old(krnl).pt_mp.spec_index(pagetable).view() == old(steps).snapshot_k().pt_mp.spec_index(pagetable).view(),
        old(krnl).pt_mp.spec_index(pagetable).being_killed() == old(steps).snapshot_k().pt_mp.spec_index(pagetable).being_killed(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).leaves_present(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows(),
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        !(old(krnl).prc_mp.spec_index(old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr).view().state.view() is TablesEmptied)
            && !(old(krnl).prc_mp.spec_index(old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr).view().state.view() is Zombie) ==> forall|l4i: L4Index|
            #![trigger old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l4(l4i)]
            old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i) && old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l4(l4i) is Some ==> old(krnl).pt_mp.spec_index(pagetable).view().spec_resolve_mapping_l4(l4i) is Some,
        !(old(krnl).prc_mp.spec_index(old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr).view().state.view() is TablesEmptied)
            && !(old(krnl).prc_mp.spec_index(old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr).view().state.view() is Zombie) ==> forall|l4i: L4Index, l3i: L3Index|
            #![trigger old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i)]
            old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i) is Some
                ==> old(krnl).pt_mp.spec_index(pagetable).view().spec_resolve_mapping_l3(l4i, l3i) is Some,
        pagetable_perm.state() is WriteLock,
        pagetable_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is None,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![thrd_ptr],
        old(lctx).pagetable_lock_map().dom() =~= set![pagetable],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == old(steps).view(),
{
    krnl.wunlock_pagetable(pagetable, Tracked(&mut *lctx), Tracked(pagetable_perm));
    krnl.wunlock_thread(thrd_ptr, Tracked(&mut *lctx), Tracked(thread_perm));
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
    proof {
        assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
        steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, Some(thrd_ptr), None, Some(pagetable), None);
    }
}
} // verus!
