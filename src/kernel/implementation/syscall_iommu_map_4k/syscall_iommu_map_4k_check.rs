use vstd::prelude::*;
use crate::*;
use super::syscall_iommu_map_4k_spec::*;
use super::syscall_iommu_map_4k_lock::*;
#[cfg(verus_keep_ghost)]
use super::syscall_iommu_map_4k_trace::*;

verus! {
pub(super) struct IommuMap4kLocked {
    pub container_ptr: RwLockContainerPtr, pub process_ptr: RwLockProcessPtr, pub thread_ptr: RwLockThreadPtr, pub pagetable_ptr: RwLockPageTableRoot, pub iommu_table_ptr: RwLockPageTableRoot,
    pub cpu_lock_perm: Tracked<LockPerm>, pub process_lock_perm: Tracked<LockPerm>, pub thread_lock_perm: Tracked<LockPerm>, pub pagetable_lock_perm: Tracked<LockPerm>,
    pub iommu_table_lock_perm: Tracked<LockPerm>, pub window_perms: Tracked<Map<WindowVa, LockPerm>>,
}

/// With `cpu_id`, its current `process_ptr` and `thread_ptr`, and the IOMMU table `iommu_table_ptr` write-held and
/// `pagetable_ptr` read-held by `pagetable_lock_perm` since the entry snapshot, with no window held and its window locks as at
/// the snapshot: releases all five and finishes the call without recording a step.
fn iommu_map_4k_unlock_rejected(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    pagetable_ptr: RwLockPageTableRoot, iommu_table_ptr: RwLockPageTableRoot, Tracked(iommu_table_lock_perm): Tracked<LockPerm>, Tracked(pagetable_lock_perm): Tracked<LockPerm>,
    Tracked(thread_lock_perm): Tracked<LockPerm>, Tracked(process_lock_perm): Tracked<LockPerm>, Tracked(cpu_lock_perm): Tracked<LockPerm>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).inv(),
        cpu_id == old(lctx).cpu_id(),
        *old(krnl) == (KernelK {
            cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower,
            it_mp: old(krnl).it_mp, ..old(steps).snapshot_k()
        }),
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        !old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().locked(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().killer_info(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cpu_lock_perm.lock_id() }),
        cpu_lock_perm.state() is WriteLock && cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(krnl).prc_mp.unchanged_except(&old(steps).snapshot_k().prc_mp, process_ptr),
        old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, thread_ptr),
        old(krnl).pt_mp.unchanged_except(&old(steps).snapshot_k().pt_mp, pagetable_ptr),
        old(krnl).it_mp.unchanged_except(&old(steps).snapshot_k().it_mp, iommu_table_ptr),
        wlock_ensures(old(steps).snapshot_k().prc_mp.spec_index(process_ptr), old(krnl).prc_mp.spec_index(process_ptr), old(steps).snapshot_k().prc_mp.lock_id_by_key(process_ptr), old(lctx), process_lock_perm),
        wlock_ensures(old(steps).snapshot_k().thr_mp.spec_index(thread_ptr), old(krnl).thr_mp.spec_index(thread_ptr), old(steps).snapshot_k().thr_mp.lock_id_by_key(thread_ptr), old(lctx), thread_lock_perm),
        wlock_ensures(old(steps).snapshot_k().it_mp.spec_index(iommu_table_ptr), old(krnl).it_mp.spec_index(iommu_table_ptr), old(steps).snapshot_k().it_mp.lock_id_by_key(iommu_table_ptr), old(lctx),
            iommu_table_lock_perm),
        !old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).wlocked(),
        !old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).locked_by_thread(old(lctx).thread_id()),
        old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread() == (RwLockState::Read {
            reader_map: (if old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).locking_thread() is Read { old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map } else { Map::empty() })
                .insert(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        }),
        old(krnl).pt_mp.spec_index(pagetable_ptr).view() == old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).view(),
        forall|q: RwLockPageTableRoot| #![trigger old(krnl).pt_lower.view().spec_index(q)] q != pagetable_ptr ==> old(krnl).pt_lower.view().spec_index(q) == old(steps).snapshot_k().pt_lower.view().spec_index(q),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable_ptr).mapping_4k(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable_ptr).mapping_2m(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable_ptr).mapping_1g(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks,
        pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).prc_mp.dom().contains(process_ptr) && !old(krnl).prc_mp.spec_index(process_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running || old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Zombie,
        old(krnl).thr_mp.dom().contains(thread_ptr) && !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean() && old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).pt_mp.dom().contains(pagetable_ptr),
        old(krnl).it_mp.dom().contains(iommu_table_ptr) && old(krnl).it_mp.spec_index(iommu_table_ptr).view().leaves_present(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id] && old(lctx).process_lock_map().dom() =~= set![process_ptr] && old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).pagetable_lock_map().dom() =~= set![pagetable_ptr] && old(lctx).iommu_table_lock_map().dom() =~= set![iommu_table_ptr],
        old(lctx).pagetable_window_lock_map().dom().is_empty() && old(lctx).page_lock_map().dom().is_empty() && old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty() && old(lctx).scheduler_lock_map().dom().is_empty() && old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty() && old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty() && old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k) && old(lctx).holds_no_allocator_locks(PageSize::SZ2m) && old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
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
    proof {
        if old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).locking_thread() is Read {
            assert(old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.insert(lctx.thread_id(), pagetable_lock_perm.lock_id()).remove(lctx.thread_id())
                =~= old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map);
        } else {
            assert(Map::<LockThreadId, LockToken>::empty().insert(lctx.thread_id(), pagetable_lock_perm.lock_id()).remove(lctx.thread_id()).dom() =~= Set::empty());
        }
    }
    krnl.wunlock_iommu_table(iommu_table_ptr, Tracked(&mut *lctx), Tracked(iommu_table_lock_perm));
    krnl.runlock_pagetable(pagetable_ptr, Tracked(&mut *lctx), Tracked(pagetable_lock_perm));
    krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
    krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
        steps.end_kernel_step_restored_locks_with_iommu_table(&*krnl, &*lctx, cpu_id, None, Some(process_ptr), Some(thread_ptr), None, Some(pagetable_ptr), None, Some(iommu_table_ptr));
    }
}

/// With `cpu_id` and its current `process_ptr` and `thread_ptr` write-held since the entry snapshot and nothing else held:
/// releases all three and finishes the call without recording a step.
fn iommu_map_4k_unlock_thread_rejected(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    Tracked(thread_lock_perm): Tracked<LockPerm>, Tracked(process_lock_perm): Tracked<LockPerm>, Tracked(cpu_lock_perm): Tracked<LockPerm>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        cpu_id == old(lctx).cpu_id(),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        !old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().locked(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().killer_info(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cpu_lock_perm.lock_id() }),
        cpu_lock_perm.state() is WriteLock && cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(krnl).prc_mp.unchanged_except(&old(steps).snapshot_k().prc_mp, process_ptr),
        old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, thread_ptr),
        wlock_ensures(old(steps).snapshot_k().prc_mp.spec_index(process_ptr), old(krnl).prc_mp.spec_index(process_ptr), old(steps).snapshot_k().prc_mp.lock_id_by_key(process_ptr), old(lctx), process_lock_perm),
        wlock_ensures(old(steps).snapshot_k().thr_mp.spec_index(thread_ptr), old(krnl).thr_mp.spec_index(thread_ptr), old(steps).snapshot_k().thr_mp.lock_id_by_key(thread_ptr), old(lctx), thread_lock_perm),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).prc_mp.dom().contains(process_ptr) && !old(krnl).prc_mp.spec_index(process_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running || old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Zombie,
        old(krnl).thr_mp.dom().contains(thread_ptr) && !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean() && old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id] && old(lctx).process_lock_map().dom() =~= set![process_ptr] && old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).pagetable_lock_map().dom().is_empty() && old(lctx).iommu_table_lock_map().dom().is_empty() && old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).page_lock_map().dom().is_empty() && old(lctx).container_lock_map().dom().is_empty() && old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty() && old(lctx).pcid_allocator_lock_map().dom().is_empty() && old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty() && old(lctx).cpu_offline_flag_lock_map().dom().is_empty() && old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k) && old(lctx).holds_no_allocator_locks(PageSize::SZ2m) && old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
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
    krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
    krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
        steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(process_ptr), Some(thread_ptr), None, None, None);
    }
}

/// Validates the arguments, write-locks cpu `cpu_id` and its running process and thread, read-locks the page table, write-locks
/// the IOMMU table, holds the existing 2M windows of the va range, and checks that every va of the range is a present user 4K
/// leaf and every iova is free. A rejected call releases every lock, records no step, and returns `iommu_map_4k_syscall_result`
/// of the entry state; otherwise every lock is held, only lock states changed, and the result is Success.
pub(super) fn iommu_map_4k_lock_and_check(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, iova: VAddr,
    range: usize) -> (ret: Result<(IommuMap4kLocked, VaRange4K, VaRange4K), RetValueType>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).view().len() == 0,
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
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
            &&& final(steps).view().len() == 0
        }),
        ret is Ok ==> ({
            let e = ret->Ok_0.0;
            let va_range = ret->Ok_0.1;
            let iova_range = ret->Ok_0.2;
            let wp = e.window_perms.view();
            let ptp = e.pagetable_ptr;
            let cpu = final(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            let thread = final(krnl).thr_mp.spec_index(e.thread_ptr).view();
            let process = final(krnl).prc_mp.spec_index(e.process_ptr).view();
            let it = final(krnl).it_mp.spec_index(e.iommu_table_ptr).view();
            let pt = pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), ptp);
            &&& RetValueType::Success == iommu_map_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, iova, range)
            &&& *final(steps) == *old(steps)
            &&& final(lctx).kernel_view_locking_state() is Acquire
            &&& va_range == iommu_map_4k_syscall_range(va, range) && iova_range == iommu_map_4k_syscall_range(iova, range)
            &&& va_range.wf() && iova_range.wf() && va_range.len == range && iova_range.len == range && range > 0
            &&& final(lctx).cpu_lock_map().dom() =~= set![cpu_id]
            &&& final(lctx).process_lock_map().dom() =~= set![e.process_ptr]
            &&& final(lctx).thread_lock_map().dom() =~= set![e.thread_ptr]
            &&& final(lctx).pagetable_lock_map().dom() =~= set![ptp]
            &&& final(lctx).iommu_table_lock_map().dom() =~= set![e.iommu_table_ptr]
            &&& final(lctx).page_lock_map().dom().is_empty() && final(lctx).container_lock_map().dom().is_empty() && final(lctx).endpoint_lock_map().dom().is_empty()
            &&& final(lctx).pcid_allocator_lock_map().dom().is_empty() && final(lctx).iommu_root_table_lock_map().dom().is_empty()
            &&& final(lctx).pcid_needflush_lock_map().dom().is_empty() && final(lctx).cpu_offline_flag_lock_map().dom().is_empty()
            &&& final(lctx).scheduler_lock_map().dom().is_empty() && final(lctx).cpu_set_lock_map().dom().is_empty()
            &&& final(lctx).holds_no_allocator_locks(PageSize::SZ4k) && final(lctx).holds_no_allocator_locks(PageSize::SZ2m) && final(lctx).holds_no_allocator_locks(PageSize::SZ1g)
            &&& typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(final(lctx).process_lock_map(), e.process_ptr, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(final(lctx).thread_lock_map(), e.thread_ptr, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), ptp, TypedLockMode::Read)
            &&& typed_lock_map_contains_mode(final(lctx).iommu_table_lock_map(), e.iommu_table_ptr, TypedLockMode::Write)
            &&& e.cpu_lock_perm.view().state() is WriteLock && e.cpu_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& e.cpu_lock_perm.view().lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id
            &&& e.process_lock_perm.view().state() is WriteLock && e.process_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& e.process_lock_perm.view().lock_id() == final(krnl).prc_mp.spec_index(e.process_ptr).locking_thread()->Write_lock_id
            &&& e.thread_lock_perm.view().state() is WriteLock && e.thread_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& e.thread_lock_perm.view().lock_id() == final(krnl).thr_mp.spec_index(e.thread_ptr).locking_thread()->Write_lock_id
            &&& e.pagetable_lock_perm.view().state() is ReadLock && e.pagetable_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& final(krnl).pt_mp.spec_index(ptp).locking_thread()->Read_reader_map.contains_pair(final(lctx).thread_id(), e.pagetable_lock_perm.view().lock_id())
            &&& e.iommu_table_lock_perm.view().state() is WriteLock && e.iommu_table_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& e.iommu_table_lock_perm.view().lock_id() == final(krnl).it_mp.spec_index(e.iommu_table_ptr).locking_thread()->Write_lock_id
            &&& cpu.current_process == Some(e.process_ptr) && cpu.current_thread == Some(e.thread_ptr) && cpu.state is Running
            &&& !final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cpu.current_cr3, cpu.current_pcid)
            &&& final(krnl).thr_mp.dom().contains(e.thread_ptr) && !final(krnl).thr_mp.spec_index(e.thread_ptr).being_killed()
            &&& thread.owning_proc == e.process_ptr && thread.owning_container == e.container_ptr && thread.state == (ThreadState::RUNNING { cpu_id })
            &&& thread.quota_4k >= 3 * range && thread.temp_alloc_clean() && thread.free_quota_pending_clean() && thread.syscall_progress.view() is None
            &&& !final(krnl).thr_mp.spec_index(e.thread_ptr).view_ghost().exited
            &&& old(krnl).ctn_mp.dom().contains(e.container_ptr)
            &&& process.pagetable == ptp && process.iommu_table == Some(e.iommu_table_ptr)
            &&& !final(krnl).prc_mp.spec_index(e.process_ptr).being_killed()
            &&& process.state.view() is Running || process.state.view() is Zombie
            &&& final(krnl).it_mp.dom().contains(e.iommu_table_ptr) && it.leaves_present()
            &&& pt.kernel_l4_end() <= spec_v2l4index(va_range.start)
            &&& forall|j: int| #![trigger va_range.view()[j]] 0 <= j < range ==> pt.mapping_4k().dom().contains(va_range.view()[j]) && pt.mapping_4k()[va_range.view()[j]].present
            &&& forall|j: int| #![trigger iova_range.view()[j]] 0 <= j < range ==> !it.mapping_4k().dom().contains(iova_range.view()[j])
            &&& forall|j: int| #![trigger va_range.view()[j]] 0 <= j < range ==> va_4k_valid(va_range.view()[j]) && final(lctx).pagetable_window_lock_map().dom().contains((ptp, window_of(va_range.view()[j])))
            &&& forall|j: int| #![trigger iova_range.view()[j]] 0 <= j < range ==> va_4k_valid(iova_range.view()[j])
            &&& forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == ptp && wp.dom().contains(w))
            &&& forall|w: WindowVa| #![trigger va_range_2m_windows(va_range).contains(w)]
                va_range_2m_windows(va_range).contains(w) && pt.higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> wp.dom().contains(w)
            &&& forall|w: WindowVa| #![trigger wp.dom().contains(w)] wp.dom().contains(w) ==> {
                &&& va_range_2m_windows(va_range).contains(w)
                &&& pt.higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (ptp, w), TypedLockMode::Write)
                &&& wp.index(w).state() is WriteLock
                &&& wp.index(w).thread_id() == final(lctx).thread_id()
                &&& pt.lower.l2_owner(pt.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)) == (SpinLockState::Some { thread_id: wp.index(w).thread_id(), lock_id: wp.index(w).lock_id() })
                &&& pt.window_leaves_present(w)
                &&& !pt.lower.window_stale_cpus.dom().contains((pt.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            }
            &&& *final(krnl) == (KernelK {
                cpu_arr: final(krnl).cpu_arr, cpu_op: final(krnl).cpu_op, prc_mp: final(krnl).prc_mp, thr_mp: final(krnl).thr_mp, pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower,
                it_mp: final(krnl).it_mp, ..*old(krnl)
            })
            &&& !old(krnl).cpu_arr.spec_index(cpu_id).value.locked()
            &&& final(krnl).cpu_arr.entries_unchanged_except(&old(krnl).cpu_arr, cpu_id)
            &&& cpu == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view()
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() is None
            &&& final(krnl).cpu_op.view().view() == old(krnl).cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep)
            &&& final(krnl).cpu_arr.spec_index(cpu_id).value.killer_info() == old(krnl).cpu_arr.spec_index(cpu_id).value.killer_info()
            &&& final(krnl).cpu_arr.spec_index(cpu_id).value.being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).value.being_killed()
            &&& final(krnl).cpu_arr.spec_index(cpu_id).value.locking_thread() is Write
            &&& !old(krnl).prc_mp.spec_index(e.process_ptr).locked()
            &&& final(krnl).prc_mp.unchanged_except(&old(krnl).prc_mp, e.process_ptr)
            &&& process == old(krnl).prc_mp.spec_index(e.process_ptr).view()
            &&& final(krnl).prc_mp.spec_index(e.process_ptr).view_rodata() == old(krnl).prc_mp.spec_index(e.process_ptr).view_rodata()
            &&& final(krnl).prc_mp.spec_index(e.process_ptr).view_ghost() == old(krnl).prc_mp.spec_index(e.process_ptr).view_ghost()
            &&& final(krnl).prc_mp.spec_index(e.process_ptr).being_killed() == old(krnl).prc_mp.spec_index(e.process_ptr).being_killed()
            &&& final(krnl).prc_mp.spec_index(e.process_ptr).locking_thread() is Write
            &&& old(krnl).thr_mp.dom().contains(e.thread_ptr) && !old(krnl).thr_mp.spec_index(e.thread_ptr).locked()
            &&& final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, e.thread_ptr)
            &&& thread == old(krnl).thr_mp.spec_index(e.thread_ptr).view()
            &&& final(krnl).thr_mp.spec_index(e.thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(e.thread_ptr).being_killed()
            &&& final(krnl).thr_mp.spec_index(e.thread_ptr).locking_thread() is Write
            &&& !old(krnl).pt_mp.spec_index(ptp).wlocked()
            &&& final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, ptp)
            &&& final(krnl).pt_mp.spec_index(ptp).view() == old(krnl).pt_mp.spec_index(ptp).view()
            &&& final(krnl).pt_mp.spec_index(ptp).locking_thread() is Read
            &&& final(krnl).pt_lower.view() == old(krnl).pt_lower.view().insert(ptp, final(krnl).pt_lower.view().spec_index(ptp))
            &&& pt.mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), ptp).mapping_4k()
            &&& pt.mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), ptp).mapping_2m()
            &&& pt.mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), ptp).mapping_1g()
            &&& pt.lower.pagetable_window_locks == pagetable_window_locks_after_locking_range(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), ptp).lower.pagetable_window_locks, va_range)
            &&& !old(krnl).it_mp.spec_index(e.iommu_table_ptr).locked()
            &&& final(krnl).it_mp.unchanged_except(&old(krnl).it_mp, e.iommu_table_ptr)
            &&& it == old(krnl).it_mp.spec_index(e.iommu_table_ptr).view()
            &&& final(krnl).it_mp.spec_index(e.iommu_table_ptr).locking_thread() is Write
        }),
{
    if range == 0 || range > usize::MAX / 4096usize || !va_4k_valid(va) || !va_4k_valid(iova) {
        proof {
            kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
        }
        return Err(RetValueType::Error);
    }
    let span = range * 4096usize;
    if va >= usize::MAX - span || !va_4k_range_valid(va, range) || iova >= usize::MAX - span || !va_4k_range_valid(iova, range) {
        proof {
            kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
        }
        return Err(RetValueType::Error);
    }
    let va_range = VaRange4K::new(va, range);
    let iova_range = VaRange4K::new(iova, range);
    let locked = match iommu_map_4k_lock_running_thread(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, iova, range) {
        Ok(e) => e,
        Err(r) => { return Err(r); },
    };
    let Tracked(cpu_lock_perm) = locked.cpu_lock_perm;
    let Tracked(process_lock_perm) = locked.process_lock_perm;
    let Tracked(thread_lock_perm) = locked.thread_lock_perm;
    let (container_ptr, process_ptr, thread_ptr) = (locked.container_ptr, locked.process_ptr, locked.thread_ptr);
    proof { process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr); thread_perms_wf_map(krnl.thr_mp); process_perms_wf_map(krnl.prc_mp); }
    let thread = krnl.thr_mp.borrow_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_lock_perm));
    let pagetable_ptr = thread.proc_pagetable_ptr;
    let quota_4k = thread.quota_4k;
    proof {
        process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, process_ptr); process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, process_ptr);
        process_iommu_table_match_process_at(old(krnl).prc_mp, old(krnl).it_mp, process_ptr);
    }
    let iommu_table = krnl.prc_mp.borrow_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(&process_lock_perm)).iommu_table;
    if iommu_table.is_none() || quota_4k < 3 * range {
        iommu_map_4k_unlock_thread_rejected(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, Tracked(thread_lock_perm), Tracked(process_lock_perm),
            Tracked(cpu_lock_perm));
        if iommu_table.is_none() {
            proof { iommu_map_4k_result_from_k(&*old(krnl), cpu_id, va, iova, range, RetValueType::ErrorPciNoIommuTable); }
            return Err(RetValueType::ErrorPciNoIommuTable);
        }
        proof { iommu_map_4k_result_from_k(&*old(krnl), cpu_id, va, iova, range, RetValueType::ErrorNoQuota); }
        return Err(RetValueType::ErrorNoQuota);
    }
    let iommu_table_ptr = iommu_table.unwrap();
    proof { krnl.pt_mp.typed_lock_map_aligned_locked_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); }
    let Tracked(pagetable_lock_perm) = krnl.rlock_pagetable(pagetable_ptr, Tracked(&mut *lctx));
    proof { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr); }
    proof { krnl.default_pagetable_wf_at(pagetable_ptr); }
    let user_range = va2index(va).0 >= krnl.dflt_pt.borrow().kernel_l4_end;
    let Tracked(iommu_table_lock_perm) = krnl.wlock_iommu_table(iommu_table_ptr, Tracked(&mut *lctx));
    let Tracked(window_perms) = if user_range {
        krnl.lock_pagetable_range_existing_windows(pagetable_ptr, &va_range, Tracked(&pagetable_lock_perm), Tracked(&mut *lctx))
    } else { Tracked(Map::tracked_empty()) };
    proof {
        iova_range.va_range_lemma(); va_range.va_range_lemma();
        assert(krnl.it_mp.spec_index(iommu_table_ptr).view() == old(krnl).it_mp.spec_index(iommu_table_ptr).view() && krnl.it_mp.spec_index(iommu_table_ptr).view().leaves_present());
        assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k());
        assert(krnl.pt_mp.spec_index(pagetable_ptr).view() == old(krnl).pt_mp.spec_index(pagetable_ptr).view());
        assert(iova_range == iommu_map_4k_syscall_range(iova, range) && va_range == iommu_map_4k_syscall_range(va, range));
    }
    let ret = if !user_range {
        proof { iommu_map_4k_result_from_k(&*old(krnl), cpu_id, va, iova, range, RetValueType::Error); }
        RetValueType::Error
    } else {
        proof { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr); }
        let pagetable = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(&pagetable_lock_perm));
        let tracked lower = krnl.pt_lower.borrow().tracked_borrow(pagetable_ptr);
        if !pagetable.mapping_4k_va_range_present(Tracked(lower), &va_range) {
            proof { iommu_map_4k_result_from_k(&*old(krnl), cpu_id, va, iova, range, RetValueType::ErrorIommuVaNotMapped); }
            RetValueType::ErrorIommuVaNotMapped
        } else {
            proof { iommu_table_perms_wf_map(krnl.it_mp); iommu_table_perms_wf_at(krnl.it_mp, iommu_table_ptr); iommu_table_perms_wf_kernel_l4_end_at(krnl.it_mp, iommu_table_ptr); }
            let it = krnl.it_mp.borrow_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(&iommu_table_lock_perm));
            if !it.mapping_4k_va_range_absent(&iova_range) {
                proof { iommu_map_4k_result_from_k(&*old(krnl), cpu_id, va, iova, range, RetValueType::ErrorIommuIovaAlreadyMapped); }
                RetValueType::ErrorIommuIovaAlreadyMapped
            } else {
                proof { iommu_map_4k_result_from_k(&*old(krnl), cpu_id, va, iova, range, RetValueType::Success); }
                RetValueType::Success
            }
        }
    };
    let success = match ret { RetValueType::Success => true, _ => false };
    proof {
        assert(lctx.cpu_lock_map().dom() =~= set![cpu_id] && lctx.process_lock_map().dom() =~= set![process_ptr] && lctx.thread_lock_map().dom() =~= set![thread_ptr]);
        assert(lctx.pagetable_lock_map().dom() =~= set![pagetable_ptr] && lctx.iommu_table_lock_map().dom() =~= set![iommu_table_ptr]);
    }
    if !success {
        if user_range { krnl.unlock_pagetable_range_existing_windows(pagetable_ptr, &va_range, Tracked(&pagetable_lock_perm), Tracked(&mut *lctx), Tracked(window_perms)); }
        proof {
            assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks =~= pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks);
        }
        iommu_map_4k_unlock_rejected(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, pagetable_ptr, iommu_table_ptr, Tracked(iommu_table_lock_perm),
            Tracked(pagetable_lock_perm), Tracked(thread_lock_perm), Tracked(process_lock_perm), Tracked(cpu_lock_perm));
        return Err(ret);
    }
    proof { va_range_2m_windows_contains_window_of_first_n_pages(va_range, range as int); }
    Ok((IommuMap4kLocked {
        container_ptr, process_ptr, thread_ptr, pagetable_ptr, iommu_table_ptr, cpu_lock_perm: Tracked(cpu_lock_perm), process_lock_perm: Tracked(process_lock_perm),
        thread_lock_perm: Tracked(thread_lock_perm), pagetable_lock_perm: Tracked(pagetable_lock_perm), iommu_table_lock_perm: Tracked(iommu_table_lock_perm), window_perms: Tracked(window_perms),
    }, va_range, iova_range))
}
} // verus!
