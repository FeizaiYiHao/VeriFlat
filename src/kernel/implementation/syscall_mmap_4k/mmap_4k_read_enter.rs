use vstd::prelude::*;
use crate::*;
use super::mmap_4k_map_range::mmap_4k_map_leaves_and_finish;
use super::mmap_4k_precheck::{mmap_4k_precheck, Mmap4kPrecheck};
use super::syscall_mmap_4k_spec::*;
use super::syscall_mmap_4k_trace::*;

verus! {
/// With `cpu_id` and its current `thread_ptr` write-held since the entry snapshot and `pagetable_ptr` read-held by
/// `pagetable_lock_perm` with no window held: releases all three and finishes the call without recording a step.
fn mmap_4k_unlock_read_rejected(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot,
    Tracked(pagetable_lock_perm): Tracked<LockPerm>, Tracked(thread_lock_perm): Tracked<LockPerm>, Tracked(cpu_lock_perm): Tracked<LockPerm>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k().inv(),
        old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).inv(),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, thr_mp: old(krnl).thr_mp, pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, thread_ptr),
        old(krnl).pt_mp.unchanged_except(&old(steps).snapshot_k().pt_mp, pagetable_ptr),
        wlock_ensures(old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view(), old(krnl).cpu_arr.spec_index(cpu_id).view(), old(steps).snapshot_k().cpu_arr.lock_id_by_index(cpu_id), old(lctx), cpu_lock_perm),
        wlock_ensures(old(steps).snapshot_k().thr_mp.spec_index(thread_ptr), old(krnl).thr_mp.spec_index(thread_ptr), old(steps).snapshot_k().thr_mp.lock_id_by_key(thread_ptr), old(lctx), thread_lock_perm),
        !old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).wlocked(),
        !old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).locked_by_thread(old(lctx).thread_id()),
        old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread() == (RwLockState::Read {
            reader_map: (if old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).locking_thread() is Read { old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map } else { Map::empty() })
                .insert(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        }),
        old(krnl).pt_mp.spec_index(pagetable_ptr).view() == old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).view(),
        old(krnl).pt_mp.spec_index(pagetable_ptr).being_killed() == old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).being_killed(),
        old(krnl).pt_lower.view() =~= old(steps).snapshot_k().pt_lower.view().insert(pagetable_ptr, old(krnl).pt_lower.view().spec_index(pagetable_ptr)),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable_ptr).mapping_4k(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable_ptr).mapping_2m(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable_ptr).mapping_1g(),
        pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).pt_mp.dom().contains(pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).pagetable_lock_map().dom() =~= set![pagetable_ptr],
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).page_lock_map().dom().is_empty(),
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
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == old(steps).view(),
        final(steps).nonlock_view() == old(steps).nonlock_view(),
{
    proof {
        if old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).locking_thread() is Read {
            assert(old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.insert(lctx.thread_id(), pagetable_lock_perm.lock_id()).remove(lctx.thread_id())
                =~= old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map);
        } else {
            assert(Map::<LockThreadId, LockToken>::empty().insert(lctx.thread_id(), pagetable_lock_perm.lock_id()).remove(lctx.thread_id()).dom() =~= Set::empty());
        }
    }
    krnl.runlock_pagetable(pagetable_ptr, Tracked(&mut *lctx), Tracked(pagetable_lock_perm));
    krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof { steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, Some(thread_ptr), None, Some(pagetable_ptr), None); }
}

/// With `cpu_id` and its current `thread_ptr` write-held since the entry snapshot `entry_lctx` was aligned with and the
/// thread's quota sufficient: read-locks the process pagetable and, if every 2M window of `va_range` exists, holds them all
/// and maps the range with the recorded steps when it is free, or releases every lock and finishes without recording a step
/// when it is not. A range below the first user L4 index finishes as an error. When some window is missing, releases every
/// lock without recording a step and returns `None`, ready to retry in the fill phase.
pub(super) fn mmap_4k_try_read_enter(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, range: usize, va_range: &VaRange4K,
    alloc_ptr_4k: RwLockPageAllocatorPtr, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, pagetable_ptr: RwLockPageTableRoot,
    Ghost(entry_lctx): Ghost<LocalContext>, Tracked(thread_lock_perm): Tracked<LockPerm>, Tracked(cpu_lock_perm): Tracked<LockPerm>,
) -> (ret: Option<RetValueType>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).view().len() == 0,
        old(steps).nonlock_view().len() == 0,
        old(steps).snapshot_k().inv(),
        typed_lock_maps_aligned(&old(steps).snapshot_k(), &entry_lctx),
        !(range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range)),
        *va_range == mmap_4k_syscall_va_range(va, range),
        va_range.wf(),
        va_range.len > 0,
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, thr_mp: old(krnl).thr_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        wlock_ensures(old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view(), old(krnl).cpu_arr.spec_index(cpu_id).view(), old(steps).snapshot_k().cpu_arr.lock_id_by_index(cpu_id), old(lctx), cpu_lock_perm),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
        old(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
        old(krnl).prc_mp.dom().contains(process_ptr),
        !old(krnl).prc_mp.spec_index(process_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        old(krnl).prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, thread_ptr),
        wlock_ensures(old(steps).snapshot_k().thr_mp.spec_index(thread_ptr), old(krnl).thr_mp.spec_index(thread_ptr), old(steps).snapshot_k().thr_mp.lock_id_by_key(thread_ptr), old(lctx), thread_lock_perm),
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= 4 * range,
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        old(krnl).pt_mp.dom().contains(pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).page_lock_map().dom().is_empty(),
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
        final(lctx).no_locks_held(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        ret is None ==> {
            &&& final(lctx).kernel_view_locking_state() is Acquire
            &&& final(steps).view() == old(steps).view()
            &&& final(steps).nonlock_view() == old(steps).nonlock_view()
            &&& mmap_4k_syscall_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, va, range) is Success
                || mmap_4k_syscall_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, va, range) is ErrorVaInUse
        },
        ret is Some ==> {
            let r = ret->Some_0;
            &&& final(lctx).kernel_view_locking_state() is Release
            &&& final(krnl).all_objects_unlocked(final(lctx))
            &&& r == mmap_4k_syscall_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, va, range)
            &&& r is Success ==> range + 2 <= final(steps).view().len() <= 4 * range + 3
            &&& r is Success ==> final(steps).nonlock_view().len() == final(steps).view().len()
            &&& r is Success ==> final(steps).view()[0].old_u == kernel_k_to_kernel_u(old(steps).snapshot_k())
            &&& r is Success ==> mmap_4k_syscall_trace(final(steps).view(), cpu_id, va, range)
            &&& r is Success ==> mmap_4k_syscall_success_mapped(final(krnl), cpu_id, va, range)
            &&& !(r is Success) ==> final(steps).view() == old(steps).view() && final(steps).nonlock_view() == old(steps).nonlock_view()
        },
{
    proof {
        krnl.pt_mp.typed_lock_map_aligned_locked_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr);
        assert(typed_lock_map_majors_lt(lctx.cpu_lock_map(), CPU_LOCK_MAJOR_OFF)) by { krnl.cpu_arr.typed_lock_map_aligned_lock_id_at(lctx.cpu_lock_map(), lctx.thread_id(), cpu_id); };
    }
    let Tracked(pagetable_lock_perm) = krnl.rlock_pagetable(pagetable_ptr, Tracked(&mut *lctx));
    proof { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr); }
    let (user_range, windows_exist) = {
        let pagetable = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(&pagetable_lock_perm));
        if va2index(va).0 < pagetable.kernel_l4_end { (false, false) } else { (true, pagetable.mapping_4k_va_range_windows_exist(va_range)) }
    };
    if !user_range || !windows_exist {
        mmap_4k_unlock_read_rejected(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, thread_ptr, pagetable_ptr, Tracked(pagetable_lock_perm), Tracked(thread_lock_perm),
            Tracked(cpu_lock_perm));
        if !user_range {
            proof { mmap_4k_result_from_k(&old(steps).snapshot_k(), cpu_id, va, range, RetValueType::Error, None, None); }
            return Some(RetValueType::Error);
        }
        proof {
            mmap_4k_result_from_k(&old(steps).snapshot_k(), cpu_id, va, range, RetValueType::Success, None, None);
            kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl);
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        }
        return None;
    }
    let Tracked(window_perms) = krnl.lock_pagetable_range_windows(pagetable_ptr, va_range, Tracked(&pagetable_lock_perm), Tracked(&mut *lctx));
    let ghost checked = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
    let (precheck, Ghost(found)) = mmap_4k_precheck(krnl, va_range, pagetable_ptr, Tracked(&*lctx), Tracked(&pagetable_lock_perm));
    let ready = match precheck { Mmap4kPrecheck::Ready => true, _ => false };
    if !ready {
        krnl.unlock_pagetable_range_windows(pagetable_ptr, va_range, Tracked(&pagetable_lock_perm), Tracked(&mut *lctx), Tracked(window_perms));
        mmap_4k_unlock_read_rejected(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, thread_ptr, pagetable_ptr, Tracked(pagetable_lock_perm), Tracked(thread_lock_perm),
            Tracked(cpu_lock_perm));
        proof { mmap_4k_result_from_k(&old(steps).snapshot_k(), cpu_id, va, range, RetValueType::ErrorVaInUse, Some(checked), found); }
        return Some(RetValueType::ErrorVaInUse);
    }
    proof { mmap_4k_result_from_k(&old(steps).snapshot_k(), cpu_id, va, range, RetValueType::Success, Some(checked), None); }
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::Mmap4k { range: *va_range, mapped: 0, directory: Mmap4kDirectory::None, phase: Mmap4kPhase::Read })),
        Tracked(&*lctx), Tracked(&thread_lock_perm));
    let ghost entered_k = *krnl;
    proof {
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        assert(mmap_4k_trace_after_enter(steps.view(), cpu_id, *va_range, Mmap4kPhase::Read)) by {
            kernel_cpu_thread_wlocked_pagetable_rlocked_and_progress_changed_implies_u_step(&old(steps).snapshot_k(), &entered_k, &entry_lctx, cpu_id, thread_ptr, process_ptr, pagetable_ptr);
            mmap_4k_enter_step_pre_from_k(&old(steps).snapshot_k(), cpu_id, process_ptr, thread_ptr);
            mmap_4k_enter_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(entered_k), cpu_id, process_ptr, thread_ptr, va, range, *va_range,
                Mmap4kPhase::Read);
            mmap_4k_trace_enter_step(&*steps, old(steps).view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(entered_k), cpu_id, *va_range, Mmap4kPhase::Read);
        };
        container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id);
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr);
        broadcast use spec_va_2m_valid_index_roundtrip;
    }
    let ghost entered = steps.view();
    mmap_4k_map_leaves_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, va_range, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, pagetable_ptr,
        Ghost(Mmap4kPhase::Read), Ghost(entered), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(cpu_lock_perm), Tracked(window_perms));
    Some(RetValueType::Success)
}
} // verus!
