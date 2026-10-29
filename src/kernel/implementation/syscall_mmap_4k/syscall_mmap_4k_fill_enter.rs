use vstd::prelude::*;
use crate::*;
use super::syscall_mmap_4k_fill_structure::mmap_4k_fill_range_structure;
use super::syscall_mmap_4k_map_range::mmap_4k_map_leaves_and_finish;
use super::syscall_mmap_4k_precheck::{mmap_4k_precheck, Mmap4kPrecheck};
use super::syscall_mmap_4k_spec::*;
use super::syscall_mmap_4k_trace::*;

verus! {
/// At the start of the fill section, with `cpu_id` and its current `thread_ptr` write-held since the recorded hold step and
/// the thread's quota sufficient: write-locks the process pagetable and, if `va_range` is free, holds its existing 2M windows,
/// installs every missing L4 and L3 directory of the range, downgrades to a read lock, and maps the range with the recorded
/// steps; otherwise releases every lock and records the release step.
pub(super) fn mmap_4k_fill_enter(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, range: usize, va_range: &VaRange4K,
    alloc_ptr_4k: RwLockPageAllocatorPtr, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, pagetable_ptr: RwLockPageTableRoot,
    Tracked(thread_lock_perm): Tracked<LockPerm>, Tracked(cpu_lock_perm): Tracked<LockPerm>,
) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        mmap_4k_trace_after_hold(old(steps).view(), cpu_id, *va_range),
        old(steps).view().len() == 1,
        old(steps).nonlock_view().len() == 0,
        !(range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range)),
        *va_range == mmap_4k_syscall_va_range(va, range),
        va_range.wf(),
        va_range.len > 0,
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cpu_lock_perm.lock_id() }),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
        old(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
        old(krnl).prc_mp.dom().contains(process_ptr),
        !old(krnl).prc_mp.spec_index(process_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        old(krnl).prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: thread_lock_perm.lock_id() }),
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
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        ret == mmap_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range),
        ret is Success ==> range + 3 <= final(steps).view().len() <= 4 * range + 4,
        ret is Success ==> final(steps).nonlock_view().len() + 1 == final(steps).view().len(),
        ret is Success ==> final(steps).view()[1].old_u == kernel_k_to_kernel_u(*old(krnl)),
        ret is Success ==> mmap_4k_syscall_trace(final(steps).view(), cpu_id, va, range, Mmap4kPhase::Fill),
        ret is Success ==> mmap_4k_syscall_success_mapped(final(krnl), cpu_id, va, range),
        !(ret is Success) ==> final(steps).nonlock_view().len() == 0,
        !(ret is Success) ==> mmap_4k_syscall_failure_trace(final(steps).view(), cpu_id, va, range) && final(steps).view()[1].old_u == kernel_k_to_kernel_u(*old(krnl)),
{
    let ghost entry_lctx = *lctx;
    let Tracked(pagetable_lock_perm) = krnl.wlock_pagetable(pagetable_ptr, Tracked(&mut *lctx));
    let ghost checked = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
    let (precheck, Ghost(found)) = mmap_4k_precheck(krnl, va_range, pagetable_ptr, Tracked(&*lctx), Tracked(&pagetable_lock_perm));
    let (ready, invalid) = match precheck { Mmap4kPrecheck::Ready => (true, false), Mmap4kPrecheck::Invalid => (false, true), Mmap4kPrecheck::InUse => (false, false) };
    if !ready {
        let ret = if invalid { RetValueType::Error } else { RetValueType::ErrorVaInUse };
        proof { mmap_4k_result_from_k(&old(steps).snapshot_k(), cpu_id, va, range, ret, if invalid { None } else { Some(checked) }, found); }
        krnl.wunlock_pagetable(pagetable_ptr, Tracked(&mut *lctx), Tracked(pagetable_lock_perm));
        krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
        krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
            assert(mmap_4k_syscall_failure_trace(steps.view(), cpu_id, va, range) && steps.view()[1].old_u == kernel_k_to_kernel_u(old(steps).snapshot_k())) by {
                kernel_cpu_thread_lock_states_changed_implies_u_step(&old(steps).snapshot_k(), &*krnl, &entry_lctx, cpu_id, thread_ptr, Some(pagetable_ptr));
                mmap_4k_release_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, thread_ptr);
                mmap_4k_trace_release_step(&*steps, old(steps).view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, va, range);
            };
        }
        return ret;
    }
    proof { mmap_4k_result_from_k(&old(steps).snapshot_k(), cpu_id, va, range, RetValueType::Success, Some(checked), None); }
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::Mmap4k { range: *va_range, mapped: 0, directory: Mmap4kDirectory::None, phase: Mmap4kPhase::Fill })),
        Tracked(&*lctx), Tracked(&thread_lock_perm));
    let ghost entered_k = *krnl;
    proof {
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        assert(mmap_4k_trace_after_enter(steps.view(), cpu_id, *va_range, Mmap4kPhase::Fill)) by {
            kernel_cpu_thread_pagetable_lock_states_and_progress_changed_implies_u_step(&old(steps).snapshot_k(), &entered_k, &entry_lctx, cpu_id, thread_ptr, process_ptr, pagetable_ptr);
            mmap_4k_enter_step_pre_from_k(&old(steps).snapshot_k(), cpu_id, process_ptr, thread_ptr);
            mmap_4k_enter_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(entered_k), cpu_id, process_ptr, thread_ptr, va, range, *va_range,
                Mmap4kPhase::Fill);
            mmap_4k_trace_enter_step(&*steps, old(steps).view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(entered_k), cpu_id, *va_range, Mmap4kPhase::Fill);
        };
        container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id);
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr);
    }
    let ghost entered = steps.view();
    let Tracked(existing_perms) = krnl.lock_pagetable_range_existing_windows(pagetable_ptr, va_range, Tracked(&pagetable_lock_perm), Tracked(&mut *lctx));
    proof { kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl); steps.rebase_snapshot_k_if_unchanged(&*krnl); cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); }
    let Tracked(window_perms) = mmap_4k_fill_range_structure(krnl, va_range, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, Tracked(&mut *lctx),
        Tracked(&mut *steps), Tracked(&thread_lock_perm), Tracked(&pagetable_lock_perm), Tracked(existing_perms));
    proof { krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); }
    let ghost filled_k = *krnl;
    let ghost filled_lctx = *lctx;
    let ghost filled_steps = steps.view();
    let Tracked(pagetable_read_perm) = krnl.downgrade_pagetable(pagetable_ptr, Tracked(&mut *lctx), Tracked(pagetable_lock_perm));
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::Mmap4k { range: *va_range, mapped: 0, directory: Mmap4kDirectory::None, phase: Mmap4kPhase::Filled })),
        Tracked(&*lctx), Tracked(&thread_lock_perm));
    let ghost downgraded_k = *krnl;
    proof {
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
        assert(downgraded_k.pt_lower.view() =~= filled_k.pt_lower.view().insert(pagetable_ptr, downgraded_k.pt_lower.view().spec_index(pagetable_ptr)));
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        kernel_pagetable_downgraded_and_progress_changed_implies_u_step(&filled_k, &downgraded_k, &filled_lctx, cpu_id, thread_ptr, process_ptr, pagetable_ptr);
        mmap_4k_downgrade_step_from_u(kernel_k_to_kernel_u(filled_k), kernel_k_to_kernel_u(downgraded_k), cpu_id, process_ptr, thread_ptr);
        mmap_4k_range_steps_from_downgrade(&*steps, filled_steps, entered.len() as int, cpu_id);
        container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id);
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr);
        broadcast use spec_va_2m_valid_index_roundtrip;
    }
    mmap_4k_map_leaves_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, va_range, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, pagetable_ptr,
        Ghost(Mmap4kPhase::Fill), Ghost(entered), Tracked(thread_lock_perm), Tracked(pagetable_read_perm), Tracked(cpu_lock_perm), Tracked(window_perms));
    RetValueType::Success
}
} // verus!
